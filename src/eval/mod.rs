//! Lisp evaluator.
//!
//! This evaluator is based on bytecode. It has three stacks of state:
//!
//! -   The _operation stack_. This is a native Rust stack of u8 opcodes.
//! -   The _operand stack_. This is a Lisp stack, represented by a pointer to its head.
//! -   The _environment stack_. This is a stack of _environments_.
//!     (An _environment_ is a list of _bindings_, where a _binding_ is a symbol+value pair.)

use crate::{
    data::{Object, Pair, Ptr, Storage},
    reader::{self},
};
use core::task::Poll;
use std::{borrow::Borrow, fmt::Display};

use self::builtins::STDLIB;
mod builtins;

#[cfg(feature = "web")]
mod render_eval;

#[cfg(test)]
mod stdlib_test;

/// Result from a single-step:
/// - An error
/// - Execution is not complete
/// - Execution is complete. The result must be retrieved separately
///     (to avoid capturing a mutable borrow of the storage).
pub type StepResult = Result<Poll<()>, Error>;

#[derive(Debug, Clone)]
pub enum Error {
    /// An error in the evaluated program's semantics.
    UserError(String),
    /// An unexpected condition in the interpreter.
    Fault(String),
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UserError(e) => write!(f, "user error in evaluation: {e}"),
            Self::Fault(e) => write!(f, "system error in evaluation: {e}"),
        }
    }
}

impl<T> From<Error> for Result<T, Error> {
    fn from(err: Error) -> Self {
        Err(err)
    }
}

// Helper trait to conveniently tell a user its their part.
trait ToUserError {
    type T;
    fn to_user_error(self, msg: impl AsRef<str>) -> Result<Self::T, Error>;
}

impl<T, E> ToUserError for Result<T, E> {
    type T = T;
    fn to_user_error(self, msg: impl AsRef<str>) -> Result<T, Error> {
        match self {
            Ok(v) => Ok(v),
            Err(_) => Err(Error::UserError(msg.as_ref().to_owned())),
        }
    }
}

enum Op {
    // Evaluate each of the expressions in the body,
    // discarding the results of all but the last after evaluation.
    // Precondition: stack is (environment, body)
    // Postcondition: stack is (value)
    EvalBody,
    // Evaluate a single expression.
    // Preconditon: stack is (environment, expresion)
    // Postcondition: stack is (value)
    EvalExpr,
    // Evaluate each expression in the body and accumulate them into a list,
    // in the same order.
    // Precondition: stack is (accumulator, environment, body);
    // accumulator must be a pointer to a cons cell, _not_ nil.
    // Postcondition: empty stack. Caller should Cdr the original accumulator value.
    EvalList,

    // After evaluating the first argument, deal with rest of the form based on the result.
    // Precondition: stack is (eval item, environment, tail of expression).
    // Postcondition: stack is (value) of evaluating the form.
    EvalForm,

    // Depending on the value of the predicate, evaluate either the positive expression or the
    // negative expression.
    // Precondition: stack is (predicate, environment, positive expression, negative expresson).
    // Postcondition: stack is (value) of evaluating the form.
    EvalCond,

    // Append the expression on the top of the stack to the end of an accumulator.
    // Evaluates to the new tail.
    // Precondition: stack is (expression, accumulator)
    // Postcondition: stack is (new accumulator tail)
    Append,
    // Precondition: stack is (value to be discarded).
    // Postcondition: empty stack.
    Discard,
    // Discard the head of the list at the top of the stack.
    // Precondition: stack is (cons cell).
    // Postcondition: stack is (cdr of that cell).
    Cdr,

    // Add a variable to the provided environment.
    // Precondition: stack is (value, symbol, environment).
    // Postcondition: symbol.
    Bind,

    // Replace a variable to the provided environment.
    // Precondition: stack is (value, symbol, environment).
    // Postcondition: symbol.
    Set,

    // Bind a list of symbols and a list of values into a target environment.
    // Precondition: stack is (values, symbols, environment).
    // Postcondition: stack is (environment)
    BindArgs,
}

impl Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Op::EvalBody => "EvalBody",
                Op::EvalExpr => "EvalExpr",
                Op::EvalList => "EvalList",
                Op::EvalForm => "EvalForm",
                Op::EvalCond => "EvalCond",
                Op::Append => "Append",
                Op::Discard => "Discard",
                Op::Cdr => "Cdr",
                Op::Bind => "Bind",
                Op::Set => "Set",
                Op::BindArgs => "BindArgs",
            }
        )
    }
}

/// Environment for an in-progress evaluation.
pub struct EvalEnvironment {
    op_stack: Vec<Op>,
    store: Storage,
}

impl Default for EvalEnvironment {
    fn default() -> EvalEnvironment {
        EvalEnvironment::new()
    }
}

impl EvalEnvironment {
    /// Initialize an empty Storage for evaluation:
    /// Load builtins, the standard environment, and the top-level environment.
    /// Creates the initial operand stack.
    pub fn new() -> EvalEnvironment {
        let store = Storage::default();
        // A frame is a list of bindings.
        // Frames are mutable.
        let mut base_frame = Ptr::nil();

        for (name, builtin) in builtins::BUILTINS {
            let symbol = store.put_symbol(name);
            let builtin = store.put(*builtin);

            // A binding is a symbol, value pair.
            // Bindings are mutable.
            let binding = store.put(Pair::cons(symbol, builtin));
            base_frame = store.put(Pair::cons(binding, base_frame));
        }

        // An environment is a list of frames.
        // TODO: I'm not sure this is accurate, or if we should consider it something different.
        let base_env = store.put(Pair::cons(base_frame, Ptr::nil()));

        // When idle, we only have the op-level environment stack.
        push(&store, base_env);
        let mut env = EvalEnvironment {
            op_stack: Vec::new(),
            store,
        };

        // TODO: Split into multiple environments-
        // - the top-level (user) environment,
        // - the builtin/stdlib envionment,
        // - the system/masked environment (which stdlib may capture but not extend)
        env.start(STDLIB)
            .expect("stdlib does not parse")
            .eval()
            .expect("stdlib execution should always succeed");

        // Discard the stdlib evaluation:
        pop(&env.store).expect("could not recover from stdlib setup");

        #[cfg(feature = "render")]
        {
            let Pair { car: base_env, .. } =
                get_pair(&env.store, env.store.root()).expect("stack top is not a pair");
            env.store.format(env.store.root()).label = "Bottom of operand stack".to_string();
            env.store.format(base_env).label = "Top-level Environment".to_string();
        }

        env
    }

    /// Start evaluating a new expression.
    ///
    /// This clears any state from any previous evaluations, effectivly cancelling them.
    /// Returns an error if the expression does not parse.
    pub fn start(&mut self, body: &str) -> Result<&mut Self, Error> {
        // To clean up an evaluation,
        // 1. Clear any operands:
        self.op_stack.clear();

        // 2. Walk back the top-level stack to the top-level env:
        loop {
            // TODO: "stack iterator" / "list iterator" in Rust?
            // TODO: Allow eval-env to be in a "poison" state, instead of expecting here
            let Pair { cdr, .. } = get_pair(&self.store, self.store.root()).unwrap();
            if cdr.is_nil() {
                // This is the top-level environment.
                break;
            }
            self.store.set_root(cdr);
        }

        let body = match reader::parse_body(&self.store, body.as_bytes()) {
            Ok(ptr) => ptr,
            Err(e) => {
                return Err(Error::UserError(format!("{e}")));
            }
        };
        // TODO: Currently "empty list", i.e. empty input, comes up as "system error".
        // That's not right; it should come up as "need more input"...right?

        // When idle, the top-level environment is the only thing on the stack.
        let top_env = peek(&self.store)?;

        // Eval-expression calls consume their environment.
        // To ensure we don't lose the top-level environment - that we wind up with "no results" -
        // ensure that the stack reads (top body top) to start off with.
        // When we complete evaluation, we'll have (result top)-
        // and can do a final pop of (result).
        push(&self.store, body);
        push(&self.store, top_env);

        // We'll execute by evalling the body.
        self.op_stack.push(Op::EvalBody);

        Ok(self)
    }

    pub fn store(&self) -> &Storage {
        &self.store
    }

    /// Perform garbage collection on storage.
    pub fn gc(&mut self) {
        self.store.gc()
    }

    /// Retrieve a pointer to the result of an evaluation, if complete.
    /// This is required as a separate method because `eval` and `step`
    /// wind up taking a mutable borrow, preventing retrieval of results.
    pub fn result_ptr(&self) -> Result<Ptr, Error> {
        if self.op_stack.is_empty() {
            peek(&self.store)
        } else {
            Err(Error::Fault("retrieved result when not ready".to_string()))
        }
    }

    /// Retrieve the result of an evaluation, if complete.
    /// This is required as a separate method because `eval` and `step`
    /// wind up taking a mutable borrow, preventing retrieval of results.
    pub fn result(&self) -> Result<Object, Error> {
        if self.op_stack.is_empty() {
            Ok(self.store.get(peek(&self.store)?))
        } else {
            Err(Error::Fault("retrieved result when not ready".to_string()))
        }
    }

    /// Evaluate until evaluation is complete, or an error is encountered.
    pub fn eval(&mut self) -> Result<Object, Error> {
        while self.step()?.is_pending() {}
        self.result()
    }

    /// Step forward: perform a single eval operation.
    pub fn step(&mut self) -> StepResult {
        let op = match self.op_stack.pop() {
            None => return Ok(Poll::Ready(())),
            Some(op) => op,
        };

        match op {
            Op::EvalBody => {
                // Pop twice: environment, then body.
                let env = pop(&self.store)?;
                let body = pop(&self.store)?;

                // An empty body is invalid.
                if body.is_nil() {
                    Err(Error::UserError(
                        "empty body cannot be evaluated".to_string(),
                    ))?;
                }

                // Deconstruct the body:
                let Pair {
                    car: expression,
                    cdr: next,
                } = get_pair(&self.store, body)?;

                if !next.is_nil() {
                    // We'll need to continue evaluating the body,
                    // in this same environment.
                    push(&self.store, next);
                    push(&self.store, env);
                    self.op_stack.push(Op::EvalBody);
                    // ...but the evaluated value of this expression will be on the stack
                    // on top of them.
                    // So we'll need to discard that value, then evaluate.
                    self.op_stack.push(Op::Discard);
                }
                // Note this degenerates to "tail call":
                // the result of a body expression is evaluation of the final expression.

                // Evaluate this expression in this environment.
                push(&self.store, expression);
                push(&self.store, env);
                self.op_stack.push(Op::EvalExpr);
            }
            Op::EvalExpr => {
                // Pop twice: environment, then expression.
                let env = pop(&self.store)?;
                let expr = pop(&self.store)?;

                match self.store.get(expr) {
                    Object::Symbol(_) => {
                        // Walk the environment tree to find the location.
                        let v = get_value(&self.store, expr, env)?;
                        push(&self.store, v);
                    }
                    Object::Pair(Pair { car, cdr }) => {
                        // Prepare "apply the form":
                        push(&self.store, cdr);
                        push(&self.store, env);
                        // But first, we need to work out what the first argument is-
                        // function or builtin, hopefully.
                        self.op_stack.push(Op::EvalForm);
                        // But we need to evaluate the first item first.
                        push(&self.store, car);
                        push(&self.store, env);
                        self.op_stack.push(Op::EvalExpr);
                    }
                    // All other types evaluate to themselves.
                    _ => {
                        push(&self.store, expr);
                    }
                }
            }
            Op::EvalList => {
                let accumulator = pop(&self.store)?;
                let env = pop(&self.store)?;
                let body = pop(&self.store)?;
                match self.store.get(body) {
                    Object::Pair(Pair {
                        car: expr,
                        cdr: next,
                    }) => {
                        // Chain to the next op.
                        // For EvalList:
                        push(&self.store, next);
                        push(&self.store, env);
                        // For Append:
                        push(&self.store, accumulator);
                        // For EvalExpr:
                        push(&self.store, expr);
                        push(&self.store, env);
                        self.op_stack.push(Op::EvalList);
                        self.op_stack.push(Op::Append);
                        self.op_stack.push(Op::EvalExpr);
                    }
                    // Caller should have the head of the accumulate list.
                    // Let them pop it in the next op.
                    // TODO: Do that here, get rid of cdr.
                    Object::Nil => (),
                    _ => return Err(Error::Fault("EvalList with non-list body".to_string())),
                }
            }
            Op::EvalCond => {
                let predicate = pop(&self.store)?;
                let env = pop(&self.store)?;
                let pos = pop(&self.store)?;
                let neg = pop(&self.store)?;

                let t = self.store.put_symbol("#t");
                let f = self.store.put_symbol("#f");
                match predicate {
                    x if x == t => push(&self.store, pos),
                    x if x == f => push(&self.store, neg),
                    v => {
                        return Err(Error::UserError(format!(
                            "if predicate is not #t or #f: {v}"
                        )))
                    }
                }
                push(&self.store, env);
                self.op_stack.push(Op::EvalExpr);
            }
            Op::Append => {
                let expr = pop(&self.store)?;
                let cell = pop(&self.store)?;
                let pair = get_pair(&self.store, cell)?;
                if !pair.cdr.is_nil() {
                    return Err(Error::Fault("Append cell is not tail of list".to_string()));
                }
                let next = self.store.put(Pair {
                    car: expr,
                    cdr: Ptr::nil(),
                });
                self.store.update(
                    cell,
                    Pair {
                        car: pair.car,
                        cdr: next,
                    },
                );
                push(&self.store, next);
            }
            Op::Discard => {
                // Simple enough:
                pop(&self.store)?;
            }
            Op::Cdr => {
                let cell = pop(&self.store)?;
                let Pair { cdr, .. } = get_pair(&self.store, cell)?;
                push(&self.store, cdr);
            }
            Op::EvalForm => {
                // Stack is (applicator, environment, tail of expression).
                let applicator = pop(&self.store)?;
                // Stack is (args, environment).
                // What do we need to do with them?
                match self.store.get(applicator) {
                    Object::Builtin(f) => f(self)?,
                    Object::Function(f) => {
                        call(&mut self.op_stack, &self.store, f)?;
                    }
                    _ => {
                        return Err(Error::UserError(format!(
                            "object {applicator} is not applicable"
                        )))
                    }
                }
            }
            Op::Bind => {
                let value = pop(&self.store)?;
                let symbol = pop(&self.store)?;
                let environment = pop(&self.store)?;
                assert!(symbol.is_symbol());
                assert!(environment.is_pair());

                // TODO: Consider generating an error for re-definition,
                // instead of this (inefficient) overwriting.

                // Environment is a stack of frames, which is a stack of bindings.
                let frame: Ptr;
                let next_frame: Ptr;
                Pair {
                    car: frame,
                    cdr: next_frame,
                } = get_pair(&self.store, environment)?;
                let binding = self.store.put(Pair::cons(symbol, value));
                let new_frame = self.store.put(Pair::cons(binding, frame));
                // Update the frame in-place within the environment.
                self.store
                    .update(environment, Pair::cons(new_frame, next_frame));
                // TODO: We're treating define as an expression; that means it has to return a
                // value, even if it gets Discarded by a body.
                push(&self.store, symbol);
            }
            Op::Set => {
                let value = pop(&self.store)?;
                let symbol = pop(&self.store)?;
                let environment = pop(&self.store)?;
                assert!(symbol.is_symbol());
                assert!(environment.is_pair());

                let loc = get_location(&self.store, symbol, environment).to_user_error(format!(
                    "no existing binding for symbol {}",
                    self.store.display(self.store.get(symbol))
                ))?;
                // Update the binding in-place in the environment.
                self.store.update(loc, Pair::cons(symbol, value));
                // TODO: We're treating define / set / bind as an expression; that means it has to return a
                // value, even if it gets Discarded by a body.
                push(&self.store, symbol);
            }
            Op::BindArgs => {
                let values = pop(&self.store)?;
                let symbols = pop(&self.store)?;
                // Note: Leaving the environment on the stack, it's also our return value.
                let environment = peek(&self.store)?;

                // End of arg list.
                if symbols.is_nil() {
                    if !values.is_nil() {
                        return Err(Error::UserError("too many arguments".to_string()));
                    }
                } else {
                    let Pair {
                        car: sym,
                        cdr: next_symbols,
                    } = get_pair(&self.store, symbols)?;

                    // Check for the special-case: is there a "rest" argument?
                    if sym == self.store.put_symbol(".") {
                        // Bind "values" to the next, final argument.
                        let Pair {
                            car: rest,
                            cdr: nil_tail,
                        } = get_pair(&self.store, next_symbols)?;
                        if !rest.is_symbol() {
                            return Err(Error::UserError(format!(
                                "{} is not an acceptable rest parameter",
                                self.store.display(self.store.get(rest))
                            )));
                        }
                        if !nil_tail.is_nil() {
                            return Err(Error::UserError(format!(
                                "{} cannot be used after rest parameter",
                                self.store.display(self.store.get(nil_tail))
                            )));
                        }
                        // OK, have sane arguments. Bind once, with "the rest":
                        push(&self.store, environment);
                        push(&self.store, rest);
                        push(&self.store, values);
                    } else {
                        let Pair {
                            car: value,
                            cdr: next_values,
                        } = get_pair(&self.store, values).to_user_error("not enough parameters")?;
                        // Prepare the next BindArgs.
                        // Environment is already on the stack:
                        push(&self.store, next_symbols);
                        push(&self.store, next_values);
                        // Prepare Bind.
                        push(&self.store, environment);
                        push(&self.store, sym);
                        push(&self.store, value);
                        // Recurse to the rest of the list.
                        self.op_stack.push(Op::BindArgs);
                    }
                    // Bind leaves the symbol on the stack, which isn't necessary for args.
                    // Discard the symbol after binding.
                    self.op_stack.push(Op::Discard);
                    self.op_stack.push(Op::Bind);
                }
            }
        }
        Ok(Poll::Pending)
    }

    pub fn label(&self, object_id: &str, format: &str) -> Result<(), Error> {
        let store = self.store.borrow();
        let ptr = store
            .lookup(object_id)
            .to_user_error(format!("object {} does not exist", object_id))?;
        store.format(ptr).label = format.to_owned();
        Ok(())
    }
}

fn call(ops: &mut Vec<Op>, store: &Storage, function: Pair) -> Result<(), Error> {
    let arg_env = pop(store)?;
    let args = pop(store)?;
    // Deconstruct the function into its components:
    let Pair {
        car: lex_env,
        cdr: fn_tail,
    } = function;
    let Pair {
        car: parameters,
        cdr: body,
    } = get_pair(store, fn_tail)?;

    // The last thing we do is evaluate the body in the "eval" environment.
    ops.push(Op::EvalBody);
    push(&store, body);
    let new_env = store.put(Pair::cons(Ptr::nil(), lex_env));
    push(&store, new_env);
    // Before that, we need to fill the "eval" environment.
    // It's already in the right place on the stack, and will be conserved;
    // push the op and the symbols:
    ops.push(Op::BindArgs);
    push(store, parameters);

    // But we need to evaluate the list.
    // That's relatively complicated, so use the helper:
    eval_list(ops, store, args, arg_env)
}

/// Evaluate each item in the list, using the provided environment.
fn eval_list(ops: &mut Vec<Op>, store: &Storage, list: Ptr, env: Ptr) -> Result<(), Error> {
    // Create a "nil head" to accumulate into.
    // This will be our result later, after a Cdr op:
    let nil_head = store.put(Pair::cons(Ptr::nil(), Ptr::nil()));
    push(store, nil_head);

    // We need to evaluate each list item:
    push(store, list);
    push(store, env);
    // Note that here, nil_head is the list _tail_;
    // above, it's the list _head_.
    push(store, nil_head);

    // Push the ops in reverse order - "cleanup" then "eval":
    ops.push(Op::Cdr);
    ops.push(Op::EvalList);

    Ok(())
}

/// Retrieve the pointer as a pair, or return a program error.
fn get_pair<'a>(store: &'a Storage, p: Ptr<'a>) -> Result<Pair<'a>, Error> {
    if let Object::Pair(p) = store.get(p) {
        Ok(p)
    } else {
        Error::Fault(format!("object {p} is not a pair")).into()
    }
}

/// Get the location for a symbol.
/// The result is a pointer to the binding (symbol, value pair).
fn get_location<'a>(
    store: &'a Storage,
    symbol: Ptr<'a>,
    mut environment: Ptr<'a>,
) -> Result<Ptr<'a>, Error> {
    assert!(symbol.is_symbol(), "pointer is: {}", symbol);
    // Environment is a stack of frames, which is a stack of bindings.
    while !environment.is_nil() {
        let mut frame: Ptr<'a>;
        Pair {
            car: frame,
            cdr: environment,
        } = get_pair(store, environment)?;

        while !frame.is_nil() {
            let binding: Ptr<'a>;
            Pair {
                car: binding,
                cdr: frame,
            } = get_pair(store, frame)?;
            let Pair {
                car: got_symbol, ..
            } = get_pair(store, binding)?;
            if got_symbol == symbol {
                return Ok(binding);
            }
        }
    }

    Err(Error::UserError(format!(
        "could not resolve symbol: {}",
        store.get_symbol_ptr(symbol)
    )))
}

/// Get the value of a symbol.
fn get_value<'a>(
    store: &'a Storage,
    symbol: Ptr<'a>,
    environment: Ptr<'a>,
) -> Result<Ptr<'a>, Error> {
    let Pair { cdr: value, .. } = get_pair(store, get_location(store, symbol, environment)?)?;
    Ok(value)
}

fn push(store: &Storage, p: Ptr) {
    let old_top = store.root();
    let new_top = store.put(Pair::cons(p, old_top));
    store.set_root(new_top);
}

/// Pop an element from the op of the operand stack.
fn pop(store: &Storage) -> Result<Ptr, Error> {
    let old_top = store.root();
    let old_obj = store.get(old_top);
    match old_obj {
        Object::Nil => Ok(Ptr::nil()),
        Object::Pair(Pair { car, cdr }) => {
            store.set_root(cdr);
            Ok(car)
        }
        _ => Error::Fault(format!("stack-top is not a pair: pointer {old_top}")).into(),
    }
}

/// Peek at the element at the top of the operand stack.
fn peek(store: &Storage) -> Result<Ptr, Error> {
    let old_top = store.root();
    let old_obj = store.get(old_top);
    match old_obj {
        Object::Nil => Ok(Ptr::nil()),
        Object::Pair(Pair { car, .. }) => Ok(car),
        _ => Error::Fault(format!("stack-top is not a pair: pointer {old_top}")).into(),
    }
}

/// A Builtin
/// Precondition on call: stack is (tail of expression, env).
pub type Builtin = fn(&mut EvalEnvironment) -> Result<(), Error>;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::Object;

    #[test]
    fn int_eval() {
        let mut eval = EvalEnvironment::new();
        eval.start("1 2 3").unwrap();

        match eval.eval().unwrap() {
            Object::Integer(3) => (),
            v => panic!("unexpected result: {v:?}"),
        };
    }

    #[test]
    fn float_eval() {
        let mut eval = EvalEnvironment::new();
        eval.start("3.5 -3.143").unwrap();
        eval.eval().unwrap();

        match eval.result().unwrap() {
            Object::Float(v) => assert!(
                f64::abs(-3.143f64 - v) < 0.000001,
                "unexpected float value: {v}"
            ),
            v => panic!("unexpected result: {v:?}"),
        };
    }

    #[test]
    fn string_eval() {
        let mut eval = EvalEnvironment::new();
        eval.start(r#"1 "hello" "world""#).unwrap();
        eval.eval().unwrap();

        match eval.result().unwrap() {
            Object::String(x) => assert_eq!(eval.store().get_string(&x).as_ref(), b"world"),
            v => panic!("unexpected result: {v:?}"),
        };
    }

    #[test]
    fn eval_nil() {
        let mut eval = EvalEnvironment::new();
        eval.start(r#"()"#).unwrap();

        match eval.eval().unwrap() {
            Object::Nil => (),
            v => panic!("unexpected result: {v:?}"),
        };
    }

    #[test]
    fn cannot_apply_number() {
        let mut eval = EvalEnvironment::new();
        eval.start(r#"(1)"#).unwrap();
        let result = eval.eval();
        match result {
            Err(super::Error::UserError(_)) => (),
            _ => panic!("unexpected result: {:?}", result),
        }
    }

    #[test]
    fn restart() {
        let mut eval = EvalEnvironment::new();
        eval.start("1 2 3").unwrap();
        match eval.eval().unwrap() {
            Object::Integer(3) => (),
            v => panic!("unexpected result: {v:?}"),
        };

        eval.start("2 3 4").unwrap();
        match eval.eval().unwrap() {
            Object::Integer(4) => (),
            v => panic!("unexpected result: {v:?}"),
        };
    }

    #[test]
    fn require_all_args() {
        let mut eval = EvalEnvironment::new();
        const TEXT: &str = r#"
            (define foo (lambda (a b) a))
            (foo 1)
        "#;
        eval.start(TEXT)
            .unwrap()
            .eval()
            .expect_err("should complain about missing args");
    }

    #[test]
    fn require_only_args() {
        let mut eval = EvalEnvironment::new();
        const TEXT: &str = r#"
            (define foo (lambda (a b) a))
            (foo 1 2 3)
        "#;
        eval.start(TEXT)
            .unwrap()
            .eval()
            .expect_err("should complain about too many args");
    }
}
