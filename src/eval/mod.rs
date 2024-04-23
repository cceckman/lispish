//!Lisp evaluator.
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
use std::fmt::Display;
mod builtins;

#[cfg(feature = "web")]
mod render_eval;

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

enum Op {
    // Precondition: stack is (body, environment)
    EvalBody,
    // Preconditon: stack is (expression, environment)
    EvalExpr,
    // Precondition: stack is (value to be discarded).
    Discard,

    // After evaluating the first argument, deal with rest of the form based on the result.
    // Precondition: stack is (eval item, tail of expression, environment).
    EvalForm,

    // Add a variable to the provided environment.
    // Precondition: stack is (value, symbol, environment).
    Bind,
}

impl Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Op::EvalBody => "EvalBody",
                Op::EvalExpr => "EvalExpr",
                Op::Discard => "Discard",
                Op::EvalForm => "EvalForm",
                Op::Bind => "Bind",
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
        // TODO: I'm not sure this is accurate, or if there's another layer in there.
        let base_env = store.put(Pair::cons(base_frame, Ptr::nil()));

        // When idle, we only have the op-level environment stack.
        push(&store, base_env);
        EvalEnvironment {
            op_stack: Vec::new(),
            store,
        }
    }

    /// Start evaluating a new expression.
    ///
    /// This clears any state from any previous evaluations, effectivly cancelling them.
    /// Returns an error if the expression does not parse.
    pub fn start(&mut self, body: &str) -> Result<(), Error> {
        // To clean up an evaluation,
        // 1. Clear any operands:
        self.op_stack.clear();
        // 2. Walk back the top-level stack to the top-level env:
        // TODO: Allow eval-env to be in a "poison" state, instead of expecting here
        loop {
            let p = pop(&self.store).expect("corrupted stack");
            let Pair { cdr, .. } = get_pair(&self.store, p).expect("corrupted stack");
            if cdr.is_nil() {
                // Oops, we exhausted the stack. Push it back.
                // p is still valid - we haven't gc'd.
                push(&self.store, p);
                break;
            }
        }

        #[cfg(feature = "render")]
        {
            self.store().add_label(self.store().root(), "TOP ENV");
        }

        let body = match reader::parse_body(&self.store, body.as_bytes()) {
            Ok(ptr) => ptr,
            Err(e) => {
                self.store.gc();
                return Err(Error::UserError(format!("{e}")));
            }
        };

        #[cfg(feature = "render")]
        {
            self.store().add_label(body, "BODY");
        }

        // When idle, the top-level environment is the only thing on the stack.
        let top_env = match peek(&self.store) {
            Ok(env) => env,
            Err(e) => return Err(e),
        };

        // Eval-expression calls consume their environment.
        // To ensure we don't lose the top-level environment - that we wind up with "no results" -
        // ensure that the stack reads (body top top) to start off with.
        // When we complete evaluation, we'll have (result top)-
        // and can do a final pop of (result).
        push(&self.store, top_env);
        push(&self.store, body);

        #[cfg(feature = "render")]
        {
            self.store().add_label(self.store.root(), "STACK");
        }

        // We'll execute by evalling the body.
        self.op_stack.push(Op::EvalBody);

        // self.store.gc();
        Ok(())
    }

    pub fn store(&self) -> &Storage {
        &self.store
    }

    /// Retrieve the result of an evaluation, if complete.
    /// This is required as a separate method because `eval` and `step`
    /// wind up taking a mutable borrow, preventing retrieval of results.
    pub fn result(&self) -> Result<Object, Error> {
        if self.op_stack.is_empty() {
            Ok(self.store().get(peek(self.store())?))
        } else {
            Err(Error::Fault("retrieved result when not ready".to_string()))
        }
    }

    /// Evaluate until evaluation is complete, or an error is encountered.
    pub fn eval(&mut self) -> Result<(), Error> {
        while self.step()?.is_pending() {}
        Ok(())
    }

    /// Step forward: perform a single eval operation.
    pub fn step(&mut self) -> StepResult {
        let op = match self.op_stack.pop() {
            None => return Ok(Poll::Ready(())),
            Some(op) => op,
        };

        match op {
            Op::Discard => {
                // Simple enough:
                pop(&self.store)?;
            }
            Op::EvalBody => {
                // Pop twice: body, then environment.
                let body = pop(&self.store)?;
                let env = pop(&self.store)?;
                // Deconstruct the body:
                let Pair {
                    car: expression,
                    cdr: next,
                } = get_pair(&self.store, body)?;

                if !next.is_nil() {
                    // We'll need to continue evaluating the body,
                    // in this same environment.
                    push(&self.store, env);
                    push(&self.store, next);
                    self.op_stack.push(Op::EvalBody);
                    // ...but the evaluated value of this expression will be on the stack
                    // on top of them.
                    // So we'll need to discard that value, then evaluate.
                    self.op_stack.push(Op::Discard);
                }
                // Note this degenerates to "tail call":
                // the result of a body expression is evaluation of the final expression.

                // Evaluate this expression in this environment.
                push(&self.store, env);
                push(&self.store, expression);
                self.op_stack.push(Op::EvalExpr);
            }
            Op::EvalExpr => {
                // Pop twice: expression, then environment.
                let expr = pop(&self.store)?;
                let env = pop(&self.store)?;

                match self.store.get(expr) {
                    Object::Symbol(_) => {
                        // Walk the environment tree to find the location.
                        let loc = get_location(&self.store, expr, env)?;
                        // In this case, what we want is the stored value.
                        let pair = get_pair(&self.store, loc)?;
                        push(&self.store, pair.cdr);
                    }
                    Object::Pair(Pair { car, cdr }) => {
                        // Prepare "apply the form":
                        push(&self.store, env);
                        push(&self.store, cdr);
                        // But first, we need to work out what the first argument is-
                        // function or builtin, hopefully.
                        self.op_stack.push(Op::EvalForm);
                        // But we need to evaluate the first item first.
                        push(&self.store, env);
                        push(&self.store, car);
                        self.op_stack.push(Op::EvalExpr);
                    }
                    // All other types evaluate to themselves.
                    _ => {
                        push(&self.store, expr);
                    }
                }
            }
            Op::EvalForm => {
                // Stack is (applicator, tail of expr, environment).
                let applicator = pop(&self.store)?;
                // Stack is (args, environment).
                // What do we need to do with them?
                match self.store.get(applicator) {
                    Object::Builtin(f) => f(self)?,
                    // TODO: Apply function
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
        }
        Ok(Poll::Pending)
    }
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
    use crate::data::Object;

    use super::EvalEnvironment;

    #[test]
    fn int_eval() {
        let mut eval = EvalEnvironment::new();
        eval.start("1 2 3").unwrap();
        eval.eval().unwrap();

        match eval.result().unwrap() {
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
        eval.eval().unwrap();

        match eval.result().unwrap() {
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
    fn symbol_eval() {
        // TODO: This is a hack for testing.
        let mut eval = EvalEnvironment::new();
        eval.start(r#"(one)"#).unwrap();
        eval.eval().unwrap();

        match eval.result().unwrap() {
            Object::Integer(1) => (),
            v => panic!("unexpected result: {v:?}"),
        };
    }

    #[test]
    fn define_int_value_and_retrieve() {
        // TODO: This is a hack for testing.
        let mut eval = EvalEnvironment::new();
        eval.start(
            r#"
        (define a 7)
        (define b a)
        b
        "#,
        )
        .unwrap();
        eval.eval().unwrap();

        match eval.result().unwrap() {
            Object::Integer(7) => (),
            v => panic!("unexpected result: {v:?}"),
        };
    }
}
