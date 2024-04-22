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
use std::fmt::Display;

/// Result from a single-step:
/// - An error
/// - Execution is not complete
/// - Execution is complete - and here's the result.
pub type StepResult<'a> = Result<Poll<Ptr<'a>>, Error>;

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

const BUILTINS: &[(&str, Builtin)] = &[("+", builtin_add)];

/// Initialize an empty Storage for evaluation:
/// Load builtins, the standard environment, and the top-level environment.
/// Creates the initial operand stack.
pub fn initialize(store: &Storage) {
    // A frame is a list of bindings.
    // Frames are mutable.
    let mut base_frame = Ptr::nil();

    for (name, builtin) in BUILTINS {
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

    // The initial operand stack consists (only) of the environment.
    push(store, base_env);
}

enum Op {
    // Precondition: stack is (body, environment)
    EvalBody,
    // Preconditon: stack is (expression, environment)
    EvalExpr,
}

/// Environment for an in-progress evaluation.
pub struct EvalEnvironment {
    op_stack: Vec<Op>,
    store: Storage,
}

impl EvalEnvironment {
    /// If evaluation is complete, return to the idle state.
    pub fn idle(self) -> Result<Storage, (Self, Error)> {
        if self.op_stack.is_empty() {
            // Consume the top-of-stack, which is the result of the top-level 'body'
            // evaluation.
            match pop(&self.store) {
                Ok(_) => (),
                Err(e) => return Err((self, e)),
            };
            Ok(self.store)
        } else {
            Err((
                self,
                Error::Fault("returning to idle but execution is not complete".to_string()),
            ))
        }
    }

    /// Set up environment and start evaluation.
    /// Returns an error (and storage) if the expression does not parse.
    pub fn start(mut store: Storage, body: &str) -> Result<EvalEnvironment, (Storage, Error)> {
        let body = match reader::parse_body(&store, body.as_bytes()) {
            Ok(ptr) => ptr,
            Err(e) => {
                store.gc();
                return Err((store, Error::UserError(format!("{e}"))));
            }
        };
        // When idle, the top-level environment is the only thing on the stack.
        let top_env = match peek(&store) {
            Ok(env) => env,
            Err(e) => return Err((store, e)),
        };

        // Eval-expression calls consume their environment.
        // To ensure we don't lose the top-level environment - that we wind up with "no results" -
        // ensure that the stack reads (body top top) to start off with.
        // When we complete evaluation, we'll have (result top)-
        // and can do a final pop of (result).
        push(&store, top_env);
        push(&store, body);

        let mut eval = EvalEnvironment {
            store,
            op_stack: Vec::new(),
        };

        // We'll execute by evalling the body.
        eval.op_stack.push(Op::EvalBody);

        eval.store.gc();
        Ok(eval)
    }

    /// Step forward: perform a single eval operation.
    pub fn step(&mut self) -> StepResult {
        let op = match self.op_stack.pop() {
            None => return Ok(Poll::Ready(peek(&self.store)?)),
            Some(op) => op,
        };

        match op {
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
                    push(&self.store, body);
                    self.op_stack.push(Op::EvalBody);
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
                let _env = pop(&self.store)?;

                match self.store.get(expr) {
                    Object::Nil | Object::Integer(_) | Object::Float(_) | Object::String(_) => {
                        // Literals evaluate to themselves.
                        push(&self.store, expr);
                    }
                    Object::Symbol(_) => {
                        todo!()
                    }
                    Object::Builtin(_) => {
                        todo!()
                    }
                    Object::Pair(_) => {
                        todo!()
                    }
                }
            }
        }
        Ok(Poll::Pending)
    }

    pub fn store(&self) -> &Storage {
        &self.store
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

pub type Builtin = fn(&mut EvalEnvironment) -> Result<(), Error>;

fn builtin_add(_eval: &mut EvalEnvironment) -> Result<(), Error> {
    Error::Fault("haven't implemented add".to_string()).into()
}
