//! Lisp evaluator.
//! 
//! This evaluator is based on bytecode. It has three stacks of state:
//! 
//! -   The _operation stack_. This is a native Rust stack of u8 opcodes.
//! -   The _operand stack_. This is a Lisp stack, represented by a pointer to its head.
//! -   The _environment stack_. This is a stack of _environments_. 
//!     (An _environment_ is a list of _bindings_, where a _binding_ is a symbol+value pair.)

use crate::data::{Ptr, Storage};

pub type Error = String;

enum Operation {}


pub struct EvalEnvironment<'a> {
    store: &'a Storage,

    operations: Vec<Operation>,
    operand: Ptr<'a>,
    environment: Ptr<'a>
}

impl EvalEnvironment<'_> {
    pub fn new<'a>(store: &'a Storage) -> EvalEnvironment<'a> {
        let e = EvalEnvironment{
            store,
            operations: Vec::with_capacity(0),
            operand: Ptr::nil(),
            environment: Ptr::nil(),
        };

        // TODO fill will builtins:

        e
    }
}

/// A Builtin is a function that acts directly on the evaluation environment.
pub type Builtin = fn(eval: &mut EvalEnvironment) -> Result<(), Error>;