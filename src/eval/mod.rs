//! Lisp evaluator.
//! 
//! This evaluator is based on bytecode. It has three stacks of state:
//! 
//! -   The _operation stack_. This is a native Rust stack of u8 opcodes.
//! -   The _operand stack_. This is a Lisp stack, represented by a pointer to its head.
//! -   The _environment stack_. This is a stack of _environments_. 
//!     (An _environment_ is a list of _bindings_, where a _binding_ is a symbol+value pair.)

use crate::data::{Pair, Ptr, Storage};

pub type Error = String;

const BUILTINS : &[(&str, Builtin)] = &[
    ("+", builtin_add),
];


/// Declare the base environment (builtins and their symbols)
/// and return the environment stack.
pub fn create_env_stack<'a>(store: &'a Storage) -> Ptr<'a> {
    // An environment is a list of bindings.
    let mut base_environment = Ptr::nil();

    for (name, builtin) in BUILTINS {
        let symbol = store.put_symbol(name);
        let builtin = store.put(*builtin);

        // A binding is a symbol, value pair.
        let binding = store.put(Pair::cons(symbol, builtin));
        base_environment = store.put(Pair::cons(binding, base_environment));
    }

    // The environment stack is a list of environments.
    // The last of those is the base environment.
    let env_stack = store.put(Pair::cons(base_environment, Ptr::nil()));
    // But we start with an empty environment on top of that- the "top level" one.
    let top_env = Ptr::nil();
    store.put(Pair::cons(top_env, env_stack))
}

pub struct EvalEnvironment { }

/// A Builtin is a function that acts directly on the evaluation environment.
pub type Builtin = fn(eval: &mut EvalEnvironment) -> Result<(), Error>;

fn builtin_add(_eval: &mut EvalEnvironment) -> Result<(), Error> {
    Err("builtin_add is unimplemented".to_string())    
}