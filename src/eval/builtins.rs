use super::{pop, push, Builtin, Error, EvalEnvironment};

pub const MASKED_BUILTINS: &[(&str, Builtin)] = &[("builtin:add", builtin_unimplemented)];

/// These could also be called "keywords".
/// We evaluate them by first selecting "is this thing a function or a builtin",
/// then dispatching the builtins with more context.
///
/// This means you _could_ do evil things like redefining "define"!
/// Don't do that, though, please.
pub const BUILTINS: &[(&str, Builtin)] = &[
    ("define", builtin_unimplemented),
    ("lambda", builtin_unimplemented),
    ("if", builtin_unimplemented),
    ("else", builtin_unimplemented),
    // TODO: This is "just" for testing.
    ("one", builtin_one),
];

fn builtin_unimplemented(_eval: &mut EvalEnvironment) -> Result<(), Error> {
    Error::Fault("haven't implemented add".to_string()).into()
}

/// The `one` builtin: evaluate to 1.
fn builtin_one(eval: &mut EvalEnvironment) -> Result<(), Error> {
    let _args = pop(eval.store())?;
    let _eval = pop(eval.store())?;
    push(eval.store(), eval.store().put(1i64));
    Ok(())
}
