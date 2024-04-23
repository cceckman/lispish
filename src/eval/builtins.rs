use crate::eval::{get_pair, pop, push, Builtin, Error, EvalEnvironment, Op};

use crate::data::{Pair, Ptr};

pub const MASKED_BUILTINS: &[(&str, Builtin)] = &[("builtin:add", builtin_unimplemented)];

/// These could also be called "keywords".
/// We evaluate them by first selecting "is this thing a function or a builtin",
/// then dispatching the builtins with more context.
///
/// This means you _could_ do evil things like redefining "define"!
/// Don't do that, though, please.
pub const BUILTINS: &[(&str, Builtin)] = &[
    ("define", builtin_define),
    ("lambda", builtin_unimplemented),
    ("if", builtin_unimplemented),
    ("cond", builtin_unimplemented),
    ("quote", builtin_unimplemented),
    ("apply", builtin_unimplemented),
    // TODO: This is "just" for testing.
    ("one", builtin_one),
];

fn builtin_unimplemented(_eval: &mut EvalEnvironment) -> Result<(), Error> {
    Error::Fault("haven't implemented this builtin".to_string()).into()
}

/// The `one` builtin: evaluate to 1.
fn builtin_one(eval: &mut EvalEnvironment) -> Result<(), Error> {
    let _args = pop(eval.store())?;
    let _env = pop(eval.store())?;
    push(eval.store(), eval.store().put(1i64));
    Ok(())
}

fn builtin_define(eval: &mut EvalEnvironment) -> Result<(), Error> {
    let args = pop(eval.store())?; // 35
    let env = pop(eval.store())?; // 34

    // Are we defining a function or a variable?
    let binding: Ptr<'_>;
    let body: Ptr<'_>;

    Pair {
        car: binding,
        cdr: body,
    } = match get_pair(eval.store(), args) {
        Ok(v) => v,
        // TODO: A nice error capability would be to be able to mark nodes as "in error" and
        // treat them as additional roots, until the next start call.
        Err(_) => {
            return Err(Error::UserError(format!(
                "define statement is missing body; got {} instead of body",
                args
            )))
        }
    };

    if binding.is_pair() {
        return Err(Error::Fault(
            "function definition is not yet implemented".to_string(),
        ));
    }

    if binding.is_symbol() {
        // Variable binding. We'll add to the current environment:
        push(eval.store(), env);
        push(eval.store(), binding);
        // After evaluating the body- which must be a single expression,
        // but which is _represented as a body.
        let Pair {
            car: value,
            cdr: nil,
        } = get_pair(eval.store(), body)?;
        if !nil.is_nil() {
            return Err(Error::UserError(format!(
                "define-variable body {} is not a single expression",
                body
            )));
        }
        push(eval.store(), env);
        push(eval.store(), value);
        eval.op_stack.push(Op::Bind);
        eval.op_stack.push(Op::EvalExpr);

        return Ok(());
    }

    Err(Error::UserError(format!(
        "cannot bind to non-symbol/non-function expression {}",
        binding
    )))
}
