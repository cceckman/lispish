use crate::eval::{get_pair, pop, push, Builtin, Error, EvalEnvironment, Op, ToUserError};

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
    ("begin", builtin_begin),
    ("lambda", builtin_lambda),
    ("list", builtin_list),
    // ("if", builtin_unimplemented),
    // ("cond", builtin_unimplemented),
    // ("quote", builtin_unimplemented),
    // ("apply", builtin_unimplemented),
    // TODO: This is "just" for testing.
    ("one", builtin_one),
];

fn builtin_unimplemented(_eval: &mut EvalEnvironment) -> Result<(), Error> {
    Error::Fault("haven't implemented this builtin".to_string()).into()
}

/// The `one` builtin: evaluate to 1.
fn builtin_one(eval: &mut EvalEnvironment) -> Result<(), Error> {
    let _env = pop(eval.store())?;
    let _args = pop(eval.store())?;
    push(eval.store(), eval.store().put(1i64));
    Ok(())
}

fn builtin_define(eval: &mut EvalEnvironment) -> Result<(), Error> {
    let env = pop(eval.store())?;
    let args = pop(eval.store())?;

    // Are we defining a function or a variable?
    let binding: Ptr<'_>;
    let body: Ptr<'_>;

    Pair {
        car: binding,
        cdr: body,
    } = get_pair(eval.store(), args).to_user_error(format!(
        "define statement is missing arguments; got {} instead of body",
        args
    ))?;

    if binding.is_pair() {
        return Err(Error::Fault(
            "function definition is not yet implemented".to_string(),
        ));
    }

    if binding.is_symbol() {
        // Variable binding. We'll add to the current environment:
        push(eval.store(), env);
        push(eval.store(), binding);
        // After evaluating the body...
        // which (for a variable) must be a single, nonempty expression.
        let Pair {
            car: value,
            cdr: nil,
        } = get_pair(eval.store(), body).to_user_error("define-variable must have a body")?;
        if !nil.is_nil() {
            return Err(Error::UserError(format!(
                "define-variable body {} is not a single expression",
                body
            )));
        }
        push(eval.store(), value);
        push(eval.store(), env);
        eval.op_stack.push(Op::Bind);
        eval.op_stack.push(Op::EvalExpr);

        return Ok(());
    }

    Err(Error::UserError(format!(
        "cannot bind to non-symbol/non-function expression {}",
        binding
    )))
}

fn builtin_begin(eval: &mut EvalEnvironment) -> Result<(), Error> {
    // "begin" is ~syntactic sugar for a block.
    // Evaluate each of the "args" as a body, in this environment.
    let env = pop(&eval.store)?;
    let body = pop(&eval.store)?;
    push(&eval.store, body);
    push(&eval.store, env);
    eval.op_stack.push(Op::EvalBody);

    // Do we need to introduce a nested environment?
    // No : MIT scheme treats
    // (begin (define a 1))
    // as defining `a` in the parent environment.
    Ok(())
}

fn builtin_list(eval: &mut EvalEnvironment) -> Result<(), Error> {
    // "list" just means to treat the arguments as a list.
    // But we have to evaluate each of them in turn.
    let env = pop(&eval.store)?;
    let body = pop(&eval.store)?;

    // Create a "nil head" to accumulate into.
    // This will be our result later, after a Cdr op:
    let nil_head = eval.store.put(Pair::cons(Ptr::nil(), Ptr::nil()));
    push(&eval.store, nil_head);

    // We'll need to evaluate the list, though:
    push(&eval.store, body);
    push(&eval.store, env);
    // Note that here, nil_head is the list _tail_;
    // above, it's the list _head_.
    push(&eval.store, nil_head);

    // Once the eval-list is done, we'll want to get the "real" list head:
    eval.op_stack.push(Op::Cdr);
    // But first, eval-list:
    eval.op_stack.push(Op::EvalList);

    Ok(())
}

fn builtin_lambda(eval: &mut EvalEnvironment) -> Result<(), Error> {
    // Remaining stack is:
    let env = pop(&eval.store)?;
    let tail = pop(&eval.store)?;

    // Deconstruct the tail further:
    let Pair {
        car: parameters,
        cdr: body,
    } = get_pair(&eval.store, tail).to_user_error()?;

    todo!()
}
