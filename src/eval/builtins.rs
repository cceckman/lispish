use crate::eval::{
    eval_list, get_pair, pop, push, Builtin, Error, EvalEnvironment, Object, Op, ToUserError,
};

use crate::data::{Pair, Ptr};

/// The standard library of functions.
/// This gets loaded during environment initialization.
const STDLIB: &[u8] = include_bytes!("stdlib.scm");

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
    // ("cons", builtin_cons)
    // ("car", builtin_car)
    // ("cdr", builtin_cdr)
    // ("eq?", builtin_eq)
    // ("if", builtin_if),
    // ("set!", builtin_set),
    // ("cond", builtin_unimplemented),
    // ("quote", builtin_unimplemented),
    // ("apply", builtin_unimplemented),

    // TODO: move this to "masked builtins"
    // These act as system functions to back standard-library functions.
    // sys:add is the function of two variables that backs the "+" operator.
    ("sys:add", builtin_add),
];

// A two-argument system function backing the "+" operator.
// A nice thing about this: we can assume the arguments
// have already been evaluated.
fn builtin_add(eval: &mut EvalEnvironment) -> Result<(), Error> {
    let _env = pop(eval.store())?;
    let args = pop(eval.store())?;

    let Pair { car: a, cdr: next } =
        get_pair(eval.store(), args).to_user_error("missing argument to +")?;
    let Pair { car: b, .. } =
        get_pair(eval.store(), next).to_user_error("missing argument to +")?;

    let result = match (eval.store().get(a), eval.store.get(b)) {
        (Object::Integer(a), Object::Integer(b)) => eval.store.put(a + b),
        (Object::Float(a), Object::Float(b)) => eval.store.put(a + b),
        (Object::String(a), Object::String(b)) => {
            let a = eval.store().get_string(&a);
            let b = eval.store().get_string(&b);
            let new: Vec<u8> = a.iter().cloned().chain(b.iter().cloned()).collect();
            eval.store().put_string(&new)
        }
        _ => {
            return Err(Error::UserError(format!(
                "incompatible arguments: {a} + {b} has mismatched types"
            )))
        }
    };

    push(eval.store(), result);
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
    eval_list(&mut eval.op_stack, &eval.store, body, env)
}

fn builtin_lambda(eval: &mut EvalEnvironment) -> Result<(), Error> {
    // Remaining stack is:
    let env = pop(&eval.store)?;
    let tail = pop(&eval.store)?;

    // Deconstruct the tail further, to check structure:
    {
        let Pair {
            car: parameters,
            cdr: body,
        } = get_pair(&eval.store, tail).to_user_error("missing parameters in lambda")?;
        let mut parameters = parameters;
        while !parameters.is_nil() {
            let Pair { car, cdr } = get_pair(&eval.store, parameters)?;
            if !car.is_symbol() {
                return Err(Error::UserError(
                    "parameter list must only be symbols".to_string(),
                ));
            }
            parameters = cdr;
        }
        if body.is_nil() {
            return Err(Error::UserError(
                "lambda must have a nonempty body".to_string(),
            ));
        }
    }

    // Function object re-uses the tail: (environment, parameters, body...)
    let obj = eval.store.put(Object::Function(Pair::cons(env, tail)));
    push(&eval.store, obj);
    Ok(())
}
