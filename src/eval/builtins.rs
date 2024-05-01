use std::ops::{BitOr, BitXor};

use crate::eval::{
    eval_list, get_pair, get_value, pop, push, Builtin, Error, EvalEnvironment, Object, Op,
    ToUserError,
};

use crate::data::{Pair, Ptr};

/// The standard library of functions.
/// This gets loaded during environment initialization.
pub const STDLIB: &str = include_str!("stdlib.scm");

/// These could also be called "keywords".
/// We evaluate them by first selecting "is this thing a function or a builtin",
/// then dispatching the builtins with more context.
///
/// This means you _could_ do evil things like redefining "define"!
/// Don't do that, though, please.
pub const BUILTINS: &[(&str, Builtin)] = &[
    // First: the forms.
    // These don't necessarily _evaluate_ their arguments.
    ("define", builtin_define),
    ("begin", builtin_begin),
    ("lambda", builtin_lambda),
    ("list", builtin_list),
    ("set!", builtin_set),
    ("quote", builtin_quote),
    ("if", builtin_if),
    // ("cond", builtin_unimplemented),
    // ("apply", builtin_unimplemented),

    // TODO: move this to "masked builtins"
    //
    // Second: backers of standard-library functions.
    // The non-'sys' versions of these act like standard functions,
    // but can't be implemented without these lower-level primitives.
    //
    // I don't want to duplicate the function-invocation/arg-eval code,
    // since doing so would require new microops for the "completion"
    // of each of these.
    // Instead: we wrap these in a function, and rely on the args having
    // already been evaluated.
    ("sys:car", builtin_sys_car),
    ("sys:cdr", builtin_sys_cdr),
    ("sys:cons", builtin_sys_cons),
    ("sys:eq?", builtin_sys_eq),
    ("sys:eqv?", builtin_sys_eqv),
    ("sys:add", builtin_sys_add),
];

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
    let obj = eval.store.put(Object::Pair(Pair::cons(env, tail)));
    push(&eval.store, obj);
    Ok(())
}

// Set a variable to a value.
fn builtin_set(eval: &mut EvalEnvironment) -> Result<(), Error> {
    let env = pop(eval.store())?;
    let tail = pop(eval.store())?;

    // Deconstruct the tail to get structure
    let Pair {
        car: symbol,
        cdr: tail,
    } = get_pair(&eval.store, tail).to_user_error("missing symbol of set!")?;
    // We don't allow set! to take an expression - just a symbol.
    if !symbol.is_symbol() {
        return Err(Error::UserError(
            "set! argument is not a variable name".to_string(),
        ));
    }
    // Evaluate then bind-in-place.
    // Bind-in-place structure:
    push(&eval.store, env);
    push(&eval.store, symbol);
    // But we need to evaluate the expression.
    // set! doesn't take a _body_, just an _expression_, but what we have is the tail;
    // we need to put just the expression there.
    let Pair {
        car: expression,
        cdr: nil_tail,
    } = get_pair(&eval.store, tail).to_user_error("missing value of set!")?;
    if !nil_tail.is_nil() {
        return Err(Error::UserError(
            "set! expression takes a single value, not a body".to_string(),
        ));
    }

    push(&eval.store, expression);
    push(&eval.store, env);
    eval.op_stack.push(Op::Set);
    eval.op_stack.push(Op::EvalExpr);

    Ok(())
}

// Return the single argument "quoted" - literally, without evaluation.
fn builtin_quote(eval: &mut EvalEnvironment) -> Result<(), Error> {
    let _env = pop(eval.store())?;
    let tail = pop(eval.store())?;

    let Pair {
        car: expression,
        cdr: nil_tail,
    } = get_pair(&eval.store, tail).to_user_error("missing argument of quote")?;
    if !nil_tail.is_nil() {
        return Err(Error::UserError(
            "quote expression takes a single argument".to_string(),
        ));
    }
    push(eval.store(), expression);

    Ok(())
}

fn builtin_if(eval: &mut EvalEnvironment) -> Result<(), Error> {
    let env = pop(eval.store())?;
    let tail = pop(eval.store())?;

    // Three expressions in the tail:
    // - Predicate
    // - Positive case
    // - Negative case
    let Pair {
        car: predicate,
        cdr: tail,
    } = get_pair(&eval.store, tail).to_user_error("missing predicate of if")?;
    let Pair {
        car: pos,
        cdr: tail,
    } = get_pair(&eval.store, tail).to_user_error("missing positive case of if")?;
    let Pair {
        car: neg,
        cdr: nil_tail,
    } = get_pair(&eval.store, tail).to_user_error("missing negative case of if")?;
    if !nil_tail.is_nil() {
        return Err(Error::UserError(
            "if expression takes three arguments: predicate, positive, negative".to_string(),
        ));
    }

    // Our steps are:
    // - Evaluate the predicate expression
    // - EvalCond
    // Set up EvalCond arguments first:
    push(eval.store(), neg);
    push(eval.store(), pos);
    push(eval.store(), env);
    // Then predicate:
    push(eval.store(), predicate);
    push(eval.store(), env);

    eval.op_stack.push(Op::EvalCond);
    eval.op_stack.push(Op::EvalExpr);

    Ok(())
}

/// Get two arguments to a sys: builtin.
///
/// `sys:`-type builtins, backed by functions, have symbolic arguments
/// as specified by the `lambda` invocation.
/// We have to look up the symbols used, and then look up the values
/// in the environment.
fn get_args<'a, const N: usize>(
    eval: &'a EvalEnvironment,
    env: Ptr<'a>,
    mut tail: Ptr<'a>,
) -> Result<[Ptr<'a>; N], Error> {
    let mut ptrs = [Ptr::nil(); N];
    for loc in ptrs.iter_mut() {
        // We treat the below errors as faults
        // because the wrapper lambda should
        // use the right number of arguments.
        let Pair {
            car: sym,
            cdr: new_tail,
        } = get_pair(&eval.store, tail)?;
        tail = new_tail;
        *loc = get_value(eval.store(), sym, env)?;
    }
    // Self-check: we consumed all the arguments.
    assert!(tail.is_nil());

    Ok(ptrs)
}

/// Return true/false based on the (two) arguments' pointer equality.
fn builtin_sys_eq(eval: &mut EvalEnvironment) -> Result<(), Error> {
    let env = pop(eval.store())?;
    let tail = pop(eval.store())?;
    let [a, b] = get_args(eval, env, tail)?;

    let symbol = if a == b {
        eval.store().put_symbol("#t")
    } else {
        eval.store().put_symbol("#f")
    };
    push(eval.store(), symbol);
    Ok(())
}

/// Return true/false based on the (two) arguments' value equality.
fn builtin_sys_eqv(eval: &mut EvalEnvironment) -> Result<(), Error> {
    let env = pop(eval.store())?;
    let tail = pop(eval.store())?;
    let [a, b] = get_args(eval, env, tail)?;
    let symbol = if a == b {
        "#t"
    } else {
        let a_val = eval.store().get(a);
        let b_val = eval.store().get(b);

        match (a_val, b_val) {
            (Object::Integer(a), Object::Integer(b)) if a == b => "#t",
            (Object::Float(a), Object::Float(b)) if a == b => "#t",
            (Object::String(ref a), Object::String(ref b)) => {
                let a = eval.store().get_string(a);
                let b = eval.store().get_string(b);
                // Do a constant-in-length comparison;
                // takes longer, but if we accidentally use this for something sensitive, oops.
                // XOR each pair of bytes; OR the differences into the accumulator.
                // If any bits are different, we'll have a nonzero answer.
                let result = a
                    .as_ref()
                    .iter()
                    .cloned()
                    .zip(b.as_ref().iter().cloned())
                    .fold(0u8, |acc, (a, b)| acc.bitor(a.bitxor(b)));
                if result == 0 {
                    "#t"
                } else {
                    "#f"
                }
            }
            (_, _) => "#f",
        }
    };

    let p = eval.store().put_symbol(symbol);
    push(eval.store(), p);
    Ok(())
}

/// Create a new `cons` cell.
fn builtin_sys_cons(eval: &mut EvalEnvironment) -> Result<(), Error> {
    let env = pop(eval.store())?;
    let tail = pop(eval.store())?;
    let [a, b] = get_args(eval, env, tail)?;
    let pair = eval.store().put(Pair::cons(a, b));
    push(eval.store(), pair);
    Ok(())
}

/// Get the `car` of the cell.
fn builtin_sys_car(eval: &mut EvalEnvironment) -> Result<(), Error> {
    let env = pop(eval.store())?;
    let tail = pop(eval.store())?;
    let [a] = get_args(eval, env, tail)?;

    let Pair { car, .. } =
        get_pair(eval.store(), a).to_user_error("argument of car is not a pair")?;
    push(eval.store(), car);
    Ok(())
}

/// Get the `cdr` of the cell.
fn builtin_sys_cdr(eval: &mut EvalEnvironment) -> Result<(), Error> {
    let env = pop(eval.store())?;
    let tail = pop(eval.store())?;
    let [a] = get_args(eval, env, tail)?;

    let Pair { cdr, .. } =
        get_pair(eval.store(), a).to_user_error("argument of cdr is not a pair")?;
    push(eval.store(), cdr);
    Ok(())
}

// A two-argument system function backing the "+" operator.
// A nice thing about this: we can assume the arguments
// have already been evaluated.
fn builtin_sys_add(eval: &mut EvalEnvironment) -> Result<(), Error> {
    let env = pop(eval.store())?;
    let tail = pop(eval.store())?;
    let [a, b] = get_args(eval, env, tail)?;

    let result = match (eval.store().get(a), eval.store.get(b)) {
        (Object::Integer(a), Object::Integer(b)) => eval.store.put(a + b),
        (Object::Float(a), Object::Float(b)) => eval.store.put(a + b),
        (Object::String(a), Object::String(b)) => {
            // get_string takes a lease on the _underlying string store_,
            // and put_string takes it.
            // We have to release our string Refs before we can put_string.
            let new: Vec<u8> = {
                let a = eval.store().get_string(&a);
                let b = eval.store().get_string(&b);
                a.iter().cloned().chain(b.iter().cloned()).collect()
            };
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
