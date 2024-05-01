//! Tests for the standard library and bulitin functions.
use super::*;
use crate::data::{Object, Pair, Ptr};

#[test]
fn begin() {
    let mut eval = EvalEnvironment::new();
    eval.start(
        r#"
        (define a (begin 1 2 3 4))
        a
        "#,
    )
    .unwrap();

    match eval.eval().unwrap() {
        Object::Integer(4) => (),
        v => panic!("unexpected result: {v:?}"),
    };
}

#[test]
fn define_requires_symbol() {
    let mut eval = EvalEnvironment::new();
    eval.start(
        r#"
        (define 1 39)
        a
        "#,
    )
    .unwrap();
    match eval.eval() {
        Err(Error::UserError(_)) => (),
        v => panic!("unexpected eval result: {:?}", v),
    };
}

#[test]
fn define_requires_body() {
    let mut eval = EvalEnvironment::new();
    eval.start(
        r#"
        (define a)
        a
        "#,
    )
    .unwrap();
    match eval.eval() {
        Err(Error::UserError(_)) => (),
        v => panic!("unexpected eval result: {:?}", v),
    };
}

#[test]
fn define_body_is_expression() {
    let mut eval = EvalEnvironment::new();
    eval.start(
        r#"
        (define a 1 2 3)
        a
        "#,
    )
    .unwrap();
    match eval.eval() {
        Err(Error::UserError(_)) => (),
        v => panic!("unexpected eval result: {:?}", v),
    };
}

#[test]
fn nonempty_list() {
    let mut eval = EvalEnvironment::new();
    eval.start(
        r#"
        (list 1 2 3)
        "#,
    )
    .unwrap();
    eval.eval().unwrap();
    let mut head = eval.result_ptr().unwrap();
    for value in [1, 2, 3] {
        let pt: Ptr;
        Pair { car: pt, cdr: head } = get_pair(eval.store(), head).unwrap();
        match eval.store().get(pt) {
            Object::Integer(v) => assert_eq!(v, value),
            v => panic!(
                "unexpected object: wanted integer {}, got {}",
                value,
                eval.store().display(v)
            ),
        }
    }
}

#[test]
fn empty_list() {
    let mut eval = EvalEnvironment::new();
    eval.start(
        r#"
        (list)
        "#,
    )
    .unwrap();
    eval.eval().unwrap();
    let head = eval.result_ptr().unwrap();
    assert!(head.is_nil());
}

#[test]
fn create_id_lambda() {
    let mut eval = EvalEnvironment::new();
    eval.start(
        r#"
        (lambda (x) i)
        "#,
    )
    .unwrap();

    match eval.eval().unwrap() {
        Object::Function(_) => (),
        v => panic!("unexpected value: {v:?}"),
    }
}

#[test]
fn invoke_id() {
    let mut eval = EvalEnvironment::new();
    eval.start(
        r#"
        (define id (lambda (x) x))
        (id 7)
        "#,
    )
    .unwrap();

    match eval.eval().unwrap() {
        Object::Integer(7) => (),
        v => panic!("unexpected value: {v:?}"),
    }
}
#[test]
fn invoke_id_split() {
    let mut eval = EvalEnvironment::new();
    eval.start("(define id (lambda (x) x))").unwrap();
    eval.eval().unwrap();
    eval.start("(id 7)").unwrap();

    match eval.eval().unwrap() {
        Object::Integer(7) => (),
        v => panic!("unexpected value: {v:?}"),
    }
}

#[test]
fn define_int_value_and_retrieve() {
    let mut eval = EvalEnvironment::new();
    eval.start(
        r#"
        (define a 7)
        (define b a)
        b
        "#,
    )
    .unwrap();

    match eval.eval().unwrap() {
        Object::Integer(7) => (),
        v => panic!("unexpected result: {v:?}"),
    };
}

#[test]
fn sys_add_integers() {
    let mut eval = EvalEnvironment::new();
    eval.start(
        r#"
        (sys:add 5 3)
        "#,
    )
    .unwrap();

    match eval.eval().unwrap() {
        Object::Integer(8) => (),
        v => panic!("unexpected result: {v:?}"),
    };
}

#[test]
fn sys_add_floats() {
    let mut eval = EvalEnvironment::new();
    eval.start("(sys:add 0.5 1.5)").unwrap();

    match eval.eval().unwrap() {
        Object::Float(v) => {
            // Yes, we're asserting equality rather than an approximation.
            // 0.5, 1.5, and 2.0 all have power-of-two fractions and whole parts,
            // so both should be exactly representations in any binary floating-point format.
            // f64 especially.
            assert_eq!(v, 2.0);
        }
        v => panic!("unexpected result: {v:?}"),
    };
}

#[test]
fn set() -> Result<(), Error> {
    let mut eval = EvalEnvironment::new();
    eval.start(
        r#"
    (define x 1)
    (set! x 2)
    x
    "#,
    )?
    .eval()?;

    match eval.result()? {
        Object::Integer(2) => Ok(()),
        x => panic!("unexpected result: {}", eval.store.display(x)),
    }
}

#[test]
fn quote() -> Result<(), Error> {
    let mut eval = EvalEnvironment::new();
    eval.start("(quote unknown-symbol)")?.eval()?;
    let got = eval.result_ptr()?;
    let want = eval.store().put_symbol("unknown-symbol");
    assert_eq!(got, want);
    Ok(())
}

#[test]
fn quote_requires_arg() -> Result<(), Error> {
    let mut eval = EvalEnvironment::new();
    eval.start("(quote)")?
        .eval()
        .expect_err("quote requires an argument");
    eval.start("(quote 1 2)")?
        .eval()
        .expect_err("quote requires exactly one argument");
    Ok(())
}

#[test]
fn booleans() -> Result<(), Error> {
    let mut eval = EvalEnvironment::new();
    eval.start("(eq? #t (quote #t))")?.eval()?;
    let t = eval.result_ptr()?;
    let hash_t = eval.store().put_symbol("#t");
    assert_eq!(t, hash_t);

    eval.start("(eq? #f (quote #f))")?.eval()?;
    let t = eval.result_ptr()?;
    let hash_t = eval.store().put_symbol("#t");
    assert_eq!(t, hash_t);

    eval.start("(eq? #f (quote #t))")?.eval()?;
    let f = eval.result_ptr()?;
    let hash_f = eval.store().put_symbol("#f");
    assert_eq!(f, hash_f);

    Ok(())
}

#[test]
fn eq() -> Result<(), Error> {
    let mut eval = EvalEnvironment::new();

    for (expr, expect) in [
        ("(eq? () ())", true),
        ("(eq? 1 2)", false),
        ("(eq? (quote a) (quote b))", false),
        ("(eq? (quote a) (quote a))", true),
        ("(eq? (list 1 2) (list 1 2))", false),
        ("(eq? 1.3 1.1)", false),
        ("(eq? 1.0 1.0)", false),
        (r#"(eq? "hello everyone" "hello everybody")"#, false),
        (r#"(eq? "hello world" "hello world")"#, false),
        ("(eq? (lambda (x) x) (lambda (x) x))", false),
        ("(define id (lambda (x) x)) (eq? id id)", true),
        (
            "(define id1 (lambda (x) x)) (define id2 (lambda (x) x)) (eq? id1 id2)",
            false,
        ),
        (r#"(eq? "hello" "hello")"#, false),
    ] {
        eval.start(expr)?.eval()?;
        let got = eval.result_ptr()?;
        let want = eval.store().put_symbol(if expect { "#t" } else { "#f" });
        assert_eq!(
            got, want,
            "unexpected result from {}: got: {} want: {}",
            expr, got, want
        );
    }

    Ok(())
}

#[test]
fn eqv() -> Result<(), Error> {
    let mut eval = EvalEnvironment::new();

    for (expr, expect) in [
        ("(eqv? () ())", true),
        ("(eqv? 1 2)", false),
        ("(eqv? 1 1)", true),
        ("(eqv? 1.0 1)", false),
        ("(eqv? (quote a) (quote b))", false),
        ("(eqv? (quote a) (quote a))", true),
        ("(eqv? (list 1 2) (list 1 2))", false),
        (r#"(eqv? "hello everyone" "hello everybody")"#, false),
        (r#"(eqv? "hello world" "hello world")"#, true),
        ("(eqv? 1.3 1.1)", false),
        ("(eqv? 1.0 1.0)", true),
        ("(eqv? (lambda (x) x) (lambda (x) x))", false),
        ("(define id (lambda (x) x)) (eq? id id)", true),
        (
            "(define id1 (lambda (x) x)) (define id2 (lambda (x) x)) (eq? id1 id2)",
            false,
        ),
        (r#"(eq? "hello" "hello")"#, false),
    ] {
        eval.start(expr)?.eval()?;
        let got = eval.result_ptr()?;
        let want_str = if expect { "#t" } else { "#f" };
        let want = eval.store().put_symbol(want_str);
        assert_eq!(
            got, want,
            "unexpected result from {}: got: {} want: {}",
            expr, got, want
        );
    }
    Ok(())
}

#[test]
fn pair_ops() -> Result<(), Error> {
    let mut eval = EvalEnvironment::new();

    for expr in [
        "(eq? (car (list (quote q))) (quote q))",
        r#"
            (define x (cons 1 2))
            (eqv? (car x) 1)
        "#,
        r#"
            (define x (cons 1 2))
            (eqv? (cdr x) 2)
        "#,
        r#"
            (define x (list 1 2 3.0 4))
            (eqv? (car (cdr (cdr x))) 3.0)
        "#,
    ] {
        eval.start(expr)?.eval()?;
        let got = eval.result_ptr()?;
        let want = eval.store().put_symbol("#t");
        assert_eq!(
            got, want,
            "unexpected result from {}: got: {} want: {}",
            expr, got, want
        );
    }

    Ok(())
}
