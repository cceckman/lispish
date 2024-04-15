
In no particular order:

-   [ ] `()` as an atom at the reader level, rather than a list?
-   [ ] Comments
-   [ ] Proper/complete symbol syntax
    -   [ ] Exclude non-symbol characters (`"`, `'`, open parens, etc)
    -   [ ] Raw/escape syntax

-   [ ] Symbol interning - how to handle?
        -   I think I need a more complete understanding of what "package" means.
        -   And: this is a _reader_ feature rather than an _evaluator_ feature?
            Is "reader" a distinct stage after the parser?
        -   Self-referential symbols...including `NIL`?

            > It's also possible for symbols to be self-evaluating in the sense that the variables they name can be assigned the value of the symbol itself. Two important constants that are defined this way are `T` and `NIL`, the canonical true and false values. I'll discuss their role as booleans in the section "Truth, Falsehood, and Equality."

            > This equivalence between `NIL` and the empty list is built into the reader: if the reader sees `()`, it reads it as the symbol `NIL`.

            But...does that mean `NIL` can be used as an empty list for e.g.
            a `map` call or similar? Hm.

        -   Keyword (`:`) symbols: "When the reader interns such a name, it automatically defines a constant variable with the name and with the symbol as the value."

-   [ ] Additional numeric syntaxes

        ...and representation thereof, e.g. rational types

-   [ ] Quote syntax, `#` syntax, ...

        (Not an immediate problem: can use `(quote foo)`, `(function foo)`
        builtins to start off with)

-   [ ] Evaluation
    -   [ ] Builtin functions (`+` etc)
    -   [ ] Control flow / special operators; `if`, then
    -   [ ] Variables - necessary for proper symbol support?
            (Backport builtins to it)

