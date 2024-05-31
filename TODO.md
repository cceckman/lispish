# TODOs

## Goals

- [ ] Get a good test suite, where I can compare the results to MIT / GNU Scheme.
- [ ] ...or maybe instead, conform to [R6RS]? Or a strict subset...R7RS?
- [ ] Benchmark.
- [ ] Refactor into a bytecode interpreter / compiler pair.
- [ ] Rewrite it in RISC-V.
- [ ] Parallel execution with message-passing.

## Tasks

- [ ] no_std support for store.
  - [x] Multiple roots in the store.
  - [x] Fold strings into the store.
    - Keep arena allocator and moving pointers, allow contiguous allocation?
      Supports vectors cleanly, given appropriate unions.
    - Make everything more complicated...?
  - [x] Fold symbols into the store. Multiple roots, one of which is the symbol table.
  - [ ] No marginal allocation for bitset / GC flow.
- [ ] no_std support for runtime.
  - [ ] Lexer, Parser use the new no_std store. This is ~a rewrite.
  - [ ] While we're at it, add "structure parsing" after "S-expression parsing".
        Determine forms up-front;   
- [ ] Batch scriptability.
    - [ ] REPL / CLI / batch interpreter frontend.
    - [ ] I/O routines (`display`, at least).
- [ ] Macros.
  It seems like these aren't arbitrary transforms - just "structure to structure"
  mappings.
- [ ] Bytecode.


[R6RS]: https://www.r6rs.org/final/r6rs.pdf
