# TODOs

## Goals

- [ ] Get a good test suite, where I can compare the results to MIT / GNU Scheme.
- [ ] ...or maybe instead, conform to [R6RS]? Or a strict subset.
- [ ] Benchmark.
- [ ] Refactor into a bytecode interpreter / compiler pair.
- [ ] Rewrite it in RISC-V.
- [ ] Parallel execution with message-passing.

## Tasks

- [ ] Batch scriptability.
    - [ ] REPL / CLI / batch interpreter frontend.
    - [ ] I/O routines (`display`, at least).
- [ ] Fixed memory for runtime.
  - [ ] Multiple roots in the store.
  - [ ] Fold strings into the store.
    - Keep arena allocator and moving pointers, allow contiguous allocation?
      Supports vectors cleanly, given appropriate unions.
    - Make everything more complicated...?
  - [ ] Fold symbols into the store. Multiple roots, one of which is the symbol table.
  - [ ] Lexer, Parser use the store.
- [ ] Macros.
  It seems like these aren't arbitrary transforms - just "structure to structure"
  mappings.
- [ ] Bytecode.


[R6RS]: https://www.r6rs.org/final/r6rs.pdf
