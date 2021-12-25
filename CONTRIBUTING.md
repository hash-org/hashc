# The Hash Programming language contributor guide

## Submitting a PR
    
Before submitting a PR, make sure that:

- Your code builds successfully, and all the tests run successfully.

- run `cargo fmt` to format the sources.

- run `cargo clippy` to make sure you're submitting code without any generated warnings. 

- All the tests pass, you can run the `cargo test` command to run the provided language test suite.

- You have updated the relevant `README.md`/`CONTRIBUTING.md`/other documentation files.

## Style guide

### Code notes

Code notes can have a label using the `##` or `@@` prefix (see below), which
makes it easy to `grep` through all occurrences.

### Actionable

Use `@@` as a prefix for TODOs, FIXMEs and other such actionable code notes.
For example:

```rust
// @@TODO: this is not a particularly efficient way of doing this
let v = my_vec.into_iter().map(|x| *x).collect();
```

### Informational

Use the `##` as a prefix for other code notes which aren't actionable, but
purely informational.
For example:

```rust
// ##Safety: this is okay I promise bla bla bla
let dog = unsafe { std::mem::transmute<Cat, Dog>(cat) };
```
