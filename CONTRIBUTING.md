# Submitting a PR
    
Before submitting a PR, make sure that:

- Your code builds successfully, and all the tests run successfully.

- run `cargo fmt` to format the sources.

- run `cargo clippy` to make sure you're submitting code without any generated warnings. 

- All the tests pass, you can run the `cargo test` command to run the provided language test suite.

# Style guide

## Code notes

Use `@@` as a prefix for TODOs, FIXMEs and other such code notes.
For example:

```rust
// @@TODO: this is not a particularly efficient way of doing this
let v = my_vec.into_iter().map(|x| *x).collect();
```

This helps to easily find all such occurrences through `grep '@@'` or
equivalent.
