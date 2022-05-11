# Functions

## Overview

`Hash` places a lot of emphasis on functions, which are first class citizens.
Functions can be assigned to name bindings in the same way that any other value is assigned, similar to languages like Python lambdas, JavaScript arrow functions, etc.

## General syntax and notes

Functions are defined by being assigned to bindings:

```rust
func := (...args) => { ...body... };

// With a return type
func := (...args) -> return_ty => { ...body... };
```

Function arguments are comma separated:

```rust
func := (arg0, arg1) => { ...body... };

// and you can optionally specify types:
func := (arg0: str, arg1: char) -> u32 => { ...body... };
```

Function types can be explicitly provided after the `:` in the declaration, in which case argument names do not have to be specified.

```rust
var: (str, char) -> u32 = (arg0, arg1) => { ... };
```

Function literals can also specify default arguments, which must come after all required arguments:

```rust
func := (arg0: str, arg1: char = 'c') -> u32 => { ... };

// The type of the argument is also inferred if provided without a type
// annotation:
func := (arg0: str, arg1 = 'c') -> u32 => { ... };
```

Default arguments do not need to be specified when the function is called:
```rust
func := (a: str, b = 'c', c = 2) -> u32 => { ... };

func("foobar"); // a = "foobar", b = 'c', c = 2

// You can optionally provide the arguments in declaration order:
func("foobar", 'b', 3);  // a = "foobar", b = 'b', c = 3
// Or you can provide them as named arguments:
func("foobar", c = 3);  // a = "foobar", b = 'c', c = 3
```

Named arguments can be used for more context when providing arguments, using the syntax `arg_name = arg_value`.
After the first named argument is provided, all following arguments must be named.
Furthermore, up until but excluding the first named argument, all previous $n$ arguments must be the first $n$ in the function definition.
For example:
```rs
foo := (a: str, b: str, c: str, d: str) => { .. };

foo("a", "b", "c", "d") // Allowed -- no arguments are named.
foo(a="a", b="b", c="c", d="d") // Allowed -- all arguments are named.
foo("a", "b", c="c", d="d") // Allowed -- first two arguments are named.
foo(a="a", "b", c="c", d="d") // Not allowed -- argument b must be named if a is named.
foo("a", "b", c="c", "d") // Not allowed -- argument d must be named.
```
