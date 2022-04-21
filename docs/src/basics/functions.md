# Functions

## Overview

`Hash` places a lot of emphasis on functions, which are first class citizens.
Functions can be assigned to variables in the same way that any other value is stored, similar to languages like Python, JavaScript, etc.

## General syntax and notes

Functions are defined by being assigned to variables as literals:

```rust
let var = (...args) => { ...body... };

// With a return type
let var = (...args) -> return_ty => { ...body... };
```

Function arguments are comma separated:

```rust
let var = (arg0, arg1) => { ...body... };

// and you can optionally specify types:
let var = (arg0: str, arg1: char) -> u32 => { ...body... };
```

Function literal definitions can also leave annotations to
the variable definition:

```rust
let var: (str, char) -> u32 = (arg0, arg1) => { ...body... };
```

## Examples

Define a function is to assign it to a variable:

```rust
let fib = (n: u32) => 
   if n == 1 || n == 2 {
       n
   } else {
       fib(n - 1) + fib(n - 2)
   };
}

print(fib) // <function at ____>
print(fib(3)) // 3
```

Multiple arguments can be specified:

```rust
let str_eq = (a: str, b: str) => a == b;
```

The type of a function can be specified in a similar way:

```rust
let str_eq: (str, str) -> str = (a, b) => a == b;
```
