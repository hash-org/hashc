# Functions

## Overview

`Hash` places a lot of emphasis on functions, which are first class citizens.
Functions can be assigned to variables in the same way that any other value is stored, similar to languages like Python, JavaScript, etc.

## General syntax and notes

Functions are defined by being assigned to variables as literals:

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

Function literal definitions can also leave annotations to
the variable definition:

```rust
var := (str, char) -> u32 = (arg0, arg1) => { ... };
```

Function literals can also specify default argument types...

```rust
func := (arg0: str, arg1: char = 'c') -> u32 => { ... };

// The type of the argument is also inferred if provided without a type
// annotation...
func := (arg0: str, arg1 = 'c') -> u32 => { ... };
```

This means that functions which have default arguments don't have to be provided, and they 
can be provided as named arguments:
```rust
func := (arg0: str, arg1 = 'c', arg3 = 2) -> u32 => { ... };

func("cccccbbbaaa"); // This is valid as all of the arguments are supplied

// You can optionally provide the arguments in declaration order:
func("cccccbbbaaa", 'b', 2); 

// Or you can provide them as named arguments:
func("cccccbbbaaa", arg3 = 2); 
```

Functions which have named arguments must follow the convention that all un-named
arguments follow  

## Examples

Define a function is to assign it to a variable:

```rust
fib := (n: u32) => {
   if n == 1 || n == 2 {
       n
   } else {
       fib(n - 1) + fib(n - 2)
   }
};

print(fib); // <function at ____>
print(fib(3)); // 3
```

Multiple arguments can be specified:

```rust
str_eq := (a: str, b: str) => a == b;
```

The type of a function can be specified in a similar way:

```rust
str_eq: (str, str) -> str = (a, b) => a == b;
```
