# Basics

Hash is an interpreted, garbage collected, strongly and statically typed language.

There are the following primitive types:

- `u8`, `u16`, `u32`, `u64`: unsigned integers
- `i8`, `i16`, `i32`, `i64`: signed integers
- `f32`, `f64` : floating point numbers
- `usize`, `isize`: unsigned and signed native integer types (for list indexing)
- `ibig`, `ubig`: unlimited size integers
- `bool`: boolean
- `str`: string, copy on write and immutable
- `[A]`: a list containing type A
- `{A:B}`: a map between type A and type B
- `(A, B, C)`: a tuple containing types A, B and C. Elements can be accessed by dot notation (`my_tuple.0`)
- `void`: the empty type. Has a corresponding `void` value.
- `never`: a type which can never be instantiated. Used, for example, for functions that never return, like `panic`.

# Variables

The formal specification of a variable declaration is
```
variable_declaration = "let" identifier ( ":" type )? ( "=" expression )? ";"
```

Declaration and assignment can happen separately:
```rust
let x: u8;
x = 3;
```

Variables cannot be used until they are assigned.

The type of a variable, if not given, is automatically inferred by the value.
In `let a: X = b`, if the type of `b` is not `X`, the language produces an error.

# Functions

`Hash` places a lot of emphasis on functions, which are first class citizens.
Functions can be assigned to variables in the same way that any other value is stored, similar to languages like Python, JavaScript, etc.
In fact, the way to define a function is to assign it to a variable.

```rust
let fib = (n: u32) => 
   if n == 1 || n == 2 {
       n
   } else {
       fib(n - 1) + fib(n - 2)
   };

print(fib) // <function at ____>
print(fib(3)) // 3
```

The formal syntax of a function expression is as follows:

```
expression = ... | function_expression
function_expression = ( identifier "=>" expression ) | ( "(" ( identifier ( ":" type )? "," )* ")" "=>" expression )
```

Multiple arguments can be specified:

```rust
let str_eq = (a: str, b: str) => a == b;
```

The type of a function can be specified in a similar way:
```
type = ... | function_type
function_type = type "=>" type | ( "(" ( type "," )* ")" ) => type
```

Again, multiple arguments can be specified:

```rust
let str_eq: (str, str) => str = (a, b) => a == b;
```
