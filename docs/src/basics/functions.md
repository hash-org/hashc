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

Multiple arguments can be specified:

```rust
let str_eq = (a: str, b: str) => a == b;
```

The type of a function can be specified in a similar way:

```rust
let str_eq: (str, str) => str = (a, b) => a == b;
```
