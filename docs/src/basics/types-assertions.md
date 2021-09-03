# Type Signature Assertions

## Basics

As in many other languages, the programmer can specify the type of a variable or
a literal by using some special syntax. For example, in languages such as typescript,
you can say that: 
```ts 
some_value as str
```
which implies that you are asserting that `some_value` is a string, this is essentially a way to avoid explicitly stating that type of a variable every
single time and telling the compiler "Trust me `some_value` is a `string`". 

The principle is somewhat similar in `Hash`, but it is more strictly enforced.
For example, within the statement `let x = 37;`, the type of `x` can be any of the
integer types. This might lead to unexpected behaviour in future statements, where
the compiler has decided the type of `x` (it might not be what you intended it).

So, you can either declare `x` to be some integer type explicitly like so:

```rs
let x: u32 = 37;
```

Or you can, use `as` to imply a type for a variable, which the compiler will assume 
to be true, like so:

```rs
let x = 37 as u32;
```

## Failing type assertions

If you specify a type assertion, the compiler will either attempt to infer this information from the left-hand side of the `as` operator
to the right. If the inference results in a different type to the right-hand side, this will raise a typechecking failure. 

For example, if you were to specify the expression:

```rust
"A" as char
```

The compiler will report this error as:

```
error: Failed to typecheck:
--> 1:1 - 1:3
  |
  |
1 | "2" as char
  | ^^^    
  |
Cannot match type 'char' with 'str'.
```

## Usefulness
 
Why are type assertions when there is already type inference within the language? Well, sometimes the type inference
system does not have enough information to infer the types of variables and declarations. 
Type inference may not have enough information when dealing with functions that are generic, so it can sometimes
be useful to assert to the compiler that a given variable is a certain type. 

Additionally, whilst the language is in an early stage of maturity and some things that are quirky or broken, type
assertions can come to the rescue and help the compiler to understand your program.

In general, type assertions should be used when the compiler cannot infer the type of some expression with 
the given information and needs assistance. You shouldn't need to use type assertions often.
