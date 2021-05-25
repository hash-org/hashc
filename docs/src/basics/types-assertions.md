# Type Signature Assertions

As in many other languages, the programmer can specify the type of a variable or
a literal by using some special syntax. For example, in languages such as typescript,
you can say that: 
```ts 
some_value as string
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
