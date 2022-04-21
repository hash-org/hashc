# Generics and polymorphism

Hash supports polymorphism through generic types.
These come in two forms:

- Function traits
- Generic structs and enums

## Function traits

Function traits are a core mechanic in Hash, which allow for different implementations of the same operation, for different types.
The following code defines a function trait `merge` which, for some type `T`, takes two `T` values and returns a `T` value.
Generic type names are denoted by single capital letters.

```rust
trait merge = <T> => (T, T) -> T;
```

Angular brackets (`<`, `>`) define a *type argument list*, containing one or more generic type names.
These can be used anywhere in the following type expression.

Traits can be implemented for specific types:

```rust
let merge<str> = (a, b) => str_concat(a, b);
```

They can also be implemented for a generic type bound.
The following code implements `merge` for any type that implements `add`.

```rust
let merge<T> where add<T> = (a, b) => a + b;
```

This is called *blanket implementation* and it can be done using the `where` keyword.
Note that the code might contain multiple overlapping implementations of the same function trait:

```rust
let merge<T> where add<T> = (a, b) => a + b;
let merge<u32> = (a, b) => a + b + 42; // But u32 also implements add!
```

In that case, for each function trait resolution, the *last-declared implementation* of the trait has precedence:

```rust
print(merge(1 as u8,  2 as u8)); // 3u8
print(merge(1 as u32, 2 as u32)); // 45u32
```

The `add` trait is defined in the standard library, and implementations of `add` for different types define how different types should be added together.
In fact, `a + b` is just syntactical sugar for `add(a, b)`.
This is the case for all operators in Hash, which are defined in the `op` standard library module.

Traits can benefit from type inference:

```rust
let simon_says = (what: str) => merge("Simon says ", what); // inferred to merge<str>
```

This is done by looking at:

1. The types of the arguments given.
2. The surrounding context, for example the expected return value of the expression.

Trait implementation bounds can make use of the special `?` type quantifier, which essentially means "any type".
For example,

```rust
let skip<I> for next<I, ?> = ...;
```

says "implement `skip<I>` for any `I` that has an implementation `next<I, T>`, where `T` is any type".
Essentially, `skip` doesn't care about the `T`, but `next` still requires a second argument, so `?` is used.

## Generic structs and enums

Hash also supports generic structs and enums.

These are essentially *type functions*, which take a type and return another type.

For example,

```rust
enum Result = <T, E> => {
   Ok(T);
   Err(E);
};
```

is a generic enum, very similar to Haskell's `Either` type or Rust's `Result` type.
It takes two types `T` and `E`, and returns a type `Result<T, E>` representing an operation which succeeds with result `T`, or fails with error `E`.
Each instantiation of a generic type is unique and is treated as a completely separate type.

```rust
let print_result = (r: Result<u32, str>) => print(conv(r));

let my_res: Result<u16, str> = Ok("Hello there!");
print_result(my_res); // Type mis // Error: Type mismatch: was expecting `Result<u32, str>`, got `Result<u16, str>`.
```

The same pattern is possible with structs:

```rust
struct Vector3 = <T> => {
   x: T;
   y: T;
   z: T;
}
```

Type inference works both for enums and structs.
It can be inferred by the types of the contents, or the expected return value, or both.

```rust
let abc = Vector3 { x = 'a'; y = 'b'; z = 'c' }; // Vector3<char>
let maybe_foo = Some("foo"); // Option<str>
```

If you want a generic type argument to be inferred, but want to specify another one, you can use the `_` syntax:

```rust
let char_list = "Hello world".iter().collect<_, [char]>();
```

## Generic parameters

Generic parameters in Hash work slightly differently than they do in other languages.

For example, one can write:

```rs
let next<Enumerate<I>, (usize, T)> where next<I, T>;
```

This implements the `next` trait from the standard library for the `Enumerate` struct.
Notice that the `Enumerate` struct takes a generic parameter, which is denoted with `I`.
Type variables in type argument lists can appear nested within other generic types.
When a type variable appears anywhere within a type argument list, it is implicitly "declared".

```rs
let next<WeirdIterator<I>, I> where next<I, ?>;
```

The above snippet implements `next` for a `WeirdIterator` struct, generic over some type `I`.
The element of the iterator is of the same type `I`.
