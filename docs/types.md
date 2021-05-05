# Types

Types in Hash can be split into three distinct categories, which are:

1. Primitives
2. Structs
3. Enums

<br/>

# Primitives
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
- `(A, B, C)`: a tuple containing types A, B and C. Elements can be accessed by dot notation (`my_tuple.first`)
- `void`: the empty type. Has a corresponding `void` value.
- `never`: a type which can never be instantiated. Used, for example, for functions that never return, like `panic`.

## Numbers

Numbers in hash are like numbers in most other statically typed language. Numbers come in 3 variants, 'unsigned', 'signed' and 'floating point'.

Floating point literals must include either a `.` or a scientific notation exponent
like `3.0`, `3e2`, `30e-1`, etc.

### Number types like `usize` & `isize` & `ibig` & `ubig`

These number primitives are added for convienience when working with a variety of
problems and host operating systems. The primitives `usize` and `isize` are intended
for list indexing. This is because on some systems (which are 32bit) may not be able
to support indexing a contiguous region of memory that is larger than '32bit' max value. So, the `usize` and `isize` primitives are host system dependent. 

The `ibig` and `ubig` number primitives are integer types that have no upper
or lower bound and will grow until the host operating system memory is exhausted 
when storing them. These types are intended to be used when working with heavy mathematical problems which may exceed the maximum '64bit' integer boundary.

## Bracketted type syntax

### List
Lists are denoted using the the common square bracket syntax where the values are
separated by commas, like so:

```rs
let x = [1,2,3,4,5,6]; // multiple elements
let y = [];
let z = [1,]; // optional trailing comma
```

To explictly declare a variable is of a `list` type, you do so:

```rs
let some_list: [u64] = [];
//             ^^^^^
//              type
```


### Tuple

Tuples have a familiar syntax with many other languages, but exhibit two distinct
differences between the common syntax. These differences are:

- Empty tuples: `(,)`
- Singleton tuple : `(A,)`
- Many membered tuple: `(A, B, C)` or `(A, B, C,)` 

To explictly declare a variable is of a `tuple` type, you do so:

```rs
let empty_tuple: (,) = (,);
//               ^^^
//               type

let some_tuple: (str, u32) = ("string", 12);
//              ^^^^^^^^^^
//                 type
```
**Note**: Trailing commas are not allowed within type defintions.


It's worth noting that tuples are fancy syntax for structures and are indexed
using 'english' numerical phrasing like `first`, `second`, `third`, etc to access
each member explicitly. Although, they are intended to be used mostly for pattern
matching, you can access members of tuples like so. However, you will not be able to access members of tuples that are larger than 10 elements in size. 
If this is the case, you should consider using a structural data type which will
allow you to do the same thing, and name the fields. Read more about patterns [here](pattern-matching.md).

### Set

Like tuples, sets have the same syntactic differences:

- Empty set: `{,}`
- Singleton set : `{A,}`
- Many membered set: `{A, B, C}` or `{A, B, C,}` 

To explictly declare a variable is of a `set` type, you do so:

```rs
let some_map: {str} = {,};
//            ^^^^^
//            set type
```

### Map

Like tuples, sets have the same syntactic differences:

- Empty map: `{:}`
- Singleton map : `{A:1}` or `{A:1,}`
- Many membered map: `{A: 1, B: 2, C: 3}` or `{A: 1, B: 2, C: 3,}` 

To explictly declare a variable is of a `map` type, you do so:

```rs
let some_map: {str: u8} = {:};
//            ^^^^^^^^^
//            map type
```

## Special types

- `void` - A type used to denote that this function does not return anything, for example a function that does some computation and the prints it, whilst having no
return statement or the last statement being the a print statement (which has a void return type signature).

- `never` - A type that can never be instantiated, passed and interacted with. This
is a special type to annotate functions that will never continue from then onwards.
For example, the provided `panic` function which will stop the current program from
running and print a stack trace, which cannot return anything since it crashes the 
compiler internally. 
The difference between `void` and `never` is that `void` returns nothing, and `never`
cannot return anything.

<br/>

# Structs

In Hash, structs are pre-defined collections of heterogeneous types, similar to C or Rust:

```rust
struct Vector3 = {
   x: f32;
   y: f32;
   z: f32;
};
```

A struct is comprised of a set of fields.
Each field has a name, a type, and an optional default value.

The formal syntax of a struct item is:

```
struct_item = "struct" identifier "=" "{" ( struct_field )* "}";
struct_field = ( ( identifier ":" type ) | ( identifier ( ":" type )? "=" expression  ) ) ";"
```

Structs can be instantiated with specific values for each of the fields.
Default values can be omitted, but can also be overridden.

```rust
struct Dog = {
   age: u32 = 42;
   name: str;
}

let d = Dog { name = "Bob" };

print(d); // Dog { name = "Bob"; age = 42; }
```

Structs are nominal types.
An argument of type `Dog` can only be fulfilled by an instance of `Dog`, and you can't pass in a struct that has the same fields but is of a different logical type.

```rust
let dog_name = (dog: Dog) => dog.name;

struct FakeDog = {
   age: u32 = 42;
   name: str;
}

print(dog_name(d)); // "Bob"
print(dog_name(FakeDog { age = 1, name = "Max" })); // Error: Type mismatch: was expecting `Dog`, got `FakeDog`.
```
<br/>

# Enums

Hash enums are similar to Rust enums or Haskell data types.
Each variant of an enum can also hold some data.
These are also known as *algebraic data types*, or *tagged unions*.

```rust
enum NetworkError = {
   NoBytesReceived;
   ConnectionTerminated;
   Unexpected(str, usize);
};
```

Enum contents consist of a semicolon-separated list of variant names.
Each variant can be paired with some data, in the form of a comma-separated list of types.

```rust
let err = NetworkError.Unexpected("something went terribly wrong", 32);
```

They can be `match`ed to discover what they contain:

```rust
let handle_error = (error: NetworkError) => match error {
   NoBytesReceived => print("No bytes received, stopping");
   ConnectionTerminated => print("Connection was terminated");
   Unexpected(err, code) => print("An unexpected error occured: " + err + " (" + conv(code) + ") ");
};
```

Like structs, enums are nominal types, rather than structural.

<br/>

# Type signature assertions

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
