## Primitives
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
- `(a: A, b: B, c: C)` a tuple which contains named members a, b, c with types A, B, C respectively.
- `void` or `()`: the empty type. Has a corresponding `void` value.
- `never`: a type which can never be instantiated. Used, for example, for functions that never return, like `panic`.

## Numbers

Numbers in hash are like numbers in most other statically typed language. Numbers come in 3 variants, 'unsigned', 'signed' and 'floating point'.

Floating point literals must include either a `.` or a scientific notation exponent
like `3.0`, `3e2`, `30e-1`, etc.

### Number types like `usize` & `isize` & `ibig` & `ubig`

These number primitives are added for convenience when working with a variety of
problems and host operating systems. The primitives `usize` and `isize` are intended
for list indexing. This is because on some systems (which are 32bit) may not be able
to support indexing a contiguous region of memory that is larger than '32bit' max value. So, the `usize` and `isize` primitives are host system dependent. 

The `ibig` and `ubig` number primitives are integer types that have no upper
or lower bound and will grow until the host operating system memory is exhausted 
when storing them. These types are intended to be used when working with heavy mathematical problems which may exceed the maximum '64bit' integer boundary.

## Bracketed type syntax

### List
Lists are denoted using the the common square bracket syntax where the values are
separated by commas, like so:

```rs
x := [1,2,3,4,5,6]; // multiple elements
y := [];
z := [1,]; // optional trailing comma
```

To explicitly declare a variable is of a `list` type, you do so:

```rs
some_list: [u64] = [];
//         ^^^^^
//          type
```


### Tuple

Tuples have a familiar syntax with many other languages, but exhibit two distinct
differences between the common syntax. These differences are:

- Empty tuples: `(,)` or `()`
- Singleton tuple : `(A,)`
- Many membered tuple: `(A, B, C)` or `(A, B, C,)` 

To explicitly declare a variable is of a `tuple` type, you do so:

```rs
empty_tuple: (,) = (,);
//           ^^^
//           type

empty_tuple: () = ();
//           ^^
//          type

some_tuple: (str, u32) = ("string", 12);
//          ^^^^^^^^^^
//             type
```
**Note**: Trailing commas are not allowed within type definitions.


It's worth noting that tuples are fancy syntax for structures and are indexed
using 'english' numerical phrasing like `first`, `second`, `third`, etc to access
each member explicitly. Although, they are intended to be used mostly for pattern
matching, you can access members of tuples like so. However, you will not be able to access members of tuples that are larger than 10 elements in size. 
If this is the case, you should consider using a structural data type which will
allow you to do the same thing, and name the fields. Read more about patterns [here](pattern-matching.md).

### Named tuples

Named tuples are a variant of tuples that specifies field names for each field within the field. This can 
be done for various purposes which might make some definitions of types convenient and not requiring 
creating a `struct` for each sub-type. For example:

```rust
struct Comment {
    contents: str,
    anchor: (
        start: u32,
        end: u32
    ),
    edited: bool,
    author_id: str,
    ...
};

// Which then means that u can create the `Comment` type and then access fields like so:

comment := Comment { .. };

print(abs(comment.anchor.start - comment.anchor.end));
```

To initialise a struct that has named fields, this can be done like so:
```rust
anchor := (start := 1, end := 2 ); // :t anchor -> (start: u32, end: u32)

// This can also be done like so (but shouldn't be used):
anchor: (start: u32, end: u32) = (1, 2);
```

Named tuples can be coerced into *unnamed* tuples if the type layout of both tuples matches. 
However, this is not recommended because specifically naming tuples implies that the type
cares about the names of the fields rather than simply being a structural type.

### Set

Like tuples, sets have the same syntactic differences:

- Empty set: `{,}`
- Singleton set : `{A,}`
- Many membered set: `{A, B, C}` or `{A, B, C,}` 

To explicitly declare a variable is of a `set` type, you do so:

```rs
some_map: {str} = {,};
//        ^^^^^
//       set type
```

### Map

Like tuples, sets have the same syntactic differences:

- Empty map: `{:}`
- Singleton map : `{A:1}` or `{A:1,}`
- Many membered map: `{A: 1, B: 2, C: 3}` or `{A: 1, B: 2, C: 3,}` 

To explicitly declare a variable is of a `map` type, you do so:

```rs
some_map: {str: u8} = {:};
//        ^^^^^^^^^
//        map type
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
