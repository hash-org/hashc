# Primitives
There are the following primitive types:

- `u8`, `u16`, `u32`, `u64`: unsigned integers
- `i8`, `i16`, `i32`, `i64`: signed integers
- `f32`, `f64` : floating point numbers
- `usize`, `isize`: unsigned and signed pointer-sized integer types (for list indexing)
- `ibig`, `ubig`: unlimited size integers
- `bool`: boolean
- `str`: string, copy on write and immutable
- `[A]`: a list containing type A
- `{A:B}`: a map between type A and type B
- `(A, B, C)`: a tuple containing types A, B and C. Elements can be accessed by dot notation (`my_tuple.first`)
- `(a: A, b: B, c: C)` a tuple which contains named members a, b, c with types A, B, C respectively.
- `void` or `()`: the empty tuple type. Has a corresponding `void`/`()` value.
- `never`: a type which can never be inhabited. Used, for example, for functions that never return, like `panic`, or an infinite loop.

Note: the list, map and set type syntax will most likely have to change eventually once literal types are introduced in the language.

## Numbers

Numbers in hash are like numbers in most other statically typed languages.
They come in 3 variants: unsigned, signed, and floating point.

Floating point literals must include either a `.` or a scientific notation exponent
like `3.0`, `3e2`, `30e-1`, etc.

### Host-sized integers

The primitives `usize` and `isize` are intended for list indexing.
This is because some systems (which are 32-bit) may not be able to support indexing a contiguous region of memory that is larger than the 32-bit max value.
So, the `usize` and `isize` primitives are host-system dependent.

#### Compile-time

In the future, Hash will support compile-time arbitrary code execution.
Considering this, the host machine's (on which the code is compiled) `usize` width might differ from the target machine's (on which the code is executed) `usize` width.
To account for this, any `usize` which gets calculated at compile time needs to be checked that it fits within the target `usize`.
This check will happen at compile time, so there is no possibility of memory corruption or wrong data.

### Unlimited-sized integers

The `ibig` and `ubig` number primitives are integer types that have no upper or lower bound and will grow until the host operating system memory is exhausted when storing them.
These types are intended to be used when working with heavy mathematical problems which may exceed the maximum 64 bit integer size.

## Lists

Lists are denoted using square bracket syntax where the values are separated by commas.

Examples:
```rs
x := [1,2,3,4,5,6]; // multiple elements
y := [];
z := [1,]; // optional trailing comma

w: [u64] = [];
// ^^^^^
//  type
```

Grammar for lists:

```
list_literal = "[" ( expr "," )* expr? "]"
list_type = "[" type "]"
```

## Tuples

Tuples have a familiar syntax with many other languages:

- Empty tuples: `(,)` or `()`
- Singleton tuple : `(A,)`
- Many membered tuple: `(A, B, C)` or `(A, B, C,)` 

Examples:
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

It's worth noting that tuples are fancy syntax for structures and are indexed using numerical indices like `0`, `1`, `2`, etc to access each member explicitly.
Although, they are intended to be used mostly for pattern matching, you can access members of tuples like so.
If this is the case, you should consider using a structural data type which will allow you to do the same thing, and name the fields.
Read more about patterns [here](patterns.md).

Grammar for tuples:

```
tuple_literal = ( "(" ( expr "," )* ")" ) | ( "(" ( expr "," )* expr ")" )
tuple_type = ( "(" ( type "," )* ")" ) | ( "(" ( type "," )* type ")" )
```

### Named tuples

Named tuples are tuples that specify field names for each field within the tuple.
This can be done, for example, to have nested fields in structs without having to create another struct for each sub-type.
For example:

```rs
Comment := struct(
    contents: str,
    anchor: (
        start: u32,
        end: u32
    ),
    edited: bool,
    author_id: str,
);
```

Then, you can create a `Comment` instance and then access its fields like so:
```rs
comment := Comment(
    contents = "Hello, world",
    anchor = (
        start = 2,
        end = 4
    ),
    edited = false,
    author_id = "f9erf8g43"
);

print(abs(comment.anchor.start - comment.anchor.end));
```

To initialise a tuple that has named fields, this can be done like so:
```rs
anchor := (start := 1, end := 2); // `anchor: (start: u32, end: u32)` inferred

// This can also be done like so (but shouldn't be used):
anchor: (start: u32, end: u32) = (1, 2); // Warning: assigning unnamed tuple to named tuple.
```

Named tuples can be coerced into *unnamed* tuples if the type layout of both tuples matches. 
However, this is not recommended because specifically naming tuples implies that the type
cares about the names of the fields rather than simply being a positionally structural type.

## Sets

Sets in Hash represent unordered collections of values.
The syntax for sets is as follows:

- Empty set: `{,}`.
- Singleton set : `{A,}`.
- Many membered set: `{A, B, C}` or `{A, B, C,}`.
- Set type: `{A}`, for example `foo: {i32} = {1, 2, 3}`.

```
set_literal = ( "{" "," "}" ) | ( "{" ( expr "," )+ "}" ) | ( "{" ( expr "," )* expr "}" )
set_type = "{" type "}"
```

### Map

Maps in Hash represent collections of key-value pairs.
Any type that implements the `Eq` and `Hash` traits can be used as the key type in a map.
The syntax for maps is as follows:

- Empty map: `{:}`.
- Singleton map : `{A:1}` or `{A:1,}`.
- Many membered map: `{A: 1, B: 2, C: 3}` or `{A: 1, B: 2, C: 3,}` .
- Map type: `{K:V}`, for example `names: {str:str} = {"thom":"yorke", "jonny":"greenwood"}`.

```
map_literal = ( "{" ":" "}" ) | ( "{" ( expr ":" expr "," )* ( expr ":" expr )? "}" )
map_type = "{" type ":" type "}"
```
