# Pattern matching

Pattern matching is a very big part of `Hash` and the productivity of the language.
Patterns are a declarative form of equality checking, similar to patterns in Rust or Haskell.

Pattern matching within `match` statements is more detailed within the [Conditional statements](./conditionals.md#match-cases) section
of the book.
This chapter is dedicated to documenting the various kinds of patterns that there are in Hash.

## Literal patterns

Literal patterns are patterns that match a specific value of a primitive type, like a number or a string.
For example, consider the following snippet of code:

```rust
foo := get_foo(); // foo: i32

match foo {
    1 => print("Got one");
    2 => print("Got two");
    3 => print("Got three");
    _ => print("Got something else");
}
```

On the left-hand side of the match cases there are the literal patterns `1`, `2` and `3`.
These perform `foo == 1`, `foo == 2` and `foo == 3` in sequence, and the code follows the branch which succeeds first.
If no branch succeeds, the `_` branch is followed, which means "match anything".
Literals can be integer literals for integer types (signed or unsigned), string literals for the `str` type, or character literals for the `char` type:

```rust
match my_char {
    'A' => print("First letter");
    'B' => print("Second letter");
    x => print("Letter is: " + conv(x));
}

match my_str {
    "fizz" => print("Multiple of 3");
    "buzz" => print("Multiple of 5");
    "fizzbuzz" => print("Multiple of 15");
    _ => print("Not a multiple of 3 or 5");
}
```

## Binding patterns

Nested values within the value being pattern matched can be bound to symbols, using binding patterns.
A binding pattern is any valid Hash identifier:
```rust
match fallible_operation() { // fallible_operation: () -> Result<f32, i32>
    Ok(success) => print("Got success " + conv(result)); // success: f32
    Err(failure) => print("Got failure " + conv(failure)); // failure: i32
}
```

## Tuple patterns

Tuple patterns match a tuple type of some given arity, and contain nested patterns.
They are irrefutable if their inner patterns are irrefutable, so they can be used in declarations.

```rust
Cat := struct(name: str);

// Creating a tuple:
my_val := (Cat("Bob"), [1, 2, 3]); // my_val: (Cat, [i32])

// Tuple pattern:
(Cat(name), elements) := my_val;

assert(name == "Bob");
assert(elements == [1, 2, 3]);
```

## Constructor patterns

Constructor patterns are used to match the members of structs or enum variants.
A struct is comprised of a single constructor, while an enum might be comprised of multiple constructors.
Struct constructors are irrefutable if their inner patterns are irrefutable, while enum constructors are irrefutable only if the enum contains a single variant.
For example:

```rust
Option := <T> => enum(Some(value: T), None);

my_val := Some("haha");

match my_val {
    // Matching the Some(..) constructor
    Some(inner) => assert(inner == "haha"); // inner: str
    // Matching the None constructor
    None => assert(false);
}
```

The names of the members of a constructor need to be specified if the matching isn't done in order:
```rust
Dog := struct(name: str, breed: str);

Dog(breed = dog_breed, name = dog_name) = Dog(
    name = "Bob",
    breed = "Husky"
) // dog_breed: str, dog_name: str

// Same as:
Dog(name, breed) = Dog(
    name = "Bob",
    breed = "Husky"
) // breed: str, name: str
```

## List patterns

A list pattern can match elements at certain positions of a list by using the following syntax:

```rust
match arr {
    [a, b] => print(conv(a) + " " + conv(b));
    _ => print("Other"); // Matches everything other than [X, Y] for some X and Y
}
```

The `...` spread operator can be used to capture or ignore the rest of the elements of the list at some position:

```rust
match arr {
    [a, b, ...] => print(conv(a) + " " + conv(b));
    _ => print("Other"); // Only matches [] and [X] for some X
}
```

If you want to match the remaining elements with some pattern, you can specify a pattern after the `spread` operator like so:

```rust
match arr {
    [a, b, ...rest] => print(conv(a) + " " + conv(b) + " " + conv(rest));
    [...rest, c] => print(conv(c)); // Only matches [X] for some X, rest is always []
    _ => print("Other"); // Only matches []
}
```

One obvious limitation of the `spread` operator is that you can only use it once in the list pattern.
For example, the following pattern will be reported as an error by the compiler:

```rust
[..., a, ...] := arr;
```

```
error: Failed to typecheck:
 --> 1:6 - 1:9, 1:15 - 1:18
  |
1 | [..., a, ...] := arr;
  |  ^^^     ^^^
  |
  = You cannot use multiple spread operators within a single list pattern.
```

## Module patterns

Module patterns are used to match members of a module.
They are used when importing symbols from other modules.
They follow a simple syntax:

```rust
// imports only a and b from the module
{a, b} = import("./my_lib");

// imports 'c' as my_c, and 'd' from the module.
{c as my_c, d} = import("./other_lib"); 
```

To read more about modules, you can click [here](./modules.md).

## Grammar

The grammar for patterns is as follows:

```
pattern = 
    |
```
