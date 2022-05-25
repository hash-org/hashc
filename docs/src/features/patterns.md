# Patterns

Pattern matching is a very big part of `Hash` and the productivity of the language.
Patterns are a declarative form of equality checking, similar to patterns in Rust or Haskell.

Pattern matching with `match` statements is more detailed within the [Control flow](./control-flow.md) section
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
{a, b} := import("./my_lib");

// imports c as my_c, and d from the module.
{c as my_c, d} := import("./other_lib"); 

// imports Cat from the nested module as NestedCat
{Cat as NestedCat} := mod {
    pub Cat := struct(name: str, age: i32);
};
```

You do not need to list all the members of a module in the pattern; the members which are not listed will be ignored.
To read more about modules, you can click [here](./modules.md).

## Or-patterns

Or-patterns are specified using the `|` pattern operator, and allow one to match multiple different patterns, and use the one which succeeds.
For example:

```rust
symmetric_result: Result<str, str> := Ok("bilbobaggins");

(Ok(inner) | Err(inner)) := symmetric_result; // inner: str
```

The pattern above is irrefutable because it matches all variants of the `Result` enum.
Furthermore, each branch has the binding `inner`, which always has the type `str`, and so is a valid pattern.
The same name binding can appear in multiple branches of an or-pattern, given that it is bound in every branch, and always to the same type.
Another use-case of or-patterns is to collapse match cases:

```rust
match color {
    Red | Blue | Green => print("Primary additive");
    Cyan | Magenta | Yellow => print("Primary subtractive");
    _ => print("Unimportant color");
}
```

## Conditional patterns

Conditional patterns allow one to specify further arbitrary boolean conditions to a pattern for it to match:

```rust
match my_result {
    Ok(inner) if inner > threshold * 2.0 => {
        print("Phew, above twice the threshold");
    };
    Ok(inner) if inner > threshold => {
        print("Phew, above the threshold but cutting it close!");
    };
    Ok(inner) => {
        print("The result was successful but the value was below the threshold");
    };
    Err(_) => {
        print("The result was unsuccessful... Commencing auto-destruct sequence.");
        auto_destruct();
    };
}
```

They are specified using the `if` keyword after a pattern.
Conditional patterns are always refutable, at least as far as the current version of the language is concerned.
With more advanced type refinement and literal types, this restriction can be lifted sometimes.

## Pattern grouping

Patterns can be grouped using parentheses `()`.
This is necessary in declarations for example, if one wants to specify a conditional pattern:

```rust
// get_value: () -> bool;
true | false := get_value(); // Error: bitwise-or not implemented between `bool` and `void`
(true | false) := get_value(); // Ok
```

## Ignore pattern

The ignore pattern, represented by a single underscore `_`, matches any value, same as a binding pattern.
However, it does not bind the value to any name, and instead ignores it.
This is useful if a value or part of a value is unimportant in the matching process:

```rust
match animal {
    Dog(name = _) => { // We don't care about the name of the dog, just that it is a dog
        ...
    };
    ...
}
```

## Grammar

The grammar for patterns is as follows:

```
pattern = 
    | single_pattern
    | or_pattern

single_pattern =
    | binding_pattern
    | constructor_pattern
    | tuple_pattern
    | module_pattern
    | literal_pattern
    | list_pattern

or_pattern = ( single_pattern "|" )+ single_pattern

binding_pattern = identifier

tuple_pattern_member = identifier | ( identifier "=" single_pattern )

constructor_pattern = access_name ( "(" ( tuple_pattern_member "," )* tuple_pattern_member? ")" )?

tuple_pattern = 
    | ( "(" ( tuple_pattern_member "," )+ tuple_pattern_member? ")" ) 
    | ( "(" tuple_pattern_member "," ")" )

module_pattern_member = identifier ( "as" single_pattern )?

module_pattern = "{" ( module_pattern_member "," )* module_pattern_member? "}"

literal_pattern = integer_literal | string_literal | character_literal | float_literal

list_pattern_member = pattern | ( "..." identifier? )

list_pattern = "[" ( list_pattern_member "," )* list_pattern_member? "]"
```

Note: ignore patterns are encapsulated within `binding_pattern` (underscore is a valid identifier).
