# Struct types

In Hash, structs are pre-defined collections of heterogeneous types, similar to C or Rust:

```rust
FloatVector3 := struct(
   x: f32,
   y: f32,
   z: f32,
);
```

A struct is comprised of a set of fields.
Each field has a name, a type, and an optional default value.

Structs can be instantiated with specific values for each of the fields.
Default values can be omitted, but can also be overridden.

```rust
Dog := struct(
   age: u32 = 42,
   name: str,
);

d := Dog(name = "Bob");

print(d); // Dog(name = "Bob", age = 42)
```

Structs are nominal types.
An argument of type `Dog` can only be fulfilled by an instance of `Dog`, and you can't pass in a struct that has the same fields but is of a different named type.

```rust
dog_name := (dog: Dog) => dog.name;

FakeDog := struct(
   age: u32 = 42,
   name: str,
);

print(dog_name(d)); // "Bob"
print(dog_name(FakeDog(age = 1, name = "Max"))); // Error: Type mismatch: was expecting `Dog`, got `FakeDog`.
```

# Enum types

Hash enums are similar to Rust enums or Haskell data types.
Each variant of an enum can also hold some data.
These are also known as *algebraic data types*, or *tagged unions*.

```rust
NetworkError := enum(
   NoBytesReceived,
   ConnectionTerminated,
   Unexpected(message: str, code: i32),
);
```

Enum contents consist of a semicolon-separated list of variant names.
Each variant can be paired with some data, in the form of a comma-separated list of types.

```rust
err := NetworkError::Unexpected("something went terribly wrong", 32);
```

They can be `match`ed to discover what they contain:

```rust
handle_error := (error: NetworkError) => match error {
   NoBytesReceived => print("No bytes received, stopping");
   ConnectionTerminated => print("Connection was terminated");
   Unexpected(message, code) => print("An unexpected error occurred: " + err + " (" + conv(code) + ") ");
};
```

Like structs, enums are nominal types, rather than structural.
Each enum member is essentially a struct type.

## Generic types

Because Hash supports type functions, structs and enums can be generic over some type parameters:

```rust
LinkedList := <T> => struct(
   head: Option<&raw T>,
);

empty_linked_list = <T> => () -> LinkedList<T> => {
   LinkedList(head = None)
};

x := empty_linked_list<i32>(); // x: LinkedList<i32> inferred
```

Notice that `struct(...)` and `enum(...)` are expressions, which are bound to names on the left hand side.
For more information, see [type functions](./type-functions.md).

## Grammar

The grammar for struct definitions is as follows:

```
struct_member =
  | ( ident ":=" expr )  // Declaration and assignment, infer type
  | ( ident ( ":" type )? "=" expr  ) // Assignment
  | ( ident ( ":" type )  ) // Declaration

struct_def := "struct" "(" struct_member* ")"
```

The grammar for enum definitions is as follows:

```
enum_member =
  | ident // No fields
  | ident "(" struct_member* ")" // With fields

enum_def := "enum" "(" enum_member* ")"
```
