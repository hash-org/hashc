# Struct types

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

Structs can be instantiated with specific values for each of the fields.
Default values can be omitted, but can also be overridden.

```rust
struct Dog = {
   age: u32 = 42;
   name: str;
}

d := Dog { name = "Bob" };

print(d); // Dog { name = "Bob"; age = 42; }
```

Structs are nominal types.
An argument of type `Dog` can only be fulfilled by an instance of `Dog`, and you can't pass in a struct that has the same fields but is of a different logical type.

```rust
dog_name := (dog: Dog) => dog.name;

struct FakeDog = {
   age: u32 = 42;
   name: str;
}

print(dog_name(d)); // "Bob"
print(dog_name(FakeDog { age = 1, name = "Max" })); // Error: Type mismatch: was expecting `Dog`, got `FakeDog`.
```

