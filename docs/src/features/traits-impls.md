# Traits and implementations

## Traits

Hash supports compile-time polymorphism through traits.
Traits are a core mechanism in Hash; they allow for different implementations of the same set of operations, for different types.
They are similar to traits in Rust, type-classes in Haskell, and protocols in Swift.
For example:
```rs
Printable := trait {
  print: (Self) -> void;
};
```
The above declares a trait called `Printable` which has a single associated function `print`.
The special type `Self` denotes the type for which the trait is implemented.

Traits can be implemented for types in the following way:
```rs
Dog := struct(
  name: str,
  age: i32,
);

Dog ~= Printable {
  // `Self = Dog` inferred
  print = (self) => io::printf(f"Doge with name {self.name} and age {self.age}");
};
```
Now a `Dog` is assignable to any type that has bound `Printable`.

The `~=` operator is the combination of `~` and `=` operators, and it is equivalent to 
```rs
Dog = Dog ~ Printable { ... };
```
The `~` operator means "attach", and it is used to attach implementations of traits to structs and enums.

Trait implementations can be created without having to attach them to a specific type:
```rs
DogPrintable := Printable {
  Self = Dog, // Self can no longer be inferred, it needs to be explicitly specified.
  print = (self) => io.printf(f"Doge with name {self.name} and age {self.age}");
};

doge := Dog(..);
DogPrintable::print(doge); // Trait implementations can be called explicitly like this

Dog ~= DogPrintable; // `DogPrintable` can be attached to `Dog` as long as `DogPrintable::Self = Dog`.

// Then you can also do this, and it will be resolved to `DogPrintable::print(doge)`:
doge.print();
```

Traits can also be generic over other types:
```rs
Sequence := <T> => trait {
  at: (self, index: usize) -> Option<T>;
  slice: (self, start: usize, end: usize) -> Self;
};

List := <T> => struct(...);

// For List (of type `<T: type> -> type`) implement Sequence (of type `<T: type> -> trait`):
// This will be implemented for all `T`.
List ~= Sequence; 
```
Notice that in addition to traits, type functions returning traits can also be implemented for other type functions returning types.
This is possible as long as both functions on the left hand side and right hand side match:
```rs
SomeTrait := <T> => trait {
  Self: type; // Restrict what `Self` can be
  ...
};

// Allowed: `<T: type> -> trait` attachable to `<T: type> -> type`.
(<T> => SomeType) ~= (<T> => SomeTrait<T> {...});

// Not allowed: `<T: type> -> trait` is not attachable to `type`
SomeType ~= (<T> => SomeTrait<T> {...});

// Not allowed: `trait` is not attachable to `<T: type> -> type` because
// `SomeTraitImpl::Self` has type `type` and not `<T: type> -> type`.
SomeType ~= (<T> => SomeTrait<T> {...});
```

Furthermore, traits do not need to have a self type:
```rs
Convert := <I, O> => trait {
  convert: (I) -> O;
};

ConvertDogeToGatos := Convert<Doge, Gatos> {
  convert = (doge) => perform_transformation_from_doge_to_gatos(doge);
};

doggo := Doge(...);
kitty := ConvertDogeToGatos::convert(doggo);
```

Traits can also be used as bounds on type parameters:
```rs
print_things_if_eq := <Thing: Printable ~ Eq> => (thing1: Thing, Thing2: thing) => {
  if thing1 == thing2 {
    print(thing1);
    print(thing2);
  }
};
```
Here, `Thing` must implement `Printable` and `Eq`.
Notice the same attachment syntax (`~`) for multiple trait bounds, just as for attaching trait implementations to types.

Traits are monomorphised at runtime, and thus are completely erased.
Therefore, there is no additional runtime overhead to structuring your code using lots of traits/generics and polymorphism, vs using plain old functions without any generics.
There is, however, additional compile-time cost to very complicated trait hierarchies and trait bounds.

## Implementations

Implementations can be attached to types without having to implement a specific trait, using `impl` blocks.
These are equivalent to trait implementation blocks, but do not correspond to any trait, and just attach the given items to the type as associated items.
Example:

```
Vector3 := <T> => struct(x: T, y: T, z: T);

Vector3 ~= <T: Mul ~ Sub> => impl {
  // Cross is an associated function on `Vector3<T>` for any `T: Mul ~ Sub`.
  cross := (self, other: Self) -> Self => {
      Vector3(
        self.y * other.z - self.z * other.y,
        self.z * other.x - self.x * other.z,
        self.x * other.y - self.y * other.x,
      )
  };
};

print(Vector3(1, 2, 3).cross(Vector3(4, 5, 6)));
```

By default, members of `impl` blocks are public, but `priv` can be written to make them private.

## Grammar

The grammar for trait definitions is as follows:

```
trait_def = "trait" "{" ( expr ";" )* "}"
```

The grammar for trait implementations is as follows:

```
trait_impl = ident "{" ( expr ";" )* "}"
```

The grammar for standalone `impl` blocks is as follows:

```
impl_block = "impl" "{" ( expr ";" )* "}"
```
