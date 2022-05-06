# Variables

## Basics
Variables are made of three distinct components. The variable name, the variable type and the 
literal expression that is assigned to the name.

Declaration and assignment can happen separately:
```rust
x: u8;
x = 3;
```

Variables cannot be used until they are assigned.

```rust
x: u8;

print(x) // :^( error
```

Will result in the compiler error:

```
error[0057]: Failed to typecheck: Un-initialised symbol
 --> src/file.hash:3:7
  |
1 | x:u8;
  |     ^ symbol 'x' declared here without initialisation.
  |
  = note: Consider giving 'x' an initial value.

 --> src/file.hash:3:7
  |
3 | print(x)
  |       ^ symbol 'x' is uninitialised.
```

## Type inference

The type of a variable, if not given, is automatically inferred by the value.
In `a: X = b`, if the type of `b` is not `X`, the language produces an error.

