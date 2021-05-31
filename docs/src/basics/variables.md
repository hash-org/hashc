# Variables

## Basics
Variables are made of three distinct components. The variable name, the variable type and the 
literal expression that is assigned to the name.

Declaration and assignment can happen separately:
```rust
let x: u8;
x = 3;
```

Variables cannot be used until they are assigned.

```rust
let x: u8;

print(x) // :^( error
```

Will result in the compiler error:

```
error: Failed to typecheck:
 --> 1:5
  |
1 | let x:u8;
  |     ^--- symbol 'x' declared here without initialisation.
  |

 --> 3:7
  |
3 | print(x)
  |       ^
  |   symbol 'x' is uninitialised.
```

## Type inference

The type of a variable, if not given, is automatically inferred by the value.
In `let a: X = b`, if the type of `b` is not `X`, the language produces an error.

