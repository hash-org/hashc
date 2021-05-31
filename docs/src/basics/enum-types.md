# Enum types

Hash enums are similar to Rust enums or Haskell data types.
Each variant of an enum can also hold some data.
These are also known as *algebraic data types*, or *tagged unions*.

```rust
enum NetworkError = {
   NoBytesReceived;
   ConnectionTerminated;
   Unexpected(str, int);
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
