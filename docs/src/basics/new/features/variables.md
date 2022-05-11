# Name bindings

## Basics

Name bindings are made of three distinct components. The name, the type and the 
value that is assigned to the name.

Declaration of variables happens using the `:` and `=` symbols:
```rs
x: i32 = 3;
```
The `:` symbol is used to denote the type of a variable, and the `=` symbol is used to assign a value to it.
The type can be omitted, in which case it is inferred:
```rs
x := "Terence Tao"; // `x: str` inferred
x: str = "Terence Tao"; // same thing
x: i32 = "Terence Tao"; // Compile error: `str` is not assignable to `i32`.
```

Declaration and assignment can happen separately:
```rs
x: i32:
print(x); // Compile error: `x` might be uninitialised at this point!
x = 3; 
print(x); // Ok
```

A variable declaration is an expression like any other, and returns the value of the variable.
This means that you can write something like:
```rs
while (bytes_read := read_file(&buffer)) != 0 {
  print("Read some bytes!");
}
```

Hash is statically typed, which means that variables cannot change types:
```
x := "Ha!";
x = Some("Baaa"); // Compile error: `Option<str>` is not assignable to `str`.
```

## Mutability

By default, all bindings in Hash are constant.
In order to declare a mutable variable, use the `mut` keyword in front of the 
