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
In order to declare a mutable variable, use the `mut` keyword in front of a name binding.

```rs
(mut a, mut b) := (1, 2);
mut test := get_test();

modify_test(&mut test);
a += 2;
b += 3;
```

## Visibility

Visibility modifiers can be added to declarations inside modules or traits.
By default, all declarations in a module scope or `impl` block are private, while all declarations in a `trait` block are public.
To declare that a member is private, use `priv`, while to declare that a member is public, use `pub`.

```rs
// Visible from outside:
pub foo := 3;

// Not visible from outside:
bar := 4;


Foo := trait {
    // Visible from outside
    foo: (Self) -> str;

    // Not visible from outside
    priv bar: (Self) -> str;
};
```

## Grammar

The grammar for name bindings (and partial name bindings/reassignments) is as follows:
 
```
pattern = pattern_binding | ...(other patterns)
pattern_binding = ( "pub" | "priv" )? "mut"? identifier

name_binding =
  | ( pattern ":=" expr )  // Declaration and assignment, infer type
  | ( pattern ( ":" type )? "=" expr  ) // Assignment
  | ( pattern ( ":" type )  ) // Declaration
```
