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
    1 => print("Got one"),
    2 => print("Got two"),
    3 => print("Got three"),
    _ => print("Got something else"),
}
```

On the left-hand side of the match cases there are the literal patterns `1`, `2` and `3`.
These perform `foo == 1`, `foo == 2` and `foo == 3` in sequence, and the code follows the branch which succeeds first.
If no branch succeeds, the `_` branch is followed, which means "match anything".
Literals can be integer literals for integer types (signed or unsigned), string literals for the `str` type, or character literals for the `char` type:

```rust
match my_char {
    'A' => print("First letter"),
    'B' => print("Second letter"),
    x => print("Letter is: " + conv(x)),
}
```

## Binding patterns


## Destructuring patterns

Destructuring patterns are used to assign parts of an object to separate variables within declarations, `for`, and
`match`statements. A very simple example of a destructuring pattern in a declaration statement would be:

```rust
tup := (1, 2); // 2D point
(x, y) = tup; // x=1, y=2
```

In this example, the `x` and `y` variables are binding to the components of the tuple `tup`.
After destructuring `tup` you can continue to use `tup` with the addition of using the binds
that were created in the statement. This feature is very handy when it comes to data structures
that are fairly complicated and large, and you only want to use three or four components
from the whole structure. 

> **Note**: When you are destructuring components that are represented as references, they are not
> copied but represented as referenced, pattern binds can be thought of as just shorthand for 
> assigning named fields to individual symbols with the same names.

Similarly to declaration statements, `for` statements can also utilise destructuring patterns:

```rust

struct Point = {
    x: int,
    y: int
}

points := [Point {x=1, y=2}, Point {x=3, y=2}, Point {x=-1, y=7}, ...];

for Point {x, y} in points.iter() {
    print(sqrt(x*x + y*y))
}
```
As you can see within the `for` loop, the pattern `Point{x, y}` is being used to
destruct each point in the array into the separate fields.

## Struct patterns

Struct patterns follow a similar syntax to struct literals in Hash. You can discard and
access fields available within a struct by specifying the field name and then followed
by an optional right-hand side pattern to either rename the field or use a literal pattern.

### Basic

Struct patterns can be used in both literals and destructuring contexts. To destructure a struct
within a declaration statement, you specify the name of the struct (it can be namespaced as well), and then
specify the binding fields:

```rust
Point {x, y} := my_point;
```

You can also use struct literal patterns within a `match` statement:


```rust

struct Person = {
    name: str;
    age: int;
    height: float;
    sex: char;
};

p := Person {
    name = "John";
    age = 23;
    height = 1.89;
    sex = 'M';
};

match p {
    Person { name = "John", age } => {
        print("John's age is " ++ conv(age));
    };
    Person { name = "Sarah", age } => {
        print("Sarah's age is " ++ conv(age))
    };
    Person { age } => { 
        print("The other person's age is " ++ conv(age))
    };
}
```

### Renaming fields

In the example, we want to rename one of the fields to a custom binding name:

```rust
struct Car = {
    name: str,
    id: int,
    ...
}

compare_id := (car: Car, id: int) => {
    // destruct the 'id' out of car and rename it
    Car {id = car_id} := car;

    id == car_id
}
```

So, in the above example (which is admittedly unrealistic) we rename the cars `id` field to
`car_id` by specifying the right-hand side binding pattern `= car_id`.

## Namespace patterns

Namespace patterns are very similar to struct patterns, but they can only be used within declarations
statements and when importing symbols from other modules. They follow a simple syntax:

```rust
// imports only a and b from the module
{a, b} = import("./my_lib");

// imports 'c' as my_c, and 'd' from the module.
{c: my_c, d} = import("./other_lib"); 
```

To read more about modules, you can click [here](./modules.md).

## Tuple patterns

Tuple patterns are straight forward, they follow the same syntax as declaring a tuple literal.

To ignore some parts of the tuple, you can use the `_` (ignore) operator to throw away parts of the
tuple. For example, if a 3-element sized tuple was provided and you only want to use the second element,
you can do:

```rust
// tri_group: (int, float, str)
(_, n, _) := tri_group;
```

Pattern matching on tuples is also currently the only way to work with tuples that are sized 9 elements
or greater. The language supports tuples that are sized larger than 9 elements, however it does not
support accessing each element via the property access. So, for example:

```rust
excessive_tup.tenth; // error
(_, _, _, _, _, _, _, _, _, tenth) :=  excessive_tup;
```
> **Note**: You shouldn't use tuples this large, this leads to code that is difficult to read and interpret,
> you should use a struct in that case which would solve the complexities of your data structures.

## List patterns

A list pattern can bind elements at certain positions of the array by using the following syntax:

```rust
[a, b] := arr;
```

Now in this example, the compiler will assume that the size of `arr` is of length 2, and if not it will error since
parts of the array are essentially unhandled. To circumvent this issue you can use the `...`, (spread) operator which
used as a capturing group for some elements. With the example above, you can ignore all of the following elements after
the first two by writing:

```rust
[a, b, ...] := arr;
```

If you want to assign the remaining elements to some bind, you can specify an identifier after the `spread` operator like
so:

```rust
[a, b, ...rest] := arr;
```

If you want to bind elements at the end of the array, you can use the `spread` operator at the start of the pattern
to ignore or capture the elements like so:

```rust
[..., a, b] := arr;
```

Assign the last two elements of the array to `a` and `b` respectively.

One obvious limitation of the `spread` operator is that you can only use it once in the array pattern.
For example, the following pattern will be reported as an error by the compiler:

```rust
[..., a, ...] := arr;
```

```
error: Failed to Typecheck:
 --> 1:6 - 1:9, 1:15 - 1:18
  |
1 | [..., a, ...] := arr;
  |  ^^^     ^^^
  |
  = You cannot use multiple spread operators within a single array pattern.
```

