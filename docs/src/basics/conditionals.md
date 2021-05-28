## Conditional statements

Conditional statements in the `Hash` programming language are very similar to other languages such as Python, Javascript, C and Rust. However, there is one subtle **difference**, which is that the statement provided to a conditional statement must always evaluate to an explicit boolean value. 


## If-else statements

If statements are very basic constructs in Hash. An example of a basic `if-else` statement is as follows:

```rust
// checking if the value 'a' evaluates to being 'true'
if a { print("a"); } else { print("b"); }

// using a comparison operator
if b == 2 { print("b is " + b); } else { print ("b is not " + conv(b)); }
```

Obviously, this checks if the evaluation of `a` returns a boolean value. If it does not
evaluate to something to be considered as true, then the block expression defined
at `else` is executed.

If you want multiple clauses, you can utilise the `else-if` syntax to define multiple
conditional statements. To use the `else-if` syntax, you do so like this:

```rust
if b == 2 {
     print("b is 2")
} else if b == 3 {
     print("b is 3")
} else {
    print("b isn't 2 or 3 ")
}
```

As mentioned in the introduction, a conditional statement must evaluate an explicit boolean value. The `if` statement syntax will not infer a boolean value from a statement within `Hash`. This design feature is motivated by the fact that in many languages, common bugs and mistakes occur with the automatic inference of conditional statements. 

An example of an invalid program is:
```rust
let a: u8 = 12;

if a { print("a") }
```

### Additional syntax

Furthermore, if you do not want an else statement you can do:

```rust
if a { print("a") }  // if a is true, then execute
```

which is syntactic sugar for:

```rust
if a { print("a") } else {}
```

Additionally, since the `if` statement body's are also equivalent to functional bodies, you
can also specifically return a type as you would normally do within a function body:

```rust
let abs: (i64: x) => i64 = if x < 0 { -x } else { x }
```

However, you cannot do something like this:

```rust
let abs: (i64: x) => i64 = if x < 0 { -x }
```

**Note**: here that you will not get a syntax error if you run this, but you will encounter an error during the interpretation stage of the program because the function may not have any return type since this has no definition
of what should happen for the `else` case.

## If statements and Enums 🚧
You can destruct enum values within if statments using the `if-let` syntax, like so:

```rust
enum Result = <T, E> => {
   Ok(T);
   Err(E);
};

// mission critical, program should exit if it failed
let result: Result<u16, str> = Ok(12);

if let Ok(value) = result  { 
  print("Got '" + conv(value) + "' from operation") 
} else let Err(e) = result {
  panic("Failed to get result: " + e);
}
```

Furthermore, for more complicated conditional statements, you can include an expression
block which is essentially treated as if it was a functional body, like so:

```rust
let f: str = "file.txt";

if { let a = open(f); is_ok(a) } {
    // run if is_ok(a) returns true
}

// the above statement can also be written as
let a = open(f);

if is_ok(a) {
    // run if is_ok(a) returns true
}

```
The only difference between those two examples is that within the first, a is contained within
the if statement condition body expression, i.e; the `a` variable will not be visible to any further
scope. This has some advantages, specifically when you don't wish to store that particular result
from the operation. But if you do, you can always use the second version to utilise the result
of `a` within the `if` statement body or later on in the program.

<br />

## Match cases

Match cases are one step above the simple `if-else` syntax.  Using a matching case, you can construct more complicated cases in a more readable format than u can with an `if-else` statement. Additionally, you can destruct Enums into their corresponding values. To use a matching case, you do the following:

```rust

let a = input<u8>();

let m2 = match a {
  1 => "one";
  2 => "two";
  _ => "not one or two";
}

// Or as a function

let convert: (x: u8) => str = (x) => match x {
  1 => "one";
  2 => "two";
  _ => "not one or two";
}

let m = convert(input<u8>());
```

The `_` case is a special wildcard case that captures any case. This is essentially synonymous with the `else` clause in many other languages like Python or JavaScript. For conventional purposes, it should be included when creating a `match` statement where the type value is not reasonably bounded (like an integer). One subtle difference with the `match` syntax is you must always explicitly define a `_` case. This language behaviour is designed to enforce that `explicit` is better than `implicit`. So, if you know that a program should never hit
the default case:

```rust
match x {
  1 => "one";
  2 => "two";
  _ => unreachable(); // we know that 'x' should never be 1 or 2.
}
```
**Note**: You do not have to provide a default case if you have defined all the cases for a type (this mainly applies to enums).


Additionally, because cases are matched incrementally, by doing the following:

```rust
let convert: (x: u8) => str = (x) => match x {
  _ => "not one or two";
  1 => "one";
  2 => "two";
}
```

The value of `m` will always evaluate as `"not one or two"` since the wildcard matches any condition.


Match statements are also really good for destructing enum types in Hash. 
For example,

```rust
enum Result = <T, E> => {
   Ok(T);
   Err(E);
};

...

// mission critical, program should exit if it failed
let result: Result<u16, str> = Ok(12);

match result {
  Ok(value) => print("Got '" + conv(value) + "' from operation");
  Err(e)    => panic("Failed to get result: " + e);
}
```


To specify multiple conditions for a single case within a `match` statement, you can do so by
writing the following syntax:

```rust
let x: u32 = input<u32>();

match x {
  1 | 2 | 3       => print("x is 1, 2, or 3");
  4 | 5 | {2 | 4} => print("x is either 4, 5 or 6"); // using bitwise or operator
  _               => print("x is something else");
}
```

To specify more complex conditional statements like and within the match case, you
can do so using the `match-if` syntax, like so:


```rust
let x: u32 = input<u32>();
let y: bool = true;

match x {
  1 | 2 | 3 if y => print("x is 1, 2, or 3 when y is true");
  {4 if y} | y   => print("x is 4 and y is true, or  x is equal to y"); // using bitwise or operator
  {2 | 4 if y}   => print("x is 6 and y is true");
  _              => print("x is something else");
}
```
