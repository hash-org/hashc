## Control flow

Control flow statements in the `Hash` programming language are very similar to other languages such as Python, JavaScript, C and Rust.
One key difference is that control flow can always be used in expression position in addition to statement position.

## If-else blocks

If-else blocks are very basic constructs in Hash.
An example of a basic if-else block is as follows:

```rust
// checking if the value 'a' evaluates to 'true'
if a { 
    print("a");
} else { 
    print("b");
}

// using a comparison operator
if b == 2 { 
    print("b is " + b);
} else { 
    print ("b is not " + conv(b));
}
```

This checks if the evaluation of `a` returns a boolean value. If it does not
evaluate to `true`, then the code in `else` is executed.

If you want multiple clauses, you can utilise the else-if syntax to define multiple
conditional statements:

```rust
if b == 2 {
    print("b is 2")
} else if b == 3 {
    print("b is 3")
} else {
    print("b isn't 2 or 3 ")
}
```

As mentioned in the introduction, the subject of an `if` statement must evaluate to a `bool` value.
If the type of the subject is something other than `bool`, an error will be generated at compile-time.

An example of an invalid program is:
```rust
a := 12;
if a { print("a"); }
// Compile error: The type of `a` is `i32`, but was expecting `bool`.
```

### Additional syntax

The `else` clause can be omitted, in which case it is equivalent to `else {}`.
However, in this case the return type of the contents of the `if` block must be `void`.

```rust
if a {
    print("a");
}

// same as:
if a {
    print("a");
} else { }
```

In general, each branch of an if-else block chain must have the same return type.
You can also assign values to if-else blocks, since they are expressions:
```rust
my_value := if some_condition() { 3 } else { 5 };
```

However, this will not work, because the two branches (including the implicit `else {}`) do not have the same return type:
```rust
my_value := if some_condition() { 3 };
// Compile error: `else` branch of `if` block returns `void`, but `if` branch returns `i32`.
```

## Match cases

Match cases are one step above the simple `if-else` syntax.  Using a matching case, you can construct more complicated cases in a more readable format than u can with an `if-else` statement. Additionally, you can destruct Enums into their corresponding values. To use a matching case, you do the following:

```rust

a := input<u8>();

m2 := match a {
  1 => "one";
  2 => "two";
  _ => "not one or two";
}

// Or as a function

convert: (x: u8) => str = (x) => match x {
  1 => "one";
  2 => "two";
  _ => "not one or two";
}

m := convert(input<u8>());
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
convert: (x: u8) => str = (x) => match x {
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
result: Result<u16, str> = Ok(12);

match result {
  Ok(value) => print("Got '" + conv(value) + "' from operation");
  Err(e)    => panic("Failed to get result: " + e);
}
```


To specify multiple conditions for a single case within a `match` statement, you can do so by
writing the following syntax:

```rust
x: u32 = input<u32>();

match x {
  1 | 2 | 3       => print("x is 1, 2, or 3");
  4 | 5 | {2 | 4} => print("x is either 4, 5 or 6"); // using bitwise or operator
  _               => print("x is something else");
}
```

To specify more complex conditional statements like and within the match case, you
can do so using the `match-if` syntax, like so:


```rust
x: u32 = input<u32>();
y: bool = true;

match x {
  1 | 2 | 3 if y => print("x is 1, 2, or 3 when y is true");
  {4 if y} | y   => print("x is 4 and y is true, or  x is equal to y"); // using bitwise or operator
  {2 | 4 if y}   => print("x is 6 and y is true");
  _              => print("x is something else");
}
```
# Loop constructs

Hash contains 3 distinct loop control constructs: `for`, `while` and `loop`. Each construct has
a distinct usage case, but they can often be used interchangeably without hassle and are merely
a style choice.

## General

Each construct supports the basic `break` and `continue` loop control flow statements. These statements
have the same properties as in many other languages like C, Rust, Python etc.

`break` - Using this control flow statements immediately terminates the loop and continues
to any statement after the loop (if any).

`continue` - Using this control flow statement will immediately skip the current iteration
of the loop body and move on to the next iteration (if any). Obviously, if no iterations
remain, `continue` behaves just like `break`.

## For loop

###  Basics

For loops are special loop control statements that are designed to be used
with iterators. 

For loops can be defined as:

```rust
for i in range(1, 10) { // range is a built in iterator
    print(i);
}
```

Iterating over lists is also quite simple using the `iter` function to 
convert the list into an iterator:

```rust
nums: [u32] = [1,2,3,4,5,6,7,8,9,10]; 

// infix functional notation
for num in nums.iter() {
    print(num);
}

// using the postfix functional notation
for num in iter(nums) {
    print(nums);
}
```

### iterators

Iterators ship with the standard library, but you can define your own iterators via the Hash generic typing system.

An iterator `I` of `T` it means to have an implementation `next<I, T>` in scope the current scope. 
So, for the example above, the `range` function is essentially a `RangeIterator` of the `u8`, `u16`, `u32`, `...` types.

More details about generics are [here](./generics-polymorphism.md).


## While loop

###  Basics

While loops are identical to 'while' constructs in other languages such as Java, C, JavaScript, etc.
The loop will check a given conditional expression ( must evaluate to a `bool`), and if it evaluates
to `true`, the loop body is executed, otherwise the interpreter moves on. The loop body can also
use loop control flow statements like `break` or `continue` to prematurely stop looping for a
given condition.

While loops can be defined as:

```rust

c: u32 = 0;

while c < 10 {
    print(i);
}
```

The `loop` keyword is equivalent of someone writing a `while` loop that has
a conditional expression that always evaluate to `true`; like so,

```rust
while true {
    // do something
}

// is the same as...

loop {
    // do something
}
```


> **Note**: In `Hash`, you cannot write `do-while` loops, but if u want to write a loop that behaves
> like a `do-while` statement, here is a good example using `loop`:


```rust

loop {
    // do something here, to enable a condition check,
    // and then use if statement, or match case to check
    // if you need to break out of the loop.

    if !condition {break}
}    
```

### Expression blocks and behaviour

Furthermore, The looping condition can also be represented as a block which means it can have any number of expressions
before the final expression. For example:

```rust
while {c += 1; c < 10} {
    print(i);
}
```

It is worth noting that the looping expression whether block or not must explicitly have the 
`boolean` return type. For example, the code below will fail typechecking:

```rust
c: u32 = 100;

while c -= 1 {
    ...
}
```
Running the following code snippet produces the following error:
```
error[0052]: Failed to Typecheck: Mismatching types.
 --> 3:7 - 3:12
1 | c: u32 = 100;
2 |
3 | while c -= 1 {
  |       ^^^^^^  Expression does not have a 'boolean' type 
  |
  = note: The type of the expression was `(,)` but expected an explicit `boolean`.
```


## Loop

The loop construct is the simplest of the three. The basic syntax for a loop is as follows:

```rust

c: u64 = 1;

loop {
    print("I looped " + c + " times!");
    c += 1;
}
```

You can also use conditional statements within the loop body (which is equivalent to a function body) like so:

```rust

c: u64 = 1;

loop {
    if c == 10 { break }

    print("I looped " + c + " times!");
    c += 1;
} // this will loop 10 times, and print all 10 times
```

```rust
c: u64 = 1;

loop {
    c += 1;
    if c % 2 != 0 { continue };

    print("I loop and I print when I get a  " + c);
} // this will loop 10 times, and print only when c is even
```
