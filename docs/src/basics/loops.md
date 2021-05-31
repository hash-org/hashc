# Loop constructs

Hash contains 3 distinct loop control constructs: `for`, `while` and `loop`. Each construct has
a distinct usage case, but they can often be used interchangebly without hastle and are merely
a style choice.

## General

Each construct supports the basic `break` and `continue` loop control flow statements. These statements
have the same properties as in many other languages like C, Rust, Python etc.

`break` - Using this control flow statements immediatelly terminates the loop and continues
to any statement after the loop (if any).

`continue` - Using this control flow statement will immediatelly skip the current iteration
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
let nums: [u32] = [1,2,3,4,5,6,7,8,9,10]; 

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
to `true`, the loop body is executed, oterhwise the interpreter moves on. The loop body can also
use loop control flow statements like `break` or `continue` to prematurely stop looping for a
given condition.

While loops can be defined as:

```rust

let c: u32 = 0;

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
let c: u32 = 100;

while c -= 1 {
    ...
}
```
Running the following code snippet produces the following error:
```
error: Failed to Typecheck:
 --> 3:7 - 3:12
  |
3 | while c -= 1 {
  |       ^^^^^^
  |       Expression does not have a boolean type 
```


## Loop

The loop consturct is the simplest of the three. The basic syntax for a loop is as follows:

```rust

let c: u64 = 1;

loop {
    print("I looped " + c + " times!");
    c += 1;
}
```

You can also use conditional statements within the loop body (which is equivalent to a function body) like so:

```rust

let c: u64 = 1;

loop {
    if c == 10 { break }

    print("I looped " + c + " times!");
    c += 1;
} // this will loop 10 times, and print all 10 times
```

```rust
let c: u64 = 1;

loop {
    c += 1;
    if c % 2 != 0 { continue };

    print("I loop and I print when I get a  " + c);
} // this will loop 10 times, and print only when c is even
```
<<<<<<< HEAD:docs/loops.md

## Miscellaneous

As mentioned at the start of the introduction, the `loop` control flow keyword
is the most universal control flow since to you can use `loop` to represent 
both the `for` and `while` loops. 

### for loop transpillation

Since `for` loops are used for iterators in hash, we transpile the construct into
a primitive loop. An iterator can be traversed by calling the `next` function on the
iterator. Since `next` returns a `Option` type, we need to check if there is a value
or if it returns `None`. If a value does exist, we essentially perform an assignment
to the pattern provided. If `None`, the branch immediatelly breaks the `for` loop.
A rough outline of what the transpillation process for a `for` loop looks like:

For example, the `for` loop can be expressed using `loop` as:

 ```
 for <pat> in <iterator> {
     <block>
 }

 // converted to
 loop {
     match next(<iterator>) {
         Some(<pat>) => <block>;
         None        => break;
     }
 }
```

An example of the transpillation process:

```rust
let i = [1,2,3,5].into_iter();

for x in i {
    print("x is " + x);
}


// the same as...
let i = [1,2,3,5].into_iter();

loop {
  match next(i) {
    Some(x) => {print("x is " + x)};
    None => break;
  }
}
```

### While loop internal representation

 In general, a while loop transpilation process occurs by transferring the looping 
 condition into a match block, which compares a boolean condition. If the boolean
 conditionb evaluates to `false`, the loop will immediatelly `break`. Otherwise
 the body expression is exected. A rough outline of what the transpillation process for a `while` loop looks like:

 ```
 while <condition> {
     <block>
 }

 // converted to
 loop {
     match <condition> {
         true  => <block>;
         false => break;
     }
 }
 ```

This is why the condition must explicitly return a boolean value.

An example of a transpilation:

And the `while` loop can be written using the `loop` directive
like so:

```rust
let c = 0;

loop {
    match c < 5 { // where 'x' is the condition for the while loop
        true  => c += 1;
        false => break;
    }
}

// same as...
let c = 0;

while c < 5 {
    c+=1;
}
```


### Loop construct

Similarly, the `loop` keyword is equivalent of someone writing a `while` loop that has
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
=======
>>>>>>> main:docs/src/basics/loops.md
