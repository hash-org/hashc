# Loop transpilation

As mentioned at the start of the [loops](./../basics/loops.md) section in the [basics](./../basics/intro.md) chapter, the `loop` control flow keyword
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
