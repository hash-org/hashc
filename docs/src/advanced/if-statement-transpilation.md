# If Statement transpilation

As mentioned at the start of the conditionals section in the basics chapter, if statements can be
represnted as `match` statements. This is especially adviced when you have many `if` branched and 
more complicated branch conditions.

Internally, the compiler will convert `if` statements into match cases so that it has to do
less work in the following stages of compilation.

In general, transpilation process can be represented as:

```
if <condition_1> {
     <block_1> 
} else if <condition_2> { 
    <block_2> 
} 
... 
} else {
    <block_n>
}

// will be converted to

match true {
    _ if <condition_1> => block_1;
    _ if <condition_2> => block_3;
    ...
    _ => block_n;
}
```


For example, the following `if` statment will be converted as follows:

```rust
if conditionA {
  print("conditionA")
} else if conditionB {
  print("conditionB")
} else {
  print("Neither")
}

// Internally, this becomes:

match true {
  _ if conditionA => { print("conditionA") };
  _ if conditionB => { print("conditionB") };
  _ => { print("Neither") };
}
```

However, this representation is not entirely accurate because the compiler will optimise out some components
out of the transpiled version. Redundant statements such as `match true { ... }` will undergo constant folding
to produce more optimal AST representations of the program.

## Missing 'else' case

If the `if` statement lacks an `else` clause or a default case branch, the compiler will insert one automatically
to avoid issues with pattern exhaustiveness. This behaviour is designed to mimic the control flow of classic `if`
statements because the `else` branch will have an assigned empty expression block.

From the above example, but without the `else` branch:


```rust
if conditionA {
  print("conditionA")
} else if conditionB {
  print("conditionB")
}

// Internally, this becomes:

match true {
  _ if conditionA => { print("conditionA") };
  _ if conditionB => { print("conditionB") };
  _ => { };
}
```
