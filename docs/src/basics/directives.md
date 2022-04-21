# Directives

## Overview

`Hash` has the ability to specify directives onto general expressions. Directives 
are essentially built-in compiler functionality. Directives are similar to annotations 
in Python decorators and Java annotations. They serve the purpose of providing a 
facet for meta-programming. Currently, directives are primarily being used when 
debugging or experimenting with compile-time evaluation and are not yet intended for full 
usage until the language has matured enough beyond a first (or a few) syntactic 
revisions.

## General syntax and notes

Directives are attached labels to expression that follow the syntax `#<identifier>`. 
This means that directives can be placed onto any expression whether it is a block
or a simple expression. 

The general syntax for directives is:

```
#<identifier> <expr>
```

This also means that multiple directives can be specified onto a single expression like so:

```
#directive_0 #directive_1 expr()
```
This means that the syntax tree for the directive is then:
```
body
└─expr
  └─directive "directive_0"
    └─directive "directive_1"
      └─function_call
        └─subject
          └─variable
            └─named "expr"
```


## Example

An Example of a directive in use is the `#dump` directive.

```rust
let fib = #dump (n: u32) -> u32 => 
   if n == 1 || n == 2 {
       n
   } else {
       fib(n - 1) + fib(n - 2)
   };
}
```

The `dump` directive is used to dump the generated instructions that the compiler produces for 
the `fib` function at compile time. This is useful when debugging code generation. However, 
this is only a very brief example of what directives can be used when using them for 
meta-programming.




## Other notes 🚧

- In the future, directives will be able to be defined by the user using a specific format. 
See discussion [here](https://github.com/hash-org/lang/discussions/149#discussioncomment-2603749).

- Many directives such as `#dump` and `#memoise` are built in compile time functions that 
may invoke specific behaviour within the compiler when being invoked.
