# Macros
 
This section describes the syntax for macros in Hash. Macros are a way to write code that writes other code. There are two kind of macro invocations: one macro works on AST items, and the other works on 
tokens.

## AST macros 

AST level macros are written with the syntax `#marco_name <subject>`
or `#[macro_name] <subject>`. The first form is a used as a shorthand 
for macros that don't have any additional arguments to the macro itself. 

For example, the `#dump_ast` macro will accept any AST item as the subject and print the parsed AST to the console. 
    
```rust
#dump_ast main := () => {
    println("Hello, world!");
}
```

An example of the AST macro being used to set some attributes on a function:
```rust
#[attr(foreign(c), no_mangle, link_name = "jpeg_read_header")]
jpeg_read_header := (&raw cinfo, bool require_image) -> i32;
```

## Token macros

Token macros follow a similar syntax to AST macros, but instead of working on AST items, they work on tokens. The syntax for token macros is `@macro_name <subject>` or `@[macro_name] <subject>`. The first form is a used as a shorthand for token macros that have no arguments. However, one significant difference between token macros and AST macros is that the token macro only accepts a token tree 
as the subject. A token tree is a sequence of tokens that are 
enclosed in a pair of delimiters. Token trees are either `[...]`, `{...}` or `(...)`. It is then up to the macro to define various 
rules for accepting the token tree:

An example of using `min` and `max` macros:
```rust
main := () => {
    min := @min {1 + 2, 3 * 4, 7 - 6 + 1 };
    max := @max {1 + 2, 3 * 4, 7 - 6 + 1 };

    if max - min == 0 {
        println("min and max are equal")
    } else {
        println("min and max are not equal")
    }
}
```

Another example of macro with a token tree for HTML:
```html
welcome := () => {
    @[xml(variant=html)] {
        <html>
            <head>
                <title>My page</title>
            </head>
            <body>
                <h1>Hello, world!</h1>
            </body>
        </html>
    }
}
```


## Defining a macro 🚧

This section hasn't been defined yet, and is still a work in progress.


## Macro Rules 🚧


### Macro invocation locations  

Both styles of macro invocations can appear in the following positions:
- `Expr`
- `Type`
- `Pat`
- `Param`
- `Arg`
- `TypeArg`
- `PatArg`
- `MatchCase`
- `EnumVariant`

Here is an example in code of all of the possible positions
where a macro invocation can appear:

```rust
#![module_attributes]

#dump_ast
Foo := struct<#dump_ast T>(
    #dump_ast x: T,
    #dump_ast y: T,
    #dump_ast z: T,
);

Bar := enum<T>(
    #dump_ast A(T),
    #dump_ast B(T),
    #dump_ast C(T),
);

bing := (#param x: i32) -> #ty i32 => {
    foo := Foo(#arg x = 5, #arg y = 6, #arg z = 7);

    match x {
        #dump_ast 0 => 0,
        #dump_ast 1 => 1,
        #dump_ast (#dump_ast _) => bing(x - 1) + bing(x - 2),
    }
}
```


### Syntax

Formally, the macro syntax invocation can be written as follows:

```bnf
token_macro_invocation ::= "@" { macro_name | macro_args } token_tree;

token_tree ::= "{" any "}" 
             | "[" any "]" 
             | "(" any ")";

ast_macro_invocation ::= '#' (macro_name | macro_args ) macro_subject;

module_macro_invocation ::= "#!" macro_args;

macro_subject ::= expr 
                  | type 
                  | pat 
                  | param 
                  | arg 
                  | type_arg
                  | pat_arg
                  | match_case 
                  | enum_variant;  

macro_args ::= "[" { ∅ | macro_invocation ("," macro_invocation)* ","? } "]";

macro_invocation ::= macro_name ( "("  ∅ | expr ("," expr )* ","?  ")" )?;

macro_name ::= ident;
```

