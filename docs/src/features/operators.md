# Operators & Symbols

This section contains all of the syntactic operators that are available within Hash

## General operators 🚧

Here are the general operators for arithmetic, bitwise assignment operators. This table does not include
all of the possible operators specified within the grammar. There are more operators that are related to
a specific group of operations or are used to convey meaning within the language.

| Operator             | Example              | Description                   | Overloadable trait |
|----------------------|----------------------|-------------------------------|--------------------|
| `==`, `!=`           | `a == 2`, `b != 'a'` | Equality                      | `eq`               |
| `=`                  | `a = 2`              | Assignment                    | N/A                |
| `!`                  | `!a`                 | Logical not                   | `not`              |
| `&&`                 | `a && b`            | Logical and                   | `and`              |
| <code>&#124;&#124;</code>               | <code>a  &#124;&#124; b</code>           | Logical or    | `or`               |
| `+`                  | `2 + 2`, `3 + b`     | Addition                      | `add`              |
| `-`                  | `3 - a`        | Subtraction | `sub`       |
| `-`                  | `-2`        | Negation | `neg`       |
| `*`                  | `3 * 2`, `2 * c`     | Multiplication                | `mul`              |
| `^^`                 | `3 ^^ 2`, `3 ^^ 2.3` | Exponentiation                | `exp`              |
| `/`                  | `4 / 2`, `a / b`     | Division                      | `div`              |
| `%`                  | `a % 1`              | Modulo                        | `mod`              |
| `<<`                 | `4 << 1`             | Bitwise left shift            | `shl`              |
| `>>`                 | `8 >> 1`             | Bitwise right shift           | `shr`              |
| `&`                  | `5 & 4`, `a & 2`     | Bitwise and                   | `andb`             |
| <code>&#124;</code>                 | <code>a  &#124; 2</code>             | Bitwise or                    | `orb`              |
| `^`                  | `3 ^ 2`              | Bitwise exclusive or          | `xorb`             |
| `~`                  | `~2`                 | Bitwise not                   | `notb`             |
| `>=`, `<=`, `<`, `>` | `2 < b`, `c >= 3`    | Order comparison              | `ord`              |
| `+=`                 | `x += y`             | Add with assignment           | `add_eq`              |
| `-=`                 | `x -= 1`             | Subtract with assignment      | `sub_eq`              |
| `*=`                 | `b *= 10`            | Multiply with assignment      | `mul_eq`              |
| `/=`                 | `b /= 2`             | Divide with assignment        | `div_eq`              |
| `%=`                 | `a %= 3`             | Modulo with assignment        | `mod_eq`              |
| `&&=`                | `b &&= c`            | Logical and with assignment   | `and_eq`              |
| `>>=`                | `b >>= 3`            | Bitwise right shift equality  | `shr_eq`              |
| `<<=`                | `b <<= 1`            | Bitwise left shift equality   | `shl_eq`              |
| <code>&#124;&#124;=</code>              | <code>b &#124;&#124;= c</code>          | Logical or with assignment    | `or_eq`               |
| `&=`                 | `a &= b`             | Bitwise and with assignment   | `andb`             |
| <code>&#124;=</code>                | <code>b  &#124;= SOME_CONST</code>   | Bitwise or with assignment    | `orb`              |
| `^=`                 | `a ^= 1`             | Bitwise xor with assignment   | `xorb`             |
| `.`  	| `a.foo`   	| Struct/Tuple enum property accessor 	| N/A 	|
| `:`  	| `{2: 'a'}`         	| Map key-value separator             	| N/A 	|
| `::` 	| `io::open()`       	| Namespace symbol access             	| N/A 	|
| `as` 	| `t as str`         	| Type assertion                      	| N/A 	|
| `@` 	| N/A              	| Pattern value binding   	| N/A 	|
| `...` 	| N/A                	| Spread operator (Not-implemented)   	| `range`? 	|
| `;` 	| `expression;`              	| statement terminator   	| N/A 	|
| `?` 	| `k<T> where s<T, ?> := ...`              	| Type argument wildcard   	| N/A 	|
| `->`                 | `(str) -> usize`     | Function return type notation | N/A                |
| `=>`                 | `(a) => a + 2`       | Function Body definition      | N/A                |

## Comments 🚧

This table represents the syntax for different types of comments in Hash:

| Symbol    | Description                 |
|-----------|-----------------------------|
| `//...`   | Line comment                |
| `/*...*/` | Block comment               |
| `///`     | function doc comment    🚧  |
| `//!`     | module doc comment      🚧  |
# Type Signature Assertions

## Basics

As in many other languages, the programmer can specify the type of a variable or
a literal by using some special syntax. For example, in languages such as typescript,
you can say that: 
```rust
some_value as str
```
which implies that you are asserting that `some_value` is a string, this is essentially a way to avoid explicitly stating that type of a variable every
single time and telling the compiler "Trust me `some_value` is a `string`". 

The principle is somewhat similar in `Hash`, but it is more strictly enforced.
For example, within the statement `x := 37;`, the type of `x` can be any of the
integer types. This might lead to unexpected behaviour in future statements, where
the compiler has decided the type of `x` (it might not be what you intended it).

So, you can either declare `x` to be some integer type explicitly like so:

```rs
x: u32 = 37;
```

Or you can, use `as` to imply a type for a variable, which the compiler will assume 
to be true, like so:

```rs
x := 37 as u32;
```

## Failing type assertions

If you specify a type assertion, the compiler will either attempt to infer this information from the left-hand side of the `as` operator
to the right. If the inference results in a different type to the right-hand side, this will raise a typechecking failure. 

For example, if you were to specify the expression:

```rust
"A" as char
```

The compiler will report this error as:

```
error[0001]: Types mismatch, got a `str`, but wanted a `char`.
 --> <interactive>:1:8
1 |   "A" as char
  |          ^^^^ This specifies that the expression should be of type `char`

 --> <interactive>:1:1
1 |   "A" as char
  |   ^^^ Found this to be of type `str`

```

## Usefulness
 
Why are type assertions when there is already type inference within the language? Well, sometimes the type inference
system does not have enough information to infer the types of variables and declarations. 
Type inference may not have enough information when dealing with functions that are generic, so it can sometimes
be useful to assert to the compiler that a given variable is a certain type. 

Additionally, whilst the language is in an early stage of maturity and some things that are quirky or broken, type
assertions can come to the rescue and help the compiler to understand your program.

In general, type assertions should be used when the compiler cannot infer the type of some expression with 
the given information and needs assistance. You shouldn't need to use type assertions often.
