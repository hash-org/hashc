# Operators & Symbols

This section contains all of the syntactic operators that are available within Hash

## General operators

Here are the general operators for arithmetic, bitwise assignment operators. This table does not include
all of the possible operators specified within the grammar. There are more operators that are related to
a specific group of operations or are used to convey meaning within the language.

| Operator             | Example              | Description                   | Overloadable trait |
|----------------------|----------------------|-------------------------------|--------------------|
| `===`, `!==`         | `a === b`, `a !== c` | Referential equality          | `ref_eq`           |
| `->`                 | N/A                  | `Reserved`                    | N/A                |
| `=>`                 | `(a) => a + 2`       | Function notation             | N/A                |
| `==`, `!=`           | `a == 2`, `b != 'a'` | Equality                      | `eq`               |
| `=`                  | `a = 2`              | Assignment                    | N/A                |
| `!`                  | `!a`                 | Logical not                   | `not`              |
| `&&`                 | `a && b`            | Logical and                   | `and`              |
| <code>&#124;&#124;</code>               | <code>a  &#124;&#124; b</code>           | Logical or                    | `or`               |
| `+`                  | `2 + 2`, `3 + b`     | Addition                      | `add`              |
| `-`                  | `3 - a`        | Subtraction | `sub`       |
| `-`                  | `-2`        | Negation | `neg`       |
| `*`                  | `3 * 2`, `2 * c`     | Multiplication                | `mul`              |
| `**`                 | `3 ** 2`, `3 ** 2.3` | Exponentiation                | `exp`              |
| `/`                  | `4 / 2`, `a / b`     | Division                      | `div`              |
| `%`                  | `a % 1`              | Modulo                        | `mod`              |
| `<<`                 | `4 << 1`             | Bitwise left shift            | `shl`              |
| `>>`                 | `8 >> 1`             | Bitwise right shift           | `shr`              |
| `&`                  | `5 & 4`, `a & 2`     | Bitwise and                   | `andb`             |
| <code>&#124;</code>                 | <code>a  &#124; 2</code>             | Bitwise or                    | `orb`              |
| `^`                  | `3 ^ 2`              | Bitwise exclusive or          | `xorb`             |
| `~`                  | `~2`                 | Bitwise not                   | `notb`             |
| `>=`, `<=`, `<`, `>` | `2 < b`, `c >= 3`    | Order comparison              | `ord`              |
| `+=`                 | `x += y`             | Add with assignment           | `add`              |
| `-=`                 | `x -= 1`             | Subtract with assignment      | `neg`              |
| `*=`                 | `b *= 10`            | Multiply with assignment      | `mul`              |
| `/=`                 | `b /= 2`             | Divide with assignment        | `div`              |
| `%=`                 | `a %= 3`             | Modulo with assignment        | `mod`              |
| `&&=`                | `b &&= c`            | Logical and with assignment   | `and`              |
| <code>&#124;&#124;=</code>              | <code>b &#124;&#124;= c</code>          | Logical or with assignment    | `or`               |
| `&=`                 | `a &= b`             | Bitwise and with assignment   | `andb`             |
| <code>&#124;=</code>                | <code>b  &#124;= SOME_CONST</code>   | Bitwise or with assignment    | `orb`              |
| `^=`                 | `a ^= 1`             | Bitwise xor with assignment   | `xorb`             |

-- 'as' ':' '::' '.' '...' ';' 

## Non-operator symbols

## Type annotations

## Comments
