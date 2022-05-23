# Types

## Grammar

```
type =
  | tuple_type
  | list_type
  | set_type
  | map_type
  | named_type_or_type_function
  | merged_types

tuple_type = ( "(" ( type "," )* ")" ) | ( "(" ( type "," )* type ")" )

list_type = "[" type "]"

map_type = "{" type ":" type "}"

set_type = "{" type "}"

type_function_call_arg = type | ( ident "=" type )
named_type_or_type_function = ident ( "<" type_function_call_arg+ ">" )?

merged_types = ( type "~" )+ type
```
