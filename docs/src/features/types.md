# Types

## Grammar

```
type =
  | tuple_type
  | list_type
  | set_type
  | map_type
  | grouped_type
  | named_type
  | function_type
  | type_function_call
  | type_function
  | merged_types
  | ref_type

tuple_type = ( "(" ( type "," )* ")" ) | ( "(" ( type "," )+ type ")" )

list_type = "[" type "]"

map_type = "{" type ":" type "}"

set_type = "{" type "}"

grouped_type = "(" type ")"

named_type = access_name

function_type_param = type | ( ident ":" type )

function_type = "(" ( function_type_param "," )* function_type_param? ")" "->" type

type_function_call_arg = type | ( ident "=" type )
type_function_call = ( grouped_type | named_type ) "<" ( type_function_call_arg "," )* type_function_call_arg? ">"

type_function_param = ident ( ":" type )? ( "=" type )?

type_function = "<" ( type_function_param "," )* type_function_param? ">" "->" type

merged_types = ( type "~" )+ type

ref_type = "&" ( "raw" )? ( "mut" )? type
```
