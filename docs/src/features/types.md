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
  | type_function_call
  | type_function
  | merged_types

tuple_type = ( "(" ( type "," )* ")" ) | ( "(" ( type "," )* type ")" )

list_type = "[" type "]"

map_type = "{" type ":" type "}"

set_type = "{" type "}"

grouped_type = "(" type ")"

named_type = access_name

type_function_call_arg = type | ( ident "=" type )
type_function_call = ( grouped_type | named_type ) "<" ( type_function_call_arg "," )* ">"

type_function_param =
  | ( ident ":=" type )  // Declaration and assignment, infer type
  | ( ident ( ":" type )? ( "=" type )?  ) // Declaration or assignment

type_function = "<" ( type_function_param "," )+ ">" "->" type

merged_types = ( type "~" )+ type
```
