# Type functions

Hash supports functions both at the value level and at the type level.
Type-level functions correspond to generics in other languages.
They are declared using angular brackets (`<` and `>`) rather than parentheses, and all parameters are types.
Other than that, they have the same syntax as normal (value-level) functions.

Type-level functions can be used to create generic structs, enums, functions, and traits.
For example, the generic `Result<T, E>` type would is defined as
```rs
Result := <T, E> => enum(
  Ok(T),
  Err(E),
);
```
This declares that `Result` is a function of kind `<T: type, E: type> -> type`.
The default bound on each type parameter is `type`, but it can be any trait (or traits) as well.
Multiple trait bounds can be specified using the `~` binary operator.
For example,
```rs
Result := <T: Clone ~ Eq, E: Error ~ Print> => enum(
  Ok(T),
  Err(E),
);
```
Here, `T` must implement `Clone` and `Eq`, and `E` must implement `Error` and `Print`.

In order to evaluate type functions, type arguments can be specified in angle brackets:
```rs
my_result: Result<i32, str> = Ok(3);
```
When calling functions or instantiating enums/structs, type arguments can be inferred so that you don't have to specify them manually:
```rs
RefCounted := <Inner: Sized> => struct(
  ptr: &raw Inner,
  references: usize
);

make_ref_counted := <Inner: Sized> => (value: Inner) -> RefCounted<Inner> => {
  data_ptr := allocate_bytes_for<Inner>();

  RefCounted( // Type argument `Inner` inferred
    ptr = data_ptr,
    references = 1,
  )
};

my_ref_counted_string = make_ref_counted("Bilbo bing bong"); // `Inner = str` inferred
```
In order to explicitly infer specific arguments, you can use the `_` sigil:
```rs
Convert := <I, O> => trait {
  convert: (input: I) -> O;
};

// ...implementations of convert

x := 3.convert<_, str>(); // `I = i32` inferred, `O = str` given.
x := 3.convert<I = _, O = str>(); // same thing.
x: str = 3.convert(); // same thing.
```

Type functions can only return types or functions; they cannot return values (though this is planned eventually).
This means that you cannot write
```rs
land_with := <T> => land_on_moon_with<T>();
signal := land<Rover>;
```
but you can write
```rs
land_with := <T> => () => land_on_moon_with<T>();
signal := land<Rover>();
```

Just like with value-level functions, type-level functions can be provided with named arguments rather than positional arguments.
These are subject to the same rules as value-level functions:
```rs
make_repository := <
  Create, Read,
  Update, Delete
> => () -> Repository<Create, Read, Update, Delete> => {
  ...
};

repo := make_repository<
  Create = DogCreate,
  Read = DogRead,
  Update = DogUpdate,
  Delete = DogDelete
>();
```

Finally, type-level function parameters can be given default arguments, which will be used if the arguments cannot be inferred from context and aren't specified explicitly:
```rs
Vec := <T, Allocator: Alloc = GlobalAllocator> => struct(
  data: RawRefInAllocator<T, Allocator>,
  length: usize,
);

make_vec := <T> => () -> Vec<T> => { ... }; // `Allocator = GlobalAllocator` inferred
make_vec_with_alloc := <T, Allocator: Alloc> => (allocator: Allocator) -> Vec<T, Allocator> => { ... };

x := make_vec<str>(); // `Allocator = GlobalAllocator` inferred
y := make_vec_with_alloc<str, _>(slab_allocator); // `Allocator = SlabAllocator` inferred
```


## Grammar

The grammar for type function definitions and type function types is as follows:

```
type_function_param =
  | ( ident ":=" type )  // Declaration and assignment, infer type
  | ( ident ( ":" type )? "=" type  ) // Assignment
  | ( ident ( ":" type )  ) // Declaration

type_function_def = "<" type_function_param+ ">" ( "->" type )? ( "=>" type )?

type_function_type = "<" type_function_param+ ">" "->" type
```

The grammar for type function calls is as follows:

```
type_function_call_arg = type | ( ident "=" type )
type_function_call = ident "(" type_function_call_arg* ")"
```
