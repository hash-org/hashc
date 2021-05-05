The Hash standard library is split into a few modules:

- `prelude`: Some basic definitions which are automatically imported into every Hash file.
- `num`: Number utilities.
- `io`: Input and output, file manipulation.
- `iter`: Iteration primitives.
- `list`: Operations on lists.
- `map`: Operations on maps.
- `str`: Operations on strings.

# `prelude`

```rust
// Output a line to standard output
let print = (message: str) => void;

// Read a line from standard input
let input = () => str;

// Panic
// Kill the process and exit with a message.
let panic = (message: str) => never;

// Convert type A to type B
trait conv = <A, B> => A => B;

// Represents an optional value.
enum Option = <T> = {
   Some(T);
   None;
};

// Represents the result of a fallible operation.
enum Result = <T, E> = {
   Ok(T);
   Err(E);
};

// Hash a value into a 64-bit integer
trait hash = <A> => (A) => int;



// Add operator (+)
// Implemented for all numeric primitives, strings, lists.
trait add = <T> => (T, T) => T;

// The following are implemented for all numeric primitives:

// Subtract operator (-)
trait sub = <T> => (T, T) => T;

// Multiply operator (*)
trait mul = <T> => (T, T) => T;

// Divide operator (/)
trait div = <T> => (T, T) => T;

// Modulus operator (%)
trait mod = <T> => (T, T) => T;

// Negation
trait neg = <T> => (T) => T;

// Bitwise
trait bit_shr = <T> => (T, T) => T;
trait bit_shl = <T> => (T, T) => T;
trait bit_not = <T> => (T) => T;
trait bit_and = <T> => (T, T) => T;
trait bit_or = <T> => (T, T) => T;
trait bit_xor = <T> => (T, T) => T;

// Ordering
// Implemented for numeric primitives and strings.
enum Ordering = {
   Lt,
   Eq,
   Gt,
};
trait ord = <T> => (T, T) => Ordering;

// Equality
// Automatically implemented for all types.
trait eq = <T> => (T, T) => bool;

// Reference equality
// Automatically implemented for all types.
trait ref_eq = <T> => (T, T) => bool;

// Indexing
// Implemented for maps and lists.
trait index_get = <T, I, O> => (T, I) => O;
trait index_set = <T, I, O> => (T, I, O) => void;
```

# `num`

```rust
// Exponentiation
trait pow = <T> => (T, T) => T;

// Trigonometry
trait sin = <T> => (T) => T;
trait cos = <T> => (T) => T;
trait tan = <T> => (T) => T;
trait asin = <T> => (T) => T;
trait acos = <T> => (T) => T;
trait atan = <T> => (T) => T;

// Logarithm (value, base)
trait log = <T> => (T, T) => T;

// Square root (may be faster than pow(conv(x), 0.5))
trait sqrt = <T> => (T) => T;
```

# `io`

```rust
// Error type for all I/O operations.
enum IoErrorType = {
   FileNotFound;
   PermissionDenied;
   AlreadyExists;
   DevBusy;
   DevFull; // Device is full
   EOF; // Failed due to end of file being reached
   IllegalOperation;
   Other;
};

struct IoError = {
    error: IoErrorType;
    message: str; // @@Cleanup: we can't really get a message so do we even need this?
};

// Send a character to stdout.
let set = (data: char): Result<void, IoError> => #intrinsic_char_set(data);

// Read a character from stdin.
let get: () => Result<char, IoError> = #intrinsic_char_get;

// File opening mode
enum OpenMode = {
   Read; // r
   ReadWrite; // r+ | w+
   Write; // w
   Append; // a
};

enum SeekMode = {
    SeekSet; // begin file offset
    SeekCur; // current handle offset
    SeekEnd; // end of file offset
};

let _mode_to_int = (mode: OpenMode): int => match mode {
    Read => 0;
    Write => 1;
    Append => 2;
    ReadWrite => 3;
};

// Convert a string representation of a mode into a mode enum
let _str_to_mode = (mode: str): OpenMode => match mode {
    "r" => Read;
    "w" => Write;
    "a" => Append;
    "r+" | "w+" => ReadWrite;
    _ => unreachable();
};

// A data structure representing a file.
struct File = { 
    handle: Native; 
};

// Standard In/Out file handles
let stdin: File = #intrinsic_get_stdin();
let stdout: File = #intrinsic_get_stdout();
let stderr: File = #intrinsic_get_stderr();

// Open a file
let open = (filename: str, mode: OpenMode): Result<File, IoError> => {
    #intrinsic_open(filename, _mode_to_int(mode))
};

// Close a file
let close = (handle: File): void => #intrinsic_close(handle);

// Send a character to a file.
let fset = (handle: File, ch: char): Result<void, IoError> => #intrinsic_fset(handle, ch);

// Read a character from a file.
let fget = (handle: File): Result<char, IoError> => #intrinsic_fget(handle);

// Send a string to a file, \n terminated.
let fprint = (handle: File, line: str): Result<void, IoError> => #intrinsic_fprint(handle, line);

// Read a line from a file.
let finput = (handle: File): Result<str, IoError> => #intrinsic_finput(handle);

// Seek a file.
let fseek = (file: File, position: int, whence: SeekMode): Result<void, IoError> => {
    let whence_mode = match whence {
        SeekSet => 0;
        SeekCur => 1;
        SeekEnd => 2;
    };
    
    #intrinsic_fseek(file, position, whence_mode)
};

// Lines iterator
struct LinesIterator = {
   index: int;
   lines: [str];
};

let next<LinesIterator, Result<str, IoError>>;
let flines = (file: File) => LinesIterator;
```

# `iter`

```rust
// Turn a container of type C into an iterator of type I
trait iter = <C, I> => (C) => I;

// Get the next item of an iterator.
// I is the iterator type.
// T is the element type.
// When next returns None, the iterator has ended iteration.
trait next = <I, T> => (I) => Option<T>;

// Skip n elements.
struct Skip = <I> => { inner: I; skip: int; current: int; };
trait skip = <I> => (I, int) => Skip<I>;
let skip<I> where next<I, ?>;
let next<Skip<I>, T> where next<I, T>;

// First n elements.
struct First = <I> => {
    elements: [I];
    first: int; 
    current: int; 
};

trait first = <I> => (I, int) => First<I>;
let first<I> where next<I, ?>;
let next<First<I>, T> where next<I, T>;

// Last n elements.
// Last n elements.
struct Last = <I> => {
    elements: [I];
    size: int;
};

trait last = <I> => (I, int) => Last<I>;
let last<I> where next<I, ?>;
let next<Last<I>, T> where next<I, T>;

// Get the nth element.
trait nth = <I, T> => (I, int) => Option<T>;
let nth<I, T> where next<I, T>;

// Reverse the iterator.
struct Reverse = <T> where next<?, T> => {
    elements: [I];
    index: int;
};

trait reverse = <I, T> => (I) => Reverse<T>;
let reverse<I, T> where next<I, T>;
let next<Reverse<T>, T>;

// Enumerate the iterator.
struct Enumerate = <I> => {
    index: int;
    item: I;
};

trait enumerate = <I> => (I) => Enumerate<I>;
let enumerate<I> where next<I, ?>;
let next<Enumerate<I>, (int, T)> where next<I, T>;

// Zip two iterators.
struct Zip = <A, B> => {
    first: A;
    second: B;
};

trait zip = <A, B> => (A, B) => Zip<A, B>;
let zip<A, B> where next<A, ?>, next<B, ?>;
let next<Zip<A, B>, (X, Y)> where next<A, X>, next<B, Y>;

// Collect into some type C
trait collect = <I, C> => (I) => C;
```

# `list`

```rust
// Push a value to the end of a list
trait push = <A> => ([A], A) => void;
let push<A>;

// Pop a value from the end of a list
trait pop = <A> => ([A]) => A;
let pop<A>;

// Remove an item at an index, and return it.
trait remove = <A> => ([A], int) => A;

// Index a list ([A]) by a number (int), returning a list element (A)
let index_get<[A], int, A>;
let index_set<[A], int, A>;

// Concat lists
let add<[A]>;

// Concat lists, first in place
trait concat = <A> => ([A], [A]) => void;

// Sorting
trait sort = <A> => ([A]) => [A];
let sort<[A]> where ord<A>;

// Equality
let eq<[A]> where eq<A>;

// Turn a list into an iterator
struct ListIterator = <A> => { list: [A]; index: int; };
let next<ListIterator<A>, A>;
let iter<[A], ListIterator<A>>;

// Collect iterator of values into a list
let collect<I, [A]> where next<I, A>;
```

# `map`

```rust
// Collect iterator of tuples into a map
let collect<I, {A:B}> where next<I, (A, B)>;

// Delete a key from a map, and return its value.
trait delete = <A, B> => ({A:B}, A) => B;

// Index a map a key, returning a value
let index_get<{A:B}, A, B>;
let index_set<{A:B}, A, B>;

// Index a map a key, returning a value if the key exists
trait try_get = <A, B> => ({A:B}, A) => Option<B>;
let try_get<A, B>;

// Merge maps
let add<{A:B}>;

// Merge maps, first in place
trait merge = <A, B> => ({A:B}, {A:B}) => void;

// Equality
let eq<{A:B}> where eq<A>, eq<B>;

// Turn a map into a tuple iterator
struct MapIterator = <A, B> => { map: {A:B}; index: int; };

let next<MapIterator<A, B>, (A, B)>;
let iter<{A:B}, MapIterator<A, B>>;
```

# `str`

```rust
// Collect iterator of characters into a string
let collect<I, str> where next<I, char>;

// Index a string, returning a character
let index_get<str, int, char>;

// Slice a string at [begin, end)
let slice: (int, int) => str;

// Concat strings
let add<str>;

// Equality
let eq<str>;

// Lexicographical ordering
let ord<str>;

// Turn a string into a character iterator
struct CharIterator = {
    index: int;
    string: str;
};

let next<CharIterator, char>;
let iter<str, CharIterator>;
```
