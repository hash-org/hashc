# Hash language modules

A module in `Hash` can contain variable definitions, function definitions, type definitions or include other modules.
Each `.hash` source file is a module, and inline modules can also be created using `mod` blocks.

## Importing

Given the project structure:
```
.
├── lib
│   ├── a.hash
│   ├── b.hash
│   └── sub
│       └── c.hash
└── main.hash
```

Modules in hash allow for a source to be split up into smaller code fragments, allowing for better source code organisation and maintenance.

You can import modules by specifying the path relative to the current path. 

For example, if you wanted to include the modules `a`, `b`, and or `c` within your main file

```rust
// main.hash
a := import("lib/a");
b := import("lib/b");
c := import("lib/sub/c");
```

By doing so, you are placing everything that is defined within each of those modules under
the namespace. 

## Exporting

In order to export items from a module, use the `pub` keyword.
For example:

```rust
/// a.hash

// Visible from outside:
pub a := 1;

// Not visible from outside (priv by default):
b := 1;

// Not visible from outside:
priv c := 1;

/// b.hash
{ a } := import("a.hash"); // Ok
{ b } := import("a.hash"); // Error: b is private
{ c } := import("a.hash"); // Error: c is private.
```

## Referencing exports 🚧

Furthermore, if the `a` module contained a public structure definition like `Point`:

```rust
// a.hash
pub Point := struct(
    x: u32,
    y: u32,
);
```

Within main, you can create a new `Point` by doing the following

```rust
// main.hash
a := import("lib/a");

p1 := a::Point(
    x = 2,
    y = 3,
);

print(p1.x); // 2
print(p1.y); // 3
```

From this example, the `::` item access operator is used to reference any exports from the module.

Furthermore, what if you wanted to import only a specific definition within a module such as the 'Point' structure from the module `a`.

You can do so by destructuring the definitions into using the syntax as
follows:

```rust
{ Point } := import("lib/a");

p1 := Point(x=2, y=3);
```

In case you have a member of your current module already reserving a name, you
can rename the exported members to your liking using the `as` pattern operator:
```rust
{ Point as LibPoint } = import("lib/a");

p1 := LibPoint(x=2, y=3);
```

## Inline modules

Other than through `.hash` files, modules can be created inline using `mod` blocks:

```rust
// a.hash
bar := 3;

pub nested := mod {
    pub Colour := enum(Red, Green, Blue);
};

// b.hash
a := import("a.hash");
red := a::nested::Colour::Red;
```

These follow the same conventions as `.hash` files, and members need to be exported with `pub` in order to be visible from the outside.
However, the external module items are always visible from within a `mod` block, so in the above example, `bar` can be used from within `nested`.

## Grammar

The grammar for file modules is as follows:

```
file_module = ( expr ";" )*
```

The grammar for `mod` blocks (which are expressions) is as follows:

```
mod_block = "mod" "{" ( expr ";" )* "}"
```
