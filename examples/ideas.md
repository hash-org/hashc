# Ideas on language design 

From 2021-07-04 call.

## References, reference counting

- At emit time, code should be transpiled to conduct reference counting.
- The compiler needs to be intelligent to figure out when to initialise a variable on the stack or on the heap. Essentially this will be determined by whether or not the variable is referenced anywhere. We can conduct further optimisations on this in the future to prevent boxing in some detectable safe cases.

## Arrays, maps, sets, how boxing works

- Arrays need to come in two forms: stack and heap.
- Stack arrays need to be generic over their size.
- Heap arrays should be in-place growable but not shrinkable; the latter could result in invalid pointer references.
- Heap arrays should be reference counted (obviously)
- Heap arrays could be slices of other heap arrays.

## Unsafe and raw pointers

- We should have unsafe blocks, which declare possible undefined behaviour if some documented invariants aren't met.
- Should be able to declare function types and literals as "unsafe".
- Some fundamental operations, such as dereferencing a raw reference, are unsafe, and thus need to happen within an unsafe function or block.

## Deferring, destructors

- We either have destructors or defer.
- We probably want to have both, because destructors meet most needs but defer is useful when working with raw references.

## Error handling using a global enum

- We can potentially take inspiration from the Zig approach to error handling, by having a global error type which can be extended from any point in the program.
- We improve this model by allowing each error variant to contain an optional reference to some other data, allowing for data inside errors (albeit at a small runtime cost of a single reference).
- We probably need language-specific syntax for this.

## Dispatch using a global enum of implementers

- Possibly a dynamic dispatch approach similar to rust's `enum_dispatch` crate.

