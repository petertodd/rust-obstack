rust-obstack
============

A fast segmented stack allocator, supporting multiple objects of any type.

A type of arena allocator, obstacks deallocate memory all at once, when the `Obstack` itself is
destroyed. The benefit is extremely fast allocation: just a pointer bump. Unlike a typed arena,
a single `Obstack` can contain values with any number of different types.

For `Copy` types pushing a value to an `Obstack` returns a standard mutable reference:

    let r: &mut u8 = stack.push_copy(42);
    assert_eq!(*r, 42);

As `Copy` types can't implement `Drop`, nothing needs to be done to deallocate the value beyond
deallocating the memory itself, which is done en-mass when the `Obstack` itself is dropped.
`push_copy()` is thus limited to types that implement `Copy`.

Types that do not implement `Copy` *may* implement `Drop`. As Rust's type system doesn't have a
negative `!Drop` trait, `Obstack` has a second method - `push()` - that is not restricted to
`Copy` types. This method returns the wrapper type `Ref<T>`, that wraps the underlying mutable
reference. This wrapper owns the value on the stack, and ensures that `drop` is
called when the wrapper goes out of scope. Essentially `Ref` is the equivalent of `Box`, but
using an `Obstack` rather than the heap.

In practice even when the `Ref` wrapper is used, if the underlying type doesn't actually
implement a meaningful `drop` method, the Rust compiler is able to optimize away all calls to
`drop`, resulting in the same performance as for `Copy` types; the actual `Ref::drop()` method
is `[inline(always)]` to aid this process. This is important as not all non-drop types can
implement `Copy` - notably mutable references can't.

`Obstack` allocates memory as a segmented stack consisting of one or more segments of
contiguous memory. Each time the top segment becomes full, a new segment is allocated from the
heap. To ensure the total number of allocations remains small, segments are allocated in a
powers-of-two fashion, with each segment being twice the size of the previous one.

Once a segment has been allocated it's stable for the life of the `Obstack`, allowing
the values contained in that segment to be referenced directly; Rust lifetimes ensure that the
references are valid for the lifetime of the `Obstack`.


## Benchmarks

Some preliminary benchmarks can be run with:

    cargo bench

tl;dr: Approximately 10x faster to allocate and deallocate a linked-list.
