# `::uninit`

> A collection of tools for a safer usage of uninitialized memory.

[![Latest version](https://img.shields.io/crates/v/uninit.svg)](https://crates.io/crates/uninit)
[![Documentation](https://docs.rs/uninit/badge.svg)](https://docs.rs/uninit)
![License](https://img.shields.io/crates/l/uninit.svg)
___

Many crates out there try to replicate C "optimization" patterns such as
handling uninitialized memory without taking into account that Rust types
carry semantics much more subtle than those of C.

For instance, the following code is _Undefined Behavior_!

```rust
use ::core::mem;

let mut array: [u8; 256] = unsafe { mem::uninitialized() };
for (i, x) in array.iter_mut().enumerate() {
    *x = i as u8;
}
```

Indeed, it creates `u8`s with uninitialized memory, which currently
has **no defined behavior** in the Rust model (see [_"What The Hardware Does"
is not What Your Program Does: Uninitialized Memory_, by Ralf Jung](
https://www.ralfj.de/blog/2019/07/14/uninit.html)), and then creates Rust
references to these invalid `u8`s, which become in turn invalid too.

## Do not use [`mem::uninitialized`]!

In hindsight, offering a [`mem::uninitialized`] function in the [`core`
library](https://doc.rust-lang.org/core) of Rust (even if it was marked
`unsafe`), has been of the worst mistakes of the language. Indeed, the function
is generic and only bounded by `Sized`, and it turns out that, except for
zero-sized types or the later introduced [`MaybeUninit`]`<T>`, **all the other
calls to this function are unsound** (instant UB).

Note that there are other ways to trigger this UB without explicitely using
[`mem::uninitialized`]`::<T>()`, such as:

  - ```rust
    use ::core::mem::MaybeUninit;
    type T = u8; // for the example

    unsafe {
        MaybeUninit::<T>::uninit() // Uninitialized `MaybeUninit<T>` => Fine
            .assume_init()         // Back to an uninitialized `T` => UB
    };
    ```

      - this is exactly equivalent to calling `mem::uninitialized::<T>()`,
        which breaks the _validity_ invariant of `T` and thus causes
        "instant UB".

        There currently only two exceptions / _valid_ use cases:

          - either [`type T = [MaybeUninit<U>; N]`][`uninit_array`],

          - or `T` is an inhabited ZST (this may, however, break safety
            invariants associated with the properties of the type, causing UB
            once such broken invariant is witnessed).

      - yes, using [`MaybeUninit`] is more subtle than just changing a function
        call.

  - ```rust
    let mut vec: Vec<u8> = Vec::with_capacity(100); // Fine
    unsafe {
        vec.set_len(100); // we have an uninitialized [u8; 100] in the heap
        // This has broken the _safety_ invariant of `Vec`, but is not yet UB
        // since no code has witnessed the broken state
    }
    let heap_bytes: &[u8] = &*vec; // Witness the broken safety invariant: UB!
    ```

## Instead, (you can) use [`MaybeUninit`]

So, the solution to manipulating uninitialized memory is to use
[`MaybeUninit`]: the special type `MaybeUninit<T>` does not assume that its
backing memory has been initialized / **the behavior of an uninitialized
`MaybeUninit<T>` is well-defined, no matter the `T`**.

### How to correctly use [`MaybeUninit`]

It is all about the _**delayed** initialization pattern_:

 1. **Creation**

    A `MaybeUninit<T>` is created, with, for instance,
    `MaybeUninit::<T>::uninit()`:

    ```rust
    use ::core::mem::MaybeUninit;

    let mut x = MaybeUninit::<i32>::uninit();
    ```

 2. **(Delayed) Initialization**

    With great care to avoid accidentally creating (even if only for an
    instant) a `&T`, `&mut T`, or even a `T` while the memory has not been
    initialized yet (which would be UB), we can write to (and thus initialize) the
    uninitialized memory through a `&mut MaybeUninit<T>`:

      - either directly, for instance:

        ```rust
        use ::core::mem::MaybeUninit;
        let mut x = MaybeUninit::<i32>::uninit();

        x = MaybeUninit::new(42);
        assert_eq!(42, unsafe { x.assume_init() });
        ```

      - or through a raw `*mut T` pointer (contrary to Rust references,
        raw pointers do not assume that the memory they point to is
        valid). For instance:

        ```rust
        use ::core::mem::MaybeUninit;
        let mut x = MaybeUninit::<i32>::uninit();

        unsafe {
            x.as_mut_ptr().write(42);
            assert_eq!(x.assume_init(), 42);
        }
        ```

      - or, if you use the tools of this crate, by upgrading the
        `&mut MaybeUninit<T>` into a "`&out T`" type called
        [`Out<T>`][`crate::prelude::Out`]:

        ```rust
        #![forbid(unsafe_code)] // no unsafe!
        use ::core::mem::MaybeUninit;
        use ::uninit::prelude::*;

        let mut x = MaybeUninit::uninit();
        let at_init_x: &i32 = x.as_out().write(42);
        assert_eq!(at_init_x, &42);
        ```

 3. **Type-level upgrade**

    Once we know, for sure, that the memory has been initialized, we can
    upgrade the `MaybeUninit<T>` type to the fully-fledged `T` type:

      - By value (`MaybeUninit<T> -> T`): [`.assume_init()`](
        https://doc.rust-lang.org/core/mem/union.MaybeUninit.html#method.assume_init)

      - By shared reference (`&MaybeUninit<T> -> &T`):
        [`.assume_init_by_ref()`]

      - By unique reference (`&mut MaybeUninit<T> -> &mut T`):
        [`.assume_init_by_mut()`]

## The problem

As you can see, manipulating [`MaybeUninit`] to initialize its contents is
done through restrictive and unergonomic types
(`&mut MaybeUninit<T>` / `*mut T`).

> So most APIs **do not** offer a way to output / write into uninitialized memory.

This is what ends up leading many people to do the step `.3` before the
step `.2`: it is oh so much ergonomic to work with a `&mut T` than a
`*mut T`, especially when arrays, slices and vectors are involved. Thus
people end up doing UB.

### One of the worst offenders of this situation is the [`Read`] trait

```rust
use ::std::io;

pub trait Read {
    fn read (&mut self, buf: &mut [u8]) -> Result<usize, io::Error>;
    // ...
}
```

that is, there is no way to `.read()` into an uninitialized buffer (it would
require an api taking either a `(*mut u8, usize)` pair, or, equivalently and
by the way more ergonomically, a [`&out [u8]`][`crate::prelude::Out`]).

# Enter `::uninit`

So, the objective of this crate is double:

  - it offers ergonomic ways to create uninitialized buffers.

    For instance:

      - [`uninit_array!`]

      - [`Vec::reserve_uninit`]

  - it tries to offer APIs that are equivalent to pervasive APIs,
    such as `Read`'s, but that are able to work with such uninitialized buffers.

    For instance:

      - [`ReadIntoUninit`]

      - [Initialize an uninitialized buffer with `.copy_from_slice()`]

### `#![no_std]` friendly

Simply disable the default-enabled `"std"` feature:

```toml
[dependencies]
uninit = { version = "x.y.z", default-features = false }
```

[`Read`]: https://doc.rust-lang.org/1.36.0/std/io/trait.Read.html
[`mem::uninitialized`]: https://doc.rust-lang.org/core/mem/fn.uninitialized.html
[`MaybeUninit`]: https://doc.rust-lang.org/core/mem/union.MaybeUninit.html
[`.assume_init_by_ref()`]: https://docs.rs/uninit/0.2.0-alpha-2/uninit/extension_traits/trait.MaybeUninitExt.html#tymethod.assume_init_by_ref
[`.assume_init_by_mut()`]: https://docs.rs/uninit/0.2.0-alpha-2/uninit/extension_traits/trait.MaybeUninitExt.html#tymethod.assume_init_by_mut
[`uninit_array!`]: https://docs.rs/uninit/0.2.0-alpha-2/uninit/macro.uninit_byte_array.html
[`Vec::reserve_uninit`]: https://docs.rs/uninit/0.2.0-alpha-2/uninit/extension_traits/trait.VecCapacity.html#tymethod.reserve_uninit
[Initialize an uninitialized buffer with `.copy_from_slice()`]: https://docs.rs/uninit/0.2.0-alpha-2/uninit/out_ref/struct.Out.html#method.copy_from_slice
[`ReadIntoUninit`]: https://docs.rs/uninit/0.2.0-alpha-2/uninit/read/trait.ReadIntoUninit.html
