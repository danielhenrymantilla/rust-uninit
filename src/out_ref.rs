//! `&out _` references in stable Rust!

use crate::{
    extension_traits::{AsOut, MaybeUninitExt},
};
use ::core::{
    mem::{self,
        ManuallyDrop,
        MaybeUninit,
    },
    ptr,
    slice,
};

/// Wrapper expressing the semantics of `&out T` references
///
/// In other words, this has the semantics of `&'out mut MaybeUninit<T>` but
/// for the ability to write garbage (`MaybeUninit::uninit()`) into it
/// (else [coercing `&mut T` to `&out T = Out<T>` would be
/// unsound][`Out::as_mut_uninit`]).
///
/// This means that the reference may point to uninitialized memory (or not),
/// and thus that writes to the pointee will not call the `.drop()` destructor.
///
/// This type can be [trivially constructed][`crate::AsOut`] from:
///
///   - a `&'out mut MaybeUninit<T>` (main point of the type),
///
///   - a `&'out mut T` (to keep the ergonomics of being able to overwrite an
///     already initialized value).
///
///       - To avoid "accidentally" leaking memory in this second case,
///         either `T` must be `Copy` (sufficient condition to prove there is
///         no drop glue), or you must first call
///         [`.manually_drop_mut()`][`crate::ManuallyDropMut`]
///         before the [`.as_out()`][`crate::AsOut`] "coercion".
#[derive(Debug)]
#[repr(transparent)]
pub
struct Out<'out, T : 'out + ?Sized> (
    ptr::NonNull<T>,
    ::core::marker::PhantomData<&'out mut T>,
);

// # Safety
//
// `Send`/`Sync` safety is related to mutation, so in that regard there is no
// difference between `Out<'_, T>` and `&'_ mut T` (in other words:
// `MaybeUninit` plays no role in that regard).
//
// Thus `Out` is `{Send,Sync}` if and only if `&mut` is.
unsafe impl<'out, T : ?Sized + 'out> Send for Out<'out, T>
where
    &'out mut T : Send,
{}
unsafe impl<'out, T : ?Sized + 'out> Sync for Out<'out, T>
where
    &'out mut T : Sync,
{}

impl<'out, T : 'out> From<&'out mut MaybeUninit<T>> for Out<'out, T> {
    #[inline]
    fn from (p: &'out mut MaybeUninit<T>)
      -> Out<'out, T>
    {
        Out(
            ptr::NonNull::<MaybeUninit<T>>::from(p).cast(),
            Default::default(),
        )
    }
}

impl<'out, T : 'out> From<&'out mut T> for Out<'out, T>
where
    T : Copy, // prevent accidentally leaking memory
{
    #[inline]
    fn from (p: &'out mut T)
      -> Out<'out, T>
    {
        unsafe {
            // # Safety
            //
            //   - `T` and `MaybeUninit<T>` have the same layout
            //     (`#[repr(transparent)]`)
            //
            //   - The API does not allow to write `MaybeUninit::uninit()` into
            //     the pointee.
            mem::transmute::<_, &'out mut MaybeUninit<T>>(p).into()
        }
    }
}

#[cfg(doc)]
use crate::extension_traits::ManuallyDropMut;

/// For non-`Copy` types, explicitely transmuting the `mut` reference into one
/// that points to a `ManuallyDrop` is required, so as to express how likely it
/// is that memory be leaked. This can be safely achieved by using the
/// [`ManuallyDropMut`] helper.
impl<'out, T : 'out> From<&'out mut ManuallyDrop<T>> for Out<'out, T> {
    #[inline]
    fn from (p: &'out mut ManuallyDrop<T>)
      -> Out<'out, T>
    {
        unsafe {
            // # Safety
            //
            //   - `ManuallyDrop<T>` and `MaybeUninit<T>` have the same layout
            //     (`#[repr(transparent)]`)
            //
            //   - The API does not allow to write `MaybeUninit::uninit()` into
            //     the pointee.
            mem::transmute::<_, &'out mut MaybeUninit<T>>(p).into()
        }
    }
}

impl<'out, T : 'out + ?Sized> Out<'out, T> {
    /// Reborrows the `&out _` reference for a shorter lifetime.
    #[inline]
    pub
    fn reborrow<'reborrow> (self: &'reborrow mut Out<'out, T>)
      -> Out<'reborrow, T>
    where
        'out : 'reborrow,
    {
        Out(self.0, Default::default())
    }

    /// Shorthand for [`.reborrow()`][`Out::reborrow`].
    #[inline]
    pub
    fn r<'reborrow> (self: &'reborrow mut Out<'out, T>)
      -> Out<'reborrow, T>
    where
        'out : 'reborrow,
    {
        self.reborrow()
    }
}

impl<'out, T : 'out> Out<'out, T> {
    /// Write a `value` into the pointee, returning an `.assume_init()`-ed
    /// reference to it.
    ///
    /// # Guarantees (that `unsafe` code may rely on)
    ///
    /// After the function returns, the pointee is guaranteed to have been
    /// initialized; it is thus sound to use that property to manually
    /// `assume_init()` it or any chunk of such items.
    #[inline]
    pub
    fn write (self: Out<'out, T>, value: T)
      -> &'out mut T
    {
        unsafe {
            // Safety: this writes a valid (non garbage) value to the pointee
            self.0.as_ptr().write(value);
            self.assume_init()
        }
    }

    /// Similar to [`.write()`][`Out::write`], but getting the previous value
    /// back. Such previous value may or may not be initialized.
    ///
    /// # Guarantees (that `unsafe` code may rely on)
    ///
    ///   - After the function returns, the pointee is guaranteed to have been
    ///     initialized; it is thus sound to use that property to manually
    ///     `assume_init()` it or any chunk of such items.
    ///
    ///   - there is **no such guarantee** regarding the previous value, which
    ///     is thus only sound to `assume_init()` if the pointee already was
    ///     (before the call to `.replace()`).
    #[inline]
    pub
    fn replace (mut self: Out<'out, T>, value: T)
      -> (MaybeUninit<T>, &'out mut T)
    {
        unsafe {
            // # Safety
            //
            //   - This:
            //
            //      1. writes a valid value to the pointee,
            //
            //      2. extracts the previous value as a now owned `MaybeUninit<T>`
            //
            //     Thus it does not not `assume_init()` the pointee nor write
            //     garbage to it.
            //
            //   - Thanks to write the pointee is known to be initialized.
            (
                mem::replace(self.r().as_mut_uninit(), MaybeUninit::new(value)),
                self.assume_init(),
            )
        }
    }

    /// Returns a raw mutable pointer to the pointee.
    ///
    /// # Guarantees (that `unsafe` code may rely on)
    ///
    ///   - The returned pointer does point to the pointee, meaning that if
    ///     such returned pointer is used to [`.write()`][`::core::ptr::write`]
    ///     to the pointee, then it is safe to `assume_init()` it.
    ///
    ///   - The returned pointer is non null, well-aligned, and writeable.
    ///
    ///     It is also technically readable:
    ///
    ///       - you can read a `MaybeUninit<T>` out of it after `.cast()`ing it,
    ///
    ///       - otherwise, except when sound to `assume_init()`, the obtained
    ///         pointer cannot be used to read the value `: T` of the pointee!
    #[inline]
    pub
    fn as_mut_ptr (self: &'_ mut Out<'out, T>)
      -> *mut T
    {
        self.0.as_ptr()
    }

    /// Upgrades the `&out _` (write-only) reference to a read-writeable
    /// `&mut _`.
    ///
    /// # Safety
    ///
    /// Don't be lured by the `&mut` reference: Rust validity invariants
    /// imply that an `&mut` reference is only sound to produce if it points
    /// to an initialized value; it is otherwise instant UB. See
    /// [`MaybeUninit::assume_init`] for more info about it. Thus:
    ///
    ///   - The pointee must have been initialized.
    ///
    /// This is a **validity invariant**, meaning that UB does happen from just
    /// calling that function to produce an ill-formed reference, even if the
    /// obtained reference is "never actually used".
    ///
    /// ## Counterexample
    ///
    /// The following program exhibits Undefined Behavior:
    ///
    /// ```rust,no_run
    /// use ::uninit::prelude::*;
    ///
    /// let mut x = MaybeUninit::uninit();
    /// let _unused: &mut u8 = unsafe {
    ///     x   .as_out()
    ///         .assume_init() // UB!
    /// };
    /// ```
    #[inline]
    pub
    unsafe
    fn assume_init (mut self: Out<'out, T>)
      -> &'out mut T
    {
        &mut *self.as_mut_ptr()
    }

    /// _Upgrades_ the `&out _`  (write-valid-values-only) reference to a
    /// `&mut MaybeUninit<_>` (write-anything) reference.
    ///
    /// # Safety
    ///
    ///   - The obtained reference cannot be used to write garbage
    ///     (`MaybeUninit::uninit()`) into the pointee.
    ///
    ///     This means that it can thus **not be fed to opaque APIs!!**
    ///
    ///   - Exception: if the given `&out` reference has originated from a
    ///     `&mut MaybeUninit<_>`, then calling `.as_mut_uninit()` is a sound
    ///     way to make the trip back.
    ///
    /// This is a **safety invariant** (_i.e._, even if it is never "instant"
    /// UB to produce such a value, it does break the safety invariant of
    /// `&mut MaybeUninit<_>` (that of being allowed to write
    /// `MaybeUninit::uninit()` garbage into the pointee), so UB can happen
    /// afterwards). This is different than `.assume_init()` soundness relying
    /// on a validity invariant, meaning that UB does happen from just calling
    /// that function to produce an ill-formed reference, even if the obtained
    /// reference is never actually used.
    ///
    /// # Counter-example
    ///
    /// The following code is Undefined Behavior:
    ///
    /// ```rust,no_run
    /// use ::uninit::prelude::*;
    ///
    /// let mut my_box = Box::new(42);
    /// let at_my_box: Out<'_, Box<i32>> =
    ///     my_box
    ///         .manually_drop_mut()
    ///         .as_out()
    /// ;
    /// // Overwrite `my_box` with uninitialized bytes / garbage content.
    /// unsafe {
    ///     *at_my_box.as_mut_uninit() = MaybeUninit::uninit();
    /// }
    /// // Runs the destructor for a `Box<i32>` using a garbage pointer that
    /// // may thus point anywhere in memory!
    /// drop(my_box)
    /// ```
    ///
    /// A function from an external library must always be seen as opaque
    /// (unless its documentation makes implementation-detail guarantees, such
    /// as this very crate does), so one cannot rely on its implementation
    /// (unless the lib is open source AND you pin-point to that version of the
    /// crate, either through `version = "=x.y.z"` or through `git = ...,
    /// rev = ...` in `Cargo.toml`).
    ///
    /// ```rust,ignore
    /// // `fn zeroize (out: &'_ mut MaybeUninit<u8>) -> &'_ mut u8;`
    /// // The author of the crate says it uses that `out` reference to write
    /// // `0` to the pointee.
    /// use ::some_lib::zeroize;
    ///
    /// let mut x = 42;
    /// let at_x = x.as_out();
    /// // Unsound! The lib implementation is free to write
    /// // `MaybeUninit::uninit()` garbage to the pointee!
    /// zeroize(unsafe { at_x.as_mut_uninit() });
    /// ```
    #[inline]
    pub
    unsafe
    fn as_mut_uninit (self: Out<'out, T>)
      -> &'out mut MaybeUninit<T>
    {
        &mut *({self}.as_mut_ptr().cast())
    }
}

/// This can be useful to get a `Out<'long ...>` out of a
/// `&'short mut Out<'long ...>` by [`mem::replace`]-ing with a `Out::default()`
/// (_e.g._, to implement an [`Iterator`]).
impl<'out, T : 'out> Default for Out<'out, [T]> {
    #[inline]
    fn default ()
      -> Self
    {
        <&mut [MaybeUninit<T>]>::into(&mut [])
    }
}

impl<'out, T : 'out> From<&'out mut [T]> for Out<'out, [T]>
where
    T : Copy,
{
    #[inline]
    fn from (slice: &'out mut [T])
      -> Out<'out, [T]>
    {
        Out(
            slice.into(),
            Default::default(),
        )
    }
}

impl<'out, T : 'out> From<&'out mut [ManuallyDrop<T>]> for Out<'out, [T]> {
    #[inline]
    fn from (slice: &'out mut [ManuallyDrop<T>])
      -> Out<'out, [T]>
    {
        unsafe {
            // # Safety
            //
            //   - The API does not allow to write `MaybeUninit::uninit()` into
            //     the pointee.
            Out(
                ptr::NonNull::new_unchecked(
                    slice as *mut [ManuallyDrop<T>] as *mut [T]
                ),
                Default::default(),
            )
        }
    }
}

impl<'out, T : 'out> From<&'out mut [MaybeUninit<T>]> for Out<'out, [T]> {
    #[inline]
    fn from (slice: &'out mut [MaybeUninit<T>])
      -> Out<'out, [T]>
    {
        unsafe {
            Out(
                ptr::NonNull::new_unchecked(
                    slice as *mut [MaybeUninit<T>] as *mut [T]
                ),
                Default::default(),
            )
        }
    }
}

impl<'out, T : 'out> Out<'out, [T]> {
    /// Converts a single item out reference into a `1`-long out slice.
    ///
    /// This is the `&out` version of
    /// [`slice::from_ref`] and [`slice::from_mut`].
    #[inline]
    pub
    fn from_out (out: Out<'out, T>)
      -> Out<'out, [T]>
    {
        unsafe {
            slice::from_mut(out.as_mut_uninit())
                .as_out()
        }
    }

    /// Obtains a read-only non-NULL and well-aligned raw pointer to a
    /// potentially uninitialized `T`.
    ///
    /// Unless maybe with interior mutability through raw pointers, there is
    /// no case where using this function is more useful than going through
    /// [`<[MaybeUninit<_>]>::assume_init_by_ref()`][
    /// `MaybeUninitExt::assume_init_by_ref`].
    ///
    /// Worse, the lack of `unsafe`-ty of the method (ignoring the one needed
    /// to use the pointer) and its "boring" name may lead to code
    /// read-dereferencing the pointer (which implicitly `assume_init()`s it)
    /// without having ensured the soundness of such (implicit) `assume_init()`.
    #[inline]
    pub
    fn as_ptr (self: &'_ Self)
      -> *const T
    {
        self.0.as_ptr().cast()
    }

    /// Returns a raw mutable pointer to the pointee.
    ///
    /// See [`Out::as_mut_ptr`] for more info regarding safety and guarantees.
    #[inline]
    pub
    fn as_mut_ptr (self: &'_ mut Self)
      -> *mut T
    {
        self.0.as_ptr().cast()
    }

    /// _Upgrades_ the `&out _`  (write-valid-values-only) reference to a
    /// `&mut MaybeUninit<_>` (write-anything) reference.
    ///
    /// See [`Out::as_mut_uninit`] for more info regarding safety.
    #[inline]
    pub
    unsafe
    fn as_mut_uninit (self: Out<'out, [T]>)
      -> &'out mut [MaybeUninit<T>]
    {
        &mut *(self.0.as_ptr() as *mut [MaybeUninit<T>])
    }

    /// Main indexing operation on an `&out [_]`.
    ///
    /// The type `Index` of `idx` may be:
    ///
    ///   - a `usize`, and then `Index::Output` is a `Out<T>` reference to a
    ///     single element.
    ///
    ///   - a `Range<usize>` (_e.g._, `a .. b`), and then `Index::Output` is
    ///     a `Out<[T]>` reference to a subslice.
    ///
    /// # Example
    ///
    /// ```rust
    /// use ::uninit::prelude::*;
    ///
    /// let src: &[u8] = b"Hello, World!";
    /// // Stack-allocate an uninitialized buffer.
    /// let mut buf = uninit_array![u8; 256];
    /// // copy `src` into this stack allocated buffer, effectively initializing it.
    /// let buf: &mut [u8] =
    ///     // buf[.. src.len()].as_out()
    ///     buf.as_out().get_out(.. src.len()).unwrap()
    ///         .copy_from_slice(src)
    /// ;
    /// assert_eq!(buf, b"Hello, World!");
    /// buf[7 ..].copy_from_slice(b"Earth!");
    /// assert_eq!(buf, b"Hello, Earth!");
    /// ```
    #[inline]
    pub
    fn get_out<Index> (self: Out<'out, [T]>, idx: Index)
      -> Option<Index::Output>
    where
        Index : UsizeOrRange<'out, T>, // renamed for the documentation
    {
        macro_rules! impl_SliceIndex {(
            $($Range:ty),+ $(,)?
        ) => (
            $(
                impl<'out, T : 'out> SliceIndex<'out, T> for $Range {
                    type Output = Out<'out, [T]>;

                    #[inline]
                    fn idx (self: Self, slice: Out<'out, [T]>)
                      -> Option<Out<'out, [T]>>
                    {
                        unsafe {
                            // Safety: this goes through an ephemeral
                            // `&mut [MaybeUninit<_>]` reference to be able to
                            // use slice indexing, but immediately downgrades
                            // it back to an `Out` reference, so no danger
                            // of writing garbage data.
                            slice.as_mut_uninit()
                                .get_mut(self)
                                .map(Out::from)
                        }
                    }
                }
            )*
        )}
        impl<'out, T : 'out> SliceIndex<'out, T> for usize {
            type Output = Out<'out, T>;

            #[inline]
            fn idx (self: usize, slice: Out<'out, [T]>)
              -> Option<Out<'out, T>>
            {
                unsafe {
                    // Safety: ditto
                    slice.as_mut_uninit()
                        .get_mut(self)
                        .map(Out::from)
                }
            }
        }
        impl_SliceIndex! {
            // a .. b
            ::core::ops::Range<usize>,
            // a ..= b
            ::core::ops::RangeInclusive<usize>,
            // a ..
            ::core::ops::RangeFrom<usize>,
            // .. b
            ::core::ops::RangeTo<usize>,
            // ..= b
            ::core::ops::RangeToInclusive<usize>,
            // ..
            ::core::ops::RangeFull,
        }

        idx.idx(self)
    }

    /// Same as `.get_out()`, but with the bound check being elided.
    ///
    /// # Safety
    ///
    /// The given `idx` mut be in bounds:
    ///
    ///   - if `idx: usize`, then `idx` must be `< self.len()`.
    ///
    ///   - if `idx` is an upper-bounded range (_e.g._, `.. b`, `a ..= b`),
    ///     then the upper bound (`b` in the example) must be `< self.len()`.
    ///
    ///   - _etc_.
    ///
    /// See [`.get_unchecked_mut()`](
    /// https://doc.rust-lang.org/std/primitive.slice.html#method.get_unchecked_mut)
    /// for more info about the safety of such call.
    #[inline]
    pub
    unsafe
    fn get_unchecked_out<Index> (self: Out<'out, [T]>, idx: Index)
      -> Index::Output
    where
        Index : UsizeOrRange<'out, T>, // renamed for the documentation
    {
        self.get_out(idx)
            .unwrap_or_else(|| if cfg!(debug_assertions) {
                panic!(concat!(
                    "Attempted to index out of bounds through unchecked ",
                    "indexing (this was detected thanks to a check still ",
                    "being present in debug mode).\n",
                    r"/!\ THIS IS A BUG AND A SOUNDNESS ISSUE /!\", "\n",
                    "Please submit an issue ASAP.",
                ));
            } else {
                ::core::hint::unreachable_unchecked()
            })
    }

    /// Downgrades the `Out<'_, [T]>` slice into a `&'_ [MaybeUninit<T>]`.
    ///
    /// This leads to a read-only<sup>1</sup> "unreadable" slice which is thus
    /// only useful for accessing `&'_ []` metadata, mainly the length of the
    /// slice.
    ///
    /// In practice, calling this function explicitely is not even needed given
    /// that `Out<'_, [T]> : Deref<Target = [MaybeUninit<T>]`, so one can do:
    ///
    /// ```rust
    /// use ::uninit::prelude::*;
    ///
    /// let mut backing_array = uninit_array![_; 42];
    /// let buf: Out<'_, [u8]> = backing_array.as_out();
    /// assert_eq!(buf.len(), 42); // no need to `.r().as_uninit()`
    /// ```
    ///
    /// <sup>1</sup> <small>Unless Interior Mutability is involved;
    /// speaking of which:</small>
    ///
    /// # Interior Mutability
    ///
    /// The whole design of `Out` references is to forbid any non-unsafe API
    /// that would allow writing `MaybeUninit::uninit()` garbage into the
    /// pointee. So, for instance, this crate does not offer any API like:
    ///
    /// ```rust
    /// use ::core::{cell::Cell, mem::MaybeUninit};
    ///
    /// // /!\ This is UNSOUND when combined with the `::uninit` crate!
    /// fn swap_mb_uninit_and_cell<T> (
    ///     p: &'_ MaybeUninit<Cell<T>>,
    /// ) -> &'_ Cell<MaybeUninit<T>>
    /// {
    ///     unsafe {
    ///         // Safety: both `Cell` and `MaybeUninit` are `#[repr(transparent)]`
    ///         ::core::mem::transmute(p)
    ///     }
    /// }
    /// ```
    ///
    /// Indeed, if both such non-`unsafe` API and the `uninit` crate were
    /// present, then one could trigger UB with:
    ///
    /// ```rust,ignore
    /// let mut x = [Cell::new(42)];
    /// let at_mb_uninit_cell: &'_ MaybeUninit<Cell<u8>> =
    ///     &x.as_out().as_uninit()[0]
    /// ;
    /// swap_mb_uninit_and_cell(at_mb_uninit_cell)
    ///     .set(MaybeUninit::uninit()) // UB!
    /// ;
    /// ```
    ///
    /// The author of the crate believes that such UB is the responsibility of
    /// the one who defined `swap_mb_uninit_and_cell`, and that in general that
    /// function is unsound: **`MaybeUninit`-ness and interior mutability do
    /// not commute!**
    ///
    ///   - the `Safety` annotation in the given example only justifies that
    ///     it is not breaking any layout-based validity invariants,
    ///     but it is actually impossible to semantically prove that it is safe
    ///     for these properties to commute.
    ///
    /// If you are strongly convinced of the opposite, please file an issue (if
    /// there isn't already one: since this question is not that clear the
    /// author is very likely to create an issue themself).
    #[inline]
    pub
    fn as_uninit (self: Out<'out, [T]>)
      -> &'out [MaybeUninit<T>]
    {
        unsafe {
            // Safety: `swap_mb_uninit_and_cell` is the one considered unsound.
            &*(self.0.as_ptr() as *const [MaybeUninit<T>])
        }
    }

    /// Upgrades the `&out [_]` (write-only) reference to a read-writeable
    /// `&mut [_]`.
    ///
    /// # Safety
    ///
    /// Don't be lured by the `&mut` reference: Rust validity invariants
    /// imply that an `&mut` reference is only sound to produce if it points
    /// to initialized values; it is otherwise instant UB. See
    /// [`MaybeUninit::assume_init`] for more info about it. Thus:
    ///
    ///   - The pointee(s) must have been initialized.
    ///
    /// This is a **validity invariant**, meaning that UB does happen from just
    /// calling that function to produce an ill-formed reference, even if the
    /// obtained reference is "never actually used".
    #[inline]
    pub
    unsafe
    fn assume_all_init (mut self: Out<'out, [T]>) -> &'out mut [T]
    {
        let len = self.len();
        slice::from_raw_parts_mut(
            self.as_mut_ptr(),
            len,
        )
    }

    /// Initialize the buffer with a copy from another (already initialized)
    /// buffer.
    ///
    /// It returns a read-writable slice to the initialized bytes for
    /// convenience (automatically
    /// [`assume_init`][`Out::assume_init`]-ed).
    ///
    /// # Panic
    ///
    /// The function panics if the slices' lengths are not equal.
    ///
    /// # Guarantees (that `unsafe` code may rely on)
    ///
    /// A non-`panic!`king return from this function **guarantees that the input
    /// slice has been (successfully) initialized**, and that it is thus then
    /// sound to `.assume_init()`.
    ///
    /// It also guarantees that the returned slice does correspond to the input
    /// slice (_e.g._, for [`crate::ReadIntoUninit`]'s safety guarantees).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use ::core::mem::{self, MaybeUninit};
    /// use ::uninit::prelude::*;
    ///
    /// let mut array = uninit_array![_; 13];
    /// assert_eq!(
    ///     array.as_out().copy_from_slice(b"Hello, World!"),
    ///     b"Hello, World!",
    /// );
    /// // we can thus soundly `assume_init` our array:
    /// let array = unsafe {
    ///     mem::transmute::<
    ///         [MaybeUninit<u8>; 13],
    ///         [            u8 ; 13],
    ///     >(array)
    /// };
    /// assert_eq!(
    ///     array,
    ///     *b"Hello, World!",
    /// );
    /// ```
    pub
    fn copy_from_slice (
        mut self: Out<'out, [T]>,
        source_slice: &'_ [T],
    ) -> &'out mut [T]
    where
        T : Copy,
    {
        unsafe {
            // # Safety
            //
            //   - Writing to `self.0` is fine since `source_slice` only
            //     contains initialized elements.
            //
            //   - the `copy_nonoverlapping()` call guarantees that the buffer
            //     has been initialized.
            self.r()
                .as_mut_uninit()
                .copy_from_slice(
                    <[MaybeUninit<T>]>::from_ref(source_slice)
                )
            ;
            self.assume_all_init()
        }
    }

    /// Fills the buffer with values from up to the first `self.len()` elements
    /// of an `iterable`.
    ///
    /// # Guarantees (that `unsafe` code may rely on)
    ///
    /// A non-panicking return from this function guarantees that the first `k`
    /// values of the buffer have been initialized and are thus sound to
    /// `.assume_init()`, where `k`, the numbers of elements that `iterable`
    /// has yielded (capped at `self.len()`), is the length of the returned
    /// buffer.
    #[inline]
    pub
    fn init_with (
        mut self: Out<'out, [T]>,
        iterable: impl IntoIterator<Item = T>,
    ) -> &'out mut [T]
    {
        let len = self.len();
        let mut iter_out = self.iter_out();
        iter_out
            .by_ref()
            .zip(iterable)
            .for_each(|(at_dst, next)| { at_dst.write(next); })
        ;
        let init_count = len - iter_out.remaining().len();
        unsafe {
            // Safety: `init_count` values of the buffer have been initialized
            self.get_unchecked_out(.. init_count)
                .assume_all_init()
        }
    }

    /// `.reborrow().into_iter()`
    #[inline]
    pub
    fn iter_out<'reborrow> (self: &'reborrow mut Out<'out, [T]>)
      -> iter::IterOut<'reborrow, T>
    {
        self.into_iter()
    }

    /// Same as [`.split_at_mut()`](https://doc.rust-lang.org/std/primitive.slice.html#method.split_at_mut
    /// ), but with `&out [_]` references.
    ///
    /// # Panic
    ///
    /// Panics if `idx > len`.
    #[inline]
    pub
    fn split_at_out (self: Out<'out, [T]>, idx: usize)
      -> (Out<'out, [T]>, Out<'out, [T]> )
    {
        let (left, right) = unsafe { self.as_mut_uninit() }.split_at_mut(idx);
        (left.as_out(), right.as_out())
    }
}

/// `Deref` into `[MaybeUninit<T>]` to get access to the slice length related
/// getters.
impl<'out, T : 'out> ::core::ops::Deref for Out<'out, [T]> {
    type Target = [MaybeUninit<T>];

    #[inline]
    fn deref (self: &'_ Self)
      -> &'_ [MaybeUninit<T>]
    {
        unsafe {
            // Safety: see `fn as_uninit`.
            &*(self.0.as_ptr() as *const [MaybeUninit<T>])
        }
    }
}

use private::{SliceIndex, SliceIndex as UsizeOrRange};
mod private {
    use super::*;

    pub
    trait SliceIndex<'out, T> {
        type Output : 'out;

        fn idx (self: Self, slice: Out<'out, [T]>)
          -> Option<Self::Output>
        ;
    }
}

/// `&out [_]` slice iteration logic.
pub
mod iter {
    use super::*;

    /// The value obtained when calling `.into_iter()` on a `Out<'out, [T]>`.
    ///
    /// An iterator over single value `Out<'out, T>` references.
    #[allow(missing_debug_implementations)]
    pub
    struct IterOut<'out, T : 'out> {
        slice: Out<'out, [T]>,
    }

    impl<'out, T : 'out> IterOut<'out, T> {
        /// Extracts an `Out<[T]>` slice reference pointing to the elements not
        /// yet yielded by the iterator.
        #[inline]
        pub
        fn remaining (self: IterOut<'out, T>)
          -> Out<'out, [T]>
        {
            self.slice
        }
    }

    impl<'out, T : 'out> IntoIterator for Out<'out, [T]> {
        type Item = Out<'out, T>;
        type IntoIter = IterOut<'out, T>;

        fn into_iter (self: Out<'out, [T]>)
          -> IterOut<'out, T>
        {
            IterOut { slice: self }
        }
    }

    impl<'out, 'inner : 'out, T : 'inner> IntoIterator
        for &'out mut Out<'inner, [T]>
    {
        type Item = Out<'out, T>;
        type IntoIter = IterOut<'out, T>;

        #[inline]
        fn into_iter (self: &'out mut Out<'inner, [T]>)
          -> IterOut<'out, T>
        {
            self.reborrow().into_iter()
        }
    }

    impl<'out, T : 'out> Iterator for IterOut<'out, T> {
        type Item = Out<'out, T>;

        #[inline]
        fn next (self: &'_ mut IterOut<'out, T>)
          -> Option<Out<'out, T>>
        {
            if self.slice.is_empty() { return None; }
            let slice = mem::replace(&mut self.slice, Out::default());
            let (first, rest) = slice.split_at_out(1);
            self.slice = rest;
            Some(unsafe {
                first.get_unchecked_out(0)
            })
        }
    }
}
