use ::core::{
    mem::{self,
        ManuallyDrop,
        MaybeUninit,
    },
    slice,
};

/// Wrapper expressing the semantics of `&out T` references
/// (slim pointer (`T : Sized`)).
///
/// In other words, this has the semantics of `&'out mut MaybeUninit<T>`, but
/// for the ability to write garbage (`MaybeUninit::uninit()`) into it
/// (else coercing `&mut T` to `&out T = Out<T>` would be unsound).
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
#[repr(transparent)]
pub
struct Out<'out, T : 'out> (
    &'out mut MaybeUninit<T>,
);

impl<'out, T : 'out> From<&'out mut T> for Out<'out, T>
where
    T : Copy, // prevent accidentally leaking memory
{
    #[inline]
    fn from (p: &'out mut T)
      -> Out<'out, T>
    {
        Out(unsafe {
            // # Safety
            //
            //   - The API does not allow to write `MaybeUninit::uninit()` into
            //     the pointee.
            mem::transmute(p)
        })
    }
}

/// For non-`Copy` types, explicitely transmuting the `mut` reference into one
/// that points to a `ManuallyDrop` is required, so as to express how likely it
/// is that memory be leaked.
impl<'out, T : 'out> From<&'out mut ManuallyDrop<T>> for Out<'out, T> {
    #[inline]
    fn from (p: &'out mut ManuallyDrop<T>)
      -> Out<'out, T>
    {
        Out(unsafe {
            // # Safety
            //
            //   - The API does not allow to write `MaybeUninit::uninit()` into
            //     the pointee.
            mem::transmute(p)
        })
    }
}

impl<'out, T : 'out> From<&'out mut MaybeUninit<T>> for Out<'out, T> {
    #[inline]
    fn from (p: &'out mut MaybeUninit<T>)
      -> Out<'out, T>
    {
        Out(p)
    }
}

impl<'out, T : 'out> Out<'out, T> {
    #[inline]
    pub
    fn new (p: impl Into<Out<'out, T>>)
      -> Self
    {
        p.into()
    }

    #[inline]
    pub
    fn write (self: Out<'out, T>, value: T)
      -> &'out mut T
    {
        *self.0 = MaybeUninit::new(value);
        unsafe {
            // Safety: pointee has just been write-initialized.
            self.assume_init()
        }
    }

    #[inline]
    pub
    fn replace (self: Out<'out, T>, value: T)
      -> (MaybeUninit<T>, &'out mut T)
    {
        (
            mem::replace(self.0, MaybeUninit::new(value)),
            unsafe {
                // Safety: pointee has just been write-initialized.
                self.assume_init()
            },
        )
    }

    #[inline]
    pub
    fn as_mut_ptr (self: &'_ mut Out<'out, T>)
      -> *mut T
    {
        self.0.as_mut_ptr()
    }

    #[inline]
    pub
    fn reborrow<'reborrow> (self: &'reborrow mut Out<'out, T>)
      -> Out<'reborrow, T>
    where
        'out : 'reborrow,
    {
        Out(&mut *self.0)
    }

    /// Shorthand for [`.reborrow()`][`Out::reborrow`]
    #[inline]
    pub
    fn r<'reborrow> (self: &'reborrow mut Out<'out, T>)
      -> Out<'reborrow, T>
    where
        'out : 'reborrow,
    {
        self.reborrow()
    }

    #[inline]
    pub
    unsafe
    fn assume_init (mut self: Out<'out, T>) -> &'out mut T
    {
        &mut *self.as_mut_ptr()
    }
}

/// Wrapper expressing the semantics of `&out [T]` references
/// (fat pointer to a slice).
///
/// In other words, this has the semantics of `&'out mut [MaybeUninit<T>]`, but
/// for the ability to write garbage (`MaybeUninit::uninit()`) into it
/// (else coercing `&mut [T]` to `&out [T] = OutSlice<T>` would be unsound).
///
/// This means that the reference may point to uninitialized memory (or not),
/// and thus that writes to the pointee will not call the `.drop()` destructor.
///
/// This type can be [trivially constructed][`crate::AsOut`] from:
///
///   - a `&'out mut [MaybeUninit<T>]` (main point of the type),
///
///   - a `&'out mut [T]` (to keep the ergonomics of being able to overwrite an
///     already initialized value).
///
///       - To avoid "accidentally" leaking memory in this second case,
///         either `T` must be `Copy` (sufficient condition to prove there is
///         no drop glue), or you must first call
///         [`.manually_drop_mut()`][`crate::ManuallyDropMut`]
///         before the [`.as_out()`][`crate::AsOut`] "coercion".
#[repr(transparent)]
pub
struct OutSlice<'out, T : 'out> (
    &'out mut [MaybeUninit<T>],
);

impl<'out, T : 'out> From<&'out mut [T]> for OutSlice<'out, T>
where
    T : Copy,
{
    #[inline]
    fn from (slice: &'out mut [T])
      -> OutSlice<'out, T>
    {
        let len = slice.len();
        OutSlice(unsafe {
            // # Safety
            //
            //   - The API does not allow to write `MaybeUninit::uninit()` into
            //     the pointee.
            slice::from_raw_parts_mut(
                slice.as_mut_ptr().cast(),
                len,
            )
        })
    }
}

impl<'out, T : 'out> From<&'out mut [ManuallyDrop<T>]> for OutSlice<'out, T> {
    #[inline]
    fn from (slice: &'out mut [ManuallyDrop<T>])
      -> OutSlice<'out, T>
    {
        let len = slice.len();
        OutSlice(unsafe {
            // # Safety
            //
            //   - The API does not allow to write `MaybeUninit::uninit()` into
            //     the pointee.
            slice::from_raw_parts_mut(
                slice.as_mut_ptr().cast(),
                len,
            )
        })
    }
}

impl<'out, T : 'out> From<&'out mut [MaybeUninit<T>]> for OutSlice<'out, T> {
    #[inline]
    fn from (slice: &'out mut [MaybeUninit<T>])
      -> OutSlice<'out, T>
    {
        OutSlice(slice)
    }
}

impl<'out, T : 'out> OutSlice<'out, T> {
    #[inline]
    pub
    fn new (slice: impl Into<OutSlice<'out, T>>)
      -> Self
    {
        slice.into()
    }

    #[inline]
    pub
    fn as_mut_ptr (self: &'_ mut Self)
      -> *mut T
    {
        self.0.as_mut_ptr().cast()
    }

    #[inline]
    pub
    fn reborrow<'reborrow> (self: &'reborrow mut OutSlice<'out, T>)
      -> OutSlice<'reborrow, T>
    where
        'out : 'reborrow,
    {
        OutSlice(&mut *self.0)
    }

    /// Shorthand for [`.reborrow()`][`OutSlice::reborrow`]
    #[inline]
    pub
    fn r<'reborrow> (self: &'reborrow mut OutSlice<'out, T>)
      -> OutSlice<'reborrow, T>
    where
        'out : 'reborrow,
    {
        self.reborrow()
    }

    #[inline]
    pub
    fn get_out<Index> (self: OutSlice<'out, T>, idx: Index)
      -> Option<Index::Output>
    where
        Index : SliceIndex<'out, T>,
    {
        impl<'out, T : 'out> SliceIndex<'out, T> for usize {
            type Output = Out<'out, T>;

            #[inline]
            fn idx (self: usize, slice: OutSlice<'out, T>)
              -> Option<Out<'out, T>>
            {
                slice.0.get_mut(self).map(Out::new)
            }
        }

        macro_rules! impl_SliceIndex {(
            $($Range:ty),+ $(,)?
        ) => (
            $(
                impl<'out, T : 'out> SliceIndex<'out, T> for $Range {
                    type Output = OutSlice<'out, T>;

                    #[inline]
                    fn idx (self: Self, slice: OutSlice<'out, T>)
                      -> Option<OutSlice<'out, T>>
                    {
                        slice.0.get_mut(self).map(OutSlice::new)
                    }
                }
            )*
        )}

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

    #[inline]
    pub
    unsafe
    fn assume_init (mut self: OutSlice<'out, T>) -> &'out mut [T]
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
    /// [`assume_init`][`OutSlice::assume_init`]-ed).
    ///
    /// # Panic
    ///
    /// The function panics if the slices' lengths are not equal.
    ///
    /// # Guarantees
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
    ///     array.as_out::<[u8]>().copy_from_slice(b"Hello, World!"),
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
        self: OutSlice<'out, T>,
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
            self.0.copy_from_slice(
                crate::extension_traits::MaybeUninitExt::from_ref(source_slice)
            );
            self.assume_init()
        }
    }

    /// Fill the buffer with values from a function mapping indices to values.
    ///
    /// # Guarantees
    ///
    /// `factory` is guaranteed to be called in the `0 .. self.len()` order.
    #[inline]
    pub
    fn fill_with (
        mut self: OutSlice<'out, T>,
        mut factory: impl FnMut(usize) -> T,
    ) -> &'out mut [T]
    {
        self.iter_out()
            .enumerate()
            .for_each(|(i, at_dst)| { at_dst.write(factory(i)); })
        ;
        unsafe {
            // Safety: The `len` values of the buffer have been initialized
            self.assume_init()
        }
    }

    /// `.reborrow().into_iter()`
    #[inline]
    pub
    fn iter_out (self: &'_ mut OutSlice<'out, T>)
      -> iter::IterOut<'_, T>
    {
        self.r().into_iter()
    }

    #[inline]
    pub
    fn split_at_out (self: OutSlice<'out, T>, idx: usize)
      -> (OutSlice<'out, T>, OutSlice<'out, T> )
    {
        let (left, right) = self.0.split_at_mut(idx);
        (left.into(), right.into())
    }
}

/// `Deref` into `[MaybeUninit<T>]` to get access to the slice length related
/// getters.
impl<'out, T : 'out> ::core::ops::Deref for OutSlice<'out, T> {
    type Target = [MaybeUninit<T>];

    #[inline]
    fn deref (self: &'_ Self)
      -> &'_ Self::Target
    {
        &*self.0
    }
}

use private::SliceIndex;
mod private {
    use super::*;

    pub
    trait SliceIndex<'out, T> {
        type Output : 'out;

        fn idx (self: Self, slice: OutSlice<'out, T>)
          -> Option<Self::Output>
        ;
    }
}

pub
mod iter {
    use super::*;

    pub
    struct IterOut<'out, T : 'out> /* = */ (
        pub
        OutSlice<'out, T>,
    );

    impl<'out, T : 'out> IntoIterator for OutSlice<'out, T> {
        type Item = Out<'out, T>;
        type IntoIter = IterOut<'out, T>;

        fn into_iter (self: OutSlice<'out, T>)
          -> IterOut<'out, T>
        {
            IterOut(self)
        }
    }

    impl<'out, T : 'out> Iterator for IterOut<'out, T> {
        type Item = Out<'out, T>;

        #[inline]
        fn next (self: &'_ mut IterOut<'out, T>)
          -> Option<Out<'out, T>>
        {
            let this = &mut self.0;
            if this.is_empty() { return None; }
            let slice = mem::replace(this, <&mut [MaybeUninit<T>]>::into(&mut []));
            let (first, rest) = slice.split_at_out(1);
            *this = rest;
            Some(first.get_out(0).unwrap_or_else(|| unsafe {
                ::core::hint::unreachable_unchecked()
            }))
        }
    }
}
