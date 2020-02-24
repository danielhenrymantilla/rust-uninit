use crate::{
    extension_traits::MaybeUninitExt,
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
/// unsound][`Out::as_uninit_mut`]).
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
struct Out<'out, T : 'out + ?Sized> (
    ptr::NonNull<T>,
    ::core::marker::PhantomData<&'out mut T>,
);

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

/// For non-`Copy` types, explicitely transmuting the `mut` reference into one
/// that points to a `ManuallyDrop` is required, so as to express how likely it
/// is that memory be leaked.
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
    #[inline]
    pub
    fn new (p: impl Into<Out<'out, T>>)
      -> Self
    {
        p.into()
    }

    #[inline]
    pub
    fn reborrow<'reborrow> (self: &'reborrow mut Out<'out, T>)
      -> Out<'reborrow, T>
    where
        'out : 'reborrow,
    {
        Out(self.0, Default::default())
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
}

impl<'out, T : 'out> Out<'out, T> {
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

    #[inline]
    pub
    fn replace (self: Out<'out, T>, value: T)
      -> (MaybeUninit<T>, &'out mut T)
    {
        unsafe {
            // # Safety
            //
            //   - This:
            //
            //      1. writes a valid value to the pointee,
            //
            //      2. extracts the previous value as now owned `MaybeUninit<T>`
            //
            //     Thus it does not not `assume_init()` the pointee nor write
            //     garbage to it.
            //
            //   - Thanks to write the pointee is known to be initialized.
            (
                ptr::replace(self.0.as_ptr().cast(), MaybeUninit::new(value)),
                self.assume_init(),
            )
        }
    }

    #[inline]
    pub
    fn as_mut_ptr (self: &'_ mut Out<'out, T>)
      -> *mut T
    {
        self.0.as_ptr()
    }

    #[inline]
    pub
    unsafe
    fn assume_init (mut self: Out<'out, T>)
      -> &'out mut T
    {
        &mut *self.as_mut_ptr()
    }

    /// # Safety
    ///
    /// The obtained reference cannot be used to write garbage
    /// (`MaybeUninit::uninit()`) into the pointee.
    ///
    /// # Counter-example
    ///
    /// The following code is Undefined Behavior
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
    ///     *at_my_box.as_uninit_mut() = MaybeUninit::uninit();
    /// }
    /// // Runs the destructor for a `Box<i32>` using a garbage pointer that
    /// // may thus point anywhere in memory!
    /// drop(my_box)
    /// ```
    #[inline]
    pub
    unsafe
    fn as_uninit_mut (self: Out<'out, T>)
      -> &'out mut MaybeUninit<T>
    {
        &mut *({self}.as_mut_ptr().cast())
    }
}

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
    #[inline]
    pub
    fn as_mut_ptr (self: &'_ mut Self)
      -> *mut T
    {
        self.0.as_ptr() as *mut T
    }

    /// # Safety
    ///
    /// The obtained reference cannot be used to write garbage
    /// (`MaybeUninit::uninit()`) into the pointee.
    #[inline]
    pub
    unsafe
    fn as_uninit_mut (self: Out<'out, [T]>)
      -> &'out mut [MaybeUninit<T>]
    {
        &mut *(self.0.as_ptr() as *mut [MaybeUninit<T>])
    }

    #[inline]
    pub
    fn get_out<Index> (self: Out<'out, [T]>, idx: Index)
      -> Option<Index::Output>
    where
        Index : SliceIndex<'out, T>,
    {
        impl<'out, T : 'out> SliceIndex<'out, T> for usize {
            type Output = Out<'out, T>;

            #[inline]
            fn idx (self: usize, slice: Out<'out, [T]>)
              -> Option<Out<'out, T>>
            {
                unsafe { slice.as_uninit_mut() }
                    .get_mut(self)
                    .map(Out::new)
            }
        }

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
                        unsafe { slice.as_uninit_mut() }
                            .get_mut(self)
                            .map(Out::new)
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

    /// # Safety
    ///
    /// The given `idx` mut be in bounds.
    #[inline]
    pub
    unsafe
    fn get_out_unchecked<Index> (self: Out<'out, [T]>, idx: Index)
      -> Index::Output
    where
        Index : SliceIndex<'out, T>,
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

    #[inline]
    pub
    unsafe
    fn assume_init (mut self: Out<'out, [T]>) -> &'out mut [T]
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
                .as_uninit_mut()
                .copy_from_slice(
                    <[MaybeUninit<T>]>::from_ref(source_slice)
                )
            ;
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
        mut self: Out<'out, [T]>,
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
    fn iter_out<'reborrow> (self: &'reborrow mut Out<'out, [T]>)
      -> iter::IterOut<'reborrow, T>
    {
        self.r().into_iter()
    }

    #[inline]
    pub
    fn split_at_out (self: Out<'out, [T]>, idx: usize)
      -> (Out<'out, [T]>, Out<'out, [T]> )
    {
        let (left, right) = unsafe { self.as_uninit_mut() }.split_at_mut(idx);
        (left.into(), right.into())
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
            &*(self.0.as_ptr() as *const [MaybeUninit<T>])
        }
    }
}

use private::SliceIndex;
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

pub
mod iter {
    use super::*;

    pub
    struct IterOut<'out, T : 'out> {
        /// Points to the remaining elements of the iterator.
        pub
        slice: Out<'out, [T]>,

        _non_exhaustive: (),
    }

    impl<'out, T : 'out> IntoIterator for Out<'out, [T]> {
        type Item = Out<'out, T>;
        type IntoIter = IterOut<'out, T>;

        fn into_iter (self: Out<'out, [T]>)
          -> IterOut<'out, T>
        {
            IterOut { slice: self, _non_exhaustive: () }
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
                first.get_out_unchecked(0)
            })
        }
    }
}
