use_prelude!();

use ::core::mem::ManuallyDrop;

/// Extension trait to convert a `&mut _` into a `&out _` by calling
/// `.as_out()` on it.
///
/// By autoref, this means that you can even just extract a `&out T` reference
/// out of a `mut` element simply by calling `.as_out()` on it.
///
/// There is, however, one restriction: to be able to call `.as_out()` on
/// something, it needs to be either `Copy`, or a value wrapped in a
/// [`MaybeUninit`] / a [`ManuallyDrop`].
///
/// This is by design. Indeed, [`Out`] references do not call the destructor
/// of the overwritten element (since it may not be initialized).
/// This could cause memory leaks when there is an initialized element with
/// [drop glue][`core::mem::needs_drop`].
///
/// To solve this limitation, one must explicitly call
/// [`.manually_drop_mut()`][`crate::ManuallyDropMut::manually_drop_mut`]
/// to automagically transmute the `&mut _` reference into a
/// `&mut ManuallyDrop<_>`.
///
/// # Examples
///
/// ```rust
/// use ::uninit::prelude::*;
///
/// let mut x = 0;
/// x.as_out().write(42);
///
/// let mut y = ::core::mem::MaybeUninit::uninit();
/// y.as_out().write(42);
/// let y = unsafe { y.assume_init() };
///
/// assert_eq!(x, y);
/// ```
pub trait AsOut<Pointee: ?Sized> {
    #[allow(missing_docs)]
    fn as_out<'out>(self: &'out mut Self) -> Out<'out, Pointee>;
}

impl<T> AsOut<T> for MaybeUninit<T> {
    #[inline]
    fn as_out<'out>(self: &'out mut MaybeUninit<T>) -> Out<'out, T> {
        self.into()
    }
}

impl<T> AsOut<T> for T
where
    T: Copy,
{
    #[inline]
    fn as_out<'out>(self: &'out mut T) -> Out<'out, T> {
        self.into()
    }
}

impl<T> AsOut<[T]> for [MaybeUninit<T>] {
    #[inline]
    fn as_out<'out>(self: &'out mut [MaybeUninit<T>]) -> Out<'out, [T]> {
        self.into()
    }
}

impl<T> AsOut<[T]> for [T]
where
    T: Copy,
{
    #[inline]
    fn as_out<'out>(self: &'out mut [T]) -> Out<'out, [T]> {
        // This appears to be necessary due to a Rust bug?
        // For some reason Rust isn't able to infer that `[T]: Copy`,
        // and inserting that bound creates a conflict with
        // `impl<T> AsOut<T> for T`.
        unsafe { Out::from_raw(self) }
    }
}

impl<T> AsOut<T> for ManuallyDrop<T> {
    #[inline]
    fn as_out<'out>(self: &'out mut ManuallyDrop<T>) -> Out<'out, T> {
        self.into()
    }
}

impl<T> AsOut<[T]> for [ManuallyDrop<T>] {
    #[inline]
    fn as_out<'out>(self: &'out mut [ManuallyDrop<T>]) -> Out<'out, [T]> {
        self.into()
    }
}

#[cfg(not(feature = "const_generics"))]
const _: () = {
    macro_rules! impl_arrays {( $($N:tt)* ) => ($(
        impl<T> AsOut<[T]> for [MaybeUninit<T>; $N] {
            #[inline]
            fn as_out<'out> (self: &'out mut Self)
              -> Out<'out, [T]>
            {
                From::from(&mut self[..])
            }
        }
        impl<T> AsOut<[T]> for [T; $N]
        where
            T : Copy,
        {
            #[inline]
            fn as_out<'out> (self: &'out mut Self)
              -> Out<'out, [T]>
            {
                From::from(&mut self[..])
            }
        }
    )*)}

    impl_arrays! {
           0  1  2  3  4  5  6  7
           8  9 10 11 12 13 14 15
          16 17 18 19 20 21 22 23
          24 25 26 27 28 29 30 31
          32 33 34 35 36 37 38 39
          40 41 42 43 44 45 46 47
          48 49 50 51 52 53 54 55
          56 57 58 59 60 61 62 63
          64
         128
         256
         512
        1024
    }
};

#[cfg(feature = "const_generics")]
const _: () = {
    #[cfg_attr(feature = "better-docs", doc(cfg(feature = "const_generics")))]
    impl<T, const N: usize> AsOut<[T]> for [MaybeUninit<T>; N] {
        #[inline]
        fn as_out<'out>(self: &'out mut Self) -> Out<'out, [T]> {
            From::from(&mut self[..])
        }
    }

    #[cfg_attr(feature = "better-docs", doc(cfg(feature = "const_generics")))]
    impl<T, const N: usize> AsOut<[T]> for [T; N]
    where
        [T]: Copy,
    {
        #[inline]
        fn as_out<'out>(self: &'out mut Self) -> Out<'out, [T]> {
            From::from(&mut self[..])
        }
    }
};
