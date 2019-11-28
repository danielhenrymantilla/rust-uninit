use_prelude!();

use ::core::mem::ManuallyDrop;

#[cfg(doc)]
use crate::extension_traits::ManuallyDropMut;

use private::Is;
mod private {
    pub trait Is { type Eq : ?Sized; }
    impl<T : ?Sized> Is for T { type Eq = T; }
}

/// Helper / extension trait to convert a `&mut _` into a `&out T` by calling
/// `.as_out::<T>()` on it.
///
/// By autoref, this means that you can even just extract a `&out T` reference
/// out of a `mut` element simply by calling `.as_out::<T>()` on it.
///
/// There is, however, one restriction: to be able to call `.as_out::<_>()` on
/// something, it needs to be either `Copy`, or a value wrapped in a
/// [`MaybeUninit`] / a [`ManuallyDrop`].
///
///   - (or a slice of such, in which case it yields a
///     [fat `&out` reference][`OutSlice`])
///
/// This is by design. Indeed, [`Out`] references do not call the destructor
/// of the overwritten element (since it may not be initialized).
/// This could cause memory leaks when there is an initialized element with
/// [drop glue][`core::mem::needs_drop`].
///
/// To solve this limitation, one must explicitly call
/// [`.manually_drop_mut()`][`ManuallyDropMut::manually_drop_mut`]
/// to automagically transmute the `&mut _` reference into a
/// `&mut ManuallyDrop<_>`.
///
/// # Examples
///
/// ```rust
/// use ::uninit::prelude::*;
///
/// let mut x = 0;
/// x.as_out::<u32>().write(42);
///
/// let mut y = ::core::mem::MaybeUninit::uninit();
/// y.as_out::<u32>().write(42);
/// let y = unsafe { y.assume_init() };
///
/// assert_eq!(x, y);
/// ```
pub
trait AsOut<Pointee_ : ?Sized> {
    type Out;

    fn as_out<Pointee : ?Sized + Is<Eq=Pointee_>> (self: Self)
      -> Self::Out
    ;
}

impl<'out, T : 'out> AsOut<T> for &'out mut MaybeUninit<T> {
    type Out = Out<'out, T>;

    #[inline]
    fn as_out<Pointee : ?Sized + Is<Eq=T>> (self: &'out mut MaybeUninit<T>)
      -> Out<'out, T>
    {
        self.into()
    }
}

impl<'out, T : 'out> AsOut<T> for &'out mut T
where
    T : Copy,
{
    type Out = Out<'out, T>;

    #[inline]
    fn as_out<Pointee : ?Sized + Is<Eq=T>> (self: &'out mut T)
      -> Out<'out, T>
    {
        self.into()
    }
}

impl<'out, T : 'out> AsOut<[T]> for &'out mut [MaybeUninit<T>] {
    type Out = OutSlice<'out, T>;

    #[inline]
    fn as_out<Pointee : ?Sized + Is<Eq=[T]>> (self: &'out mut [MaybeUninit<T>])
      -> OutSlice<'out, T>
    {
        self.into()
    }
}

impl<'out, T : 'out> AsOut<[T]> for &'out mut [T]
where
    T : Copy,
{
    type Out = OutSlice<'out, T>;

    #[inline]
    fn as_out<Pointee : ?Sized + Is<Eq=[T]>> (self: &'out mut [T])
      -> OutSlice<'out, T>
    {
        self.into()
    }
}

impl<'out, T : 'out> AsOut<T> for &'out mut ManuallyDrop<T> {
    type Out = Out<'out, T>;

    #[inline]
    fn as_out<Pointee : ?Sized + Is<Eq=T>> (self: &'out mut ManuallyDrop<T>)
      -> Out<'out, T>
    {
        self.into()
    }
}

impl<'out, T : 'out> AsOut<[T]> for &'out mut [ManuallyDrop<T>] {
    type Out = OutSlice<'out, T>;

    #[inline]
    fn as_out<Pointee : ?Sized + Is<Eq=[T]>> (self: &'out mut [ManuallyDrop<T>])
      -> OutSlice<'out, T>
    {
        self.into()
    }
}

macro_rules! impl_arrays {( $($N:tt)* ) => ($(
    impl<'out, T : 'out> AsOut<[T]> for &'out mut [MaybeUninit<T>; $N] {
        type Out = OutSlice<'out, T>;

        #[inline]
        fn as_out<Pointee : ?Sized + Is<Eq=[T]>> (self: Self)
          -> OutSlice<'out, T>
        {
            From::from(&mut self[..])
        }
    }
)*)}

impl_arrays! {
    0 1 2 3 4 5 6 7 8
    9 10 11 12 13 14 15 16
    17 18 19 20 21 22 23 24
    25 26 27 28 29 30 31 32
    33 34 35 36 37 38 39 40
    41 42 43 44 45 46 47 48
    49 50 51 52 53 54 55 56
    57 58 59 60 61 62 63 64
    128 256 512 1024
}
