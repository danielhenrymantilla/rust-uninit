use_prelude!();

/// Extension trait providing tranformations between init and uninit.
///
/// This is currently only implemented for [`Copy`] types, since the
/// semantics when [`drop` glue][`mem::needs_drop`] is involved are less
/// easy to handle correctly (danger of leaking memory).
///
/// # `from_mut`?
///
/// The conversion `&mut T` to `&mut MaybeUninit<T>` is actually unsound,
/// since there is nothing preventing the obtained `mut` reference to be used
/// to overwrite the pointee with `MaybeUninit::uninit()`, _i.e._, an
/// uninitialised (and thus garbage) value:
///
/// ```rust,no_run
/// use ::core::mem::{MaybeUninit, transmute};
///
/// unsafe fn from_mut<T> (it: &'_ mut T) -> &'_ mut MaybeUninit<T>
/// {
///     transmute(it)
/// }
///
/// let mut x = Box::new(42);
/// let at_x_uninit: &mut MaybeUninit<Box<i32>> = unsafe {
///     // If this were safe...
///     from_mut(&mut x)
/// };
/// // Then safe code would be able to do this:
/// *at_x_uninit = MaybeUninit::uninit(); // <--------+
/// // drop(x); // drops an uninitialized value! UB --+
/// ```
///
/// The author of the crate did overlook that and offered such transformation
/// within a non-`unsafe` function, leading to an unsound function. Hence the
/// yanked versions of the crate.
///
/// The correct way to do this now is through
/// [the `&out` reference abstraction][`crate::out_ref`].
pub
trait MaybeUninitExt {
    #[allow(missing_docs)]
    type T : ?Sized;

    /// Converts a `&MaybeUninit<_>` to a `& _`.
    ///
    /// # Safety
    ///
    /// Don't be lured by the reference: this has the same safety requirements
    /// that [`.assume_init`][`MaybeUninit::assume_init`] does. Mainly:
    ///
    ///   - The `Self::T` that `self` points to must be initialized.
    unsafe
    fn assume_init_by_ref (self: &'_ Self)
      -> &'_ Self::T
    ;

    /// Converts a `&mut MaybeUninit<_>` to a `&mut _`.
    ///
    /// # Safety
    ///
    /// Don't be lured by the `mut` reference: this has the same safety
    /// requirements that [`.assume_init`][`MaybeUninit::assume_init`] does.
    /// Mainly:
    ///
    ///   - The `Self::T` that `self` points to must be initialized.
    unsafe
    fn assume_init_by_mut (self: &'_ mut Self)
      -> &'_ mut Self::T
    ;

    /// Downgrades a `& _` to a `&MaybeUninit<_>`. Rarely useful.
    fn from_ref (init_ref: &'_ Self::T)
      -> &'_ Self
    ;
}

#[require_unsafe_in_bodies]
impl<T : Copy> MaybeUninitExt for MaybeUninit<T> {
    type T = T;

    #[inline]
    unsafe
    fn assume_init_by_ref (self: &'_ Self)
      -> &'_ Self::T
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(self)
        }
    }

    #[inline]
    unsafe
    fn assume_init_by_mut (self: &'_ mut Self)
      -> &'_ mut Self::T
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(self)
        }
    }

    #[inline]
    fn from_ref (some_ref: &'_ Self::T)
      -> &'_ Self
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(some_ref)
        }
    }
}

#[require_unsafe_in_bodies]
impl<T : Copy> MaybeUninitExt for [MaybeUninit<T>] {
    type T = [T];

    #[inline]
    unsafe
    fn assume_init_by_ref (self: &'_ Self)
      -> &'_ Self::T
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            let len = self.len();
            slice::from_raw_parts(
                self.as_ptr().cast(),
                len,
            )
        }
    }

    #[inline]
    unsafe
    fn assume_init_by_mut (self: &'_ mut Self)
      -> &'_ mut Self::T
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            let len = self.len();
            slice::from_raw_parts_mut(
                self.as_mut_ptr().cast(),
                len,
            )
        }
    }

    #[inline]
    fn from_ref (slice: &'_ Self::T)
      -> &'_ Self
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            let len = slice.len();
            slice::from_raw_parts(
                slice.as_ptr().cast(),
                len,
            )
        }
    }
}
