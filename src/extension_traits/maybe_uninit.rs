use_prelude!();

/// Extension trait providing tranformations between init and uninit.
///
/// # `from_mut`?
/// 
/// This is provided [`AsUninit::as_mut_uninit]
///
/// The conversion `&mut T` to `&mut MaybeUninit<T>` is dangerous, since there
/// are restrictions on what safe code can do with the output. These are the same
/// requirements as [`Out::as_uninit_mut`], and is similar in soundness requirement
/// to [`Pin::get_unchecked_mut`].
/// 
/// Specifically, nothing must overwrite an initialized pointee
/// with `MaybeUninit::uninit()` data, _i.e._, an
/// uninitialised (and thus garbage) value, even though it is safe:
///
/// // TODO: 
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
    /// The inner type that `assume_init` initializes as.
    type T : ?Sized;

    /// Gets a raw pointer to the inner type.
    fn as_ptr(&self)-> *const Self::T;

    /// Gets a raw mutable pointer to the inner type.
    fn as_mut_ptr(&mut self) -> *mut Self::T;

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

    #[deprecated = "Use `AsUninit::as_ref_uninit` instead"]
    /// Downgrades a `& _` to a `&MaybeUninit<_>`. Rarely useful.
    fn from_ref (init_ref: &'_ Self::T)
      -> &'_ Self
    ;
}

#[allow(unused_unsafe)]
impl<T> MaybeUninitExt for MaybeUninit<T> {
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
            &*(self as *const _ as *const Self::T)
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
            &mut *(self as *mut _ as *mut Self::T)
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
            &*(some_ref as *const _ as *const Self)
        }
    }

    fn as_ptr(&self)-> *const Self::T {
        self.as_ptr()
    }

    fn as_mut_ptr(&mut self) -> *mut Self::T {
        self.as_mut_ptr()
    }
}

#[allow(unused_unsafe)]
impl<T> MaybeUninitExt for [MaybeUninit<T>] {
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

    fn as_ptr(&self)-> *const Self::T {
        self as *const _ as *const Self::T
    }

    fn as_mut_ptr(&mut self) -> *mut Self::T {
        self as *mut _ as *mut Self::T
    }
}
