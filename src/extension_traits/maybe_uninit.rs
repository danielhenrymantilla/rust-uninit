use_prelude!();

/// Extension trait providing tranformations between init and uninit.
///
/// # `from_mut`?
///
/// This is provided by [`AsMaybeUninit::as_mut_uninit`].
///
/// The conversion from `&mut T` to `&mut MaybeUninit<T>` is `unsafe`, since there
/// are restrictions on what safe code can do with the output. These are the same
/// requirements as [`Out::as_mut_uninit`].
///
/// Specifically, nothing must overwrite an initialized pointee
/// with `MaybeUninit::uninit()` data, _i.e._, an
/// uninitialised (and thus garbage) value, even though the API of `&mut T`
/// allows this safely. This is similar to `Pin::get_mut_unchecked`.
///
/// The correct way to convert `&mut T` into a maybe-initialized reference is through
/// [the `&out` reference abstraction][`crate::out_ref`].
///
/// [`AsMaybeUninit::as_mut_uninit`]: crate::AsMaybeUninit::as_mut_uninit
/// [`Out::as_mut_uninit`]: crate::out_ref::Out::as_mut_uninit
pub trait MaybeUninitExt {
    /// The inner type that may be initialized.
    ///
    /// - For `MaybeUninit<T: Sized>`, this is `T`.
    /// - For `[MaybeUninit<T>]`, this is `[T]`.
    type T: ?Sized;

    /// Gets a raw pointer to the inner type.
    fn as_ptr(&self) -> *const Self::T;

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
    unsafe fn assume_init_by_ref(&self) -> &Self::T;

    /// Converts a `&mut MaybeUninit<_>` to a `&mut _`.
    ///
    /// # Safety
    ///
    /// Don't be lured by the `mut` reference: this has the same safety
    /// requirements that [`.assume_init`][`MaybeUninit::assume_init`] does.
    /// Mainly:
    ///
    ///   - The `Self::T` that `self` points to must be initialized.
    unsafe fn assume_init_by_mut(&mut self) -> &mut Self::T;

    /// Downgrades a `& _` to a `&MaybeUninit<_>`. Rarely useful.
    #[deprecated = "Use `AsUninit::as_ref_uninit` instead"]
    fn from_ref(init_ref: &'_ Self::T) -> &'_ Self;
}

impl<T> MaybeUninitExt for MaybeUninit<T> {
    type T = T;

    #[inline]
    fn as_ptr(&self) -> *const Self::T {
        self.as_ptr()
    }

    #[inline]
    fn as_mut_ptr(&mut self) -> *mut Self::T {
        self.as_mut_ptr()
    }

    #[inline]
    unsafe fn assume_init_by_ref(self: &'_ Self) -> &'_ Self::T {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            &*(self as *const _ as *const Self::T)
        }
    }

    #[inline]
    unsafe fn assume_init_by_mut(self: &'_ mut Self) -> &'_ mut Self::T {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            &mut *(self as *mut _ as *mut Self::T)
        }
    }

    #[inline]
    fn from_ref(some_ref: &'_ Self::T) -> &'_ Self {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(some_ref)
        }
    }
}

impl<T> MaybeUninitExt for [MaybeUninit<T>] {
    type T = [T];

    #[inline]
    fn as_ptr(&self) -> *const Self::T {
        self as *const _ as *const Self::T
    }

    #[inline]
    fn as_mut_ptr(&mut self) -> *mut Self::T {
        self as *mut _ as *mut Self::T
    }

    #[inline]
    unsafe fn assume_init_by_ref(self: &'_ Self) -> &'_ Self::T {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            let len = self.len();
            slice::from_raw_parts(self.as_ptr().cast(), len)
        }
    }

    #[inline]
    unsafe fn assume_init_by_mut(self: &'_ mut Self) -> &'_ mut Self::T {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            let len = self.len();
            slice::from_raw_parts_mut(self.as_mut_ptr().cast(), len)
        }
    }

    #[inline]
    fn from_ref(slice: &'_ Self::T) -> &'_ Self {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            let len = slice.len();
            slice::from_raw_parts(slice.as_ptr().cast(), len)
        }
    }
}
