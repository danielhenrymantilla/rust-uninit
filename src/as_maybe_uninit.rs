use_prelude!();

use crate::extension_traits::MaybeUninitExt;
use core::mem::MaybeUninit;

/// Converts a reference into its maybe-initialized form.
///
/// This trait allows you to use a unified API for `MaybeUninit`
/// on sized and unsized types.
///
/// You probably don't need to implement this trait yourself:
/// it is automatically implemented for all `T: Sized` and `[T]`.
///
/// # Safety
/// - `Uninit` must have the same layout as `Self` but with no requirement on its contents.
///   See the [`MaybeUninit` layout](https://doc.rust-lang.org/std/mem/union.MaybeUninit.html#layout-1).
/// - All methods return pointers that point to the same memory as their input.
pub unsafe trait AsMaybeUninit {
    /// This type in its maybe-uninitialized form.
    type Uninit: ?Sized + MaybeUninitExt<T = Self>;

    /// Converts a `&self` to its maybe-initialized equivalent.
    fn as_ref_uninit(&self) -> &Self::Uninit;

    /// Converts a `&mut T` to its maybe-initialized equivalent.
    ///
    /// This converts a read-write-valid-values-only reference to a write-anything reference.
    ///
    /// # Safety
    ///
    /// The same requirements as [`Out::as_mut_uninit`].
    /// Care should be taken with usage of the output - uninitialized garbage must not be written.
    ///
    /// [`Out::as_mut_uninit`]: crate::out_ref::Out::as_mut_uninit
    unsafe fn as_mut_uninit(&mut self) -> &mut Self::Uninit;

    /// Converts a raw pointer to a reference to maybe-uninit.
    ///
    /// # Safety
    ///
    /// This has the same requirements as `&*(raw as *const Self::Uninit)`.
    ///
    /// - `raw` must point to a readable allocated memory for `'a` for the size of `T`
    /// - `raw` must be aligned for `T`
    unsafe fn raw_as_uninit<'a>(raw: *const Self) -> &'a Self::Uninit;

    /// Converts a raw mutable pointer to a mutable reference to maybe-uninit.
    ///
    /// # Safety
    ///
    /// This has the same requirements as `&mut *(raw as *mut Self::Uninit)`.
    ///
    /// - `raw` must point to a readable and writeable allocated object for `'a` for the size of `T`
    /// - The pointer must not alias any other mutable references for `'a`
    /// - `raw` must be aligned for `T`
    unsafe fn raw_mut_as_uninit<'a>(raw: *mut Self) -> &'a mut Self::Uninit;
}

// SAFETY:
// - `MaybeUninit<T>` has the same layout as `T` but with no requirements on its contents.
// - `as_ref_uninit` and `as_mut_uninit` return the same address as their input.
unsafe impl<T> AsMaybeUninit for T {
    type Uninit = MaybeUninit<T>;

    #[inline]
    fn as_ref_uninit(&self) -> &Self::Uninit {
        unsafe { &*(self as *const T).cast() }
    }

    #[inline]
    unsafe fn as_mut_uninit(&mut self) -> &mut Self::Uninit {
        &mut *(self as *mut T).cast()
    }

    #[inline]
    unsafe fn raw_as_uninit<'a>(raw: *const Self) -> &'a Self::Uninit {
        &*(raw as *const MaybeUninit<T>)
    }

    #[inline]
    unsafe fn raw_mut_as_uninit<'a>(raw: *mut Self) -> &'a mut Self::Uninit {
        &mut *(raw as *mut MaybeUninit<T>)
    }
}

// Unfortunately this cannot `impl<T: ?Sized> AsMaybeUninit for ManuallyDrop<T>` as
// that would conflict with the `Sized` blanket impl.

// SAFETY:
// - `[MaybeUninit<T>]` has the same layout as `[T]` but with no requirements on its contents.
// - `as_ref_uninit` and `as_mut_uninit` return the same address as their input.
unsafe impl<T> AsMaybeUninit for [T] {
    type Uninit = [MaybeUninit<T>];

    #[inline]
    fn as_ref_uninit(&self) -> &Self::Uninit {
        unsafe { &*(self as *const [T] as *const [MaybeUninit<T>]) }
    }

    #[inline]
    unsafe fn as_mut_uninit(&mut self) -> &mut Self::Uninit {
        &mut *(self as *mut [T] as *mut [MaybeUninit<T>])
    }

    #[inline]
    unsafe fn raw_as_uninit<'a>(raw: *const Self) -> &'a Self::Uninit {
        &*(raw as *const [MaybeUninit<T>])
    }

    #[inline]
    unsafe fn raw_mut_as_uninit<'a>(raw: *mut Self) -> &'a mut Self::Uninit {
        &mut *(raw as *mut [MaybeUninit<T>])
    }
}
