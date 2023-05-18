use super::MaybeUninitExt;

use_prelude!();

// Notes for the reviewer:
// This is similar to `MaybeUninitExt` - should it be consolidated into this one?
// Should this be in this module? It's used more as a marker/conversion trait than an extension trait.

/// Converts a reference to its uninitialized form.
pub unsafe trait AsUninit {
    /// # Guarantees (that `unsafe` code may rely on)
    /// 
    /// This type must have the same layout as `Self` but with no requirement on its contents.
    type Uninit: ?Sized + MaybeUninitExt<T = Self>;

    /// Converts a `&self` to its uninitialized equivalent.
    /// 
    /// # Guarantees (that `unsafe` code may rely on)
    /// 
    /// - The input and output address match.
    fn as_ref_uninit(&self) -> &Self::Uninit;

    /// Converts a `&mut T` to its uninitialized equivalent.
    ///
    /// This _upgrades_ the `&mut T` (read-write-valid-values-only) reference to a
    /// `&mut MaybeUninit<_>` (write-anything) reference.
    /// 
    /// # Safety (for callers)
    ///
    /// The same requirements as [`Out::as_uninit_mut`].
    /// Care should be taken with usage of the output - uninitialized garbage must not be written.
    /// 
    /// # Guarantees (that `unsafe` code may rely on)
    /// 
    /// - The input and output address match.
    unsafe fn as_mut_uninit(&mut self) -> &mut Self::Uninit;
}

unsafe impl<T> AsUninit for T {
    type Uninit = MaybeUninit<T>;

    fn as_ref_uninit(&self) -> &Self::Uninit {
        unsafe { &*(self as *const T).cast() }
    }

    unsafe fn as_mut_uninit(&mut self) -> &mut Self::Uninit {
        &mut *(self as *mut T).cast()
    }
}

// // Unfortunately this cannot `impl<T: ?Sized> AsUninit for ManuallyDrop<T>` as
// // that would conflict with the `Sized` blanket impl.
// unsafe impl<T> AsUninit for ManuallyDrop<[T]> {
//     type Uninit = [MaybeUninit<ManuallyDrop<T>>];

//     fn as_ref_uninit(&self) -> &Self::Uninit {
//         todo!()
//     }

//     unsafe fn as_mut_uninit(&mut self) -> &mut Self::Uninit {
//         todo!()
//     }
// }

unsafe impl<T> AsUninit for [T] {
    type Uninit = [MaybeUninit<T>];

    fn as_ref_uninit(&self) -> &Self::Uninit {
        unsafe { &*(self as *const [T] as *const [MaybeUninit<T>]) }
    }

    unsafe fn as_mut_uninit(&mut self) -> &mut Self::Uninit {
        &mut *(self as *mut [T] as *mut [MaybeUninit<T>])
    }
}
