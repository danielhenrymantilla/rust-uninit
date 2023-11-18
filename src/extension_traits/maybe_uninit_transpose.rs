use_prelude!();

/// Extension trait to transform between `[MaybeUninit<T>; N]` and `MaybeUninit<[T; N]>`,
/// as well as between references to each.
///
/// # Examples
///
/// ## Initializing an array element-by-element
///
/// This example [adapted from the standard library][stdlib-mu-array-init] needs less
/// `unsafe` and no `transmute`s.
///
/// ```
/// use std::mem::{self, MaybeUninit};
/// use uninit::extension_traits::MaybeUninitTranspose;
///
/// let data = {
///     // Create an uninitialized array of `MaybeUninit`.
///     // The initial `uninit` constructs a `MaybeUninit<[Vec<u32>; 1000]>`,
///     // and the `transpose` exposes individual elements.
///     let mut data: [MaybeUninit<Vec<u32>>; 1000] = MaybeUninit::uninit().transpose();
///
///     // Dropping a `MaybeUninit` does nothing, so if there is a panic during this loop,
///     // we have a memory leak, but there is no memory safety issue.
///     for elem in &mut data[..] {
///         elem.write(vec![42]);
///     }
///
///     // Everything is initialized.
///     // Transpose back into a `MaybeUninit` of an array and `assume_init` it.
///     unsafe { data.transpose().assume_init() }
/// };
///
/// assert_eq!(&data[0], &[42]);
/// ```
///
/// [stdlib-mu-array-init]: https://doc.rust-lang.org/std/mem/union.MaybeUninit.html#initializing-an-array-element-by-element
///
pub trait MaybeUninitTranspose {
    /// `Self` but with the array and `MaybeUninit` parts swapped.
    ///
    /// | `Self` | `Self::Transposed` |
    /// | ------ | ------------------ |
    /// | `[MaybeUninit<T>; N]` | `MaybeUninit<[T; N]>` |
    /// | `MaybeUninit<[T; N]>` | `[MaybeUninit<T>; N]` |
    /// | `&'a [MaybeUninit<T>; N]` | `&'a MaybeUninit<[T; N]>` |
    /// | `&'a MaybeUninit<[T; N]>` | `&'a [MaybeUninit<T>; N]` |
    /// | `&'a mut [MaybeUninit<T>; N]` | `&'a mut MaybeUninit<[T; N]>` |
    /// | `&'a mut MaybeUninit<[T; N]>` | `&'a mut [MaybeUninit<T>; N]` |
    ///
    /// Like with [`Result::transpose`] and [`Option::transpose`],
    /// `x.transpose().transpose()` is a no-op.
    type Transposed: MaybeUninitTranspose<Transposed = Self>;

    /// Transpose between an array-of-`MaybeUninit` and a `MaybeUninit` of an array.
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use uninit::extension_traits::MaybeUninitTranspose;
    ///
    /// let mut uninit_of_array: MaybeUninit<[u32; 4]> = MaybeUninit::new([1,2,3,4]);
    ///
    /// // `transpose` of an array consumes, copying if the array element is `Copy`.
    /// let mut array_of_uninit: [MaybeUninit<u32>; 4] = uninit_of_array.transpose();
    ///
    /// array_of_uninit[0].write(10);
    ///
    /// // `transpose` of a reference does not copy.
    /// let uoa_ref = (&uninit_of_array).transpose();
    ///
    /// // SAFETY: the first element of `uninit_of_array` has been initialized
    /// assert_eq!(unsafe { uoa_ref[0].assume_init() }, 1);
    ///
    /// // SAFETY: the first element of `array_of_uninit` has been initialized
    /// assert_eq!(unsafe { array_of_uninit[0].assume_init() }, 10);
    ///
    /// // `transpose` can also go the other way and be used to mutate.
    /// let aou_mut: &mut MaybeUninit<[u32; 4]> = (&mut array_of_uninit).transpose();
    /// aou_mut.write([5,6,7,8]);
    /// assert_eq!(unsafe { array_of_uninit[0].assume_init() }, 5);
    /// ```
    fn transpose(self) -> Self::Transposed;

    /// An alternate way to spell `(&self).transpose()`.
    ///
    /// This explicitly communicates this is a conversion between references.
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use uninit::extension_traits::MaybeUninitTranspose;
    ///
    /// let uninit_of_array: MaybeUninit<[u32; 4]> = MaybeUninit::new([4,5,6,7]);
    ///
    /// // SAFETY: the second element of `uninit_of_array` has been initialized
    /// assert_eq!(unsafe { uninit_of_array.transpose_ref()[1].assume_init() }, 5);
    /// ```
    fn transpose_ref<'a>(&'a self) -> &'a Self::Transposed
    where
        &'a Self: MaybeUninitTranspose<Transposed = &'a Self::Transposed>,
    {
        self.transpose()
    }

    /// An alternate way to spell `(&mut self).transpose()`.
    ///
    /// This explicitly communicates this is a conversion between references.
    ///
    /// # Example
    ///
    /// ```
    /// use std::mem::MaybeUninit;
    /// use uninit::extension_traits::MaybeUninitTranspose;
    ///
    /// let mut uninit_of_array: MaybeUninit<[u32; 4]> = MaybeUninit::uninit();
    ///
    /// let array_of_uninit_mut = uninit_of_array.transpose_mut();
    /// array_of_uninit_mut[0].write(10);
    /// array_of_uninit_mut[1].write(20);
    /// array_of_uninit_mut[2].write(30);
    /// array_of_uninit_mut[3].write(40);
    ///
    /// // SAFETY: all of the elements of `uninit_of_array` have been initialized
    /// assert_eq!(unsafe { uninit_of_array.assume_init_ref() }, &[10, 20, 30, 40]);
    /// ```
    fn transpose_mut<'a>(&'a mut self) -> &'a mut Self::Transposed
    where
        &'a mut Self: MaybeUninitTranspose<Transposed = &'a mut Self::Transposed>,
    {
        self.transpose()
    }
}

#[cfg(feature = "const_generics")]
impl<T, const N: usize> MaybeUninitTranspose for [MaybeUninit<T>; N] {
    type Transposed = MaybeUninit<[T; N]>;

    fn transpose(self) -> Self::Transposed {
        // This does not use `mem::transmute` because the compiler's special
        // identical-size check does not function for generic code of this kind.

        // SAFETY:
        // - Neither `Self` nor `Self::Transposed` have drop glue,
        //   since they're composed of only `MaybeUninit`.
        // - `T` and `MaybeUninit<T>` are guaranteed to have the same layout.
        // - `[MaybeUninit<T>; N]` and `MaybeUninit<[T; N]>` both have no
        //   requirement for initialization for their entire memory span.
        // - `[MaybeUninit<T>; N]` and `MaybeUninit<[T; N]>` are guaranteed to have
        //   the same layout. This isn't universally applicable to types containing
        //   `MaybeUninit<T>` vs. `T`, but is true for arrays, which have a size of
        //   `size_of::<T>() * N` and the align of `T`.
        unsafe { core::mem::transmute_copy(&self) }
    }
}

#[cfg(feature = "const_generics")]
impl<T, const N: usize> MaybeUninitTranspose for MaybeUninit<[T; N]> {
    type Transposed = [MaybeUninit<T>; N];

    fn transpose(self) -> Self::Transposed {
        // This does not use `mem::transmute` because the compiler's special
        // identical-size check does not function for generic code of this kind.

        // SAFETY:
        // - Neither `Self` nor `Self::Transposed` have drop glue,
        //   since they're composed of only `MaybeUninit`.
        // - `T` and `MaybeUninit<T>` are guaranteed to have the same layout.
        // - `[MaybeUninit<T>; N]` and `MaybeUninit<[T; N]>` both have no
        //   requirement for initialization for their entire memory span.
        // - `[MaybeUninit<T>; N]` and `MaybeUninit<[T; N]>` are guaranteed to have
        //   the same layout. This isn't universally applicable to types containing
        //   `MaybeUninit<T>` vs. `T`, but is true for arrays, which have a size of
        //   `size_of::<T>() * N` and the align of `T`.
        unsafe { core::mem::transmute_copy(&self) }
    }
}

#[cfg(feature = "const_generics")]
impl<'a, T: 'a, const N: usize> MaybeUninitTranspose for &'a [MaybeUninit<T>; N] {
    type Transposed = &'a MaybeUninit<[T; N]>;

    fn transpose(self) -> Self::Transposed {
        // SAFETY:
        // - `T` and `MaybeUninit<T>` are guaranteed to have the same layout.
        // - `[MaybeUninit<T>; N]` and `MaybeUninit<[T; N]>` both have no
        //   requirement for initialization for their entire memory span.
        // - `[MaybeUninit<T>; N]` and `MaybeUninit<[T; N]>` are guaranteed to have
        //   the same layout. This isn't universally applicable to types containing
        //   `MaybeUninit<T>` vs. `T`, but is true for arrays, which have a size of
        //   `size_of::<T>() * N` and the align of `T`.
        unsafe { &*(self as *const [MaybeUninit<T>; N] as *const MaybeUninit<[T; N]>) }
    }
}

#[cfg(feature = "const_generics")]
impl<'a, T: 'a, const N: usize> MaybeUninitTranspose for &'a MaybeUninit<[T; N]> {
    type Transposed = &'a [MaybeUninit<T>; N];

    fn transpose(self) -> Self::Transposed {
        // SAFETY:
        // - `T` and `MaybeUninit<T>` are guaranteed to have the same layout.
        // - `[MaybeUninit<T>; N]` and `MaybeUninit<[T; N]>` both have no
        //   requirement for initialization for their entire memory span.
        // - `[MaybeUninit<T>; N]` and `MaybeUninit<[T; N]>` are guaranteed to have
        //   the same layout. This isn't universally applicable to types containing
        //   `MaybeUninit<T>` vs. `T`, but is true for arrays, which have a size of
        //   `size_of::<T>() * N` and the align of `T`.
        unsafe { &*(self as *const MaybeUninit<[T; N]> as *const [MaybeUninit<T>; N]) }
    }
}

#[cfg(feature = "const_generics")]
impl<'a, T: 'a, const N: usize> MaybeUninitTranspose for &'a mut [MaybeUninit<T>; N] {
    type Transposed = &'a mut MaybeUninit<[T; N]>;

    fn transpose(self) -> Self::Transposed {
        // SAFETY:
        // - `T` and `MaybeUninit<T>` are guaranteed to have the same layout.
        // - `[MaybeUninit<T>; N]` and `MaybeUninit<[T; N]>` both have no
        //   requirement for initialization for their entire memory span.
        // - `[MaybeUninit<T>; N]` and `MaybeUninit<[T; N]>` are guaranteed to have
        //   the same layout. This isn't universally applicable to types containing
        //   `MaybeUninit<T>` vs. `T`, but is true for arrays, which have a size of
        //   `size_of::<T>() * N` and the align of `T`.
        unsafe { &mut *(self as *mut [MaybeUninit<T>; N] as *mut MaybeUninit<[T; N]>) }
    }
}

#[cfg(feature = "const_generics")]
impl<'a, T: 'a, const N: usize> MaybeUninitTranspose for &'a mut MaybeUninit<[T; N]> {
    type Transposed = &'a mut [MaybeUninit<T>; N];

    fn transpose(self) -> Self::Transposed {
        // SAFETY:
        // - `T` and `MaybeUninit<T>` are guaranteed to have the same layout.
        // - `[MaybeUninit<T>; N]` and `MaybeUninit<[T; N]>` both have no
        //   requirement for initialization for their entire memory span.
        // - `[MaybeUninit<T>; N]` and `MaybeUninit<[T; N]>` are guaranteed to have
        //   the same layout. This isn't universally applicable to types containing
        //   `MaybeUninit<T>` vs. `T`, but is true for arrays, which have a size of
        //   `size_of::<T>() * N` and the align of `T`.
        unsafe { &mut *(self as *mut MaybeUninit<[T; N]> as *mut [MaybeUninit<T>; N]) }
    }
}
