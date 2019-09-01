use super::*;
use ::core::ptr;

/// Extension trait for `[`[`MaybeUninit`]`<u8>]`, that initializes the buffer
/// with a copy from another (already initialized) buffer.
///
/// It returns a read-writable slice to the initialized bytes for convenience
/// (automatically
/// [`assume_init_by_mut`][`MaybeUninitExt::assume_init_by_mut`]-ed).
///
/// # Panic
///
/// The function panics if the slices' lengths are not equal.
///
/// # Guarantees
///
/// A non-`panic!`king return from this function **guarantees that the input
/// slice has been (successfully) initialized**, and it is thus then sound to
/// `.assume_init()`.
///
/// It also guarantees that the returned slice does correspond to the input
/// slice (_e.g._, for [`ReadIntoUninit`]'s safety guarantees).
///
/// # Example
///
/// ```rust
/// # use ::core::mem::{self, MaybeUninit};
/// use ::uninit::{InitWithCopyFromSlice, uninit_byte_array};
///
/// let mut array = uninit_byte_array![_; 13];
/// assert_eq!(
///     array.init_with_copy_from_slice(b"Hello, World!"),
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
trait InitWithCopyFromSlice {
    type T;

    fn init_with_copy_from_slice<'out> (
        self: &'out mut Self,
        source_slice: &'_ [Self::T],
    ) -> &'out mut [Self::T]
    ;
}

impl<T : Copy> InitWithCopyFromSlice for [MaybeUninit<T>] {
    type T = T;

    fn init_with_copy_from_slice<'out> (
        self: &'out mut [MaybeUninit<T>],
        source_slice: &'_ [T],
    ) -> &'out mut [T]
    {
        assert_eq!(
            self.len(),
            source_slice.len(),
            "`init_with_copy_from_slice()`: length mismatch",
        );
        unsafe {
            // # Safety
            //
            //   - `&mut` guarantees no overlap;
            //
            //   - `self[.. len]` is valid to write to;
            //
            //   - `source_slice[.. len]` is valid to read (and copy) from.
            ptr::copy_nonoverlapping(
                source_slice.as_ptr(),
                utils::ptr_cast_mut::<MaybeUninit<T>, T>(self.as_mut_ptr()),
                self.len(),
            );
        }
        unsafe {
            // # Safety
            //
            //   - the `copy_nonoverlapping()` call guarantees that the buffer
            //     has been initialized
            <[MaybeUninit<T>]>::assume_init_by_mut(self)
        }
    }
}
