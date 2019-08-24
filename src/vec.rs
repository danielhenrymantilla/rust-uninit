use super::*;

/// Extension trait for [`Vec`], that reserves extra uninitialized memory for
/// it, and **returns a mutable handle on those extra (uninitialized) bytes**.
///
/// # Example
///
/// ```rust
/// # use ::core::mem::MaybeUninit;
/// use ::uninit::VecReserveUninit;
///
/// let mut vec = b"Hello, ".to_vec();
/// const WORLD: &[u8] = b"World!";
/// let uninit_start: *mut u8 = vec.as_mut_ptr().wrapping_add(vec.len());
///
/// let extra: &mut [MaybeUninit<u8>] = vec.reserve_uninit(WORLD.len());
/// assert_eq!(extra.as_mut_ptr() as *mut u8, uninit_start);
/// unsafe {
///     assert_eq!(extra.len(), WORLD.len());
///     ::core::ptr::copy_nonoverlapping(
///         WORLD.as_ptr(),
///         extra.as_mut_ptr() as *mut u8,
///         extra.len(),
///     );
///     vec.set_len(vec.len() + 6);
/// }
/// assert_eq!(
///     vec,
///     b"Hello, World!",
/// );
/// ```
pub
trait VecReserveUninit {
    fn reserve_uninit (self: &'_ mut Self, additional: usize)
        -> &'_ mut [MaybeUninit<u8>]
    ;
}
impl VecReserveUninit for Vec<u8> {
    fn reserve_uninit (self: &'_ mut Self, additional: usize)
        -> &'_ mut [MaybeUninit<u8>]
    {
        self.reserve(additional);
        unsafe {
            // # Safety
            //
            //  1. Vec<T> contract guarantees that after a call to `.reserve(n)`
            //     at least `n` uninitialized elements after the end of the
            //     Vec's current length can be soundly written to.
            //
            //  2. `Vec` also guarantees that `self.len()` does not overflow
            //     `isize`, so neither does `self.len() * 1`
            slice::from_raw_parts_mut( // 1.
                utils::ptr_cast_mut::<u8, MaybeUninit<u8>>(
                    self.as_mut_ptr()
                        .add(self.len()) // 2.
                ),
                additional,
            )
        }
    }
}


/// Extension trait for [`Vec`], that grows the vec by a _bounded_ amount of
/// bytes, obtained when reading from `R`.
///
/// This guarantees that the allocated memory starts uninitialized (before
/// being initialized when read), for maximum performance.
///
/// # Example
///
/// ```rust
/// use ::uninit::VecExtendFromReader;
///
/// let mut reader = &b"World!"[..];
/// let mut vec = b"Greetings, ".to_vec();
/// vec.extend_from_reader(6, &mut reader).unwrap();
/// assert_eq!(
///     vec,
///     b"Greetings, World!",
/// );
/// ```
pub
trait VecExtendFromReader<R : ReadIntoUninit> {
    fn extend_from_reader (
        self: &'_ mut Self,
        count: usize,
        reader: R,
    ) -> io::Result<()>
    ;
}

#[require_unsafe_in_bodies]
impl<R : ReadIntoUninit> VecExtendFromReader<R> for Vec<u8> {
    fn extend_from_reader (
        self: &'_ mut Self,
        count: usize,
        mut reader: R,
    ) -> io::Result<()>
    {
        let buf: &mut [MaybeUninit<u8>] = self.reserve_uninit(count);
        let buf: &mut [u8] = reader.read_into_uninit_exact(buf)?;
        let count: usize = buf.len();
        debug_assert_eq!(
            buf .as_mut_ptr()
            ,
            self.as_mut_ptr()
                .wrapping_add(self.len())
            ,
            "This is a bug and a soundness issue. Please submit an issue ASAP",
        );
        let new_len = self.len().checked_add(count);
        debug_assert!(
            new_len
                .map(|new_len| new_len <= self.capacity())
                .unwrap_or(false)
            ,
            "This is a bug and a soundness issue. Please submit an issue ASAP",
        );
        unsafe {
            // # Safety
            //
            //   - `buf: &mut [u8]` has been a witness of the initialization of
            //     the bytes in the `len .. len + count` range.
            self.set_len(
                new_len
                    .unwrap_or_else(|| hint::unreachable_unchecked())
            );
        }
        Ok(())
    }
}
