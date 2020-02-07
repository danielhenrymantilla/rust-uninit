use crate::*;
use ::core::slice;

/// Extension trait for [`Vec`], allowing a non-`unsafe` API to interact
/// with the backing buffer / allocation.
pub
trait VecAllocation : Sealed {
    type Item;
    fn get_backing_buffer (self: &'_ mut Self)
      -> OutSlice<'_, Self::Item>
    ;
    fn into_backing_buffer (self: Self)
      -> Vec<MaybeUninit<Self::Item>> // ideally this would be a `Box<[]>`, but `Vec` does not guarantee it.
    ;
    fn split_at_extra_capacity (self: &'_ mut Self)
      -> (&'_ mut [Self::Item], &'_ mut [MaybeUninit<Self::Item>])
    ;
    fn reserve_uninit (self: &'_ mut Self, additional: usize)
      -> &'_ mut [MaybeUninit<Self::Item>]
    ;
}

mod private { pub trait Sealed : Sized {} } use private::Sealed;

impl<T> Sealed for Vec<T> {}
impl<T> VecAllocation for Vec<T>
where
    T : Copy, // Opinionated position against accidental memory leaks
{
    type Item = T;

    /// Gets an [`&out` slice][`OutSlice`] (of `self.capacity()` elements) to the backing buffer.
    fn get_backing_buffer (self: &'_ mut Vec<T>)
      -> OutSlice<'_, T>
    {
        let capacity = self.capacity();
        unsafe {
            // # Safety
            //
            //   - `Vec<T>` safety invariant / layout guarantees state that
            //     it owns a `Box<[MaybeUninit<T>]` of length `self.capacity()`
            //     and starting at `self.as_mut_ptr()`.
            slice::from_raw_parts_mut(
                self.as_mut_ptr().cast::<MaybeUninit<T>>(),
                capacity,
            ).as_out::<[Self::Item]>()
        }
    }

    /// Extracts an owned handle to the backing buffer.
    ///
    /// Ideally the return type would be a `Box<[MaybeUninit<T>]>`, but AFAIK,
    /// it is not officially guaranteed that the allocation of a `Vec`
    /// (a `RawVec`) matches the allocation of a boxed slice, even if in their
    /// current implementations they do.
    fn into_backing_buffer (self: Vec<T>)
      -> Vec<MaybeUninit<T>> // ideally this would be a `Box<[]>`, but `Vec` does not guarantee it.
    {
        let mut this = mem::ManuallyDrop::new(self);
        let capacity = this.capacity();
        unsafe {
            // Safety:
            //
            //   - same layout;
            //
            //   - `MaybeUninit<MaybeUninit<_>>` is sound to `.assume_init()`;
            //
            //   - init -> uninit conversion is sound by "covariance of ownership".
            Vec::from_raw_parts(
                this.as_mut_ptr().cast::<MaybeUninit<T>>(),
                capacity,
                capacity,
            )
        }
    }

    /// Splits the `Vec<T>`'s [backing buffer] into two slices of initialized and
    /// unitialized elements.
    ///
    /// Imagine this as doing
    /// `self.get_backing_buffer().split_at_out(self.len())`
    /// while upgrading the first half to `&mut [T]` and the second half to a
    /// `&mut [MaybeUninit<T>]`.
    ///
    /// [backing buffer]: `VecAllocation::get_backing_buffer`
    fn split_at_extra_capacity (self: &'_ mut Vec<T>)
      -> (&'_ mut [T], &'_ mut [MaybeUninit<T>])
    {
        let (ptr, len, cap) = {
            let len = self.len();
            let cap = self.capacity();
            let ptr = self.as_mut_ptr().cast::<MaybeUninit<T>>();
            (ptr, len, cap)
        };
        unsafe {
            // # Safety
            //
            //   - `ptr[.. cap]` can be `&mut`-ed ("backing buffer");
            //
            //   - ptr[.. len] and ptr[len .. cap] do not overlap and thus do
            //     not alias;
            //
            //   - ptr[.. len] is made of initialized elements;
            //
            //   - ptr[len .. cap] is made of uninitialized elements;
            //
            //   - the "optimized indexing" guarantees of `Vec<T>` make the usage
            //     of `.add()` indexing sound (`RawVec<T>` guards against the
            //     `mem::size_of::<T>() * cap > isize::MAX as usize` overflow).
            //
            //   - `cap >= len` is a safety invariant of `Vec<T>`.
            (
                slice::from_raw_parts_mut(
                    ptr.cast::<T>(),
                    len,
                ),
                slice::from_raw_parts_mut(
                    ptr.add(len),
                    cap .checked_sub(len)
                        .unwrap_or_else(|| hint::unreachable_unchecked())
                    ,
                ),
            )
        }
    }

    /// [Reserves][`Vec::reserve`] extra (uninitialized) memory for it,
    /// **returning a mutable handle to those extra (uninitialized) elements**.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use ::core::mem::MaybeUninit;
    /// use ::uninit::prelude::*;
    ///
    /// let mut vec = b"Hello, ".to_vec();
    /// const WORLD: &[u8] = b"World!";
    ///
    /// let extra: &mut [MaybeUninit<u8>] = vec.reserve_uninit(WORLD.len());
    /// extra.as_out::<[u8]>().copy_from_slice(WORLD);
    ///
    /// // `.reserve_uninit()` guarantees the following properties:
    /// assert_eq!(extra.len(), WORLD.len());
    /// let extra_start: *mut u8 = extra.as_mut_ptr().cast();
    /// let uninit_start: *mut u8 = vec.as_mut_ptr().wrapping_add(vec.len());
    /// assert_eq!(extra_start, uninit_start);
    ///
    /// unsafe {
    ///     // # Safety
    ///     //
    ///     //   - `.copy_from_slice()` contract guarantees initialization
    ///     //     of `extra`, which, in turn, from `reserve_uninit`'s contract,
    ///     //     leads to the `vec` extra capacity having been initialized.
    ///     vec.set_len(vec.len() + WORLD.len());
    /// }
    /// assert_eq!(
    ///     vec,
    ///     b"Hello, World!",
    /// );
    /// ```
    fn reserve_uninit (self: &'_ mut Vec<T>, additional: usize)
      -> &'_ mut [MaybeUninit<T>]
    {
        self.reserve(additional);
        let (_, extra) = self.split_at_extra_capacity();
        unsafe {
            // Safety: `Vec<T>` guarantees that `cap >= len + additional` and
            // thus that `cap - len >= additional`.
            extra.get_unchecked_mut(.. additional)
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
/// use ::uninit::read::VecExtendFromReader;
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
        let buf: OutSlice<'_, u8> = self.reserve_uninit(count).into();
        let buf: &mut [u8] = reader.read_into_uninit_exact(buf)?;
        let count: usize = buf.len();
        debug_assert_eq!(
            buf.as_mut_ptr(),
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
