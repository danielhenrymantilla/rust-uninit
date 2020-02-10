use crate::*;
use ::core::slice;

/// Extension trait for [`Vec`], allowing a non-`unsafe` API to interact
/// with the backing buffer / allocation.
pub
trait VecCapacity : Sealed {
    type Item;

    fn split_at_extra_cap (self: &'_ mut Self)
      -> (&'_ mut [Self::Item], OutSlice<'_, Self::Item>)
    ;
    fn reserve_uninit (self: &'_ mut Self, additional: usize)
      -> OutSlice<'_, Self::Item>
    ;
    fn get_backing_buffer (self: &'_ mut Self)
      -> OutSlice<'_, Self::Item>
    where
        Self::Item : Copy, // Opinionated stance against accidental memory leaks
    ;
    fn into_backing_buffer (self: Self)
      -> Box<[MaybeUninit<Self::Item>]>
    where
        Self::Item : Copy, // Opinionated stance against accidental memory leaks
    ;
    fn get_backing_buffer_manually_drop (self: &'_ mut Self)
      -> OutSlice<'_, Self::Item>
    ;
    fn into_backing_buffer_manually_drop (self: Self)
      -> Box<[MaybeUninit<Self::Item>]>
    ;
}

mod private { pub trait Sealed : Sized {} } use private::Sealed;

impl<T> Sealed for Vec<T> {}
impl<T> VecCapacity for Vec<T> {
    type Item = T;

    /// Splits the `Vec<T>`'s
    /// [backing buffer][`VecCapacity::get_backing_buffer`] into two slices of
    /// initialized and uninitialized elements.
    ///
    /// Imagine this as doing
    /// `self.get_backing_buffer().split_at_out(self.len())`
    /// while upgrading the first half to `&mut [T]` and the second half to a
    /// `&mut [MaybeUninit<T>]`.
    ///
    /// # Guarantees (that `unsafe` code may rely on):
    ///
    /// Given a vector `v`, and `let (xs, extra) = v.split_at_extra_cap()`,
    /// then:
    ///
    ///   - `xs` _is_ `v.as_slice()`, so:
    ///
    ///       - `xs.len() == v.len()`,
    ///
    ///       - `xs.as_ptr() == v.as_ptr()`,
    ///
    ///   - `extra.len() == (v.capacity() - v.len())`;
    ///
    ///       - if `.split_at_extra_cap()` is called right after a call to
    ///         `.reserve(n)`, then `v.capacity() ≥ v.len() + n`, and thus
    ///         **`extra.len() ≥ n`**.
    ///
    ///         For the `extra.len() == n` equality to hold, one must subslice
    ///         `extra`: `extra = &mut extra[.. n];`.
    ///         And given the aformentioned guarantees, one can even:
    ///         `extra = extra.get_mut_unchecked(.. n);`
    ///
    ///         This last idiom is covered by
    ///         [`.reserve_uninit(n)`][`VecCapacity::reserve_uninit`].
    ///
    ///   - `extra.as_ptr().cast() == v.as_ptr().add(v.len())`.
    ///
    ///   - Thus, (only) after initializing the first `k` elements of `extra`,
    ///     it is sound to `v.set_len(v.len() + k);`.
    ///
    /// # Example
    ///
    /// Making a palindrome `Vec`:
    ///
    /// ```rust
    /// use ::uninit::prelude::*;
    ///
    /// fn make_palindrome<T : Copy> (v: &'_ mut Vec<T>)
    /// {
    ///     let len = v.len();
    ///     v.reserve(len);
    ///     let (xs, extra) = v.split_at_extra_cap();
    ///     for (&x, at_dst) in xs.iter().rev().zip(extra) {
    ///         at_dst.write(x);
    ///     }
    ///     unsafe {
    ///         // Safety: the first `len` elements of `extra` have been initialized.
    ///         v.set_len(2 * len);
    ///     }
    /// }
    ///
    /// let mut v = vec![1, 2, 3];
    /// make_palindrome(&mut v);
    /// assert_eq!(v, [1, 2, 3, 3, 2, 1]);
    /// ```
    #[inline]
    fn split_at_extra_cap (self: &'_ mut Vec<T>)
      -> (&'_ mut [T], OutSlice<'_, T>)
    {
        let len = self.len();
        let backing_buffer = self.get_backing_buffer_manually_drop();
        let (mut xs, extra) = backing_buffer.split_at_out(len);
        (
            unsafe {
                // Safety: the first `len` elements are initialized (safety
                // invariant of `Vec<T>`).
                slice::from_raw_parts_mut(xs.as_mut_ptr(), len)
            },
            extra,
        )
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
    /// let mut extra: OutSlice<u8> = vec.reserve_uninit(WORLD.len());
    /// extra.r().copy_from_slice(WORLD);
    ///
    /// // `.reserve_uninit()` guarantees the following properties:
    /// assert_eq!(extra.len(), WORLD.len());
    /// let extra_start: *mut u8 = extra.r().as_mut_ptr().cast();
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
    #[inline]
    fn reserve_uninit (self: &'_ mut Vec<T>, additional: usize)
      -> OutSlice<'_, T>
    {
        self.reserve(additional);
        let (_, extra) = self.split_at_extra_cap();
        unsafe {
            // Safety: `Vec<T>` guarantees that `cap >= len + additional` and
            // thus that `cap - len >= additional`.
            extra.get_out(.. additional)
                 .unwrap_or_else(|| hint::unreachable_unchecked())
        }
    }

    /// Gets an [`&out [T]` slice][`OutSlice`] (of `self.capacity()` elements)
    /// to the backing buffer.
    #[inline]
    fn get_backing_buffer (self: &'_ mut Vec<T>)
      -> OutSlice<'_, T>
    where
        T : Copy, // Opinionated stance against accidental memory leaks
    {
        self.get_backing_buffer_manually_drop()
    }

    /// Same as [`.get_backing_buffer()`][`VecCapacity::get_backing_buffer`]
    /// but without the `Copy` bound.
    ///
    /// This means that extra care should be taken if
    /// `mem::needs_drop::<Self::Item>()`. Indeed, if the `OutSlice` is used to
    /// overwrite initialized elements, then such elements will be destroyed
    /// without their `.drop()` glue / destructors ever being run.
    ///
    /// ⚠️ **Misusage of this function can thus lead to memory leaks** ⚠️
    ///
    /// # Counter-example
    ///
    /// ```rust
    /// use ::uninit::prelude::*;
    ///
    /// let mut v = vec![Some(Box::new(42))];
    /// v   .get_backing_buffer_manually_drop()
    ///     .get_out(0)
    ///     .unwrap()
    ///     .write(None) // the box is not freed despite now being unreachable.
    /// ;
    /// ```
    ///
    /// # Example
    ///
    /// ```rust
    /// use ::uninit::prelude::*;
    /// use ::std::cell::Cell;
    ///
    /// let mut v = vec![Cell::new(0)];
    /// v   .get_backing_buffer_manually_drop() // No drop glue, so this is fine
    ///     .get_out(0)
    ///     .unwrap()
    ///     .write(Cell::new(42))
    /// ;
    /// assert_eq!(v[0].get(), 42);
    /// ```
    #[inline]
    fn get_backing_buffer_manually_drop (self: &'_ mut Vec<T>)
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
            ).as_out::<[T]>()
        }
    }

    /// Extracts an owned handle to the backing buffer.
    #[inline]
    fn into_backing_buffer (self: Vec<T>)
      -> Box<[MaybeUninit<T>]>
    where
        T : Copy, // Opinionated stance against accidental memory leaks
    {
        self.into_backing_buffer_manually_drop()
    }

    /// Same as [`.into_backing_buffer()`][
    /// `VecCapacity::into_backing_buffer`] but without the `Copy` bound.
    ///
    /// This means that extra care should be taken if
    /// `mem::needs_drop::<Self::Item>()`. Indeed, the returned boxed slice
    /// will not run the destructor of its initialized elements (since it no
    /// longer knows which are).
    ///
    /// ⚠️ **Misusage of this function can thus lead to memory leaks** ⚠️
    #[inline]
    fn into_backing_buffer_manually_drop (self: Vec<T>)
      -> Box<[MaybeUninit<T>]>
    {
        // We need to go through an intermediate max-capacity `Vec` because
        // there is no official guarantee that a `Vec`'s backing allocation
        // matches that of a boxed slice.
        let this: Vec<MaybeUninit<T>> = unsafe {
            // Safety:
            //
            //   - same layout;
            //
            //   - `MaybeUninit<MaybeUninit<_>>` is sound to `.assume_init()`;
            //
            //   - init -> uninit conversion is sound by "covariance of ownership".
            let mut this = mem::ManuallyDrop::new(self);
            let capacity = this.capacity();
            Vec::from_raw_parts(
                this.as_mut_ptr().cast::<MaybeUninit<T>>(),
                capacity,
                capacity,
            )
        };
        this.into_boxed_slice() // hopefully a no-op
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

impl<R : ReadIntoUninit> VecExtendFromReader<R> for Vec<u8> {
    #[inline]
    fn extend_from_reader (
        self: &'_ mut Self,
        count: usize,
        mut reader: R,
    ) -> io::Result<()>
    {
        let buf: OutSlice<'_, u8> = self.reserve_uninit(count);
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
                new_len.unwrap_or_else(|| hint::unreachable_unchecked())
            );
        }
        Ok(())
    }
}
