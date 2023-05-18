cfg_alloc! {
use crate::*;
use ::core::slice;

/// Extension trait for [`Vec`], allowing a non-`unsafe` API to interact
/// with the backing buffer / allocation.
#[allow(missing_docs)]
pub
trait VecCapacity : Sealed {
    type Item;

    /// See <a href="#method.split_at_extra_cap">↓ below ↓</a>.
    fn split_at_extra_cap (self: &'_ mut Self)
      -> (&'_ mut [Self::Item], &'_ mut [MaybeUninit<Self::Item>])
    ;

    /// See <a href="#method.spare_cap">↓ below ↓</a>.
    fn spare_cap (self: &'_ mut Self)
      -> &'_ mut [MaybeUninit<Self::Item>]
    ;

    /// See <a href="#method.reserve_uninit">↓ below ↓</a>.
    fn reserve_uninit (self: &'_ mut Self, additional: usize)
      -> &'_ mut [MaybeUninit<Self::Item>]
    ;

    /// See <a href="#method.get_backing_buffer">↓ below ↓</a>.
    fn get_backing_buffer (self: &'_ mut Self)
      -> Out<'_, [Self::Item]>
    where
        Self::Item : Copy, // Opinionated stance against accidental memory leaks
    ;

    /// See <a href="#method.into_backing_buffer">↓ below ↓</a>.
    fn into_backing_buffer (self: Self)
      -> Box<[MaybeUninit<Self::Item>]>
    where
        Self::Item : Copy, // Opinionated stance against accidental memory leaks
    ;

    /// See <a href="#method.get_backing_buffer_with_leaking_writes">↓ below ↓</a>.
    fn get_backing_buffer_with_leaking_writes (self: &'_ mut Self)
      -> Out<'_, [Self::Item]>
    ;

    /// See <a href="#method.into_backing_buffer_forget_elems">↓ below ↓</a>.
    fn into_backing_buffer_forget_elems (self: Self)
      -> Box<[MaybeUninit<Self::Item>]>
    ;
}

mod private { pub trait Sealed : Sized {} } use private::Sealed;

impl<T> Sealed for Vec<T> {}
impl<T> VecCapacity for Vec<T> {
    #[allow(missing_docs)]
    type Item = T;

    /// Same as `.split_at_extra_cap().1`, but for not invalidating
    /// —_w.r.t._ aliasing / Stacked Borrows— pointers to the initialized area
    /// of this `Vec`:
    ///
    /// ```rust
    /// use ::uninit::prelude::*;
    ///
    /// let mut v = Vec::with_capacity(2); // len = 0 && 2 uninit
    /// v.push(0); // len = 1 && 1 uninit
    /// let at_fst = v.as_mut_ptr();
    /// v.spare_cap()[0] = MaybeUninit::new(27); // len = 1 && 1 init
    /// unsafe {
    ///     v.set_len(2); // len = 2
    ///     *at_fst += 42; // OK, neither `spare_cap()` nor the `len` interactions invalidated this.
    /// }
    /// assert_eq!(v.iter().sum::<i32>(), 42 + 27);
    /// ```
    fn spare_cap (self: &'_ mut Vec<T>)
      -> &'_ mut [MaybeUninit<T>]
    {
        let len = self.len();
        let cap = self.capacity();
        unsafe {
            // Safety:
            //   - The `.add()` is valid per invariants of `Vec`.
            //   - Per `Vec`'s guarantees, the `len.. cap` range of its backing
            //     buffer does contain `cap - len` contiguous `MaybeUninit<T>`s.
            //   - the `.as_mut_ptr()` ptr has RW provenance over the whole
            //     `0.. cap` range, _a fortiori_ over `len.. cap`.
            ::core::slice::from_raw_parts_mut(
                self.as_mut_ptr().add(len).cast::<MaybeUninit<T>>(),
                cap - len,
            )
        }
    }

    /// Splits the `Vec<T>`'s
    /// [backing buffer][`VecCapacity::get_backing_buffer`] into two slices of
    /// initialized and uninitialized elements.
    ///
    /// Imagine this as doing
    /// `self.get_backing_buffer().split_at_out(self.len())`
    /// while upgrading the first half to `&mut [T]`.
    ///
    /// # Guarantees (that `unsafe` code may rely on)
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
    ///         `extra`:
    ///
    ///           - `extra = extra.get_out(.. n).unwrap();`.
    ///
    ///         And given the aformentioned guarantees, one can even:
    ///
    ///           - `extra = extra.get_unchecked_out(.. n);`
    ///
    ///         This last idiom is covered by
    ///         [`.reserve_uninit(n)`][`VecCapacity::reserve_uninit`].
    ///
    ///   - `extra.as_ptr() == v.as_ptr().add(v.len())`.
    ///
    ///   - Thus, only after initializing the first `k` elements of `extra`,
    ///     is it sound to `v.set_len(v.len() + k);`.
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
    ///     for (&x, at_dst) in xs.iter().rev().zip(extra.as_out()) {
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
      -> (&'_ mut [T], &'_ mut [MaybeUninit<T>])
    {
        let len = self.len();
        let backing_buffer = self.get_backing_buffer_with_leaking_writes();
        let (mut xs, extra) = backing_buffer.split_at_out(len);
        (
            unsafe {
                // Safety: the first `len` elements are initialized (safety
                // invariant of `Vec<T>`).
                &mut *xs.as_mut_ptr()
            },
            unsafe {
                // Safety: that part is indeed uninit and garbage can be written
                // to it.
                extra.as_mut_uninit()
            },
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
    /// let mut extra: Out<'_, [u8]> = vec.reserve_uninit(WORLD.len()).as_out();
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
      -> &'_ mut [MaybeUninit<T>]
    {
        self.reserve(additional);
        let extra = self.spare_cap();
        unsafe {
            // Safety: `Vec<T>` guarantees that `cap >= len + additional` and
            // thus that `cap - len >= additional`.
            extra.get_unchecked_mut(.. additional)
        }
    }

    /// Gets an [`&out [T]`][`Out`] slice (of `self.capacity()` elements)
    /// to the backing buffer.
    #[inline]
    fn get_backing_buffer (self: &'_ mut Vec<T>)
      -> Out<'_, [T]>
    where
        T : Copy, // Opinionated stance against accidental memory leaks
    {
        self.get_backing_buffer_with_leaking_writes()
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
    /// use ::std::rc::Rc;
    ///
    /// let rc = Rc::new(());
    /// assert_eq!(Rc::strong_count(&rc), 1);
    /// let mut v = vec![ Some(Rc::clone(&rc)) ];
    /// assert_eq!(Rc::strong_count(&rc), 2);
    /// // This overwrites the `rc` clone  without running any destructor
    /// // whatsoever, hence leaking it.
    /// v   .get_backing_buffer_with_leaking_writes()
    ///     .get_out(0)
    ///     .unwrap()
    ///     .write(None) // the `rc` clone is not freed
    /// ;
    /// assert_eq!(Rc::strong_count(&rc), 2);
    /// assert!(Rc::try_unwrap(rc).is_err());
    /// ```
    ///
    /// # Example
    ///
    /// ```rust
    /// use ::uninit::prelude::*;
    /// use ::std::cell::Cell;
    ///
    /// let mut v = vec![Cell::new(0)];
    /// v   .get_backing_buffer_with_leaking_writes() // No drop glue, so this is fine
    ///     .get_out(0)
    ///     .unwrap()
    ///     .write(Cell::new(42))
    /// ;
    /// assert_eq!(v[0].get(), 42);
    /// ```
    #[inline]
    fn get_backing_buffer_with_leaking_writes (self: &'_ mut Vec<T>)
      -> Out<'_, [T]>
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
            ).as_out()
        }
    }

    /// Extracts an owned handle to the backing buffer.
    #[inline]
    fn into_backing_buffer (self: Vec<T>)
      -> Box<[MaybeUninit<T>]>
    where
        T : Copy, // Opinionated stance against accidental memory leaks
    {
        self.into_backing_buffer_forget_elems()
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
    ///
    /// # Counter-example
    ///
    /// ```rust
    /// use ::uninit::prelude::*;
    /// use ::std::rc::Rc;
    ///
    /// let rc = Rc::new(());
    /// assert_eq!(Rc::strong_count(&rc), 1);
    /// let mut v = vec![ Some(Rc::clone(&rc)) ];
    /// assert_eq!(Rc::strong_count(&rc), 2);
    /// // This leaks the `rc` clone (but not the heap-allocated array containing it)
    /// let _ = v.into_backing_buffer_forget_elems();
    /// assert_eq!(Rc::strong_count(&rc), 2);
    /// assert!(Rc::try_unwrap(rc).is_err());
    /// ```
    ///
    /// # Example
    ///
    /// ```rust
    /// use ::uninit::prelude::*;
    ///
    /// let mut v = vec![String::from("Hello!")];
    /// // Good practice: before calling `.into_backing_buffer_forget_elems()`
    /// // one ought to `.clear()` the `Vec`:
    /// v.clear(); // drops `"Hello!"`
    /// let mut strings_buffer: Box<[MaybeUninit<String>]> =
    ///     v.into_backing_buffer_forget_elems()
    /// ;
    /// strings_buffer[0] = MaybeUninit::new(String::from("Greetings!"));
    /// let strings_buffer: Box<[String]> = unsafe {
    ///     Box::assume_init(strings_buffer)
    /// };
    /// assert_eq!(&*strings_buffer[0], "Greetings!");
    /// // This does free the contained "Greetings!" `String`.
    /// drop(strings_buffer);
    /// ```
    #[inline]
    fn into_backing_buffer_forget_elems (self: Vec<T>)
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

cfg_std! {
/// Extension trait for [`Vec`], that grows the vec by a _bounded_ amount of
/// bytes, obtained when reading from `R`.
///
/// This guarantees that the allocated memory starts uninitialized (before
/// being initialized by the read), for maximum performance.
///
/// # Example
///
/// ```rust
/// use ::uninit::read::VecExtendFromReader;
///
/// let mut reader = &b"World!"[..];
/// let mut vec = b"Greetings, ".to_vec();
/// vec.extend_from_reader_exact(6, &mut reader).unwrap();
/// assert_eq!(
///     vec,
///     b"Greetings, World!",
/// );
/// ```
pub
trait VecExtendFromReader {
    /// Tries to extends the `Vec` with up to `max_count` bytes read from
    /// `reader`.
    fn extend_from_reader<R : ReadIntoUninit> (
        self: &'_ mut Self,
        max_count: usize,
        reader: R,
    ) -> io::Result<usize>
    ;
    /// Tries to extends the `Vec` with exactly `exact_count` bytes read from
    /// `reader`.
    fn extend_from_reader_exact<R : ReadIntoUninit> (
        self: &'_ mut Self,
        exact_count: usize,
        reader: R,
    ) -> io::Result<()>
    ;
}

macro_rules! make_extend {(
    name = $fname:ident,
    count_name = $count_param:ident,
    read_into_buf = |$reader:ident, $buf:ident| $read_into_buf:expr,
    ret_of_count = |$count:ident| -> $Ret:ty { $ret_of_count:expr },
) => (
    #[inline]
    fn $fname<R : ReadIntoUninit> (
        self: &'_ mut Self,
        $count_param: usize,
        mut $reader: R,
    ) -> io::Result<$Ret>
    {
        let $buf: Out<'_, [u8]> = self.reserve_uninit($count_param).as_out();
        let buf: &mut [u8] = $read_into_buf?;
        let $count: usize = buf.len();
        debug_assert_eq!(
            buf.as_mut_ptr(),
            self.as_mut_ptr()
                .wrapping_add(self.len())
            ,
            "This is a bug and a soundness issue. Please submit an issue ASAP",
        );
        let new_len = self.len().checked_add($count);
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
        Ok($ret_of_count)
    }
)}

impl VecExtendFromReader for Vec<u8> {
    make_extend! {
        name = extend_from_reader,
        count_name = max_count,
        read_into_buf = |reader, buf| reader.read_into_uninit(buf),
        ret_of_count = |count| -> usize { count },
    }
    make_extend! {
        name = extend_from_reader_exact,
        count_name = exact_count,
        read_into_buf = |reader, buf| reader.read_into_uninit_exact(buf),
        ret_of_count = |count| -> () { () },
    }
}
} // cfg_std!


} // cfg_alloc!
