use_prelude!(); cfg_alloc! {

mod private {
    use_prelude!();

    pub trait Sealed : Sized {}
    impl<T> Sealed for Box<::core::mem::MaybeUninit<T>>
    {}
}

/// Extension trait for uninitalized `Box` allocations and
/// the optimized delayed-initialization pattern.
///
/// # Optimized in-place heap initialization
///
/// The `Box::uninit().init(...)` delayed-initialization pattern is suprisingly
/// effective in helping the optimizer inline the creation of the value directly
/// into the heap.
///
///   - In other words, this bundles [`::copyless`](https://docs.rs/copyless)
///     functionality.
///
///   - For those wondering why `Box::new(...)` could not be made as efficient,
///     the answer lies in temporaries: the `...` temporary when calling
///     `Box::new()` is created _before_ attempting the allocation, and given
///     that this allocation can fail / have side-effects, the optimizer is not
///     allowed to reorder the creation of the temporary after the allocation,
///     since it can change the semantics of the code for these corner (but
///     not unreachable) cases. It is hence illegal for the optimizer to inline
///     the creation of `...` directly into the heap.
///
///     Whereas `Box::uninit().init(...)` only creates the temporary after
///     the allocation attempted in `uninit()` has succeeded, at which point
///     it should be trivial for the optimizer to inline its creation directly
///     into the heap.
///
///   - Note, however, that this property cannot be guaranteed from a library
///     perspective; for instance, **the heap-inlined initialization does not
///     seem to happen when the optimization level (`opt-level`) is less than
///     `2`. Inversely, the author has observed that the heap-inlined
///     initialization does seem to kick in when compiling with `-C
///     opt-level=2`** (or `3`), _e.g._, when running on `--release`.
///
///
/// ### Example
///
/// ```rust
/// use ::uninit::prelude::*;
///
/// let ft: Box<u8> = Box::uninit().init(42);
/// assert_eq!(*ft, 42);
/// ```
///
/// This optimization can even allow creating arrays too big to fit in the
/// stack.
///
///   - For instance, the following implementation panics:
///
///     ```rust,should_panic
///     fn alloc_big_boxed_array () -> Box<[u64; 10_000_000]>
///     {
///         // This can panic because of the `[0; 10_000_000]` stack
///         // temporary overflowing the stack.
///         Box::new([0; 10_000_000])
///     }
///     # println!("Address: {:p}", alloc_big_boxed_array());
///     # panic!();
///     ```
///
///   - Whereas the following one does not
///     (doc-tested with `RUSTDOCFLAGS=-Copt-level=2`):
///
///     ```rust
///     # use ::uninit::prelude::*;
///     fn alloc_big_boxed_array () -> Box<[u64; 10_000_000]>
///     {
///         // But this works fine, since there is no stack temporary!
///         Box::uninit().init([0; 10_000_000])
///     }
///     # println!("Address: {:p}", alloc_big_boxed_array());
///     ```
///
/// # Handling allocation failure
///
/// A neat side-effect of this implementation is to expose the intermediate
/// state of `Box::try_alloc()`, which yields an `Option<Box<MaybeUninit<T>>>`
/// depending on whether the attempted allocation succeeded or not.
///
/// ### Example
///
/// ```rust,no_run
/// use ::uninit::prelude::*;
///
/// let buf: Box<[u8; ::core::i32::MAX as _]> = match Box::try_alloc() {
///     | Some(uninit) => uninit.init([0; ::core::i32::MAX as _]),
///     | None => {
///         panic!("Failed to allocate 2GB of memory");
///     }
/// };
/// # let _ = buf;
/// ```
impl<T> BoxUninit for Box<MaybeUninit<T>> {
    type T = T;

    /// Idiomatic allocation-failure unwrapping of [`BoxUninit::try_alloc`]`()`.
    #[inline]
    fn uninit ()
      -> Box<MaybeUninit<T>>
    {
        let layout = alloc::Layout::new::<T>();
        if let Some(it) = Self::try_alloc() { it } else {
            alloc::handle_alloc_error(layout);
        }
    }

    /// Attempts to `Box`-allocate memory for `T`, without initializing it.
    ///
    /// Returns `None` when the allocation fails.
    #[inline]
    fn try_alloc ()
      -> Option<Box<MaybeUninit<T>>>
    {Some({
        if ::core::mem::size_of::<T>() == 0 {
            Self::new(MaybeUninit::uninit())
        } else {
            unsafe {
                // Safety: we have guarded against ZST
                let layout = alloc::Layout::new::<T>();
                Self::from_raw(
                    ptr::NonNull::new(alloc::alloc(layout))?
                        .as_ptr()
                        .cast()

                )
            }
        }
    })}

    /// Safely initialize a `Box::MaybeUninit<T>` by providing a `value: T`
    /// (that can be inlined into the `Box`), and safely return the ergonomic
    /// `Box<T>` witness of that initialization.
    #[inline(always)]
    fn init (mut self: Box<MaybeUninit<T>>, value: T)
      -> Box<T>
    {
        *self = MaybeUninit::new(value);
        unsafe {
            // Safety: `self` has just been initialized.
            Box::from_raw(Box::into_raw(self).cast())
        }
    }
}
/// Extension trait for uninitalized `Box` allocations and
/// the optimized delayed-initialization pattern.
#[allow(missing_docs)]
pub
trait BoxUninit : private::Sealed {
    type T;
    fn uninit ()
      -> Self
    ;
    fn init (self, value: Self::T)
      -> Box<Self::T>
    ;
    fn try_alloc ()
      -> Option<Self>
    ;
}

mod private2 {
    use_prelude!();

    pub trait Sealed {}
    impl<T> Sealed for Box<[::core::mem::MaybeUninit<T>]>
    {}
    impl<T> Sealed for Box<::core::mem::MaybeUninit<T>>
    {}
}

impl<T> BoxAssumeInit for Box<[MaybeUninit<T>]> {
    #[allow(missing_docs)]
    type Ret = [T];


    /// Allows to "`.assume_init()`" a boxed `[MaybeUninit<T>]`.
    ///
    /// # Safety
    ///
    ///   - This has the same safety requirements as
    ///     [`.assume_init()`][`MaybeUninit::assume_init`].
    #[inline]
    unsafe
    fn assume_init (this: Box<[MaybeUninit<T>]>)
      -> Box<[T]>
    {
        let len = this.len();
        let ptr = Box::leak(this).as_mut_ptr();
        Box::from_raw(slice::from_raw_parts_mut(
            ptr.cast(), len,
        ))
    }
}

impl<T> BoxAssumeInit for Box<MaybeUninit<T>> {
    type Ret = T;

    /// Allows to "`.assume_init()`" a boxed `MaybeUninit<T>`.
    ///
    /// # Safety
    ///
    ///   - This has the same safety requirements as
    ///     [`.assume_init()`][`MaybeUninit::assume_init`].
    #[inline]
    unsafe
    fn assume_init (this: Box<MaybeUninit<T>>)
      -> Box<T>
    {
        Box::from_raw(Box::into_raw(this).cast())
    }
}

/// Extension trait to `.assume_init()` through a `Box`.
///
/// This is a compatibility helper trait. For versions of Rust where the
/// `feature(box_uninit)` is unstable, this trait enables the feature in stable
/// Rust. This may trigger an `unstable_name_collisions` lint, but this is fine,
/// since the implementation is the same. You can dismiss that lint with:
///
/// ```rust
/// #![allow(unstable_name_collisions)]
/// ```
#[allow(missing_docs)]
pub
trait BoxAssumeInit : private2::Sealed {
    type Ret : ?Sized;

    unsafe
    fn assume_init (this: Self)
      -> Box<Self::Ret>
    ;
}

} // cfg_alloc!
