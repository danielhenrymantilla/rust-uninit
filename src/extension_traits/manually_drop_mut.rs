use ::core::mem::ManuallyDrop;

#[cfg(doc)]
use crate::Out;

/// Extension trait providing a cast to the [`ManuallyDrop`] type.
///
/// This is useful if you want to use an [`Out`] reference to something that
/// is not `Copy` (potentially because it has drop glue, in which case you
/// either don't mind leaking / skipping that drop glue, or you know you will
/// be manually handling it).
///
/// ⚠️ **Misusage of this function can thus lead to memory leaks** ⚠️
///
/// # Example
///
/// The following fails to compile because of the missing `Copy` bound:
///
/// ```rust,compile_fail
/// use ::uninit::prelude::*;
/// use ::core::cell::Cell;
///
/// let mut cell = Cell::new(0);
/// cell.as_out().write(Cell::new(42)); // Error, not `Copy`
/// assert_eq!(cell.get(), 42);
/// ```
///
/// We see here that the `Copy` bound can be too restrictive. By calling
/// `.manually_drop_mut()`, we no longer need to satisfy this `Copy` bound; but
/// then we need to be careful with memory leaks.
///
/// Since `::core::mem::needs_drop::<Cell<_>>() == false`, there is nothing to
/// worry about:
///
/// ```rust
/// use ::uninit::prelude::*;
/// use ::core::cell::Cell;
///
/// let mut cell = Cell::new(0);
/// cell.manually_drop_mut().as_out().write(Cell::new(42)); // OK
/// assert_eq!(cell.get(), 42);
/// ```
///
/// # Counterexample
///
/// ```rust
/// use ::uninit::prelude::*;
/// use ::std::rc::Rc;
///
/// let rc = Rc::new(());
/// assert_eq!(Rc::strong_count(&rc), 1);
/// let mut rc2 = Some(Rc::clone(&rc));
/// assert_eq!(Rc::strong_count(&rc), 2);
/// // This overwrites `rc2` without running any destructor whatsoever, hence
/// // leaking the `rc` clone.
/// rc2.manually_drop_mut().as_out().write(None);
/// assert_eq!(Rc::strong_count(&rc), 2);
/// assert!(Rc::try_unwrap(rc).is_err());
/// ```
#[allow(missing_docs)]
pub trait ManuallyDropMut {
    type Ret: ?Sized;

    fn manually_drop_mut(self: &'_ mut Self) -> &'_ mut Self::Ret;
}

impl<T> ManuallyDropMut for [T] {
    type Ret = [ManuallyDrop<T>];

    #[inline]
    fn manually_drop_mut<'__>(self: &'__ mut [T]) -> &'__ mut [ManuallyDrop<T>] {
        let len = self.len();
        unsafe {
            // Safety: `ManuallyDrop<T>` is `#[repr(transparent)]`
            ::core::slice::from_raw_parts_mut(self.as_mut_ptr().cast(), len)
        }
    }
}

impl<T> ManuallyDropMut for T {
    type Ret = ManuallyDrop<T>;

    #[inline]
    fn manually_drop_mut<'__>(self: &'__ mut T) -> &'__ mut ManuallyDrop<T> {
        unsafe {
            // Safety: `ManuallyDrop<T>` is `#[repr(transparent)]`
            ::core::mem::transmute(self)
        }
    }
}
