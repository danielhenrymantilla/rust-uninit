use ::core::mem::ManuallyDrop;

#[cfg(doc)] use crate::Out;

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
/// ```rust,compile_fail
/// use ::core::cell::Cell;
/// use ::uninit::prelude::{AsOut, ManuallyDropMut};
///
/// let mut cell = Cell::new(0);
/// cell.as_out::<Cell<_>>().write(Cell::new(42)); // Error, not `Copy`
/// assert_eq!(cell.get(), 42);
/// ```
///
/// ```rust
/// use ::core::cell::Cell;
/// use ::uninit::prelude::{AsOut, ManuallyDropMut};
///
/// let mut cell = Cell::new(0);
/// cell.manually_drop_mut().as_out::<Cell<_>>().write(Cell::new(42)); // OK
/// assert_eq!(cell.get(), 42);
/// ```
pub
trait ManuallyDropMut {
    type Ret : ?Sized;

    fn manually_drop_mut (self: &'_ mut Self)
      -> &'_ mut Self::Ret
    ;
}

impl<T> ManuallyDropMut for [T] {
    type Ret = [ManuallyDrop<T>];

    fn manually_drop_mut<'__> (self: &'__ mut [T])
      -> &'__ mut [ManuallyDrop<T>]
    {
        let len = self.len();
        unsafe {
            // Safety: `ManuallyDrop<T>` is `#[repr(transparent)]`
            ::core::slice::from_raw_parts_mut(
                self.as_mut_ptr().cast(), len,
            )
        }
    }
}

impl<T> ManuallyDropMut for T {
    type Ret = ManuallyDrop<T>;

    fn manually_drop_mut<'__> (self: &'__ mut T)
      -> &'__ mut ManuallyDrop<T>
    {
        unsafe {
            // Safety: `ManuallyDrop<T>` is `#[repr(transparent)]`
            ::core::mem::transmute(self)
        }
    }
}
