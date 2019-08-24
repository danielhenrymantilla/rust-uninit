use_prelude!();

/// Extension trait providing tranformations between init and uninit.
///
/// This is currently only implemented for [`Copy`] types, since the
/// semantics when [`drop` glue][`mem::needs_drop`] is involved are less
/// easy to handle correctly (danger of leaking memory).
pub
trait MaybeUninitExt {
    type T : ?Sized;

    /// # Safety
    ///
    ///  - The `Self::T` that `self` points to must be initialized.
    unsafe
    fn assume_init_by_ref (self: &'_ Self)
        -> &'_ Self::T
    ;

    /// # Safety
    ///
    ///  - The `Self::T` that `self` points to must be initialized.
    unsafe
    fn assume_init_by_mut (self: &'_ mut Self)
        -> &'_ mut Self::T
    ;

    fn from_ref (init_ref: &'_ Self::T)
        -> &'_ Self
    ;

    fn from_mut (init_mut: &'_ mut Self::T)
        -> &'_ mut Self
    ;
}

#[require_unsafe_in_bodies]
impl<T : Copy> MaybeUninitExt for MaybeUninit<T> {
    type T = T;

    unsafe
    fn assume_init_by_ref (self: &'_ Self)
        -> &'_ Self::T
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(self)
        }
    }

    unsafe
    fn assume_init_by_mut (self: &'_ mut Self)
        -> &'_ mut Self::T
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(self)
        }
    }

    fn from_ref (some_ref: &'_ Self::T)
        -> &'_ Self
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(some_ref)
        }
    }

    fn from_mut (some_mut_ref: &'_ mut Self::T)
        -> &'_ mut Self
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(some_mut_ref)
        }
    }
}

#[require_unsafe_in_bodies]
impl<T : Copy> MaybeUninitExt for [MaybeUninit<T>] {
    type T = [T];

    unsafe
    fn assume_init_by_ref (self: &'_ Self)
        -> &'_ Self::T
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(self)
        }
    }

    unsafe
    fn assume_init_by_mut (self: &'_ mut Self)
        -> &'_ mut Self::T
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(self)
        }
    }

    fn from_ref (slice: &'_ Self::T)
        -> &'_ Self
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(slice)
        }
    }

    fn from_mut (slice: &'_ mut Self::T)
        -> &'_ mut Self
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(slice)
        }
    }
}
