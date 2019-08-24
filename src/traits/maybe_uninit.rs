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
    fn assume_init_by_ref<'__> (self: &'__ Self)
        -> &'__ Self::T
    where
        Self : '__,
        Self::T : '__,
    ;

    /// # Safety
    ///
    ///  - The `Self::T` that `self` points to must be initialized.
    unsafe
    fn assume_init_by_mut<'__> (self: &'__ mut Self)
        -> &'__ mut Self::T
    where
        Self : '__,
        Self::T : '__,
    ;

    fn from_ref<'__> (init_ref: &'__ Self::T)
        -> &'__ Self
    where
        Self : '__,
        Self::T : '__,
    ;

    fn from_mut<'__> (init_mut: &'__ mut Self::T)
        -> &'__ mut Self
    where
        Self : '__,
        Self::T : '__,
    ;
}

#[require_unsafe_in_bodies]
impl<T : Copy> MaybeUninitExt for MaybeUninit<T> {
    type T = T;

    unsafe
    fn assume_init_by_ref<'__> (self: &'__ Self)
        -> &'__ Self::T
    where
        Self : '__,
        Self::T : '__,
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(self)
        }
    }

    unsafe
    fn assume_init_by_mut<'__> (self: &'__ mut Self)
        -> &'__ mut Self::T
    where
        Self : '__,
        Self::T : '__,
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(self)
        }
    }

    fn from_ref<'__> (some_ref: &'__ Self::T)
        -> &'__ Self
    where
        Self : '__,
        Self::T : '__,
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(some_ref)
        }
    }

    fn from_mut<'__> (some_mut_ref: &'__ mut Self::T)
        -> &'__ mut Self
    where
        Self : '__,
        Self::T : '__,
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
    fn assume_init_by_ref<'__> (self: &'__ Self)
        -> &'__ Self::T
    where
        Self : '__,
        Self::T : '__,
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(self)
        }
    }

    unsafe
    fn assume_init_by_mut<'__> (self: &'__ mut Self)
        -> &'__ mut Self::T
    where
        Self : '__,
        Self::T : '__,
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(self)
        }
    }

    fn from_ref<'__> (slice: &'__ Self::T)
        -> &'__ Self
    where
        Self : '__,
        Self::T : '__,
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(slice)
        }
    }

    fn from_mut<'__> (slice: &'__ mut Self::T)
        -> &'__ mut Self
    where
        Self : '__,
        Self::T : '__,
    {
        unsafe {
            // # Safety
            //
            //   - Same memory layout, bounded lifetimes, same mut-ness
            mem::transmute(slice)
        }
    }
}
