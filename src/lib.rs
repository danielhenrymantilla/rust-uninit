#![cfg_attr(feature = "nightly",
    feature(doc_cfg, external_doc),
    doc(include = "../README.md"),
)]
#![cfg_attr(feature = "specialization",
    feature(specialization),
)]
#![cfg_attr(feature = "const_generics",
    feature(const_generics),
)]
#![deny(
    elided_lifetimes_in_paths,
)]

#[macro_use]
extern crate require_unsafe_in_body;

#[macro_use]
mod utils;
pub mod prelude {
    #[doc(no_inline)]
    pub use crate::{
        extension_traits::{
            AsOut,
            BoxUninit,
            ManuallyDropMut,
            VecAllocation,
        },
        out_references::{
            Out,
            OutSlice,
        },
        uninit_array,
    };
    pub use ::core::mem::MaybeUninit;
}

use_prelude!();

pub
mod extension_traits;

pub
mod read;

pub
mod out_references;

#[doc(hidden)]
pub use ::core;

/// Sets up an inline / stack-allocated array of
/// [uninitialized][`MaybeUninit`] elements.
///
/// # Example
///
/// ```rust
/// use ::uninit::{prelude::*, read::ReadIntoUninit};
///
/// let mut reader = &b"Hello, World!"[..];
/// let mut backing_array = uninit_array![u8; 4]; // : [MaybeUninit<u8>; 4]
/// let buf = OutSlice::from(&mut backing_array[..]);
/// assert_eq!(
///     reader.read_into_uninit_exact(buf).unwrap(),
///     b"Hell",
/// );
/// ```
#[macro_export]
macro_rules! uninit_array {(
    $T:ty ; $count:expr
) => ({
    use $crate::core::mem::MaybeUninit;
    const __UNINIT_ARRAY_COUNT__: usize = $count;
    unsafe {
        // # Safety
        //
        //   - `mem::uninitialized::<[MaybeUninit<_>; _]>()` is sound.
        MaybeUninit::<[MaybeUninit<$T>; __UNINIT_ARRAY_COUNT__]>::uninit()
            .assume_init()
    }
})}
