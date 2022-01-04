#![cfg_attr(feature = "better-docs",
    feature(doc_cfg, decl_macro, rustc_attrs),
    cfg_attr(all(), doc = include_str!("../README.md")),
)]
//!
#![cfg_attr(feature = "specialization",
    feature(specialization),
)]

#![allow(unused_attributes)]
#![deny(
    elided_lifetimes_in_paths,
    missing_docs,
    missing_copy_implementations,
    missing_debug_implementations,
    unused_must_use,
)]

#![no_std]

#[doc(hidden)]
pub use ::core;

#[cfg(feature = "alloc")]
#[doc(hidden)] /// Not part of the public API
pub extern crate alloc;

#[cfg(feature = "std")]
#[doc(hidden)] /// Not part of the public API
pub extern crate std;

#[macro_use]
mod utils;
pub mod prelude {
    //! Reexports of pervasive items.
    #[doc(no_inline)]
    pub use crate::{
        extension_traits::{
            AsOut,
            ManuallyDropMut,
        },
        out_ref::{
            Out,
        },
        uninit_array,
    };
    cfg_alloc! {
        #[doc(no_inline)]
        pub use crate::extension_traits::{
            BoxUninit,
            BoxAssumeInit,
            VecCapacity,
        };
    }
    pub use ::core::mem::MaybeUninit;
}

use_prelude!();

pub
mod extension_traits;

#[cfg(feature = "std")]
#[cfg_attr(feature = "nightly",
    doc(cfg(feature = "std")),
)]
pub
mod read;

pub
mod out_ref;

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
/// let buf = backing_array.as_out();
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
