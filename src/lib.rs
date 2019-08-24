#![cfg_attr(feature = "nightly",
    feature(external_doc),
    doc(include = "../README.md"),
)]

#[macro_use]
extern crate require_unsafe_in_body;

#[macro_use]
mod utils;
#[path = "utils/prelude.rs"]
mod prelude;

use_prelude!();

mod impls;

pub use self::traits::{
    MaybeUninitExt,
};
mod traits;

pub use self::vec::{
    VecExtendFromReader,
    VecReserveUninit,
};
mod vec;

#[doc(hidden)]
pub use ::core;

/// Sets up an inline / stack-allocated array of
/// [uninitialized bytes][`MaybeUninit`].
///
/// # Example
///
/// ```rust
/// use ::uninit::{ReadIntoUninit, uninit_byte_array};
///
/// let mut reader = &b"Hello, World!"[..];
/// let mut array = uninit_byte_array![_; 4]; // : [MaybeUninit<u8>; 4]
/// assert_eq!(
///     reader.read_into_uninit_exact(&mut array).unwrap(),
///     b"Hell",
/// );
/// ```
#[macro_export]
macro_rules! uninit_byte_array {(
    _; $count:expr
) => ({
    use $crate::core::mem::MaybeUninit;
    type Array = [MaybeUninit<u8>; $count];
    unsafe {
        // # Safety
        //
        //   - mem::uninitialized::<[MaybeUninit<_>; _]>() is sound.
        MaybeUninit::<Array>::uninit().assume_init()
    }
})}

/// Basically [`AsMut`]`<[`[`MaybeUninit`]`<u8>]>` but with a more explicit
/// name.
pub
trait AsUninitSliceMut {
    fn as_uninit_slice_mut (self: &'_ mut Self)
        -> &'_ mut [MaybeUninit<u8>]
    ;
}

/// Init bytes can be seen as uninit.
impl AsUninitSliceMut for [u8]
{
    #[inline]
    fn as_uninit_slice_mut (self: &'_ mut Self)
        -> &'_ mut [MaybeUninit<u8>]
    {
        <[MaybeUninit<u8>]>::from_mut(self)
    }
}

/// Init bytes can be seen as uninit.
impl AsUninitSliceMut for Vec<u8>
{
    #[inline]
    fn as_uninit_slice_mut (self: &'_ mut Self)
        -> &'_ mut [MaybeUninit<u8>]
    {
        <[MaybeUninit<u8>]>::from_mut(self)
    }
}

/// Identity
impl AsUninitSliceMut for [MaybeUninit<u8>] {
    /// This can be trusted to return the same slice as given in input,
    /// so that initializing the returned slice is guaranteed to have initialized
    /// the input slice.
    #[inline]
    fn as_uninit_slice_mut<'__> (self: &'__ mut [MaybeUninit<u8>])
        -> &'__ mut [MaybeUninit<u8>]
    {
        self
    }
}

#[cfg(not(feature = "downcast_as_ReadIntoUninit"))]
use io::Read;

#[cfg(feature = "downcast_as_ReadIntoUninit")]
// With specialization this can be overriden
impl<R : ?Sized + io::Read> Read for R {
    #[inline]
    // default
    fn downcast_read_uninit (self: &'_ mut Self)
        -> Option<&'_ mut dyn ReadIntoUninit>
    {
        None
    }
}

#[cfg(feature = "downcast_as_ReadIntoUninit")]
pub
trait Read: io::Read {
    #[allow(bad_style)]
    #[inline]
    fn downcast_as_ReadIntoUninit (self: &'_ mut Self)
        -> Option<&'_ mut dyn ReadIntoUninit>
    {
        None
    }

    fn mb_read_into_uninit<'buf> (
        self: &'_ mut Self,
        buf: &'buf mut [MaybeUninit<u8>],
    )   -> io::Result<&'buf mut [u8]>
    {
        if let Some(uninit_reader) = self.downcast_as_ReadIntoUninit() {
            uninit_reader
                .read_into_uninit(buf)
        } else {
            buf.iter_mut().for_each(|at_uninit_byte| {
                *at_uninit_byte = MaybeUninit::new(0);
            });
            let buf: &mut [u8] = unsafe {
                // # Safety
                //
                //   - buf has been initialized
                <[MaybeUninit<u8>]>::assume_init_by_mut(buf)
            };
            let n = self.read(buf)?;
            Ok(&mut buf[.. n])
        }
    }
}

/// Trait for a [`Read`](https://doc.rust-lang.org/std/io/trait.Read.html)able
/// type that can output the bytes read into
/// [uninitialised memory][`MaybeUninit`].
///
/// # Safety
///
/// The trait is marked `unsafe` because it **needs to guarantee** that:
///
///   - `if let Ok(init_buf) = self.read_into_uninit(buf)`, then
///     `init_buf` is a prefix slice of `buf`.
///
///       - this property is equivalent to:
///
///         `init_buf.as_mut_ptr() == buf.as_mut_ptr() as *mut u8` and
///         `init_buf.len() <= buf.len()`
///
///       - as well as:
///
///         **`buf[.. init_buf.len()]` is sound to `assume_init`**
///
/// `unsafe` code can assume this property to skip checks or manual
/// initialization, and that's why incorrectly `impl`-ementing this marker
/// trait can compromise memory safety.
pub
unsafe
trait ReadIntoUninit : Read
{
    /// "Read into uninitialized memory" logic.
    #[inline]
    fn read_into_uninit<'buf> (
        self: &'_ mut Self,
        buf: &'buf mut [MaybeUninit<u8>],
    )   -> io::Result<&'buf mut [u8]>
    ;

    /// "Read into uninitialized memory" logic.
    // # Safety
    //   - delegates to `self.read_into_uninit()` calls.
    #[inline]
    fn read_into_uninit_exact<'buf> (
        self: &'_ mut Self,
        buf: &'buf mut [MaybeUninit<u8>],
    )   -> io::Result<&'buf mut [u8]>
    {
        {
            let mut buf = &mut *buf;
            while buf.is_empty().not() {
                match self.read_into_uninit(buf).map(|x| x.len()) {
                    | Ok(0) => break,
                    | Ok(n) => buf = &mut buf[n ..],
                    | Err(ref e)
                        if e.kind() == io::ErrorKind::Interrupted
                    => {},
                    | Err(e) => return Err(e),
                }
            }
            if buf.is_empty().not() {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "failed to fill whole buffer",
                ));
            }
        }
        Ok(unsafe {
            // # Safety
            //
            //   - this is the "concatenation" of all the "buf[.. n]"
            //     initialisation witnesses.
            <[MaybeUninit<u8>]>::assume_init_by_mut(buf)
        })
    }

    #[cfg(feature = "chain")]
    fn chain <R : ReadIntoUninit> (
        self: Self,
        next: R,
    )   -> Chain<Self, R>
    where
        Self : Sized,
    {
        Chain { first: self, second: next, first_done: false }
    }

}

#[allow(unused_macros)]
macro_rules! auto_impl {(
    #[derived_from(ReadIntoUninit)]
    impl [$($generics:tt)*] io::Read for $T:ty
    where
        $($where_clause:tt)*
) => (
    impl<$($generics)*> io::Read for $T
    where
        $($where_clause)*
    {
        #[inline]
        fn read (
            self: &'_ mut Self,
            buf: &'_ mut [u8],
        )   -> io::Result<usize>
        {
            <Self as ReadIntoUninit>::read_into_uninit(
                self,
                buf.as_uninit_slice_mut(),
            ).map(|x| x.len())
        }
    }
)}

#[cfg(feature = "chain")]
mod chain {
    use super::*;

    #[derive(Debug)]
    pub
    struct Chain<R1, R2>
    where
        R1 : ReadIntoUninit,
        R2 : ReadIntoUninit,
    {
        first: R1,
        second: R2,
        first_done: bool,
    }

    impl<R1, R2> Chain<R1, R2>
    where
        R1 : ReadIntoUninit,
        R2 : ReadIntoUninit,
    {
        pub
        fn into_inner (self: Self)
            -> (R1, R2)
        {
            let Self { first, second, ..} = self;
            (first, second)
        }

        pub
        fn get_ref (self: &'_ Self)
            -> (&'_ R1, &'_ R2)
        {
            let Self { first, second, ..} = self;
            (first, second)
        }
    }

    /// This test verifies the soundness of the lifetime erasure in
    /// `<Chain<_, _> as ReadIntoUninit>::read_into_uninit()`
    #[cfg(all(
        test,
        not(feature = "polonius-check"),
    ))]
    #[test]
    fn check ()
    {
        assert!(
            ::std::process::Command::new("cargo")
                .arg("+nightly")
                .arg("rustc")
                .arg("--features")
                .arg(
                    [
                        "chain",
                        "polonius-check",
                    ].join(" ")
                )
                .arg("--")
                .arg("-Zpolonius")
                .status()
                .unwrap()
                .success()
        );
    }

    unsafe
    impl<R1, R2> ReadIntoUninit for Chain<R1, R2>
    where
        R1 : ReadIntoUninit,
        R2 : ReadIntoUninit,
    {
        fn read_into_uninit<'buf> (
            self: &'_ mut Self,
            buf: &'buf mut [MaybeUninit<u8>],
        )   -> io::Result<&'buf mut [u8]>
        {
            if buf.len() == 0 {
                return Ok(unsafe {
                    // # Safety
                    //
                    //   - since it has `0` elements,
                    //     it does have `0` initialized elements.
                    <[MaybeUninit<u8>]>::assume_init_by_mut(buf)
                })
            }
            if self.first_done.not() {
                #[cfg(not(feature = "polonius-check"))]
                let buf: &mut [MaybeUninit<u8>] = unsafe {
                    // Lifetime hack while waiting for polonius
                    //
                    // # Safety
                    //
                    //   - `cargo rustc --features polonius-check -- -Zpolonius`
                    //     passes.
                    slice::from_raw_parts_mut(
                        buf.as_mut_ptr(),
                        buf.len(),
                    )
                };
                let buf = self.first.read_into_uninit(buf)?;
                if buf.is_empty() {
                    self.first_done = true;
                } else {
                    return Ok(buf);
                }
            }
            self.second.read_into_uninit(buf)
        }
    }

    auto_impl!(
        #[derived_from(ReadIntoUninit)]
        impl[R1, R2] io::Read for Chain<R1, R2>
        where
            R1 : ReadIntoUninit,
            R2 : ReadIntoUninit,
    );
}
