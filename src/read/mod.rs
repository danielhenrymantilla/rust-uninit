//! Read into uninitialized bytes logic.

use_prelude!();

use ::std::io::Read;

/// Trait for a [`Read`](https://doc.rust-lang.org/std/io/trait.Read.html)able
/// type that can output the bytes read into
/// [uninitialised memory][`MaybeUninit`].
///
/// # Safety (to implement) / Guarantees (for users of `impl ReadIntoUninit` types)
///
/// The trait is `unsafe` (to implement) because it **needs to guarantee** to
/// users of generic `R : ReadIntoUninit` code (that may use `unsafe` code
/// relying on it!) that:
///
///   - `if let Ok(init_buf) = self.read_into_uninit(buf)`, then it must be
///     sound to:
///
///     ```rust
///     # macro_rules! ignore {($($t:tt)*) => ()} ignore! {
///     unsafe {
///         buf.get_out_unchecked(.. init_buf.len()).assume_init()
///     }
///     # }
///     ```
///
///   - `if self.read_into_uninit_exact(buf).is_ok()`, then it must be
///     sound to: `buf.assume_init()`.
///
/// # Counterexample
///
/// ```rust,no_run
/// use ::uninit::{prelude::*,
///     read::{auto_impl, ReadIntoUninit},
/// };
///
/// pub
/// struct Evil;
///
/// auto_impl! { #[derived_from(ReadIntoUninit)] impl Read for Evil }
/// unsafe // unsound!
/// impl ReadIntoUninit for Evil {
///     fn read_into_uninit<'buf> (
///         self: &'_ mut Self,
///         buf: Out<'buf, [u8]>,
///     ) -> ::std::io::Result<&'buf mut [u8]>
///     {
///         Ok(Box::leak(vec![0; buf.len()].into_boxed_slice()))
///     }
/// }
/// ```
///
/// Indeed, with such an impl, the following function could cause UB, when
/// instanced with `R = Evil`:
///
/// ```rust
/// use ::uninit::{prelude::*, read::ReadIntoUninit};
///
/// fn read_byte<R> (reader: &'_ mut R)
///   -> ::std::io::Result<u8>
/// where
///     R : ReadIntoUninit,
/// {
///     let mut byte = MaybeUninit::uninit();
///     reader.read_into_uninit_exact(::std::slice::from_mut(&mut byte).as_out())?;
///     Ok(unsafe {
///         // Safety: Guaranteed by `ReadIntoUninit` contract
///         byte.assume_init()
///     })
/// }
/// ```
pub
unsafe // Safety: `.read_into_uninit_exact()` delegates to `.read_into_uninit()`.
trait ReadIntoUninit : Read {
    /// Single attempt to read bytes from `Self` into `buf`.
    ///
    /// On success, it returns the bytes having been read.
    ///
    /// # Guarantees (that `unsafe` code may rely on)
    ///
    ///   - `if let Ok(init_buf) = self.read_into_uninit(buf)`, then it is
    ///     sound to:
    ///
    ///     ```rust
    ///     # macro_rules! ignore {($($t:tt)*) => ()} ignore! {
    ///     unsafe {
    ///         buf.get_out_unchecked(.. init_buf.len()).assume_init()
    ///     }
    ///     # }
    ///     ```
    ///
    /// This is not guaranteed to read `buf.len()` bytes, see the docs of
    /// [`.read()`][`Read::read`] for more information.
    fn read_into_uninit<'buf> (
        self: &'_ mut Self,
        buf: Out<'buf, [u8]>,
    ) -> io::Result<&'buf mut [u8]>
    ;

    /// Attempts to _fill_ `buf` through multiple `.read()` calls if necessary.
    ///
    /// On success, it returns the bytes having been read.
    ///
    /// # Guarantees (that `unsafe` code may rely on)
    ///
    ///   - `if self.read_into_uninit_exact(buf).is_ok()`, then it is
    ///     sound to: `buf.assume_init()`.
    ///
    /// See the docs of [`.read_exact()`][`Read::read_exact`] for more
    /// information.
    fn read_into_uninit_exact<'buf> (
        self: &'_ mut Self,
        mut buf: Out<'buf, [u8]>,
    ) -> io::Result<&'buf mut [u8]>
    {
        {
            let mut buf = buf.reborrow();
            while buf.is_empty().not() {
                match self
                        .read_into_uninit(buf.r())
                        .map(|it| it.len())
                {
                    | Ok(0) => {
                        return Err(io::Error::new(
                            io::ErrorKind::UnexpectedEof,
                            "failed to fill whole buffer",
                        ));
                    },
                    | Ok(n) => {
                        // buf = &mut buf[n ..];
                        buf = buf.get_out(n ..).unwrap();
                    },
                    | Err(ref e)
                        if e.kind() == io::ErrorKind::Interrupted
                    => {},
                    | Err(e) => {
                        return Err(e);
                    },
                }
            }
        }
        Ok(unsafe {
            // # Safety
            //
            //   - this is the "concatenation" of all the "buf[.. n]"
            //     initialisation witnesses.
            buf.assume_all_init()
        })
    }

    /// Chains / concats two `ReadIntoUninit` readers into one.
    #[cfg(feature = "chain")]
    #[cfg_attr(feature = "nightly",
        doc(cfg(feature = "chain")),
    )]
    fn chain<R : ReadIntoUninit> (
        self: Self,
        next: R,
    ) -> chain::Chain<Self, R>
    where
        Self : Sized,
    {
        chain::Chain { first: self, second: next, first_done: false }
    }

}

// Note: since `rustdoc` is currently unable to handle a `#[doc(hidden)]` not
// infecting a `#[doc(inline)] pub use ...`, we get our hands dirty and hide
// the stuff manually ^^'

macro_rules! well_located_public_macro {(
    $(
        #[doc = $doc:expr]
    )*
    pub
    macro_rules! $macro_name:ident {
        $(
            $input:tt => $output:tt
        );+ $(;)?
    }
) => (
    #[cfg(not(feature = "better-docs"))]
    #[doc(hidden)]
    #[macro_export]
    macro_rules! $macro_name {
        $(
            $input => $output;
        )+
    }

    #[cfg(not(feature = "better-docs"))]
    pub use $macro_name;

    $(
        #[doc = $doc]
    )*
    #[cfg(feature = "better-docs")]
    #[rustc_macro_transparency = "semitransparent"]
    pub
    macro $macro_name {
        $(
            $input => $output,
        )+
    }
)}

well_located_public_macro! {
    /// Helper macro to alleviate the code duplication from implementing both
    /// `Read` and `ReadIntoUninit`.
    ///
    /// Once some type `T` implements `ReadIntoUninit`, you can derive `Read` by
    /// doing:
    ///
    /// ```rust
    /// # macro_rules! ignore {($($t:tt)*) => ()} ignore! {
    /// ::uninit::read::auto_impl! {
    ///     #[derived_from(ReadIntoUninit)]
    ///     impl Read for X
    /// }
    /// // and if X is generic, over, for instance, `Generics`
    /// ::uninit::read::auto_impl! {
    ///     #[derived_from(ReadIntoUninit)]
    ///     impl[Generics] Read for X<Generics>
    /// }
    /// # }
    /// ```
    pub
    macro_rules! auto_impl {(
        #[derived_from(ReadIntoUninit)]
        impl $( [$($generics:tt)*] )? Read for $T:ty
        $(
            where
            $($where_clause:tt)*
        )?
    ) => (
        impl$(<$($generics)*>)? $crate::std::io::Read for $T
        where
            $( $($where_clause)* )?
        {
            #[inline]
            fn read (self: &'_ mut Self, buf: &'_ mut [u8])
              -> $crate::std::io::Result<usize>
            {
                <Self as $crate::read::ReadIntoUninit>::read_into_uninit(
                    self,
                    buf.as_out(),
                ).map(|x| x.len())
            }

            #[inline]
            fn read_exact (self: &'_ mut Self, buf: &'_ mut [u8])
              -> $crate::std::io::Result<()>
            {
                <Self as $crate::read::ReadIntoUninit>::read_into_uninit_exact(
                    self,
                    buf.as_out(),
                ).map(drop)
            }
        }
    )}
}

pub use crate::extension_traits::VecExtendFromReader;

mod impls;

#[cfg(feature = "chain")]
#[cfg_attr(feature = "nightly",
    doc(cfg(feature = "chain")),
)]
pub
mod chain {
    #![allow(missing_docs)]
    use super::*;

    #[cfg_attr(feature = "nightly",
        doc(cfg(feature = "chain")),
    )]
    #[derive(Debug)]
    pub
    struct Chain<R1, R2>
    where
        R1 : ReadIntoUninit,
        R2 : ReadIntoUninit,
    {
        pub(in super)
        first: R1,

        pub(in super)
        second: R2,

        pub(in super)
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

    unsafe
    impl<R1, R2> ReadIntoUninit for Chain<R1, R2>
    where
        R1 : ReadIntoUninit,
        R2 : ReadIntoUninit,
    {
        fn read_into_uninit<'buf> (
            self: &'_ mut Self,
            mut buf: Out<'buf, [u8]>,
        )   -> io::Result<&'buf mut [u8]>
        {
            let len = buf.len();
            if len == 0 {
                return Ok(buf.copy_from_slice(&[]));
            }
            if self.first_done.not() {
                let buf_ = self.first.read_into_uninit(buf.r())?;
                if buf_.is_empty() {
                    self.first_done = true;
                } else {
                    return unsafe {
                        // Safety: `buf_` has been a witness of the
                        // initialization of these bytes.
                        let len = buf_.len();
                        let buf = buf.get_out(.. len).unwrap();
                        Ok(buf.assume_all_init())
                    };
                }
            }
            self.second.read_into_uninit(buf)
        }
    }

    super::auto_impl! {
        #[derived_from(ReadIntoUninit)]
        impl[R1, R2] Read for Chain<R1, R2>
        where
            R1 : ReadIntoUninit,
            R2 : ReadIntoUninit,
    }
}
