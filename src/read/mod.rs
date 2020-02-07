use_prelude!();

use ::std::io::Read;

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
unsafe // Safety: `.read_into_uninit_exact()` delegates to `.read_into_uninit()`.
trait ReadIntoUninit : Read {
    /// Single attempt to read bytes from `Self` into `buf`.
    ///
    /// On success, it returns the bytes having been read.
    /// **This returned slice is guaranteed to be a prefix slice of `buf`**.
    ///
    /// This is not guaranteed to read `buf.len()` bytes, see the docs of
    /// [`.read()`][`Read::read`] for more information.
    fn read_into_uninit<'buf> (
        self: &'_ mut Self,
        buf: OutSlice<'buf, u8>,
    ) -> io::Result<&'buf mut [u8]>
    ;

    /// Attempts to _fill_ `buf` through multiple `.read()` calls if necessary.
    ///
    /// On success, it returns the bytes having been read.
    /// **This returned slice is guaranteed to be `buf`**.
    ///
    /// See the docs of [`.read_exact()`][`Read::read_exact`] for more
    /// information.
    fn read_into_uninit_exact<'buf> (
        self: &'_ mut Self,
        mut buf: OutSlice<'buf, u8>,
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
            buf.assume_init()
        })
    }

    #[cfg(feature = "chain")]
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
        fn read (self: &'_ mut Self, buf: &'_ mut [u8])
          -> io::Result<usize>
        {
            <Self as ReadIntoUninit>::read_into_uninit(
                self,
                buf.as_out_slice(),
            ).map(|x| x.len())
        }
    }
)}

#[cfg(feature = "specialization")]
#[doc(cfg(feature = "specialization"))]
default
unsafe impl<R : Read> ReadIntoUninit for R {
    default
    fn read_into_uninit<'buf> (
        self: &'_ mut Self,
        buf: OutSlice<'buf, u8>,
    ) -> io::Result<&'buf mut [u8]>
    {
        let buf = buf.fill_with(|_| 0);
        self.read(buf).map(move |n| &mut buf[.. n])
    }

    #[inline]
    default
    fn read_into_uninit_exact<'buf> (
        self: &'_ mut Self,
        buf: OutSlice<'buf, u8>,
    ) -> io::Result<&'buf mut [u8]>
    {
        let buf = buf.fill_with(|_| 0);
        self.read_exact(buf).map(|()| buf)
    }
}

pub use crate::extension_traits::VecExtendFromReader;

mod impls;

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
            mut buf: OutSlice<'buf, u8>,
        )   -> io::Result<&'buf mut [u8]>
        {
            let len = buf.len();
            if len == 0 {
                return Ok(self.copy_from_slice(&[]));
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
                        Ok(buf.assume_init())
                    };
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
