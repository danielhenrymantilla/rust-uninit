use super::*;

#[cfg(feature = "specialization")]
#[doc(cfg(feature = "specialization"))]
default
unsafe impl<R : Read> ReadIntoUninit for R {
    #[inline]
    default
    fn read_into_uninit<'buf> (
        self: &'_ mut Self,
        buf: Out<'buf, [u8]>,
    ) -> io::Result<&'buf mut [u8]>
    {
        let buf = buf.init_with(::core::iter::repeat(0));
        self.read(buf)
            .map(move |n| &mut buf[.. n])
    }

    #[inline]
    default
    fn read_into_uninit_exact<'buf> (
        self: &'_ mut Self,
        buf: Out<'buf, [u8]>,
    ) -> io::Result<&'buf mut [u8]>
    {
        let buf = buf.init_with(::core::iter::repeat(0));
        self.read_exact(buf)
            .map(|()| buf)
    }
}

// # Safety:
//
//   - basic delegation
//
//   - `read_into_uninit_exact` is not overriden
unsafe
impl<R : ReadIntoUninit + ?Sized> ReadIntoUninit for &'_ mut R {
    #[inline]
    fn read_into_uninit<'buf> (
        self: &'_ mut Self,
        buf: Out<'buf, [u8]>,
    ) -> io::Result<&'buf mut [u8]>
    {
        (**self).read_into_uninit(buf)
    }
}

// # Safety
//
//   - `read_into_uninit` does return a prefix slice on success;
//
//   - `read_into_uninit_exact` is not overriden
unsafe
impl ReadIntoUninit for &'_ [u8] {
    #[inline]
    fn read_into_uninit<'buf> (
        self: &'_ mut Self,
        buf: Out<'buf, [u8]>,
    ) -> io::Result<&'buf mut [u8]>
    {
        let count = ::std::cmp::min(buf.len(), self.len());
        let (to_copy, remaining) = self.split_at(count);
        *self = remaining;

        // Taken from stdlib:
        // "First check if the amount of bytes we want to read is small:
        // `copy_from_slice` will generally expand to a call to `memcpy`, and
        // for a single byte the overhead is significant."
        if count == 1 {
            Ok( slice::from_mut(buf.get_out(0).unwrap().write(to_copy[0])) )
        } else {
            Ok( buf.get_out(.. count).unwrap().copy_from_slice(to_copy) )
        }
    }
}

macro_rules! impl_ReadIntoUninit_for_impl_BufRead {(
    $(
        for [$($generics:tt)*]
            $T:ty
        $(where {
            $($wc:tt)*
        })? ;
    )*
) => (
    $(
        // # Safety:
        //
        //   - delegates to `<&'_ [u8] as ReadIntoUninit>::read_into_uninit`
        //
        //   - `read_into_uninit_exact` is not overriden
        unsafe
        impl<$($generics)*> ReadIntoUninit
            for $T
        $(where
            $($wc)*
        )?
        {
            #[inline]
            fn read_into_uninit<'buf> (
                self: &'_ mut Self,
                buf: Out<'buf, [u8]>,
            ) -> io::Result<&'buf mut [u8]>
            {
                let buf = {
                    let mut read_buf: &[u8] = io::BufRead::fill_buf(self)?;
                    read_buf.read_into_uninit(buf)?
                };
                io::BufRead::consume(self, buf.len());
                Ok(buf)
            }

        }
    )*
)}

impl_ReadIntoUninit_for_impl_BufRead! {
    for [R : io::Read]
        io::BufReader<R>
    ;
    for [T : AsRef<[u8]>]
        io::Cursor<T>
    ;
    for []
        io::Empty
    ;
    for []
        io::StdinLock<'_>
    ;
    for [T : io::BufRead]
        io::Take<T>
    ;
}

// # Safety:
//
//   - basic delegation
//
//   - `read_into_uninit_exact` is not overriden
unsafe
impl<R : ReadIntoUninit + ?Sized> ReadIntoUninit for Box<R> {
    #[inline]
    fn read_into_uninit<'buf> (
        self: &'_ mut Self,
        buf: Out<'buf, [u8]>,
    ) -> io::Result<&'buf mut [u8]>
    {
        (**self).read_into_uninit(buf)
    }
}
