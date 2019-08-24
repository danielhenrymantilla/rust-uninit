use super::*;

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
        buf: &'buf mut [MaybeUninit<u8>],
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
    fn read_into_uninit<'buf> (
        self: &'_ mut Self,
        buf: &'buf mut [MaybeUninit<u8>],
    ) -> io::Result<&'buf mut [u8]>
    {
        let count = ::std::cmp::min(buf.len(), self.len());
        let (to_copy, remaining) = self.split_at(count);
        *self = remaining;

        // First check if the amount of bytes we want to read is small:
        // `copy_from_slice` will generally expand to a call to `memcpy`, and
        // for a single byte the overhead is significant.
        if count == 1 {
            buf[0] = MaybeUninit::new(to_copy[0]);
        } else {
            unsafe {
                // # Safety
                //
                // This is an unchecked version of `copy_from_slice`:
                //
                //   - `to_copy[.. count]` is aligned and valid to read from,
                //
                //   - `buf[.. count]` is aligned and valid to write to,
                //
                //   - they cannot overlap given the `&mut` access on `buf`
                ptr::copy_nonoverlapping::<u8>(
                    to_copy
                        .as_ptr()
                    ,
                utils::ptr_cast_mut::<MaybeUninit<u8>, u8>(
                    buf
                        .as_mut_ptr()
                )   ,
                    count,
                );
            }
        }
        Ok(unsafe {
            // # Safety
            //
            //   - `buf[.. count]` has been initialized
            <[MaybeUninit<u8>]>::assume_init_by_mut(&mut buf[.. count])
        })
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
                buf: &'buf mut [MaybeUninit<u8>],
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
        buf: &'buf mut [MaybeUninit<u8>],
    ) -> io::Result<&'buf mut [u8]>
    {
        (**self).read_into_uninit(buf)
    }
}
