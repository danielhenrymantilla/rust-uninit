#![cfg(miri)]
#![allow(unused)]
#![deny(unused_must_use)]

macro_rules! mk_tests {(
    $(
        $name:ident : $body:block
    ),* $(,)?
) => (
    $(
        #[test]
        fn $name ()
        $body
    )*
)}

mk_tests! {
    readme_0: {
        use ::core::mem::MaybeUninit;
        let mut x = MaybeUninit::<i32>::uninit();
        x = MaybeUninit::new(42);
        assert_eq!(42, unsafe { x.assume_init() });
    },

    readme_1: {
        use ::core::mem::MaybeUninit;
        let mut x = MaybeUninit::<i32>::uninit();

        unsafe {
            x.as_mut_ptr().write(42);
            assert_eq!(x.assume_init(), 42);
        }
    },

    readme_2: {
        use ::core::mem::MaybeUninit;
        use ::uninit::prelude::*;

        let mut x = MaybeUninit::uninit();
        let at_init_x: &i32 = x.as_out().write(42);
        assert_eq!(at_init_x, &42);
    },

    uninit_array: {
        use ::uninit::{prelude::*, read::ReadIntoUninit};

        let mut reader = &b"Hello, World!"[..];
        let mut backing_array = uninit_array![u8; 4]; // : [MaybeUninit<u8>; 4]
        let buf = backing_array.as_out();
        assert_eq!(
            reader.read_into_uninit_exact(buf).unwrap(),
            b"Hell",
        );
    },

    vec_extend_from_reader: {
        use ::uninit::read::VecExtendFromReader;

        let mut reader = &b"World!"[..];
        let mut vec = b"Greetings, ".to_vec();
        vec.extend_from_reader_exact(6, &mut reader).unwrap();
        assert_eq!(
            vec,
            b"Greetings, World!",
        );
    },
}

mod extension_traits {
    mk_tests! {
        as_out: {
            use ::uninit::prelude::*;

            let mut x = 0;
            x.as_out().write(42);

            let mut y = ::core::mem::MaybeUninit::uninit();
            y.as_out().write(42);
            let y = unsafe { y.assume_init() };

            assert_eq!(x, y);
        },

        box_uninit: {
            use ::uninit::prelude::*;

            let ft: Box<u8> = Box::uninit().init(42);
            assert_eq!(*ft, 42);
        },

        manually_drop_mut: {
            use ::uninit::prelude::*;
            use ::core::cell::Cell;

            let mut cell = Cell::new(0);
            cell.manually_drop_mut().as_out().write(Cell::new(42)); // OK
            assert_eq!(cell.get(), 42);
        },

        vec_split_at_extra_cap: {
            use ::uninit::prelude::*;

            fn make_palindrome<T : Copy> (v: &'_ mut Vec<T>)
            {
                let len = v.len();
                v.reserve(len);
                let (xs, extra) = v.split_at_extra_cap();
                for (&x, at_dst) in xs.iter().rev().zip(extra) {
                    at_dst.write(x);
                }
                unsafe {
                    // Safety: the first `len` elements of `extra` have been initialized.
                    v.set_len(2 * len);
                }
            }

            let mut v = vec![1, 2, 3];
            make_palindrome(&mut v);
            assert_eq!(v, [1, 2, 3, 3, 2, 1]);
        },

        vec_reserve_uninit: {
            use ::uninit::prelude::*;

            let mut vec = b"Hello, ".to_vec();
            const WORLD: &[u8] = b"World!";

            let mut extra: Out<'_, [u8]> = vec.reserve_uninit(WORLD.len());
            extra.r().copy_from_slice(WORLD);

            // `.reserve_uninit()` guarantees the following properties:
            assert_eq!(extra.len(), WORLD.len());
            let extra_start: *mut u8 = extra.r().as_mut_ptr().cast();
            let uninit_start: *mut u8 = vec.as_mut_ptr().wrapping_add(vec.len());
            assert_eq!(extra_start, uninit_start);

            unsafe {
                // # Safety
                //
                //   - `.copy_from_slice()` contract guarantees initialization
                //     of `extra`, which, in turn, from `reserve_uninit`'s contract,
                //     leads to the `vec` extra capacity having been initialized.
                vec.set_len(vec.len() + WORLD.len());
            }
            assert_eq!(
                vec,
                b"Hello, World!",
            );
        },
    }
}

mod out_refs {
    mk_tests! {
        get_out: {
            use ::uninit::prelude::*;

            let src: &[u8] = b"Hello, World!";
            // Stack-allocate an uninitialized buffer.
            let mut buf = uninit_array![u8; 256];
            // copy `src` into this stack allocated buffer, effectively initializing it.
            let buf: &mut [u8] =
                // buf[.. src.len()].as_out()
                buf.as_out().get_out(.. src.len()).unwrap()
                    .copy_from_slice(src)
            ;
            assert_eq!(buf, b"Hello, World!");
            buf[7 ..].copy_from_slice(b"Earth!");
            assert_eq!(buf, b"Hello, Earth!");
        },

        copy_from_slice: {
            use ::uninit::prelude::*;

            let mut array = uninit_array![_; 13];
            assert_eq!(
                array.as_out().copy_from_slice(b"Hello, World!"),
                b"Hello, World!",
            );
            // we can thus soundly `assume_init` our array:
            let array = unsafe {
                ::core::mem::transmute::<
                    [MaybeUninit<u8>; 13],
                    [            u8 ; 13],
                >(array)
            };
            assert_eq!(
                array,
                *b"Hello, World!",
            );
        },
    }
}
