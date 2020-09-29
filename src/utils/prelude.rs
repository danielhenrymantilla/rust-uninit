//! Internal crate-global `use` imports.

#![allow(unused_imports)]

pub_in_crate! {
    use ::core::{
        convert::{
            TryFrom,
            TryInto,
        },
        hint,
        mem::{self,
            MaybeUninit,
        },
        ptr,
        ops::{
            Not,
        },
        slice,
    };
    #[cfg(feature = "alloc")]
    use ::alloc::{
        alloc,
        boxed::Box,
        string::String,
        vec::Vec,
    };
    #[cfg(feature = "std")]
    use ::std::{
        io,
    };
    use crate::{
        prelude::*,
    };
    #[cfg(feature = "std")]
    use crate::{
        extension_traits::{
            VecExtendFromReader,
        },
        read::{
            ReadIntoUninit,
        },
    };
}
