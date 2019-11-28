//! Internal crate-global `use` imports.

#![allow(unused_imports)]

pub_in_crate! {
    use std::{*,
        convert::{
            TryFrom,
            TryInto,
        },
        mem::MaybeUninit,
        ops::{
            Not,
        },
    };
    use crate::{
        prelude::*,
        extension_traits::{
            VecExtendFromReader,
        },
        read::{
            ReadIntoUninit,
        },
    };
}
