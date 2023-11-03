macro_rules! pub_in_crate {(
    $(
        $(#[$meta:meta])*
        use $($first:ident)? $(:: $extra:ident)* :: {
            $($tree:tt)*
        };
    )*
) => (
    $(
        $(#[$meta])*
        pub(in crate)
        use $($first)? $(:: $extra)* :: {
            $($tree)*
        };
    )*
)}

macro_rules! use_prelude {
    () => {
        #[allow(unused_imports)]
        pub(crate) use crate::utils::prelude::*;
    };
}

macro_rules! cfg_std {(
    $($item:item)*
) => (
    $(
        #[cfg(feature = "std")]
        #[cfg_attr(feature = "nightly",
            doc(cfg(feature = "std")),
        )]
        $item
    )*
)}

macro_rules! cfg_alloc {(
    $($item:item)*
) => (
    $(
        #[cfg(feature = "alloc")]
        #[cfg_attr(feature = "nightly",
            doc(cfg(any(feature = "alloc", feature = "std"))),
        )]
        $item
    )*
)}
