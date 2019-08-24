macro_rules! pub_in_crate {(
    $(
        use $($first:ident)? $(:: $extra:ident)* :: {
            $($tree:tt)*
        };
    )*
) => (
    $(
        pub(in crate)
        use $($first)? $(:: $extra)* :: {
            $($tree)*
        };
    )*
)}

macro_rules! use_prelude {() => (
    pub(in crate) use crate::prelude::*;
)}
