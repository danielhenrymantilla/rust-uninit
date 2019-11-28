#[macro_use]
mod macros;

pub(in crate)
mod prelude;

#[inline]
pub(in crate)
fn ptr_cast_mut<T, U> (p: *mut T) -> *mut U
{
    p as _
}
