use std::borrow::{Borrow, BorrowMut};
use std::cmp;
use std::convert;
use std::fmt;
use std::ops;

use super::Ref;

impl<'a, T> ops::Deref for Ref<'a, T>
{
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &T {
        self.ptr
    }
}

impl<'a, T> ops::DerefMut for Ref<'a, T>
{
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        self.ptr
    }
}

impl<'a, T> fmt::Pointer for Ref<'a, T>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{:p}", self.ptr)
    }
}

impl<'a, T> fmt::Debug for Ref<'a, T>
    where T: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <T as fmt::Debug>::fmt(self, f)
    }
}
impl<'a, T> fmt::Display for Ref<'a, T>
    where T: fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <T as fmt::Display>::fmt(self, f)
    }
}

impl<'a, T> PartialEq for Ref<'a, T>
    where T: PartialEq<T>
{
    fn eq(&self, other: &Ref<'a, T>) -> bool {
        PartialEq::eq(self.ptr, other.ptr)
    }
    fn ne(&self, other: &Ref<'a, T>) -> bool {
        PartialEq::ne(self.ptr, other.ptr)
    }
}
impl<'a, T> Eq for Ref<'a, T> where T: Eq {}

impl<'a, T> Ord for Ref<'a, T>
    where T: Ord
{
    fn cmp(&self, other: &Ref<'a, T>) -> cmp::Ordering {
        Ord::cmp(self.ptr, other.ptr)
    }
}
impl<'a, T> PartialOrd for Ref<'a, T>
    where T: PartialOrd
{
    fn partial_cmp(&self, other: &Ref<'a, T>) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.ptr, other.ptr)
    }
    fn le(&self, other: &Ref<'a, T>) -> bool {
        PartialOrd::le(self.ptr, other.ptr)
    }
    fn lt(&self, other: &Ref<'a, T>) -> bool {
        PartialOrd::le(self.ptr, other.ptr)
    }
    fn gt(&self, other: &Ref<'a, T>) -> bool {
        PartialOrd::le(self.ptr, other.ptr)
    }
    fn ge(&self, other: &Ref<'a, T>) -> bool {
        PartialOrd::le(self.ptr, other.ptr)
    }
}

impl<'a, T> convert::AsMut<T> for Ref<'a, T>
{
    fn as_mut(&mut self) -> &mut T {
        self.ptr
    }
}
impl<'a, T> convert::AsRef<T> for Ref<'a, T>
{
    fn as_ref(&self) -> &T {
        self.ptr
    }
}

impl<'a, T> Borrow<T> for Ref<'a, T> {
    fn borrow(&self) -> &T {
        self.ptr
    }
}
impl<'a, T> BorrowMut<T> for Ref<'a, T> {
    fn borrow_mut(&mut self) -> &mut T {
        self.ptr
    }
}


#[cfg(test)]
mod tests {
    #[test]
    fn test() {
    }
}
