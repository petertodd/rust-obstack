use std::ops;
use std::fmt;

use super::Ref;

impl<'a, T: ?Sized> ops::Deref for Ref<'a, T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &T {
        self.ptr
    }
}

impl<'a, T: ?Sized> ops::DerefMut for Ref<'a, T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        self.ptr
    }
}

impl<'a, T: ?Sized> fmt::Pointer for Ref<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{:p}", self.ptr)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test() {
    }
}
