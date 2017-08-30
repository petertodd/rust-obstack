use std::mem;

#[derive(Debug)]
pub struct AlignedVec<A>(Vec<A>);

impl<A> AlignedVec<A> {
    /// Convert bytes to #items, rounding up
    pub fn bytes_to_items(n_bytes: usize) -> usize {
        if n_bytes > 0 {
            debug_assert!(mem::size_of::<A>().is_power_of_two());
            ((n_bytes - 1) / mem::size_of::<A>()) + 1
        } else {
            0
        }
    }

    pub fn items_to_bytes(n_items: usize) -> usize {
        n_items * mem::size_of::<A>()
    }

    pub fn with_capacity_bytes(n_bytes: usize) -> AlignedVec<A> {
        AlignedVec(Vec::with_capacity(Self::bytes_to_items(n_bytes)))
    }

    pub fn len_bytes(&self) -> usize {
        Self::items_to_bytes(self.0.len())
    }
    pub fn capacity_bytes(&self) -> usize {
        Self::items_to_bytes(self.0.capacity())
    }
    pub fn len_items(&self) -> usize {
        self.0.len()
    }
    pub unsafe fn set_len_items(&mut self, new_len: usize) {
        self.0.set_len(new_len);
    }
    pub fn capacity_items(&self) -> usize {
        self.0.capacity()
    }
    pub fn as_ptr(&self) -> *const A {
        self.0.as_ptr()
    }
    pub fn as_mut_ptr(&mut self) -> *mut A {
        self.0.as_mut_ptr()
    }
}
