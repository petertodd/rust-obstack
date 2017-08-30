use std::cell::RefCell;
use std::cmp;
use std::fmt::Write;
use std::fmt;
use std::marker::PhantomData;
use std::mem;
use std::ptr;
use std::slice;

pub struct Ref<'a, T: 'a + ?Sized> {
    ptr: &'a mut T,
}

impl<'a, T: ?Sized> Drop for Ref<'a, T> {
    #[inline(always)]
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(self.ptr);
        }
    }
}


pub const DEFAULT_INITIAL_CAPACITY: usize = 256;

#[derive(Debug)]
struct State {
    tip: Vec<u8>,
    used_slabs: Vec<Vec<u8>>,
}

impl State {
    fn next_capacity(prev_capacity: usize, required: usize, alignment: usize) -> usize {
        cmp::max(prev_capacity + 1, required + alignment)
            .checked_next_power_of_two()
            .expect("Obstack capacity overflow")
    }

    fn new(min_initial_capacity: usize) -> State {
        State {
           tip: Vec::with_capacity(Self::next_capacity(0, min_initial_capacity, 0)),
           used_slabs: Vec::new(),
        }
    }

    unsafe fn alloc_from_new_slab(&mut self, size: usize, alignment: usize) -> *mut u8 {
        let new_tip = Vec::with_capacity(Self::next_capacity(self.tip.capacity(), size, alignment));
        let old_tip = mem::replace(&mut self.tip, new_tip);
        self.used_slabs.push(old_tip);

        self.alloc(size, alignment)
    }

    #[inline]
    unsafe fn alloc(&mut self, size: usize, alignment: usize) -> *mut u8 {
        let start_ptr = self.tip.as_mut_ptr()
                                .offset(self.tip.len() as isize);

        let padding = start_ptr as usize % alignment;

        debug_assert!(padding < alignment);
        debug_assert_eq!(padding, 0);

        let start_ptr = start_ptr.offset(padding as isize);

        let new_used = self.tip.len() + padding + size;

        if new_used <= self.tip.capacity() {
            self.tip.set_len(new_used);
            start_ptr
        } else {
            self.alloc_from_new_slab(size, alignment)
        }
    }
}

#[derive(Debug)]
pub struct Obstack {
    state: RefCell<State>,
}

impl Obstack {
    pub fn with_initial_capacity(n: usize) -> Obstack {
        let n = if n.is_power_of_two() { n } else { n.next_power_of_two() };

        let state = State::new(n);
        Obstack {
            state: RefCell::new(state)
        }
    }

    pub fn new() -> Obstack {
        Self::with_initial_capacity(DEFAULT_INITIAL_CAPACITY-1)
    }


    #[inline]
    pub fn push_copy<'a, T>(&'a self, value: T) -> &'a mut T
        where T: Copy,
    {
        self.push_nodrop(value)
    }

    #[inline]
    pub fn push<'a, T>(&'a self, value: T) -> Ref<'a, T> {
        Ref {
            ptr: self.push_nodrop(value),
        }
    }

    #[inline]
    pub fn push_nodrop<'a, T>(&'a self, value: T) -> &'a mut T
    {
        let ptr = self.alloc(&value) as *mut T;
        unsafe {
            ptr::write(ptr, value);
            &mut *ptr
        }
    }

    #[inline]
    pub fn copy_from_slice<'a, T>(&'a self, src: &[T]) -> &'a mut [T]
        where T: Copy,
    {
        let ptr = self.alloc(src) as *mut T;
        unsafe {
            let dst = slice::from_raw_parts_mut(ptr, src.len());
            dst.copy_from_slice(src);
            dst
        }
    }

    #[inline]
    pub fn alloc<'a, T: ?Sized>(&'a self, value_ref: &T) -> *mut u8 {
        let size = mem::size_of_val(value_ref);
        let alignment = mem::align_of_val(value_ref);

        if size > 0 {
            unsafe {
                self.state.borrow_mut()
                          .alloc(size, alignment)
            }
        } else {
            mem::align_of_val(value_ref) as *mut u8
        }
    }

    /// Return total bytes allocated
    pub fn allocated(&self) -> usize {

        let state = self.state.borrow();

        let mut sum = state.tip.len();
        for slab in &state.used_slabs {
            sum += slab.len();
        }
        sum
    }
}

impl fmt::Display for Obstack {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let state = self.state.borrow();

        write!(f, "Obstack Slabs:\n")?;

        write!(f, "    {:p}: size = {}, used = {}\n",
               state.tip.as_ptr(), state.tip.capacity(), state.tip.len())?;

        for slab in state.used_slabs.iter().rev() {
            write!(f, "    {:p}: size = {}, used = {}\n",
                   slab.as_ptr(), slab.capacity(), slab.len())?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
struct DropWatch<T: fmt::Debug>(T);

impl<T: fmt::Debug> Drop for DropWatch<T> {
    fn drop(&mut self) {
        println!("dropping {:p} {:?}", self, self.0);
    }
}

mod impls;
pub use impls::*;

#[no_mangle]
pub fn test_all_return<'a>(stack: &'a Obstack, i: u64) -> &'a u64 {
    stack.push_copy(i)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        struct Empty([usize;0]);
        use std::ops::Deref;
        println!("{:p}", Box::new(Empty([])).deref());

        let stack = Obstack::new();

        println!("{}", &stack);

        let mut v = Vec::new();
        for i in 0 .. 10 {
            println!("{:?}", stack);
            let orig = DropWatch(i);
            let r = stack.push(orig.clone());
            v.push((r, orig));
        }

        /*for (r, orig) in v {
            assert_eq!(*r, orig);
        }*/

        println!("{:?}", stack);
        println!("{}", stack);
    }
}
