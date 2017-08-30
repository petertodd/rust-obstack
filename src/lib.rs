#[cfg(test)]
extern crate rand;

use std::cell::UnsafeCell;
use std::cmp;
use std::fmt;
use std::mem;
use std::ptr;
use std::slice;

mod alignedvec;
use alignedvec::AlignedVec;

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
struct State<A> {
    tip: AlignedVec<A>,
    used_slabs: Vec<AlignedVec<A>>,
}

impl<A> State<A> {
    fn next_capacity(prev_capacity: usize, required: usize, alignment: usize) -> usize {
        cmp::max(prev_capacity + 1, required + alignment)
            .next_power_of_two()
    }

    fn new(min_initial_capacity: usize) -> State<A> {
        let capacity = Self::next_capacity(0, min_initial_capacity, 0);
        State {
           tip: AlignedVec::with_capacity_bytes(capacity),
           used_slabs: Vec::new(),
        }
    }

    #[inline(never)]
    unsafe fn alloc_from_new_slab(&mut self, size: usize, alignment: usize) -> *mut A {
        let new_capacity = Self::next_capacity(self.tip.capacity_bytes(),
                                               size, alignment);
        let new_tip = AlignedVec::with_capacity_bytes(new_capacity);
        let old_tip = mem::replace(&mut self.tip, new_tip);
        self.used_slabs.push(old_tip);

        self.alloc(size, alignment)
    }

    #[inline]
    unsafe fn alloc(&mut self, size: usize, alignment: usize) -> *mut A {
        let start_ptr = self.tip.as_mut_ptr()
                                .offset(self.tip.len_items() as isize);

        let padding = start_ptr as usize % alignment;

        debug_assert!(padding < alignment);
        debug_assert_eq!(padding, 0);

        let start_ptr = start_ptr.offset(AlignedVec::<A>::bytes_to_items(padding) as isize);

        let new_used = self.tip.len_items() + padding + AlignedVec::<A>::bytes_to_items(size);

        if new_used <= self.tip.capacity_items() {
            self.tip.set_len_items(new_used);
            start_ptr as *mut A
        } else {
            self.alloc_from_new_slab(size, alignment)
        }
    }
}

#[derive(Debug)]
pub struct Obstack<A = usize> {
    state: UnsafeCell<State<A>>,
}

impl<A> Obstack<A> {
    pub fn with_initial_capacity(n: usize) -> Self {
        let n = if n.is_power_of_two() { n } else { n.next_power_of_two() };

        let state = State::new(n);
        Obstack {
            state: UnsafeCell::new(state)
        }
    }

    pub fn new() -> Self {
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
    pub fn alloc<'a, T: ?Sized>(&'a self, value_ref: &T) -> *mut A {
        let size = mem::size_of_val(value_ref);
        let alignment = mem::align_of_val(value_ref);

        if size > 0 {
            unsafe {
                let state = &mut *self.state.get();
                state.alloc(size, alignment)
            }
        } else {
            mem::align_of_val(value_ref) as *mut A
        }
    }

    /// Return total bytes allocated
    pub fn allocated(&self) -> usize {
        unsafe {
            let state = &*self.state.get();

            let mut sum = state.tip.len_bytes();
            for slab in &state.used_slabs {
                sum += slab.len_bytes();
            }
            sum
        }
    }
}

impl fmt::Display for Obstack {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        unsafe {
            let state = &*self.state.get();

            write!(f, "Obstack Slabs:\n")?;

            write!(f, "    {:p}: size = {}, used = {}\n",
                   state.tip.as_ptr(),
                   state.tip.capacity_bytes(),
                   state.tip.len_bytes())?;

            for slab in state.used_slabs.iter().rev() {
                write!(f, "    {:p}: size = {}, used = {}\n",
                       slab.as_ptr(), slab.capacity_bytes(), slab.len_bytes())?;
            }
            Ok(())
        }
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
pub fn test_all_return<'a>(stack: &'a Obstack, i: u64) -> (&'a u64, &'a u64) {
    (stack.push_copy(i),
     stack.push_copy(i + 0xdeadbeef))
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::cell::Cell;
    use std::ops::{Deref, DerefMut};
    use std::rc::Rc;

    use rand::{Rng, thread_rng};

    #[test]
    fn test_consistency_simple() {
        let stack: Obstack = Obstack::new();

        let mut v = Vec::new();
        for i in 0 .. 10_000 {
            let r: &mut usize = stack.push_copy(i);
            assert_eq!(*r, i);
            v.push((i, r));
        }

        // After filling the stack every value should have it's original value
        for &(ref orig, ref stack_ref) in v.iter() {
            assert_eq!(*orig, **stack_ref);
        }

        // Change every value and make sure what changed was what we expected
        for &mut(_, ref mut stack_ref) in v.iter_mut() {
            **stack_ref = **stack_ref + 42;
        }
        for &(ref orig, ref stack_ref) in v.iter() {
            assert_eq!(*orig + 42, **stack_ref);
        }
    }

    #[test]
    fn test_consistency_multiple_types() {
        let stack: Obstack = Obstack::new();

        #[derive(Debug)]
        enum Multi<'a> {
            Bool((bool, &'a mut bool)),
            U32((u32, &'a mut u32)),
            U64((u64, &'a mut u64)),
            ArrayU8(([u8;5], &'a mut [u8;5])),
            Unit(&'a mut ()),
            UnitRef(Ref<'a, ()>),
            RcBool((Rc<bool>, Ref<'a, Rc<bool>>)),
            BoxU64((u64, Ref<'a, Box<u64>>)),
        }

        fn fill<'a>(stack: &'a Obstack) -> Multi<'a> {
            match thread_rng().next_u32() % 8 {
                0 => {
                    let value = thread_rng().gen();
                    Multi::Bool((value, stack.push_copy(value)))
                },
                1 => {
                    let value = thread_rng().gen();
                    Multi::U32((value, stack.push_copy(value)))
                },
                2 => {
                    let value = thread_rng().gen();
                    Multi::U64((value, stack.push_copy(value)))
                },
                3 => {
                    let value = thread_rng().gen();
                    Multi::ArrayU8((value, stack.push_copy(value)))
                },
                4 => {
                    Multi::Unit(stack.push_copy(()))
                },
                5 => {
                    Multi::UnitRef(stack.push(()))
                },
                6 => {
                    let rc_bool = Rc::new(thread_rng().gen::<bool>());
                    Multi::RcBool((rc_bool.clone(), stack.push(rc_bool)))
                },
                7 => {
                    let i = thread_rng().gen();
                    Multi::BoxU64((i, stack.push(Box::new(i))))
                },
                _ => unreachable!(),
            }
        }

        fn check(entry: &Multi) {
            match *entry {
                Multi::Bool((ref v, ref r))    => assert_eq!(v, *r),
                Multi::U32((ref v, ref r))     => assert_eq!(v, *r),
                Multi::U64((ref v, ref r))     => assert_eq!(v, *r),
                Multi::ArrayU8((ref v, ref r)) => assert_eq!(v, *r),
                Multi::Unit(ref r)             => assert_eq!(&(), r.deref()),
                Multi::UnitRef(ref r)          => assert_eq!(&(), r.deref()),
                Multi::RcBool((ref v, ref r))  => assert!(Rc::ptr_eq(v, r)),
                Multi::BoxU64((ref v, ref r))  => assert_eq!(*v, ***r),
            }
        }

        fn mutate(entry: &mut Multi) {
            match *entry {
                Multi::Bool((ref mut v, ref mut r)) => {
                    let nv = thread_rng().gen();
                    *v = nv;
                    **r = nv;
                },
                Multi::U32((ref mut v, ref mut r)) => {
                    let nv = thread_rng().gen();
                    *v = nv;
                    **r = nv;
                },
                Multi::U64((ref mut v, ref mut r)) => {
                    let nv = thread_rng().gen();
                    *v = nv;
                    **r = nv;
                },
                Multi::ArrayU8((ref mut v, ref mut r)) => {
                    let nv = thread_rng().gen();
                    *v = nv;
                    **r = nv;
                },
                Multi::Unit(ref mut r) => { **r = (); },
                Multi::UnitRef(ref mut r) => { *r.deref_mut() = (); },
                Multi::RcBool(_) => {},
                Multi::BoxU64((ref mut v, ref mut r)) => {
                    let nv = thread_rng().gen();
                    *v = nv;
                    *(r.deref_mut().deref_mut()) = nv;
                },
            }
        }

        let mut v = Vec::new();
        for _ in 0 .. 10_000 {
            let entry = fill(&stack);
            check(&entry);
            v.push(entry);
        }

        for entry_ref in v.iter() {
            check(entry_ref);
        }
        for entry_ref in v.iter_mut() {
            mutate(entry_ref);
        }
        for entry_ref in v.iter() {
            check(entry_ref);
        }
    }

    #[test]
    fn test_ref_drop() {
        let stack: Obstack = Obstack::new();

        struct DropCounter<'a> {
            count_ref: &'a Cell<usize>,
        }

        impl<'a> Drop for DropCounter<'a> {
            fn drop(&mut self) {
                self.count_ref.set(self.count_ref.get() + 1);
            }
        }

        let drop_counts = vec![Cell::new(0); 10000];
        let mut dropcounter_refs = Vec::new();

        for count_ref in drop_counts.iter() {
            assert_eq!(count_ref.get(), 0);

            let drop_counter = DropCounter {
                count_ref: count_ref,
            };

            let r = stack.push(drop_counter);
            if thread_rng().gen() {
                dropcounter_refs.push(r);
                assert_eq!(count_ref.get(), 0);
            } else {
                mem::drop(r);
                assert_eq!(count_ref.get(), 1);
            }
        }

        mem::drop(dropcounter_refs);
        for drop_count in drop_counts.iter() {
            assert_eq!(drop_count.get(), 1);
        }
    }
}
