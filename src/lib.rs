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

#[derive(Debug)]
struct Slab<T: ?Sized> {
    prev: Option<Box<Slab<[u8]>>>,
    used: usize,
    buf: T,
}

impl Slab<[u8]> {
    fn new(capacity: usize) -> Box<Slab<[u8]>> {
        assert!(capacity > 0);

        let hdr = Slab {
            prev: None,
            used: 0,
            buf: [0u8;0],
        };

        assert_eq!(mem::align_of_val(&hdr), mem::align_of::<usize>());

        let allocation_size = mem::size_of_val(&hdr) + capacity;
        let v_capacity = ((allocation_size - 1) / mem::size_of::<usize>()) + 1;
        let mut v_usize: Vec<usize> = Vec::with_capacity(v_capacity);
        unsafe {
            v_usize.set_len(v_capacity);
            let p_usize = Box::into_raw(v_usize.into_boxed_slice());
            let dummy_slice = slice::from_raw_parts_mut(p_usize as *mut u8, capacity);
            let ref_self = mem::transmute::<&mut [u8], &mut Slab<[u8]>>(dummy_slice);
            Box::from_raw(ref_self)
        }
    }

    fn walk<F>(&self, mut f: F)
        where F: FnMut(&Slab<[u8]>)
    {
        f(self);
        if let Some(ref prev) = self.prev {
            prev.walk(f)
        }
    }
}

#[derive(Debug)]
struct State {
    tip: Box<Slab<[u8]>>,
}

impl State {
    fn new(initial_capacity: usize) -> State {
        State {
            tip: Slab::new(initial_capacity),
        }
    }

    fn alloc_from_new_slab(&mut self, size: usize, alignment: usize) -> *mut u8 {
        let next_capacity = cmp::max(self.tip.buf.len() + 1, size)
                            .next_power_of_two();

        let mut new_tip = Slab::new(next_capacity);

        unsafe {
            let old_tip = mem::replace(&mut self.tip, mem::uninitialized());
            assert!(new_tip.prev.is_none());
            new_tip.prev = Some(old_tip);
            mem::forget(mem::replace(&mut self.tip, new_tip));
        }
        self.alloc(size, alignment)
    }

    #[inline]
    fn alloc(&mut self, size: usize, alignment: usize) -> *mut u8 {
        let used = self.tip.used;
        let padding = used % alignment;
        let new_used = used + padding + size;

        if new_used <= self.tip.buf.len() {
            let r = self.tip.buf[used .. ].as_mut_ptr();
            self.tip.used = new_used;
            r
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
        Self::with_initial_capacity(128)
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
            self.state.borrow_mut()
                      .alloc(size, alignment)
        } else {
            mem::align_of_val(value_ref) as *mut u8
        }
    }

    /// Return total bytes allocated
    pub fn allocated(&self) -> usize {
        let mut sum = 0;

        let state = self.state.borrow();

        state.tip.walk(|slab| {
            sum += slab.used;
        });

        sum
    }
}

impl fmt::Display for Obstack {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let state = self.state.borrow();
        let mut idx = 0;
        let mut r = String::new();

        write!(f, "Obstack Slabs:\n")?;
        state.tip.walk(|slab| {
            write!(&mut r, "    {:p}: size = {}, used = {}\n", slab, slab.buf.len(), slab.used).unwrap();
            idx += 1;
        });
        write!(f, "{}", r)
    }
}

#[derive(Debug, Clone)]
struct DropWatch<T: fmt::Debug>(T);

impl<T: fmt::Debug> Drop for DropWatch<T> {
    fn drop(&mut self) {
        println!("dropping {:?}", self.0);
    }
}

mod impls;
pub use impls::*;

#[no_mangle]
pub fn test_all_return(i: u64) -> Obstack {
    let stack = Obstack::new();

    for i in 0 .. 10 {
        let orig = DropWatch(i);
        let r = stack.push(orig.clone());
    }
    stack
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
        for i in 0 .. 500 {
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
