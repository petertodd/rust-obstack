#[macro_use]
extern crate bencher;

extern crate obstack;

use std::mem;
use std::rc::Rc;

use bencher::Bencher;

use obstack::{Obstack, Ref};

const CONS_ITERS: usize = 10000;
const CONS_SUM: usize = 49995000;

fn cons_list_with_box(bench: &mut Bencher) {
    enum BoxCons<T> {
        Nil,
        Cell(T, Box<BoxCons<T>>),
    }

    bench.iter(|| {
        let mut tip = BoxCons::Nil;
        for i in 0 .. CONS_ITERS {
            let old_tip = mem::replace(&mut tip, BoxCons::Nil);
            tip = BoxCons::Cell(i, Box::new(old_tip));
        }

        let mut cur_tip = &tip;
        let mut sum = 0;
        while let BoxCons::Cell(ref v, ref cdr) = *cur_tip {
            sum += *v;
            cur_tip = &*cdr;
        }
        assert_eq!(sum, CONS_SUM);
    })
}

fn cons_list_with_rc(bench: &mut Bencher) {
    enum RcCons<T> {
        Nil,
        Cell(T, Rc<RcCons<T>>),
    }

    bench.iter(|| {
        let mut tip = RcCons::Nil;
        for i in 0 .. CONS_ITERS {
            let old_tip = mem::replace(&mut tip, RcCons::Nil);
            tip = RcCons::Cell(i, Rc::new(old_tip));
        }

        let mut cur_tip = &tip;
        let mut sum = 0;
        while let RcCons::Cell(ref v, ref cdr) = *cur_tip {
            sum += *v;
            cur_tip = &*cdr;
        }
        assert_eq!(sum, CONS_SUM);
    })
}

fn cons_list_with_obstack(bench: &mut Bencher) {
    enum RefCons<'a, T: 'a> {
        Nil,
        Cell(T, Ref<'a, RefCons<'a, T>>),
    }

    bench.iter(|| {
        let stack = Obstack::new();

        let mut tip = RefCons::Nil;
        for i in 0 .. CONS_ITERS {
            let old_tip = mem::replace(&mut tip, RefCons::Nil);
            tip = RefCons::Cell(i, stack.push(old_tip));
        }

        let mut cur_tip = &tip;
        let mut sum = 0;
        while let RefCons::Cell(ref v, ref cdr) = *cur_tip {
            sum += *v;
            cur_tip = &*cdr;
        }
        assert_eq!(sum, CONS_SUM);
    })
}

fn str_cons_list_stack(bench: &mut Bencher) {
    enum RefCons<'a, T: 'a> {
        Nil,
        Cell(T, Ref<'a, RefCons<'a, T>>),
    }

    bench.iter(|| {
        let stack = Obstack::new();

        let mut tip = RefCons::Nil;
        for i in 0 .. CONS_ITERS {
            let s = i.to_string();
            let old_tip = mem::replace(&mut tip, RefCons::Nil);
            tip = RefCons::Cell(s, stack.push(old_tip));
        }
    })
}

fn str_cons_list_box(bench: &mut Bencher) {
    enum BoxCons<T> {
        Nil,
        Cell(T, Box<BoxCons<T>>),
    }

    bench.iter(|| {
        let mut tip = BoxCons::Nil;
        for i in 0 .. CONS_ITERS {
            let s = i.to_string();
            let old_tip = mem::replace(&mut tip, BoxCons::Nil);
            tip = BoxCons::Cell(s, Box::new(old_tip));
        }
    })
}

benchmark_group!(benches,
                 cons_list_with_box,
                 cons_list_with_rc,
                 cons_list_with_obstack,
                 str_cons_list_stack,
                 str_cons_list_box);
benchmark_main!(benches);
