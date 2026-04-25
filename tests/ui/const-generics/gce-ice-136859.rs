#![feature(generic_const_exprs)]

trait If<const COND: bool> {}
impl If<true> for () {}

trait IsZero<const N: u8> {
    type Answer;
}

struct True;
struct False;

impl<const N: u8> IsZero<N> for ()
//~^ ERROR: not all trait items implemented, missing: `Answer`
where (): If<{N == 0}> {
    type Msg = True;
    //~^ ERROR: type `Msg` is not a member of trait `IsZero`
}

trait Foobar<const N: u8> {}

impl<const N: u8> Foobar<N> for ()
where (): IsZero<N, Answer = True> {}

impl<const N: u8> Foobar<{{ N }}> for ()
//~^ ERROR: conflicting implementations of trait `Foobar<_>` for type `()`
//~| ERROR: the const parameter `N` is not constrained by the impl trait, self type, or predicates
where (): IsZero<N, Answer = False> {}

fn main() {}
