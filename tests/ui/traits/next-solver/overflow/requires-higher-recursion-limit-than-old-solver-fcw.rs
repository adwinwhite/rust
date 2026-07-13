//@ compile-flags: -Znext-solver
//@ check-pass

#![recursion_limit = "8"]

// The field order matters 😂
#[allow(dead_code)]
struct Foo<T> {
    t: T,
    opt_t: Option<T>,
}

fn require_sync<T: Sync>() {}

fn main() {
    require_sync::<Foo<Foo<Foo<Foo<Foo<Foo<()>>>>>>>();
    //~^ WARN: reached the recursion limit 8 when resolving trait bounds [next_trait_solver_overflow]
    //~| WARN: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
    //~| WARN: reached the recursion limit 8 when resolving trait bounds [next_trait_solver_overflow]
    //~| WARN: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
}
