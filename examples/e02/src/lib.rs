use anodized::arithmetic::int;
use anodized::spec;

#[spec(
    requires: n > 0,
    ensures: *output == 1,
)]
pub fn collatz(mut n: int) -> int {
    while n > 1 {
        n = f(&n);
    }
    n
}

fn f(n: &int) -> int {
    if n % 2 == 0 {
        n / 2
    } else {
        3 * n + 1
    }
}

// Functions on `u8` whose specifications are written with the logical `int` type.
// The operations on `u8` (`x - 1`, `x + y`, ...) are fallible, so they cannot appear inside
// a pure-`bool` spec predicate. Lifting the operands to `int` (mathematical ℤ, total ops)
// makes the predicates expressible while still describing the `u8` function exactly.

#[spec(
    requires: x > 0,
    ensures: int::from(*output) == int::from(x) - int::from(1u8),
)]
pub fn decrement(x: u8) -> u8 {
    x - 1
}

#[spec(
    requires: int::from(x) + int::from(y) <= int::from(255u8),
    ensures: int::from(*output) == int::from(x) + int::from(y),
)]
pub fn add(x: u8, y: u8) -> u8 {
    x + y
}

#[spec(
    requires: int::from(y) <= int::from(x),
    ensures: int::from(*output) == int::from(x) - int::from(y),
)]
pub fn sub(x: u8, y: u8) -> u8 {
    x - y
}
