use cairo_vm::utils::CAIRO_PRIME;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{One, Zero};
use std::sync::LazyLock;

/// RC_BOUND = 2^128
pub static RC_BOUND: LazyLock<BigUint> = LazyLock::new(|| BigUint::from(2u64).pow(128));

/// MAX_DIV = CAIRO_PRIME // RC_BOUND
pub static MAX_DIV: LazyLock<BigUint> = LazyLock::new(|| CAIRO_PRIME.div_floor(&RC_BOUND));

/// Returns true if `x` is a quadratic residue modulo `prime` (using Euler's criterion).
pub fn is_quad_residue(x: &BigUint, prime: &BigUint) -> bool {
    if x.is_zero() || x.is_one() {
        return true;
    }
    // Euler's criterion: x is QR iff x^((p-1)/2) ≡ 1 (mod p)
    let exp = (prime - BigUint::one()) / 2u32;
    x.modpow(&exp, prime).is_one()
}
/// Computes (b - a) mod CAIRO_PRIME
pub fn sub_mod_prime(a: &BigUint, b: &BigUint) -> BigUint {
    if b >= a {
        (b - a) % &*CAIRO_PRIME
    } else {
        (&*CAIRO_PRIME + b - a) % &*CAIRO_PRIME
    }
}
