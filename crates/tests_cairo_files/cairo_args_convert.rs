//! Utility types and macros for converting Rust values into Cairo VM arguments.

use cairo_vm::types::relocatable::{MaybeRelocatable, Relocatable};
use cairo_vm::vm::runners::cairo_runner::CairoArg;
use cairo_vm::Felt252;
use num_bigint::{BigInt, BigUint};

/// A trait for converting values into [`CairoArg`].
///
/// Implemented for primitive integers, [`Felt252`], [`BigUint`], [`BigInt`], [`Relocatable`], and
/// [`MaybeRelocatable`].
pub trait IntoCairoArg {
    fn into_cairo_arg(self) -> CairoArg;
}

impl IntoCairoArg for CairoArg {
    fn into_cairo_arg(self) -> CairoArg {
        self
    }
}

impl IntoCairoArg for MaybeRelocatable {
    fn into_cairo_arg(self) -> CairoArg {
        CairoArg::Single(self)
    }
}

impl IntoCairoArg for Vec<MaybeRelocatable> {
    fn into_cairo_arg(self) -> CairoArg {
        CairoArg::Array(self)
    }
}

impl IntoCairoArg for Relocatable {
    fn into_cairo_arg(self) -> CairoArg {
        CairoArg::Single(MaybeRelocatable::from(self))
    }
}

impl IntoCairoArg for Felt252 {
    fn into_cairo_arg(self) -> CairoArg {
        CairoArg::Single(MaybeRelocatable::from(self))
    }
}

impl IntoCairoArg for BigUint {
    fn into_cairo_arg(self) -> CairoArg {
        CairoArg::Single(MaybeRelocatable::from(Felt252::from(self)))
    }
}

impl IntoCairoArg for BigInt {
    fn into_cairo_arg(self) -> CairoArg {
        CairoArg::Single(MaybeRelocatable::from(Felt252::from(self)))
    }
}

impl<T: IntoCairoArg + Clone> IntoCairoArg for &T {
    fn into_cairo_arg(self) -> CairoArg {
        self.clone().into_cairo_arg()
    }
}

macro_rules! impl_from_for_int {
    ($($t:ty),* $(,)?) => {
        $(
            impl IntoCairoArg for $t {
                fn into_cairo_arg(self) -> CairoArg {
                    CairoArg::Single(
                        MaybeRelocatable::Int(Felt252::from(self))
                    )
                }
            }
        )*
    };
}

impl_from_for_int!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

/// Creates a `Vec<CairoArg>` from a list of expressions.
///
/// Each expression is converted using the [`IntoCairoArg`] trait.
#[macro_export]
macro_rules! cairo_args {
    ($($x:expr),* $(,)?) => {
        vec![$($crate::cairo_args_convert::IntoCairoArg::into_cairo_arg(&$x)),*]
    };
}

/// Adds a `usize` offset to a [`MaybeRelocatable`].
///
/// For integer values, the offset is added to the felt. For relocatable values, the offset is
/// added to the relocatable's offset component.
pub fn add_maybe_relocatable(a: MaybeRelocatable, b: usize) -> MaybeRelocatable {
    match a {
        MaybeRelocatable::Int(felt) => MaybeRelocatable::Int(felt + Felt252::from(b)),
        MaybeRelocatable::RelocatableValue(reloc) => MaybeRelocatable::from((reloc + b).unwrap()),
    }
}
/// Helper to create MaybeRelocatable from i64 (used in assertions).
pub fn mr_from_i64(val: i64) -> MaybeRelocatable {
    MaybeRelocatable::from(Felt252::from(val))
}

/// Helper to create MaybeRelocatable from BigUint (used in assertions).
pub fn mr_from_biguint(val: &BigUint) -> MaybeRelocatable {
    MaybeRelocatable::from(Felt252::from(val.clone()))
}
