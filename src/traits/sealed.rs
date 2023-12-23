//! Sealed traits.

use super::PrecomputeInverter;

/// Obtain a precomputed inverter which applies the given adjustment factor, i.e. for Montgomery form.
pub trait PrecomputeInverterWithAdjuster<Adjuster>: PrecomputeInverter {
    /// Obtain a precomputed inverter for `&self` as the modulus, supplying a custom adjusting parameter (e.g. R^2 for
    /// when computing inversions in Montgomery form).
    fn precompute_inverter_with_adjuster(&self, adjuster: &Adjuster) -> Self::Inverter;
}
