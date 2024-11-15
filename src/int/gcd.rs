//! Support for computing the greatest common divisor of two [`Int`]s.

use crate::{Int, Odd, PrecomputeInverter, Uint};
use crate::modular::SafeGcdInverter;

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> Int<SAT_LIMBS>
where
    Odd<Uint<SAT_LIMBS>>: PrecomputeInverter<Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>>,
{
    /// Compute the greatest common divisor (`gcd`) of `self` and `rhs`.
    /// Always returns a non-negative value.
    pub const fn gcd(&self, rhs: &Self) -> Uint<SAT_LIMBS> {
        self.abs().gcd(&rhs.abs())
    }
}

impl<const SAT_LIMBS: usize, const UNSAT_LIMBS: usize> Odd<Int<SAT_LIMBS>>
where
    Odd<Uint<SAT_LIMBS>>: PrecomputeInverter<Inverter = SafeGcdInverter<SAT_LIMBS, UNSAT_LIMBS>>,
{
    /// Compute the greatest common divisor (GCD) of this number and another.
    ///
    /// Runs in variable time with respect to `rhs`.
    pub fn gcd_vartime(&self, rhs: &Int<SAT_LIMBS>) -> Uint<SAT_LIMBS> {
        // safe to unwrap; self is odd
        self.abs().to_odd().unwrap().gcd_vartime(&rhs.abs())
    }
}

// TODO: implement Gcd trait. Depends on Integer trait.

#[cfg(test)]
mod tests {
    use crate::{I1024, I128, Int, U1024, U128};

    #[test]
    fn gcd() {
        // Odd GCD
        assert_eq!(I128::from(-77).gcd(&I128::from(14)), U128::from(7u32));
        assert_eq!(I128::from(-77).gcd(&I128::from(-14)), U128::from(7u32));
        assert_eq!(I128::from(77).gcd(&I128::from(14)), U128::from(7u32));
        assert_eq!(I128::from(77).gcd(&I128::from(-14)), U128::from(7u32));

        // Even GCD
        assert_eq!(I128::from(-144).gcd(&I128::from(28)), U128::from(4u32));
        assert_eq!(I128::from(-144).gcd(&I128::from(-28)), U128::from(4u32));
        assert_eq!(I128::from(144).gcd(&I128::from(28)), U128::from(4u32));
        assert_eq!(I128::from(144).gcd(&I128::from(-28)), U128::from(4u32));
    }

    #[test]
    fn gcd_large() {
        // larger values
        let x = I1024::from_be_hex(concat![
        "0084A671979467BD329796EF6B55CC555C4B6DE1DA7425F7DF0175C04164A2F1",
        "D333D2DD4BCD1BE078E0FC9C1616F8532F3A4AB2CA9102B948B7217955344BF3",
        "FBD687F205789E5118FF43B372AE93F131BF6624721518CF73BE04DA1645495B",
        "12DDE8032226F1D02E1939631CC5D0B43AC47212CF819447C05F8899EFD13C80"
        ]);
        let y = I1024::from_be_hex(concat![
        "6FE1503B3DD76A256360BC23041D2D47D47DA27E2474C1CB8ABCBB0617320996",
        "C9319B3DC29FC24F38E2D9B9BE9B48BFB0A7B955B03F784F3DCE963CFD03ED07",
        "C0A89583B00BE7EDDFFC229087CF08DADF838B3A65EE5F85BAE06132B1FED2DA",
        "B3FF12CCB8E0357AEAF95195E59A0D06E0626B894A20DFDC7B1252A5E1ABF000"
        ]).checked_neg().unwrap();
        let target = U1024::from_be_hex(concat![
        "0000000000000000000000000000000000000000000000000000106F3345CEC3",
        "099E40DD1CD11AA51AA63D0351C8B83B200CAC0563F10BA25470C66EDE1E1A98",
        "FFFD0EBC98641BE024071CC9798D213826A24786FF1A2D26E5C819DFBF3E9071",
        "12EA34CE9E40A3AB8D59190A361A1AE6E3D9393211621B27EEFB4D5FD3DF5580"
        ]);

        let res = x.gcd(&y);
        assert_eq!(res, target);

        // divide out factors
        let x_on_gcd = x.checked_div(&Int::new_from_uint(res)).unwrap();
        let y_on_gcd = y.checked_div(&Int::new_from_uint(res)).unwrap();

        assert_eq!(x_on_gcd.gcd(&y_on_gcd), U1024::ONE);
    }

    #[test]
    fn gcd_vartime() {
        let min_77 = I128::from(-77).to_odd().unwrap();
        assert_eq!(min_77.gcd_vartime(&I128::from(21)), U128::from(7u32));
        assert_eq!(min_77.gcd_vartime(&I128::from(-21)), U128::from(7u32));
        let pos_77 = I128::from(77).to_odd().unwrap();
        assert_eq!(pos_77.gcd_vartime(&I128::from(21)), U128::from(7u32));
        assert_eq!(pos_77.gcd_vartime(&I128::from(-21)), U128::from(7u32));
    }
}
