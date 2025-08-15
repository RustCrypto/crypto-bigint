//! Support for computing modular symbols.

use crate::{ConstChoice, Int, Odd, Uint};

impl<const LIMBS: usize> Int<LIMBS> {
    /// Compute the Jacobi symbol `(self|rhs)`.
    ///
    /// For prime `rhs`, this corresponds to the Legendre symbol and
    /// indicates whether `self` is quadratic residue modulo `rhs`.
    pub const fn jacobi_symbol(&self, rhs: &Odd<Uint<LIMBS>>) -> i8 {
        let (abs, sign) = self.abs_sign();
        let jacobi = abs.jacobi_symbol(rhs) as i64;
        // (-self|rhs) = -(self|rhs) iff rhs = 3 mod 4
        let swap = sign.and(ConstChoice::from_word_eq(rhs.as_ref().limbs[0].0 & 3, 3));
        swap.select_i64(jacobi, -jacobi) as i8
    }

    /// Compute the Jacobi symbol `(self|rhs)`.
    ///
    /// For prime `rhs`, this corresponds to the Legendre symbol and
    /// indicates whether `self` is quadratic residue modulo `rhs`.
    ///
    /// This method executes in variable-time for the value of `self`.
    pub const fn jacobi_symbol_vartime(&self, rhs: &Odd<Uint<LIMBS>>) -> i8 {
        let (abs, sign) = self.abs_sign();
        let jacobi = abs.jacobi_symbol(rhs);
        if sign.is_true_vartime() && rhs.as_ref().limbs[0].0 & 3 == 3 {
            -jacobi
        } else {
            jacobi
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{I256, U256};

    #[test]
    fn jacobi_quad_residue() {
        // Two semiprimes with no common factors, and
        // f is quadratic residue modulo g
        let f = I256::from(59i32 * 67);
        let g = U256::from(61u32 * 71).to_odd().unwrap();
        let res = f.jacobi_symbol(&g);
        let res_vartime = f.jacobi_symbol_vartime(&g);
        assert_eq!(res, 1);
        assert_eq!(res, res_vartime);
    }

    #[test]
    fn jacobi_non_quad_residue() {
        // f and g have no common factors, but
        // f is not quadratic residue modulo g
        let f = I256::from(59i32 * 67 + 2);
        let g = U256::from(61u32 * 71).to_odd().unwrap();
        let res = f.jacobi_symbol(&g);
        let res_vartime = f.jacobi_symbol_vartime(&g);
        assert_eq!(res, -1);
        assert_eq!(res, res_vartime);
    }

    #[test]
    fn jacobi_non_coprime() {
        let f = I256::from(4391633i32);
        let g = U256::from(2022161u32).to_odd().unwrap();
        let res = f.jacobi_symbol(&g);
        let res_vartime = f.jacobi_symbol_vartime(&g);
        assert_eq!(res, 0);
        assert_eq!(res, res_vartime);
    }

    #[test]
    fn jacobi_zero() {
        assert_eq!(I256::ZERO.jacobi_symbol(&U256::ONE.to_odd().unwrap()), 1);
    }

    #[test]
    fn jacobi_neg_one() {
        let f = I256::ONE;
        assert_eq!(f.jacobi_symbol(&U256::ONE.to_odd().unwrap()), 1);
        assert_eq!(f.jacobi_symbol(&U256::from(3u8).to_odd().unwrap()), 1);
    }

    #[test]
    fn jacobi_int() {
        // Two semiprimes with no common factors, and
        // f is quadratic residue modulo g
        let f = I256::from(59i32 * 67);
        let g = U256::from(61u32 * 71).to_odd().unwrap();
        let res = f.jacobi_symbol(&g);
        let res_vartime = f.jacobi_symbol_vartime(&g);
        assert_eq!(res, 1);
        assert_eq!(res, res_vartime);

        // let res = f.checked_neg().unwrap().jacobi_symbol(&g);
        // let res_vartime = f.jacobi_symbol_vartime(&g);
        // assert_eq!(res, -1);
        // assert_eq!(res, res_vartime);
    }
}
