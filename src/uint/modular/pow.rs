use crate::{Concat, Split, UInt, Word};

use super::{Residue, ResidueParams};

impl<MOD: ResidueParams<LIMBS>, const LIMBS: usize, const DLIMBS: usize> Residue<MOD, LIMBS>
where
    UInt<LIMBS>: Concat<Output = UInt<DLIMBS>>,
    UInt<DLIMBS>: Split<Output = UInt<LIMBS>>,
{
    pub fn pow(&self, exponent: &UInt<LIMBS>) -> Residue<MOD, LIMBS> {
        self.pow_specific(exponent, LIMBS * Word::BITS as usize)
    }

    /// Perform modular exponentiation using Montgomery's ladder. `exponent_bits` represents the number of bits to take into account for the exponent. Note that this value is leaked in the time pattern.
    pub fn pow_specific(&self, exponent: &UInt<LIMBS>, exponent_bits: usize) -> Residue<MOD, LIMBS> {
        let mut x1: Residue<MOD, LIMBS> = Residue::ONE;
        let mut x2: Residue<MOD, LIMBS> = *self;

        // Shift the exponent all the way to the left so the leftmost bit is the MSB of the `UInt`
        let mut n: UInt<LIMBS> =
            exponent.shl_vartime((LIMBS * Word::BITS as usize) - exponent_bits);

        for _ in 0..exponent_bits {
            // TODO: Remove one of the squares and instead conditionally select x1 or x2 to square
            // Peel off one bit at a time from the left side
            let (next_n, overflow) = n.shl_1();
            n = next_n;

            let mut product: Residue<MOD, LIMBS> = x1;
            product *= x2;

            let mut square = Residue::ct_select(x1, x2, overflow);
            square.square();

            x1 = Residue::ct_select(square, product, overflow);
            x2 = Residue::ct_select(product, square, overflow);
        }

        x1
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        uint::modular::{Residue, ResidueParams},
        U1024, U64,
    };

    // #[test]
    // fn test_powmod_specific_mini() {
    //     let modulus = U64::from(11u64);
    //     let modulus_params = ResidueParams::new(modulus);

    //     let base = U64::from(3u64);
    //     let base_mod = Residue::new(base);

    //     let exponent = U64::from(7u64);

    //     let res = base_mod.pow_specific(&exponent, 3);

    //     let expected = U64::from(9u64);
    //     assert_eq!(res.retrieve(), expected);
    // }

    // #[test]
    // fn test_powmod_mini() {
    //     let modulus = U64::from(11u64);
    //     let modulus_params = ResidueParams::new(modulus);

    //     let base = U64::from(3u64);
    //     let base_mod = Residue::new(base);

    //     let exponent = U64::from(7u64);

    //     let res = base_mod.pow(&exponent);

    //     let expected = U64::from(9u64);
    //     assert_eq!(res.retrieve(), expected);
    // }

    // #[test]
    // fn test_powmod_small_base() {
    //     let modulus = U1024::from_be_hex("D509E7854ABDC81921F669F1DC6F61359523F3949803E58ED4EA8BC16483DC6F37BFE27A9AC9EEA2969B357ABC5C0EE214BE16A7D4C58FC620D5B5A20AFF001AD198D3155E5799DC4EA76652D64983A7E130B5EACEBAC768D28D589C36EC749C558D0B64E37CD0775C0D0104AE7D98BA23C815185DD43CD8B16292FD94156767");
    //     let modulus_params = ResidueParams::new(modulus);

    //     let base = U1024::from(105u64);
    //     let base_mod = Residue::new(base);

    //     let exponent = U1024::from_be_hex("84385019BF5E0213C46BA7F0B1A9667925F9BD65FC8CE280A728AEF543B7468E7C7AA7297EF67A50F2FF3E1C36DF532F8B83684F211D98FF39B0C3CE6E3E2C86A353DC2E3A34A05139704992F59068BE80BD86FFDA8BEEF98528D12231CD102D24C1C41F778C3618DC9C1AF1ADE2AF3689683B0C05930985BF15D771F4DCCE9B");

    //     let res = base_mod.pow(&exponent);

    //     let expected = U1024::from_be_hex("84FADE244D8A183FD9D209B07312E017F53BBDF4377108EDB4FEAD2AEB1DFF83B6CE604A2DACF49E52574E69055C6E2D30980938CF259421E17AB277C67663712B185C565C97D3200659D83B287C1D8325BFD258C7DBA4BB2766A57C5F2A7EE3FA784A8669C54839F3D29E73215E7939B16E8293524D871D56F67759D553A242");
    //     assert_eq!(res.retrieve(), expected);
    // }

    // #[test]
    // fn test_powmod_small_exponent() {
    //     let modulus = U1024::from_be_hex("D509E7854ABDC81921F669F1DC6F61359523F3949803E58ED4EA8BC16483DC6F37BFE27A9AC9EEA2969B357ABC5C0EE214BE16A7D4C58FC620D5B5A20AFF001AD198D3155E5799DC4EA76652D64983A7E130B5EACEBAC768D28D589C36EC749C558D0B64E37CD0775C0D0104AE7D98BA23C815185DD43CD8B16292FD94156767");
    //     let modulus_params = ResidueParams::new(modulus);

    //     let base = U1024::from_be_hex("84385019BF5E0213C46BA7F0B1A9667925F9BD65FC8CE280A728AEF543B7468E7C7AA7297EF67A50F2FF3E1C36DF532F8B83684F211D98FF39B0C3CE6E3E2C86A353DC2E3A34A05139704992F59068BE80BD86FFDA8BEEF98528D12231CD102D24C1C41F778C3618DC9C1AF1ADE2AF3689683B0C05930985BF15D771F4DCCE9B");
    //     let base_mod = Residue::new(base);

    //     let exponent = U1024::from(105u64);

    //     let res = base_mod.pow(&exponent);

    //     let expected = U1024::from_be_hex("6B717DC3571BEC59C1E370780630280B05F13D9BB69E192DA75EAE2A817B270840881034B0AB9EE6B47382C58424AE00F90B88DFA7DFF7C9417B28E4C9DF170BCDFC4689140E9BA067FDB224831A33E2E18232655D15EA985EC0C8FB774BFA967B734A60DD8FC1F9214B7C262050F269C248F3255D5D1E7BD63626707232FF72");
    //     assert_eq!(res.retrieve(), expected);
    // }
}
