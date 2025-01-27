use crypto_bigint::{Limb, Word};
use proptest::prelude::*;

prop_compose! {
    fn limb()(x in any::<Word>()) -> Limb {
        Limb::from(x)
    }
}
proptest! {
    #[test]
    fn carrying_shr_doesnt_panic(limb in limb(), shift in 0..32u32) {
        limb.carrying_shr(shift);
    }

    #[test]
    fn carrying_shr(limb in limb(), shift in 0..32u32) {
        if shift == 0 {
            assert_eq!(limb.carrying_shr(shift), (limb, Limb::ZERO));
        } else {
            assert_eq!(limb.carrying_shr(shift), (limb.shr(shift), limb.shl(Limb::BITS - shift)));
        }
    }
}
