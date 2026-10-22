use crate::rng::{PrivateRng, PublicRng};
use checkct_macros::checkct;
use core::hint::black_box;
use crypto_bigint::{NonZero, U256};

// Generate inputs that previously triggered non-constant-time behavior.
fn inputs() -> (U256, U256, NonZero<U256>) {
    let mut private = PrivateRng::new();
    let mut public = PublicRng::new();
    let mut bytes = [0u8; 32];

    private.fill_bytes(&mut bytes);
    bytes[0] &= 0x7f;
    let a = U256::from_be_slice(&bytes);

    private.fill_bytes(&mut bytes);
    bytes[0] &= 0x7f;
    let b = U256::from_be_slice(&bytes);

    public.fill_bytes(&mut bytes);
    bytes[0] |= 0x80;
    let p = U256::from_be_slice(&bytes).to_nz().unwrap();

    (a, b, p)
}

#[checkct]
pub fn sub_mod_u256() {
    let (a, b, p) = inputs();
    black_box(a.sub_mod(&b, &p));
}
