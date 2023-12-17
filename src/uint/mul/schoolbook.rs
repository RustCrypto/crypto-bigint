use num_traits::Zero;

use crate::{uint::add::adc, Limb, WideWord, Word};

/// Schoolbook multiplication
pub(super) fn mul(x: &[Limb], y: &[Limb], acc: &mut [Limb]) {
    for (i, xi) in x.iter().enumerate() {
        mac_digit(&mut acc[i..], y, *xi);
    }
}

fn mac_digit(acc: &mut [Limb], b: &[Limb], c: Limb) {
    if c.is_zero() {
        return;
    }

    let mut carry = 0;
    let (a_lo, a_hi) = acc.split_at_mut(b.len());

    for (a, &b) in a_lo.iter_mut().zip(b) {
        *a = mac_with_carry(*a, b, c, &mut carry);
    }

    let mut a = a_hi.iter_mut();
    while carry != 0 {
        let a = a.next().expect("carry overflow during multiplication!");
        *a = Limb(adc(a.0, 0, &mut carry));
    }
}

#[inline]
fn mac_with_carry(a: Limb, b: Limb, c: Limb, acc: &mut WideWord) -> Limb {
    *acc += a.0 as WideWord;
    *acc += (b.0 as WideWord) * (c.0 as WideWord);
    let lo = *acc as Word;
    *acc >>= Word::BITS;
    Limb(lo)
}
