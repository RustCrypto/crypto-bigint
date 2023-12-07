use crate::{WideWord, Word};

use super::karatsuba::adc;

/// Schoolbook multiplication
pub(super) fn mul(x: &[Word], y: &[Word], acc: &mut [Word]) {
    for (i, xi) in x.iter().enumerate() {
        mac_digit(&mut acc[i..], y, *xi);
    }
}

fn mac_digit(acc: &mut [Word], b: &[Word], c: Word) {
    if c == 0 {
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
        *a = adc(*a, 0, &mut carry);
    }
}

#[inline]
fn mac_with_carry(a: Word, b: Word, c: Word, acc: &mut WideWord) -> Word {
    *acc += a as WideWord;
    *acc += (b as WideWord) * (c as WideWord);
    let lo = *acc as Word;
    *acc >>= Word::BITS;
    lo
}
