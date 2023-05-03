#![no_main]
use libfuzzer_sys::fuzz_target;
use crypto_bigint::{U64, Limb};
use arbitrary::Arbitrary;

#[derive(Arbitrary, Debug)]
pub enum Operation {
    Add, Sub, Mul, Square
}

fuzz_target!(|operations: Vec<(u64, Operation)>| {
    operations.into_iter().fold(U64::ZERO, |acc, (operand, op)| match op {
        Operation::Add => acc.add_mod(&U64::from_u64(operand), &U64::MAX),
        Operation::Sub => acc.sub_mod(&U64::from_u64(operand), &U64::MAX),
        Operation::Mul => acc.mul_mod_special(&U64::from_u64(operand), Limb::MAX),
        Operation::Square => acc.square_wide().0,
    });
});