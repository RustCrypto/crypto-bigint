#![no_main]
use libfuzzer_sys::fuzz_target;
use crypto_bigint::{U256, Limb};
use arbitrary::Arbitrary;

#[derive(Arbitrary, Debug)]
pub enum Operation {
    Add, Sub, Mul, Square
}

fuzz_target!(|operations: Vec<(u64, Operation)>| {
    operations.into_iter().fold(U256::ZERO, |acc, (operand, op)| match op {
        Operation::Add => acc.add_mod(&U256::from_u64(operand), &U256::MAX),
        Operation::Sub => acc.sub_mod(&U256::from_u64(operand), &U256::MAX),
        Operation::Mul => acc.mul_mod_special(&U256::from_u64(operand), Limb::MAX),
        Operation::Square => acc.square_wide().0,
    });
});