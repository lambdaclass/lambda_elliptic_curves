/// Poseidon implementation for curve BLS12381
use self::parameters::Parameters;

use lambdaworks_math::{
    elliptic_curve::short_weierstrass::curves::bls12_381::field_extension::BLS12381PrimeField,
    field::{element::FieldElement, traits::IsField},
};
use std::ops::{Add, Mul};

use super::traits::IsCryptoHash;

mod parameters;

pub struct Poseidon<F: IsField> {
    params: Parameters<F>,
}

impl IsCryptoHash<BLS12381PrimeField> for Poseidon<BLS12381PrimeField> {
    fn hash_one(
        &self,
        input: FieldElement<BLS12381PrimeField>,
    ) -> FieldElement<BLS12381PrimeField> {
        // return first element of the state (unwraps to be removed after trait changes to return Result<>)
        self.hash(&[input]).unwrap().first().unwrap().clone()
    }

    fn hash_two(
        &self,
        left: FieldElement<BLS12381PrimeField>,
        right: FieldElement<BLS12381PrimeField>,
    ) -> FieldElement<BLS12381PrimeField> {
        // return first element of the state (unwraps to be removed after trait changes to return Result<>)
        self.hash(&[left, right]).unwrap().first().unwrap().clone()
    }

    fn new() -> Self {
        Poseidon {
            params: Parameters::with_t2()
                .expect("Error loading parameters for Posedon BLS12381 hasher"),
        }
    }
}

impl<F> Poseidon<F>
where
    F: IsField,
{
    pub fn new_with_params(params: Parameters<F>) -> Self {
        Poseidon { params }
    }

    pub fn ark(&self, state: &mut [FieldElement<F>], round_number: usize) {
        let state_size = state.len();
        for (i, state) in state.iter_mut().enumerate() {
            *state += self.params.round_constants[round_number * state_size + i].clone();
        }
    }

    pub fn sbox(&self, state: &mut [FieldElement<F>], round_number: usize) {
        let is_full_round = round_number < self.params.n_full_rounds / 2
            || round_number >= self.params.n_full_rounds / 2 + self.params.n_partial_rounds;

        if is_full_round {
            // full s-box
            for current_state in state.iter_mut() {
                *current_state = current_state.pow(self.params.alpha);
            }
        } else {
            // partial s-box
            let last_state_index = state.len() - 1;
            state[last_state_index] = state[last_state_index].pow(self.params.alpha);
        }
    }

    pub fn mix(&self, state: &mut [FieldElement<F>]) {
        let mut new_state: Vec<FieldElement<F>> = Vec::with_capacity(state.len());
        for i in 0..state.len() {
            new_state.push(FieldElement::zero());
            for (j, current_state) in state.iter().enumerate() {
                let mut mij = self.params.mds_matrix[i][j].clone();
                mij = mij.mul(current_state);
                new_state[i] = new_state[i].clone().add(&mij);
            }
        }
        state.clone_from_slice(&new_state[0..state.len()]);
    }

    fn permute(&self, state: &mut [FieldElement<F>]) {
        for i in 0..(self.params.n_full_rounds + self.params.n_partial_rounds) {
            self.ark(state, i);
            self.sbox(state, i);
            self.mix(state);
        }
    }

    fn ensure_permuted(&self, state: &mut [FieldElement<F>], offset: &mut usize) {
        // offset should be <= rate, so really testing for equality
        if *offset >= self.params.rate {
            self.permute(state);
            *offset = 0;
        }
    }

    fn hash(&self, inputs: &[FieldElement<F>]) -> Result<Vec<FieldElement<F>>, String>
    where
        F: IsField,
    {
        let t = self.params.rate + self.params.capacity;
        if inputs.is_empty() || inputs.len() >= self.params.n_partial_rounds - 1 {
            return Err("Wrong input length".to_string());
        }

        let mut state = vec![FieldElement::zero(); t];
        let mut offset: usize = 0;

        let n_remaining = inputs.len() % self.params.rate;
        if n_remaining != 0 {
            return Err(format!(
                "Input length {} must be a multiple of the hash rate {}",
                inputs.len(),
                self.params.rate
            ));
        }

        // absorb
        for input in inputs {
            self.ensure_permuted(&mut state, &mut offset);
            state[offset] += input.clone();
            offset += 1;
        }

        // squeeze
        let mut result = vec![FieldElement::zero(); self.params.rate];
        for result_element in result.iter_mut().take(self.params.rate) {
            self.ensure_permuted(&mut state, &mut offset);
            *result_element = state[offset].clone();
            offset += 1;
        }

        Ok(result)
    }
}

// Test values and parameters are taken from https://github.com/keep-starknet-strange/poseidon-rs/blob/f01ff35ab4dca63a9d6feb7ff3f46c9b04b28b04/src/permutation.rs#L136
// (values are parsed from decimals and have been converted to hex in our mod)
// The field that these tests use is defined below, and parameters are stored under /s128b
#[cfg(test)]
mod tests {
    use lambdaworks_math::{
        field::fields::u384_prime_field::{IsMontgomeryConfiguration, MontgomeryBackendPrimeField},
        unsigned_integer::element::U384,
    };

    use super::*;

    #[derive(Clone, Debug)]
    pub struct TestFieldConfig;
    impl IsMontgomeryConfiguration for TestFieldConfig {
        const MODULUS: U384 =
            U384::from("2000000000000080000000000000000000000000000000000000000000000001");
        const MP: u64 = 18446744073709551615u64;
        const R2: U384 =
            U384::from("C0000FFFFCFFFF800000000C0001FFFFFFFFBFFFF80000000140001FFFFE00");
    }

    pub type PoseidonTestField = MontgomeryBackendPrimeField<TestFieldConfig>;
    type TestFieldElement = FieldElement<PoseidonTestField>;

    pub fn load_test_parameters() -> Result<Parameters<PoseidonTestField>, String> {
        let round_constants_csv = include_str!("s128b/round_constants.csv");
        let mds_constants_csv = include_str!("s128b/mds_matrix.csv");

        let round_constants = round_constants_csv
            .split(',')
            .map(|c| TestFieldElement::new(U384::from(c.trim())))
            .collect();

        let mut mds_matrix = vec![];

        for line in mds_constants_csv.lines() {
            let matrix_line = line
                .split(',')
                .map(|c| TestFieldElement::new(U384::from(c.trim())))
                .collect();

            mds_matrix.push(matrix_line);
        }

        Ok(Parameters {
            rate: 2,
            capacity: 1,
            alpha: 3,
            n_full_rounds: 8,
            n_partial_rounds: 83,
            round_constants,
            mds_matrix,
        })
    }

    #[test]
    fn test_poseidon_s128b_t() {
        let mut state = [
            TestFieldElement::new(U384::from_u64(7)),
            TestFieldElement::new(U384::from_u64(98)),
            TestFieldElement::new(U384::from_u64(0)),
        ];
        let poseidon = Poseidon::new_with_params(load_test_parameters().unwrap());

        poseidon.ark(&mut state, 0);
        let expected = [
            TestFieldElement::new(U384::from(
                "16861759ea5568dd39dd92f9562a30b9e58e2ad98109ae4780b7fd8eac77fe8a",
            )),
            TestFieldElement::new(U384::from(
                "13827681995D5ADFFFC8397A3D00425A3DA43F76ABF28A64E4AB1A22F275092B",
            )),
            TestFieldElement::new(U384::from(
                "BA3956D2FAD4469E7F760A2277DC7CB2CAC75DC279B2D687A0DBE17704A8310",
            )),
        ];
        assert_eq!(state, expected);
    }

    #[test]
    fn test_mix() {
        let mut state = [
            TestFieldElement::new(U384::from(
                "13f891b043b3b740cc3e1b3051127d335f08e488322f360a776b3810b7dc690a",
            )),
            TestFieldElement::new(U384::from(
                "1bd24b7cb99acf0dbea719ff4007bd60105bcefef21ec509d2f8d4f9bb6a3a1a",
            )),
            TestFieldElement::new(U384::from(
                "110853eb2ebee0d940454fe420229a2a0974e666d16c92bab9f36cbd1a0eded",
            )),
        ];

        let poseidon = Poseidon::new_with_params(load_test_parameters().unwrap());

        poseidon.mix(&mut state);

        let expected = [
            TestFieldElement::new(U384::from(
                "1d30b34b465f8cddc8dc468f137891659c7e32b510cf41cec3aac0b26741681d",
            )),
            TestFieldElement::new(U384::from(
                "c445fa4dd2af583994272bede589b06b98fe9cd6d868bf718f6748ba6165620",
            )),
            TestFieldElement::new(U384::from(
                "1ed95ae0ea03bb892691f5200fb5902957ac17b3466afa62be808682801f97f9",
            )),
        ];
        assert_eq!(state, expected);
    }

    #[test]
    fn test_hash() {
        let poseidon: Poseidon<BLS12381PrimeField> = Poseidon::new();

        let a = FieldElement::one();
        let b = FieldElement::zero();

        poseidon.hash_one(a.clone());
        poseidon.hash_two(a, b);
    }

    #[test]
    fn test_permutation() {
        let poseidon = Poseidon::new_with_params(load_test_parameters().unwrap());

        let mut state = [
            TestFieldElement::new(U384::from_u64(7)),
            TestFieldElement::new(U384::from_u64(98)),
            TestFieldElement::new(U384::from_u64(0)),
        ];

        poseidon.permute(&mut state);

        let expected = [
            TestFieldElement::new(U384::from(
                "18700783647721BB9AD092B176BBEB5348401C21132CCF83C30134DFAB5A2DEB",
            )),
            TestFieldElement::new(U384::from(
                "1CC8856652601B3C81139AD5EC13E4A3A8F4A5DB242555521A09E002E7A10B2B",
            )),
            TestFieldElement::new(U384::from(
                "3DCB1CEC811FC2D7401CA7B9B084D167F33B6983D4428C8E0534C9C3CECF46D",
            )),
        ];

        assert_eq!(state, expected);
    }
}
