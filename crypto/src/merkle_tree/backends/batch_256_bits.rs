use std::marker::PhantomData;

use lambdaworks_math::{
    field::{element::FieldElement, traits::IsField},
    traits::ByteConversion,
};
use sha3::Digest;

use crate::merkle_tree::traits::IsMerkleTreeBackend;

#[derive(Clone)]
pub struct Batch256BitsTree<F, D: Digest> {
    phantom1: PhantomData<F>,
    phantom2: PhantomData<D>,
}

impl<F, D: Digest> Default for Batch256BitsTree<F, D> {
    fn default() -> Self {
        Self {
            phantom1: PhantomData,
            phantom2: PhantomData,
        }
    }
}

impl<F, D: Digest> IsMerkleTreeBackend for Batch256BitsTree<F, D>
where
    F: IsField,
    FieldElement<F>: ByteConversion,
{
    type Node = [u8; 32];
    type Data = Vec<FieldElement<F>>;

    fn hash_data(&self, input: &Vec<FieldElement<F>>) -> [u8; 32] {
        let mut hasher = D::new();
        for element in input.iter() {
            hasher.update(element.to_bytes_be());
        }
        let mut result_hash = [0_u8; 32];
        result_hash.copy_from_slice(&hasher.finalize());
        result_hash
    }

    fn hash_new_parent(&self, left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
        let mut hasher = D::new();
        hasher.update(left);
        hasher.update(right);
        let mut result_hash = [0_u8; 32];
        result_hash.copy_from_slice(&hasher.finalize());
        result_hash
    }
}

#[cfg(test)]
mod tests {
    use lambdaworks_math::field::{
        element::FieldElement, fields::fft_friendly::stark_252_prime_field::Stark252PrimeField,
    };
    use sha3::{Keccak256, Sha3_256};

    use crate::merkle_tree::{backends::batch_256_bits::Batch256BitsTree, merkle::MerkleTree};

    type F = Stark252PrimeField;
    type FE = FieldElement<F>;

    #[test]
    fn hash_data_field_element_backend_works_with_sha3_256() {
        let values = [
            vec![FE::from(2u64), FE::from(11u64)],
            vec![FE::from(3u64), FE::from(14u64)],
            vec![FE::from(4u64), FE::from(7u64)],
            vec![FE::from(5u64), FE::from(3u64)],
            vec![FE::from(6u64), FE::from(5u64)],
            vec![FE::from(7u64), FE::from(16u64)],
            vec![FE::from(8u64), FE::from(19u64)],
            vec![FE::from(9u64), FE::from(21u64)],
        ];
        let merkle_tree = MerkleTree::<Batch256BitsTree<F, Sha3_256>>::build(&values);
        let proof = merkle_tree.get_proof_by_pos(0).unwrap();
        assert!(proof.verify::<Batch256BitsTree<F, Sha3_256>>(&merkle_tree.root, 0, &values[0]));
    }

    #[test]
    fn hash_data_field_element_backend_works_with_keccak256() {
        let values = [
            vec![FE::from(2u64), FE::from(11u64)],
            vec![FE::from(3u64), FE::from(14u64)],
            vec![FE::from(4u64), FE::from(7u64)],
            vec![FE::from(5u64), FE::from(3u64)],
            vec![FE::from(6u64), FE::from(5u64)],
            vec![FE::from(7u64), FE::from(16u64)],
            vec![FE::from(8u64), FE::from(19u64)],
            vec![FE::from(9u64), FE::from(21u64)],
        ];
        let merkle_tree = MerkleTree::<Batch256BitsTree<F, Keccak256>>::build(&values);
        let proof = merkle_tree.get_proof_by_pos(0).unwrap();
        assert!(proof.verify::<Batch256BitsTree<F, Keccak256>>(&merkle_tree.root, 0, &values[0]));
    }
}
