use crate::hash::traits::IsCryptoHash;
use lambdaworks_math::field::{element::FieldElement, traits::IsField};

use super::proof::Proof;
use super::utils::*;

pub struct MerkleTree<F: IsField, H: IsCryptoHash<F>> {
    pub root: FieldElement<F>,
    nodes: Vec<FieldElement<F>>,
    hasher: H,
}

const ROOT: usize = 0;

impl<F: IsField, H: IsCryptoHash<F> + Clone> MerkleTree<F, H> {
    pub fn build(values: &[FieldElement<F>]) -> MerkleTree<F, H> {
        let hasher = H::new();
        let mut nodes: Vec<FieldElement<F>> = hash_leaves(values, &hasher);

        //The leaf must be a power of 2 set
        nodes = complete_until_power_of_two(&mut nodes);

        //The length of leaves minus one inner node in the merkle tree
        let mut inner_nodes = vec![FieldElement::zero(); nodes.len() - 1];
        inner_nodes.extend(nodes);

        //Build the inner nodes of the tree
        let nodes = build(&mut inner_nodes, ROOT, &hasher);

        MerkleTree {
            root: nodes[ROOT].clone(),
            nodes,
            hasher,
        }
    }

    fn get_leaves(&self) -> Vec<FieldElement<F>> {
        let leaves_start = self.nodes.len() / 2;
        Vec::from(&self.nodes[leaves_start..])
    }

    pub fn get_proof(&self, value: &FieldElement<F>) -> Option<Proof<F, H>> {
        let hashed_leaf = self.hasher.hash_one(value.clone());

        if let Some(mut pos) = self
            .get_leaves()
            .iter()
            .position(|leaf| *leaf == hashed_leaf)
        {
            pos += self.nodes.len() / 2;

            let merkle_path = self.build_merkle_path(pos);

            return self.create_proof(merkle_path, value);
        }

        None
    }

    pub fn get_proof_by_pos(&self, pos: usize, value: FieldElement<F>) -> Option<Proof<F, H>> {
        let hashed_leaf = self.hasher.hash_one(value.clone());

        let pos = pos + self.nodes.len() / 2;

        if self.nodes[pos] != hashed_leaf {
            return None;
        }

        let merkle_path = self.build_merkle_path(pos);

        self.create_proof(merkle_path, &value)
    }

    fn create_proof(
        &self,
        merkle_path: Vec<(FieldElement<F>, bool)>,
        value: &FieldElement<F>,
    ) -> Option<Proof<F, H>> {
        Some(Proof {
            value: value.clone(),
            merkle_path,
            hasher: self.hasher.clone(),
        })
    }

    fn build_merkle_path(&self, pos: usize) -> Vec<(FieldElement<F>, bool)> {
        let mut merkle_path = Vec::new();
        let mut pos = pos;

        while pos != ROOT {
            merkle_path.push((self.nodes[sibling_index(pos)].clone(), pos % 2 == 0));
            pos = parent_index(pos);
        }

        merkle_path
    }

    pub fn verify(proof: &Proof<F, H>, root_hash: FieldElement<F>) -> bool {
        let mut hashed_value = proof.hasher.hash_one(proof.value.clone());

        for (sibling_node, is_left) in proof.merkle_path.iter().rev() {
            if *is_left {
                hashed_value = proof.hasher.hash_two(hashed_value, sibling_node.clone());
            } else {
                hashed_value = proof.hasher.hash_two(sibling_node.clone(), hashed_value);
            }
        }

        root_hash == hashed_value
    }
}

#[cfg(test)]
mod tests {
    use crate::merkle_tree::DefaultHasher;

    use super::*;

    use lambdaworks_math::field::{element::FieldElement, fields::u64_prime_field::U64PrimeField};

    const MODULUS: u64 = 13;
    type U64PF = U64PrimeField<MODULUS>;
    type FE = FieldElement<U64PF>;

    #[test]
    // expected | 10 | 3 | 7 | 1 | 2 | 3 | 4 |
    fn build_merkle_tree_from_a_power_of_two_list_of_values() {
        let values: Vec<FE> = (1..5).map(FE::new).collect();
        let merkle_tree = MerkleTree::<U64PF, DefaultHasher>::build(&values);
        assert_eq!(merkle_tree.root, FE::new(20));
    }

    #[test]
    // expected | 8 | 7 | 1 | 6 | 1 | 7 | 7 | 2 | 4 | 6 | 8 | 10 | 10 | 10 | 10 |
    fn build_merkle_tree_from_an_odd_set_of_leaves() {
        let values: Vec<FE> = (1..6).map(FE::new).collect();
        let merkle_tree = MerkleTree::<U64PF, DefaultHasher>::build(&values);
        assert_eq!(merkle_tree.root, FE::new(8));
    }

    #[test]
    // expected | 8 | 7 | 1 | 6 | 1 | 7 | 7 | 2 | 4 | 6 | 8 | 10 | 10 | 10 | 10 |
    fn create_a_proof_over_value_that_belongs_to_a_given_merkle_tree_when_given_the_leaf_position()
    {
        let values: Vec<FE> = (1..6).map(FE::new).collect();
        let merkle_tree = MerkleTree::<U64PF, DefaultHasher>::build(&values);
        let proof = &merkle_tree.get_proof_by_pos(1, FE::new(2)).unwrap();
        assert_merkle_path(&proof.merkle_path, &[FE::new(2), FE::new(1), FE::new(1)]);
        assert!(MerkleTree::verify(proof, merkle_tree.root));
    }

    #[test]
    // expected | 2 | 1 | 1 |
    fn verify_a_proof_over_value_that_belongs_to_a_given_merkle_tree() {
        let values: Vec<FE> = (1..6).map(FE::new).collect();
        let merkle_tree = MerkleTree::<U64PF, DefaultHasher>::build(&values);

        let proof = merkle_tree.get_proof(&FE::new(2)).unwrap();
        assert_merkle_path(&proof.merkle_path, &[FE::new(2), FE::new(1), FE::new(1)]);

        assert!(MerkleTree::verify(&proof, merkle_tree.root));
    }

    fn assert_merkle_path(values: &[(FE, bool)], expected_values: &[FE]) {
        for ((node, _), expected_node) in values.iter().zip(expected_values) {
            assert_eq!(node, expected_node);
        }
    }
}
