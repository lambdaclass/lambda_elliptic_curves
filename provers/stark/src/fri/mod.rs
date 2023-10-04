pub mod fri_commitment;
pub mod fri_decommit;
mod fri_functions;

use lambdaworks_math::fft::polynomial::FFTPoly;
use lambdaworks_math::field::traits::{IsFFTField, IsField};
use lambdaworks_math::traits::Serializable;
pub use lambdaworks_math::{
    field::{element::FieldElement, fields::u64_prime_field::U64PrimeField},
    polynomial::Polynomial,
};

use crate::config::FriMerkleTree;
use crate::transcript::IsStarkTranscript;

use self::fri_commitment::FriLayer;
use self::fri_decommit::FriDecommitment;
use self::fri_functions::fold_polynomial;

pub trait IsFri {
    fn new_fri_layer<F>(
        poly: &Polynomial<FieldElement<F>>,
        coset_offset: &FieldElement<F>,
        domain_size: usize,
    ) -> FriLayer<F>
    where
        F: IsFFTField,
        FieldElement<F>: Serializable,
    {
        let evaluation = poly
            .evaluate_offset_fft(1, Some(domain_size), coset_offset)
            .unwrap(); // TODO: return error

        let merkle_tree = FriMerkleTree::build(&evaluation);

        FriLayer::new(&evaluation, merkle_tree, coset_offset.clone(), domain_size)
    }

    fn fri_commit_phase<F: IsField + IsFFTField>(
        number_layers: usize,
        p_0: Polynomial<FieldElement<F>>,
        transcript: &mut impl IsStarkTranscript<F>,
        coset_offset: &FieldElement<F>,
        domain_size: usize,
    ) -> (FieldElement<F>, Vec<FriLayer<F>>)
    where
        FieldElement<F>: Serializable,
    {
        let mut domain_size = domain_size;

        let mut fri_layer_list = Vec::with_capacity(number_layers);
        let mut current_layer = Self::new_fri_layer(&p_0, coset_offset, domain_size);
        fri_layer_list.push(current_layer.clone());
        let mut current_poly = p_0;
        // >>>> Send commitment: [p₀]
        transcript.append_bytes(&current_layer.merkle_tree.root);

        let mut coset_offset = coset_offset.clone();

        for _ in 1..number_layers {
            // <<<< Receive challenge 𝜁ₖ₋₁
            let zeta = transcript.sample_field_element();
            coset_offset = coset_offset.square();
            domain_size /= 2;

            // Compute layer polynomial and domain
            current_poly = fold_polynomial(&current_poly, &zeta);
            current_layer = Self::new_fri_layer(&current_poly, &coset_offset, domain_size);
            let new_data = &current_layer.merkle_tree.root;
            fri_layer_list.push(current_layer.clone()); // TODO: remove this clone

            // >>>> Send commitment: [pₖ]
            transcript.append_bytes(new_data);
        }

        // <<<< Receive challenge: 𝜁ₙ₋₁
        let zeta = transcript.sample_field_element();

        let last_poly = fold_polynomial(&current_poly, &zeta);

        let last_value = last_poly
            .coefficients()
            .get(0)
            .unwrap_or(&FieldElement::zero())
            .clone();

        // >>>> Send value: pₙ
        transcript.append_field_element(&last_value);

        (last_value, fri_layer_list)
    }

    fn fri_query_phase<F>(fri_layers: &Vec<FriLayer<F>>, iotas: &[usize]) -> Vec<FriDecommitment<F>>
    where
        F: IsFFTField,
        FieldElement<F>: Serializable,
    {
        if !fri_layers.is_empty() {
            let query_list = iotas
                .iter()
                .map(|iota_s| {
                    // <<<< Receive challenge 𝜄ₛ (iota_s)
                    let mut layers_auth_paths_sym = vec![];
                    let mut layers_evaluations_sym = vec![];
                    let mut layers_evaluations = vec![];
                    let mut layers_auth_paths = vec![];

                    for layer in fri_layers {
                        // symmetric element
                        let index = iota_s % layer.domain_size;
                        let index_sym = (iota_s + layer.domain_size / 2) % layer.domain_size;
                        let evaluation_sym = layer.evaluation[index_sym].clone();
                        let auth_path_sym = layer.merkle_tree.get_proof_by_pos(index_sym).unwrap();
                        let evaluation = layer.evaluation[index].clone();
                        let auth_path = layer.merkle_tree.get_proof_by_pos(index).unwrap();
                        layers_auth_paths_sym.push(auth_path_sym);
                        layers_evaluations_sym.push(evaluation_sym);
                        layers_evaluations.push(evaluation);
                        layers_auth_paths.push(auth_path);
                    }

                    FriDecommitment {
                        layers_auth_paths_sym,
                        layers_evaluations_sym,
                        layers_evaluations,
                        layers_auth_paths,
                    }
                })
                .collect();

            query_list
        } else {
            vec![]
        }
    }
}

pub struct Fri;

impl IsFri for Fri {}
