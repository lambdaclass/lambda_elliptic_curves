#[cfg(feature = "instruments")]
use std::time::Instant;

use lambdaworks_crypto::merkle_tree::proof::Proof;
//use itertools::multizip;
#[cfg(not(feature = "test_fiat_shamir"))]
use log::error;

use lambdaworks_math::{
    field::{
        element::FieldElement,
        traits::{IsFFTField, IsField},
    },
    traits::Serializable,
};

use crate::{
    config::Commitment, grinding, proof::stark::DeepPolynomialOpenings,
    transcript::IsStarkTranscript,
};

use super::{
    config::{BatchedMerkleTreeBackend, FriMerkleTreeBackend},
    domain::Domain,
    fri::fri_decommit::FriDecommitment,
    grinding::hash_transcript_with_int_and_get_leading_zeros,
    proof::{options::ProofOptions, stark::StarkProof},
    traits::AIR,
};

pub struct Challenges<F, A>
where
    F: IsFFTField,
    A: AIR<Field = F>,
{
    pub z: FieldElement<F>,
    pub boundary_coeffs: Vec<FieldElement<F>>,
    pub transition_coeffs: Vec<FieldElement<F>>,
    pub trace_term_coeffs: Vec<Vec<FieldElement<F>>>,
    pub gammas: Vec<FieldElement<F>>,
    pub zetas: Vec<FieldElement<F>>,
    pub iotas: Vec<usize>,
    pub rap_challenges: A::RAPChallenges,
    pub leading_zeros_count: u8, // number of leading zeros in the grinding
}

pub trait IsStarkVerifier {
    fn sample_query_indexes<F: IsFFTField>(
        number_of_queries: usize,
        domain: &Domain<F>,
        transcript: &mut impl IsStarkTranscript<F>,
    ) -> Vec<usize> {
        (0..number_of_queries)
            .map(|_| (transcript.sample_u64(domain.lde_roots_of_unity_coset.len() as u64)) as usize)
            .collect::<Vec<usize>>()
    }

    fn step_1_replay_rounds_and_recover_challenges<F, A>(
        air: &A,
        proof: &StarkProof<F>,
        domain: &Domain<F>,
        transcript: &mut impl IsStarkTranscript<F>,
    ) -> Challenges<F, A>
    where
        F: IsFFTField,
        FieldElement<F>: Serializable,
        A: AIR<Field = F>,
    {
        // ===================================
        // ==========|   Round 1   |==========
        // ===================================

        // <<<< Receive commitments:[tⱼ]
        let total_columns = air.context().trace_columns;

        transcript.append_bytes(&proof.lde_trace_merkle_roots[0]);

        let rap_challenges = air.build_rap_challenges(transcript);

        if let Some(root) = proof.lde_trace_merkle_roots.get(1) {
            transcript.append_bytes(root);
        }

        // ===================================
        // ==========|   Round 2   |==========
        // ===================================

        // <<<< Receive challenge: 𝛽
        let beta = transcript.sample_field_element();
        let num_boundary_constraints = air.boundary_constraints(&rap_challenges).constraints.len();

        let num_transition_constraints = air.context().num_transition_constraints;

        let mut coefficients: Vec<_> = (0..num_boundary_constraints + num_transition_constraints)
            .map(|i| beta.pow(i))
            .collect();

        let transition_coeffs: Vec<_> = coefficients.drain(..num_transition_constraints).collect();
        let boundary_coeffs = coefficients;

        // <<<< Receive commitments: [H₁], [H₂]
        transcript.append_bytes(&proof.composition_poly_root);

        // ===================================
        // ==========|   Round 3   |==========
        // ===================================

        // >>>> Send challenge: z
        let z = transcript.sample_z_ood(
            &domain.lde_roots_of_unity_coset,
            &domain.trace_roots_of_unity,
        );

        // <<<< Receive values: tⱼ(zgᵏ)
        for i in 0..proof.trace_ood_frame_evaluations.num_columns() {
            for j in 0..proof.trace_ood_frame_evaluations.num_rows() {
                transcript.append_field_element(&proof.trace_ood_frame_evaluations.get_row(j)[i]);
            }
        }
        // <<<< Receive value: Hᵢ(z^N)
        for element in proof.composition_poly_parts_ood_evaluation.iter() {
            transcript.append_field_element(element);
        }

        // ===================================
        // ==========|   Round 4   |==========
        // ===================================

        let n_terms_composition_poly = proof.composition_poly_parts_ood_evaluation.len();
        let n_terms_trace = air.context().transition_offsets.len() * air.context().trace_columns;
        let gamma = transcript.sample_field_element();

        // <<<< Receive challenges: 𝛾, 𝛾'
        let mut deep_composition_coefficients: Vec<_> =
            core::iter::successors(Some(FieldElement::one()), |x| Some(x * &gamma))
                .take(n_terms_composition_poly + n_terms_trace)
                .collect();

        let trace_term_coeffs: Vec<_> = deep_composition_coefficients
            .drain(..n_terms_trace)
            .collect::<Vec<_>>()
            .chunks(air.context().transition_offsets.len())
            .map(|chunk| chunk.to_vec())
            .collect();

        // <<<< Receive challenges: 𝛾ⱼ, 𝛾ⱼ'
        let gammas = deep_composition_coefficients;

        // FRI commit phase
        let merkle_roots = &proof.fri_layers_merkle_roots;
        let mut zetas = merkle_roots
            .iter()
            .map(|root| {
                // >>>> Send challenge 𝜁ₖ
                let element = transcript.sample_field_element();
                // <<<< Receive commitment: [pₖ] (the first one is [p₀])
                transcript.append_bytes(root);
                element
            })
            .collect::<Vec<FieldElement<F>>>();

        // >>>> Send challenge 𝜁ₙ₋₁
        zetas.push(transcript.sample_field_element());

        // <<<< Receive value: pₙ
        transcript.append_field_element(&proof.fri_last_value);

        // Receive grinding value
        // 1) Receive challenge from the transcript
        let security_bits = air.context().proof_options.grinding_factor;
        let mut leading_zeros_count = 0;
        if security_bits > 0 {
            let transcript_challenge = transcript.state();
            let nonce = proof.nonce;
            leading_zeros_count =
                hash_transcript_with_int_and_get_leading_zeros(&transcript_challenge, nonce);
            transcript.append_bytes(&nonce.to_be_bytes());
        }

        // FRI query phase
        // <<<< Send challenges 𝜄ₛ (iota_s)
        let number_of_queries = air.options().fri_number_of_queries;
        let iotas = Self::sample_query_indexes(number_of_queries, &domain, transcript);

        Challenges {
            z,
            boundary_coeffs,
            transition_coeffs,
            trace_term_coeffs,
            gammas,
            zetas,
            iotas,
            rap_challenges,
            leading_zeros_count,
        }
    }

    fn step_2_verify_claimed_composition_polynomial<F: IsFFTField, A: AIR<Field = F>>(
        air: &A,
        proof: &StarkProof<F>,
        domain: &Domain<F>,
        challenges: &Challenges<F, A>,
    ) -> bool {
        // BEGIN TRACE <-> Composition poly consistency evaluation check

        let boundary_constraints = air.boundary_constraints(&challenges.rap_challenges);

        //let n_trace_cols = air.context().trace_columns;
        // special cases.
        let trace_length = air.trace_length();
        let number_of_b_constraints = boundary_constraints.constraints.len();

        // Following naming conventions from https://www.notamonadtutorial.com/diving-deep-fri/
        let (boundary_c_i_evaluations_num, mut boundary_c_i_evaluations_den): (
            Vec<FieldElement<F>>,
            Vec<FieldElement<F>>,
        ) = (0..number_of_b_constraints)
            .map(|index| {
                let step = boundary_constraints.constraints[index].step;
                let point = &domain.trace_primitive_root.pow(step as u64);
                let trace_idx = boundary_constraints.constraints[index].col;
                let trace_evaluation = &proof.trace_ood_frame_evaluations.get_row(0)[trace_idx];
                let boundary_zerofier_challenges_z_den = &challenges.z - point;

                let boundary_quotient_ood_evaluation_num =
                    trace_evaluation - &boundary_constraints.constraints[index].value;

                (
                    boundary_quotient_ood_evaluation_num,
                    boundary_zerofier_challenges_z_den,
                )
            })
            .collect::<Vec<_>>()
            .into_iter()
            .unzip();

        FieldElement::inplace_batch_inverse(&mut boundary_c_i_evaluations_den).unwrap();

        let boundary_quotient_ood_evaluation: FieldElement<F> = boundary_c_i_evaluations_num
            .iter()
            .zip(&boundary_c_i_evaluations_den)
            .zip(&challenges.boundary_coeffs)
            .map(|((num, den), beta)| num * den * beta)
            .fold(FieldElement::<F>::zero(), |acc, x| acc + x);

        let transition_ood_frame_evaluations = air.compute_transition(
            &proof.trace_ood_frame_evaluations,
            &challenges.rap_challenges,
        );

        let denominator = (&challenges.z.pow(trace_length) - FieldElement::<F>::one())
            .inv()
            .unwrap();

        let exemption = air
            .transition_exemptions_verifier(
                domain.trace_roots_of_unity.iter().last().expect("has last"),
            )
            .iter()
            .map(|poly| poly.evaluate(&challenges.z))
            .collect::<Vec<FieldElement<F>>>();

        let unity = &FieldElement::one();
        let transition_c_i_evaluations_sum = transition_ood_frame_evaluations
            .iter()
            .zip(&air.context().transition_degrees)
            .zip(&air.context().transition_exemptions)
            .zip(&challenges.transition_coeffs)
            .fold(FieldElement::zero(), |acc, (((eval, _), except), beta)| {
                let except = except
                    .checked_sub(1)
                    .map(|i| &exemption[i])
                    .unwrap_or(unity);
                acc + &denominator * eval * beta * except
            });

        let composition_poly_ood_evaluation =
            &boundary_quotient_ood_evaluation + transition_c_i_evaluations_sum;

        let composition_poly_claimed_ood_evaluation = proof
            .composition_poly_parts_ood_evaluation
            .iter()
            .rev()
            .fold(FieldElement::zero(), |acc, coeff| {
                acc * &challenges.z + coeff
            });

        composition_poly_claimed_ood_evaluation == composition_poly_ood_evaluation
    }

    fn step_3_verify_fri<F, A>(
        proof: &StarkProof<F>,
        domain: &Domain<F>,
        challenges: &Challenges<F, A>,
    ) -> bool
    where
        F: IsFFTField,
        FieldElement<F>: Serializable,
        A: AIR<Field = F>,
    {
        let (deep_poly_evaluations, deep_poly_evaluations_sym) =
            Self::reconstruct_deep_composition_poly_evaluations_for_all_queries(
                challenges, domain, proof,
            );

        // verify FRI
        let mut evaluation_point_inverse = challenges
            .iotas
            .iter()
            .map(|iota| Self::query_challenge_to_evaluation_point(*iota, domain))
            .collect::<Vec<FieldElement<F>>>();
        FieldElement::inplace_batch_inverse(&mut evaluation_point_inverse).unwrap();
        proof
            .query_list
            .iter()
            .zip(&challenges.iotas)
            .zip(evaluation_point_inverse)
            .enumerate()
            .fold(true, |mut result, (i, ((proof_s, iota_s), eval))| {
                // this is done in constant time
                result &= Self::verify_query_and_sym_openings(
                    proof,
                    &challenges.zetas,
                    *iota_s,
                    proof_s,
                    domain,
                    eval,
                    &deep_poly_evaluations[i],
                    &deep_poly_evaluations_sym[i],
                );
                result
            })
    }
    fn query_challenge_to_merkle_root_index(index: usize, domain_size: usize) -> usize {
        index
    }

    fn query_challenge_to_merkle_root_index_sym(index: usize, domain_size: usize) -> usize {
        (index + domain_size / 2) % domain_size
    }

    fn query_challenge_to_evaluation_point<F: IsFFTField>(
        iota: usize,
        domain: &Domain<F>,
    ) -> FieldElement<F> {
        domain.lde_roots_of_unity_coset[iota].clone()
    }

    fn query_challenge_to_evaluation_point_sym<F: IsFFTField>(
        iota: usize,
        domain: &Domain<F>,
    ) -> FieldElement<F> {
        let domain_size = domain.lde_roots_of_unity_coset.len();
        domain.lde_roots_of_unity_coset[(iota + domain_size / 2) % domain_size].clone()
    }

    fn verify_trace_openings<F>(
        domain: &Domain<F>,
        num_main_columns: usize,
        proof: &StarkProof<F>,
        deep_poly_opening: &DeepPolynomialOpenings<F>,
        deep_poly_opening_sym: &DeepPolynomialOpenings<F>,
        iota: usize,
    ) -> bool
    where
        F: IsFFTField,
        FieldElement<F>: Serializable,
    {
        let lde_trace_evaluations = vec![
            deep_poly_opening.lde_trace_evaluations[..num_main_columns].to_vec(),
            deep_poly_opening.lde_trace_evaluations[num_main_columns..].to_vec(),
        ];

        let index =
            Self::query_challenge_to_merkle_root_index(iota, domain.lde_roots_of_unity_coset.len());
        let openings_are_valid = proof
            .lde_trace_merkle_roots
            .iter()
            .zip(&deep_poly_opening.lde_trace_merkle_proofs)
            .zip(lde_trace_evaluations)
            .fold(true, |acc, ((merkle_root, merkle_proof), evaluation)| {
                acc & Self::verify_opening(&merkle_proof, &merkle_root, index, &evaluation)
            });

        let lde_trace_evaluations_sym = vec![
            deep_poly_opening_sym.lde_trace_evaluations[..num_main_columns].to_vec(),
            deep_poly_opening_sym.lde_trace_evaluations[num_main_columns..].to_vec(),
        ];

        let index_sym = Self::query_challenge_to_merkle_root_index_sym(
            iota,
            domain.lde_roots_of_unity_coset.len(),
        );
        let openings_sym_are_valid = proof
            .lde_trace_merkle_roots
            .iter()
            .zip(&deep_poly_opening_sym.lde_trace_merkle_proofs)
            .zip(lde_trace_evaluations_sym)
            .fold(true, |acc, ((merkle_root, merkle_proof), evaluation)| {
                acc & Self::verify_opening(&merkle_proof, &merkle_root, index_sym, &evaluation)
            });
        openings_are_valid & openings_sym_are_valid
    }

    fn verify_opening<F>(
        proof: &Proof<Commitment>,
        root: &Commitment,
        index: usize,
        value: &Vec<FieldElement<F>>,
    ) -> bool
    where
        F: IsField,
        FieldElement<F>: Serializable,
    {
        proof.verify::<BatchedMerkleTreeBackend<F>>(&root, index, &value)
    }

    fn verify_composition_poly_opening<F>(
        domain: &Domain<F>,
        deep_poly_opening: &DeepPolynomialOpenings<F>,
        deep_poly_opening_sym: &DeepPolynomialOpenings<F>,
        composition_poly_merkle_root: &Commitment,
        iota: &usize,
    ) -> bool
    where
        F: IsFFTField,
        FieldElement<F>: Serializable,
    {
        let openings_are_valid = deep_poly_opening
            .lde_composition_poly_proof
            .verify::<BatchedMerkleTreeBackend<F>>(
            composition_poly_merkle_root,
            *iota,
            &deep_poly_opening.lde_composition_poly_parts_evaluation,
        );

        let openings_sym_are_valid = deep_poly_opening_sym
            .lde_composition_poly_proof
            .verify::<BatchedMerkleTreeBackend<F>>(
            composition_poly_merkle_root,
            *iota + domain.lde_roots_of_unity_coset.len() / 2,
            &deep_poly_opening_sym.lde_composition_poly_parts_evaluation,
        );

        openings_are_valid & openings_sym_are_valid
    }

    fn step_4_verify_trace_and_composition_openings<F: IsFFTField, A: AIR<Field = F>>(
        air: &A,
        proof: &StarkProof<F>,
        domain: &Domain<F>,
        challenges: &Challenges<F, A>,
    ) -> bool
    where
        FieldElement<F>: Serializable,
    {
        challenges
            .iotas
            .iter()
            .zip(&proof.deep_poly_openings)
            .zip(&proof.deep_poly_openings_sym)
            .fold(
                true,
                |mut result, ((iota_n, deep_poly_opening), deep_poly_openings_sym)| {
                    // Verify opening Open(H₁(D_LDE, 𝜐₀) and Open(H₂(D_LDE, 𝜐₀),
                    result &= Self::verify_composition_poly_opening(
                        domain,
                        &deep_poly_opening,
                        &deep_poly_openings_sym,
                        &proof.composition_poly_root,
                        iota_n,
                    );

                    let num_main_columns =
                        air.context().trace_columns - air.number_auxiliary_rap_columns();
                    // Verify openings Open(tⱼ(D_LDE), 𝜐₀)
                    result &= Self::verify_trace_openings(
                        domain,
                        num_main_columns,
                        proof,
                        deep_poly_opening,
                        deep_poly_openings_sym,
                        *iota_n,
                    );
                    result
                },
            )
    }

    fn verify_fri_layer_openings<F>(
        merkle_root: &Commitment,
        auth_path: &Proof<Commitment>,
        auth_path_sym: &Proof<Commitment>,
        evaluation: &FieldElement<F>,
        evaluation_sym: &FieldElement<F>,
        domain_length: usize,
        iota: usize,
    ) -> bool
    where
        F: IsFFTField,
        FieldElement<F>: Serializable,
    {
        let index = iota % domain_length;
        let index_sym = (iota + domain_length / 2) % domain_length;

        // Verify opening Open(pₖ(Dₖ), −𝜐ₛ^(2ᵏ))
        let eval_sym_ok =
            auth_path_sym.verify::<FriMerkleTreeBackend<F>>(merkle_root, index_sym, evaluation_sym);

        let eval_ok = auth_path.verify::<FriMerkleTreeBackend<F>>(merkle_root, index, evaluation);

        eval_ok & eval_sym_ok
    }

    fn verify_query_and_sym_openings<F: IsField + IsFFTField>(
        proof: &StarkProof<F>,
        zetas: &[FieldElement<F>],
        iota: usize,
        fri_decommitment: &FriDecommitment<F>,
        domain: &Domain<F>,
        evaluation_point_inverse: FieldElement<F>,
        deep_composition_evaluation: &FieldElement<F>,
        deep_composition_evaluation_sym: &FieldElement<F>,
    ) -> bool
    where
        FieldElement<F>: Serializable,
    {
        let fri_layers_merkle_roots = &proof.fri_layers_merkle_roots;
        let evaluation_point_vec: Vec<FieldElement<F>> = core::iter::successors(
            Some(evaluation_point_inverse.square()),
            |evaluation_point| Some(evaluation_point.square()),
        )
        .take(fri_layers_merkle_roots.len())
        .collect();

        let pi0 = deep_composition_evaluation;
        let pi0_sym = deep_composition_evaluation_sym;
        let mut v = (pi0 + pi0_sym) + &zetas[0] * (pi0 - pi0_sym) * evaluation_point_inverse;

        // For each fri layer merkle proof check:
        // That each merkle path verifies

        // Sample beta with fiat shamir
        // Compute v = [P_i(z_i) + P_i(-z_i)] / 2 + beta * [P_i(z_i) - P_i(-z_i)] / (2 * z_i)
        // Where P_i is the folded polynomial of the i-th fiat shamir round
        // z_i is obtained from the first z (that was derived through Fiat-Shamir) through a known calculation
        // The calculation is, given the index, index % length_of_evaluation_domain

        // Check that v = P_{i+1}(z_i)

        // For each (merkle_root, merkle_auth_path) / fold
        // With the auth path containining the element that the path proves it's existence
        fri_layers_merkle_roots
            .iter()
            .enumerate()
            .zip(&fri_decommitment.layers_auth_paths)
            .zip(&fri_decommitment.layers_evaluations)
            .zip(&fri_decommitment.layers_auth_paths_sym)
            .zip(&fri_decommitment.layers_evaluations_sym)
            .zip(evaluation_point_vec)
            .fold(
                true,
                |result,
                 (
                    (((((k, merkle_root), auth_path), evaluation), auth_path_sym), evaluation_sym),
                    evaluation_point_inv,
                )| {
                    let domain_length = 1 << (domain.lde_root_order - (k + 1) as u32);
                    // Since we always derive the current layer from the previous layer
                    // We start with the second one, skipping the first, so previous is layer is the first one
                    // This is the current layer's evaluation domain length.
                    // We need it to know what the decommitment index for the current
                    // layer is, so we can check the merkle paths at the right index.

                    // Verify opening Open(pₖ(Dₖ), −𝜐ₛ^(2ᵏ))
                    let openings_ok = Self::verify_fri_layer_openings(
                        merkle_root,
                        auth_path,
                        auth_path_sym,
                        &v,
                        evaluation_sym,
                        domain_length,
                        iota,
                    );

                    let beta = &zetas[k + 1];
                    // v is the calculated element for the co linearity check
                    v = (&v + evaluation_sym) + beta * (&v - evaluation_sym) * evaluation_point_inv;

                    // Check that next value is the given by the prover
                    if k < fri_decommitment.layers_evaluations.len() - 1 {
                        result & openings_ok
                    } else {
                        result & (v == proof.fri_last_value) & openings_ok
                    }
                },
            )
    }

    fn reconstruct_deep_composition_poly_evaluations_for_all_queries<
        F: IsFFTField,
        A: AIR<Field = F>,
    >(
        challenges: &Challenges<F, A>,
        domain: &Domain<F>,
        proof: &StarkProof<F>,
    ) -> (Vec<FieldElement<F>>, Vec<FieldElement<F>>) {
        let mut deep_poly_evaluations = Vec::new();
        let mut deep_poly_evaluations_sym = Vec::new();
        for (i, iota) in challenges.iotas.iter().enumerate() {
            // Reconstruct deep composition evaluation
            let primitive_root = &F::get_primitive_root_of_unity(domain.root_order as u64).unwrap();

            let evaluation_point = Self::query_challenge_to_evaluation_point(*iota, domain);
            deep_poly_evaluations.push(Self::reconstruct_deep_composition_poly_evaluation(
                proof,
                &evaluation_point,
                &primitive_root,
                challenges,
                &proof.deep_poly_openings[i].lde_trace_evaluations,
                &proof.deep_poly_openings[i].lde_composition_poly_parts_evaluation,
            ));

            let evaluation_point = Self::query_challenge_to_evaluation_point_sym(*iota, domain);
            deep_poly_evaluations_sym.push(Self::reconstruct_deep_composition_poly_evaluation(
                proof,
                &evaluation_point,
                &primitive_root,
                challenges,
                &proof.deep_poly_openings_sym[i].lde_trace_evaluations,
                &proof.deep_poly_openings_sym[i].lde_composition_poly_parts_evaluation,
            ));
        }
        (deep_poly_evaluations, deep_poly_evaluations_sym)
    }

    // Reconstruct Deep(\upsilon_0) off the values in the proof
    fn reconstruct_deep_composition_poly_evaluation<F: IsFFTField, A: AIR<Field = F>>(
        proof: &StarkProof<F>,
        evaluation_point: &FieldElement<F>,
        primitive_root: &FieldElement<F>,
        challenges: &Challenges<F, A>,
        lde_trace_evaluations: &[FieldElement<F>],
        lde_composition_poly_parts_evaluation: &[FieldElement<F>],
    ) -> FieldElement<F> {
        let mut denoms_trace = (0..proof.trace_ood_frame_evaluations.num_rows())
            .map(|row_idx| evaluation_point - &challenges.z * primitive_root.pow(row_idx as u64))
            .collect::<Vec<FieldElement<F>>>();
        FieldElement::inplace_batch_inverse(&mut denoms_trace).unwrap();

        let trace_term = (0..proof.trace_ood_frame_evaluations.num_columns())
            .zip(&challenges.trace_term_coeffs)
            .fold(FieldElement::zero(), |trace_terms, (col_idx, coeff_row)| {
                let trace_i = (0..proof.trace_ood_frame_evaluations.num_rows())
                    .zip(coeff_row)
                    .fold(FieldElement::zero(), |trace_t, (row_idx, coeff)| {
                        let poly_evaluation = (lde_trace_evaluations[col_idx].clone()
                            - proof.trace_ood_frame_evaluations.get_row(row_idx)[col_idx].clone())
                            * &denoms_trace[row_idx];
                        trace_t + &poly_evaluation * coeff
                    });
                trace_terms + trace_i
            });

        let number_of_parts = lde_composition_poly_parts_evaluation.len();
        let z_pow = &challenges.z.pow(number_of_parts);

        let denom_composition = (evaluation_point - z_pow).inv().unwrap();
        let mut h_terms = FieldElement::zero();
        for (j, h_i_upsilon) in lde_composition_poly_parts_evaluation.iter().enumerate() {
            let h_i_zpower = &proof.composition_poly_parts_ood_evaluation[j];
            let h_i_term = (h_i_upsilon - h_i_zpower) * &challenges.gammas[j];
            h_terms = h_terms + h_i_term;
        }
        h_terms = h_terms * denom_composition;

        trace_term + h_terms
    }

    fn verify<F, A>(
        proof: &StarkProof<F>,
        pub_input: &A::PublicInputs,
        proof_options: &ProofOptions,
        mut transcript: impl IsStarkTranscript<F>,
    ) -> bool
    where
        F: IsFFTField,
        A: AIR<Field = F>,
        FieldElement<F>: Serializable,
    {
        // Verify there are enough queries
        if proof.query_list.len() < proof_options.fri_number_of_queries {
            return false;
        }

        #[cfg(feature = "instruments")]
        println!("- Started step 1: Recover challenges");
        #[cfg(feature = "instruments")]
        let timer1 = Instant::now();

        let air = A::new(proof.trace_length, pub_input, proof_options);
        let domain = Domain::new(&air);

        let challenges = Self::step_1_replay_rounds_and_recover_challenges(
            &air,
            proof,
            &domain,
            &mut transcript,
        );

        // verify grinding
        let grinding_factor = air.context().proof_options.grinding_factor;
        if challenges.leading_zeros_count < grinding_factor {
            error!("Grinding factor not satisfied");
            return false;
        }

        #[cfg(feature = "instruments")]
        let elapsed1 = timer1.elapsed();
        #[cfg(feature = "instruments")]
        println!("  Time spent: {:?}", elapsed1);

        #[cfg(feature = "instruments")]
        println!("- Started step 2: Verify claimed polynomial");
        #[cfg(feature = "instruments")]
        let timer2 = Instant::now();

        if !Self::step_2_verify_claimed_composition_polynomial(&air, proof, &domain, &challenges) {
            error!("Composition Polynomial verification failed");
            return false;
        }

        #[cfg(feature = "instruments")]
        let elapsed2 = timer2.elapsed();
        #[cfg(feature = "instruments")]
        println!("  Time spent: {:?}", elapsed2);
        #[cfg(feature = "instruments")]

        println!("- Started step 3: Verify FRI");
        #[cfg(feature = "instruments")]
        let timer3 = Instant::now();

        if !Self::step_3_verify_fri(proof, &domain, &challenges) {
            error!("FRI verification failed");
            return false;
        }

        #[cfg(feature = "instruments")]
        let elapsed3 = timer3.elapsed();
        #[cfg(feature = "instruments")]
        println!("  Time spent: {:?}", elapsed3);

        #[cfg(feature = "instruments")]
        println!("- Started step 4: Verify deep composition polynomial");
        #[cfg(feature = "instruments")]
        let timer4 = Instant::now();

        #[allow(clippy::let_and_return)]
        if !Self::step_4_verify_trace_and_composition_openings(&air, proof, &domain, &challenges) {
            error!("DEEP Composition Polynomial verification failed");
            return false;
        }

        #[cfg(feature = "instruments")]
        let elapsed4 = timer4.elapsed();
        #[cfg(feature = "instruments")]
        println!("  Time spent: {:?}", elapsed4);

        #[cfg(feature = "instruments")]
        {
            let total_time = elapsed1 + elapsed2 + elapsed3 + elapsed4;
            println!(
                " Fraction of verifying time per step: {:.4} {:.4} {:.4} {:.4}",
                elapsed1.as_nanos() as f64 / total_time.as_nanos() as f64,
                elapsed2.as_nanos() as f64 / total_time.as_nanos() as f64,
                elapsed3.as_nanos() as f64 / total_time.as_nanos() as f64,
                elapsed4.as_nanos() as f64 / total_time.as_nanos() as f64
            );
        }

        true
    }
}

pub struct Verifier;

impl IsStarkVerifier for Verifier {}
