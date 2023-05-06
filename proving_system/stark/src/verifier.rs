use super::{
    air::{constraints::evaluator::ConstraintEvaluator, AIR},
    fri::fri_decommit::FriDecommitment,
    sample_z_ood,
};
use crate::{
    air::frame::Frame,
    batch_sample_challenges,
    fri::HASHER,
    proof::{DeepPolynomialOpenings, StarkProof},
    transcript_to_field, transcript_to_usize, Domain,
};
#[cfg(not(feature = "test_fiat_shamir"))]
use lambdaworks_crypto::fiat_shamir::default_transcript::DefaultTranscript;
use lambdaworks_crypto::fiat_shamir::transcript::Transcript;

#[cfg(feature = "test_fiat_shamir")]
use lambdaworks_crypto::fiat_shamir::test_transcript::TestTranscript;

use lambdaworks_math::{
    field::{
        element::FieldElement,
        traits::{IsFFTField, IsField},
    },
    helpers,
    polynomial::Polynomial,
    traits::ByteConversion,
};

#[cfg(feature = "test_fiat_shamir")]
fn step_1_transcript_initialization() -> TestTranscript {
    TestTranscript::new()
}

#[cfg(not(feature = "test_fiat_shamir"))]
fn step_1_transcript_initialization() -> DefaultTranscript {
    // TODO: add strong fiat shamir
    DefaultTranscript::new()
}

struct Challenges<F: IsFFTField> {
    z: FieldElement<F>,
    boundary_coeffs: Vec<(FieldElement<F>, FieldElement<F>)>,
    transition_coeffs: Vec<(FieldElement<F>, FieldElement<F>)>,
    trace_term_coeffs: Vec<Vec<FieldElement<F>>>,
    gamma_even: FieldElement<F>,
    gamma_odd: FieldElement<F>,
    beta_list: Vec<FieldElement<F>>,
    q_0: usize,
}

fn step_1_replay_rounds_and_recover_challenges<F, A, T>(
    air: &A,
    proof: &StarkProof<F>,
    domain: &Domain<F>,
    transcript: &mut T,
) -> Challenges<F>
where
    F: IsFFTField,
    FieldElement<F>: ByteConversion,
    A: AIR<Field = F>,
    T: Transcript,
{
    // Fiat-Shamir
    // we have to make sure that the result is not either
    // a root of unity or an element of the lde coset.
    let n_trace_cols = air.context().trace_columns;

    for root in proof.lde_trace_merkle_roots.iter() {
        transcript.append(&root.to_bytes_be());
    }

    // Round 2
    // These are the challenges alpha^B_j and beta^B_j
    let boundary_coeffs_alphas = batch_sample_challenges(n_trace_cols, transcript);
    let boundary_coeffs_betas = batch_sample_challenges(n_trace_cols, transcript);
    let boundary_coeffs: Vec<_> = boundary_coeffs_alphas
        .into_iter()
        .zip(boundary_coeffs_betas)
        .collect();

    // These are the challenges alpha^T_j and beta^T_j
    let transition_coeffs_alphas =
        batch_sample_challenges(air.context().num_transition_constraints, transcript);
    let transition_coeffs_betas =
        batch_sample_challenges(air.context().num_transition_constraints, transcript);
    let transition_coeffs: Vec<_> = transition_coeffs_alphas
        .into_iter()
        .zip(transition_coeffs_betas)
        .collect();

    transcript.append(&proof.composition_poly_even_root.to_bytes_be());
    transcript.append(&proof.composition_poly_odd_root.to_bytes_be());

    let z = sample_z_ood(
        &domain.lde_roots_of_unity_coset,
        &domain.trace_roots_of_unity,
        transcript,
    );

    // H_1(z^2)
    transcript.append(&proof.composition_poly_even_ood_evaluation.to_bytes_be());
    // H_2(z^2)
    transcript.append(&proof.composition_poly_odd_ood_evaluation.to_bytes_be());
    // These are the values t_j(zg^i)
    for i in 0..proof.trace_ood_frame_evaluations.num_rows() {
        for element in proof.trace_ood_frame_evaluations.get_row(i).iter() {
            transcript.append(&element.to_bytes_be());
        }
    }

    // Get the number of trace terms the DEEP composition poly will have.
    // One coefficient will be sampled for each of them.
    // TODO: try remove this, call transcript inside for and move gamma declarations
    let trace_term_coeffs = (0..n_trace_cols)
        .map(|_| {
            (0..air.context().transition_offsets.len())
                .map(|_| transcript_to_field(transcript))
                .collect()
        })
        .collect::<Vec<Vec<FieldElement<F>>>>();

    // Get coefficients for even and odd terms of the composition polynomial H(x)
    let gamma_even = transcript_to_field::<F, _>(transcript);
    let gamma_odd = transcript_to_field::<F, _>(transcript);
    //
    // construct vector of betas
    let mut beta_list: Vec<FieldElement<F>> = Vec::new();
    let merkle_roots = &proof.fri_layers_merkle_roots;
    for root in merkle_roots.iter() {
        let root_bytes = root.to_bytes_be();
        transcript.append(&root_bytes);

        let beta = transcript_to_field(transcript);
        beta_list.push(beta);
    }

    let last_evaluation = &proof.fri_last_value;
    let last_evaluation_bytes = last_evaluation.to_bytes_be();
    transcript.append(&last_evaluation_bytes);

    let q_0 = transcript_to_usize(transcript) % (2_usize.pow(domain.lde_root_order));

    Challenges {
        z,
        boundary_coeffs,
        transition_coeffs,
        trace_term_coeffs,
        gamma_even,
        gamma_odd,
        beta_list,
        q_0,
    }
}

fn step_2_verify_claimed_composition_polynomial<F: IsFFTField, A: AIR<Field = F>>(
    air: &A,
    proof: &StarkProof<F>,
    domain: &Domain<F>,
    challenges: &Challenges<F>,
) -> bool {
    // BEGIN TRACE <-> Composition poly consistency evaluation check
    // These are H_1(z^2) and H_2(z^2)
    let composition_poly_even_ood_evaluation = &proof.composition_poly_even_ood_evaluation;
    let composition_poly_odd_ood_evaluation = &proof.composition_poly_odd_ood_evaluation;

    let boundary_constraints = air.boundary_constraints();

    let n_trace_cols = air.context().trace_columns;

    let boundary_constraint_domains =
        boundary_constraints.generate_roots_of_unity(&domain.trace_primitive_root, n_trace_cols);
    let values = boundary_constraints.values(n_trace_cols);

    // Following naming conventions from https://www.notamonadtutorial.com/diving-deep-fri/
    let mut boundary_c_i_evaluations = Vec::with_capacity(n_trace_cols);
    let mut boundary_quotient_degrees = Vec::with_capacity(n_trace_cols);

    for trace_idx in 0..n_trace_cols {
        let trace_evaluation = &proof.trace_ood_frame_evaluations.get_row(0)[trace_idx];
        let boundary_constraints_domain = boundary_constraint_domains[trace_idx].clone();
        let boundary_interpolating_polynomial =
            &Polynomial::interpolate(&boundary_constraints_domain, &values[trace_idx]);

        let boundary_zerofier =
            boundary_constraints.compute_zerofier(&domain.trace_primitive_root, trace_idx);

        let boundary_quotient_ood_evaluation = (trace_evaluation
            - boundary_interpolating_polynomial.evaluate(&challenges.z))
            / boundary_zerofier.evaluate(&challenges.z);

        let boundary_quotient_degree = air.context().trace_length - boundary_zerofier.degree() - 1;

        boundary_c_i_evaluations.push(boundary_quotient_ood_evaluation);
        boundary_quotient_degrees.push(boundary_quotient_degree);
    }

    // TODO: Get trace polys degrees in a better way. The degree may not be trace_length - 1 in some
    // special cases.
    let transition_divisors = air.transition_divisors();

    let transition_quotients_max_degree = transition_divisors
        .iter()
        .zip(air.context().transition_degrees())
        .map(|(div, degree)| (air.context().trace_length - 1) * degree - div.degree())
        .max()
        .unwrap();

    let boundary_quotients_max_degree = boundary_quotient_degrees.iter().max().unwrap();

    let max_degree = std::cmp::max(
        transition_quotients_max_degree,
        *boundary_quotients_max_degree,
    );
    let max_degree_power_of_two = helpers::next_power_of_two(max_degree as u64);

    let boundary_quotient_ood_evaluations: Vec<FieldElement<F>> = boundary_c_i_evaluations
        .iter()
        .zip(boundary_quotient_degrees)
        .zip(&challenges.boundary_coeffs)
        .map(|((poly_eval, poly_degree), (alpha, beta))| {
            poly_eval
                * (alpha
                    * challenges
                        .z
                        .pow(max_degree_power_of_two - poly_degree as u64)
                    + beta)
        })
        .collect();

    let boundary_quotient_ood_evaluation = boundary_quotient_ood_evaluations
        .iter()
        .fold(FieldElement::<F>::zero(), |acc, x| acc + x);

    let transition_ood_frame_evaluations =
        air.compute_transition(&proof.trace_ood_frame_evaluations);

    let transition_c_i_evaluations =
        ConstraintEvaluator::compute_constraint_composition_poly_evaluations(
            air,
            &transition_ood_frame_evaluations,
            &challenges.transition_coeffs,
            max_degree_power_of_two,
            &challenges.z,
        );

    let composition_poly_ood_evaluation = &boundary_quotient_ood_evaluation
        + transition_c_i_evaluations
            .iter()
            .fold(FieldElement::<F>::zero(), |acc, evaluation| {
                acc + evaluation
            });

    let composition_poly_claimed_ood_evaluation =
        composition_poly_even_ood_evaluation + &challenges.z * composition_poly_odd_ood_evaluation;

    composition_poly_claimed_ood_evaluation == composition_poly_ood_evaluation
}

fn step_3_verify_fri<F, A, T>(
    air: &A,
    proof: &StarkProof<F>,
    domain: &Domain<F>,
    challenges: &Challenges<F>,
    transcript: &mut T,
) -> bool
where
    F: IsFFTField,
    FieldElement<F>: ByteConversion,
    A: AIR<Field = F>,
    T: Transcript,
{
    // Verify that t(x_0) is a trace evaluation
    // and verify first layer of FRI
    if !verify_trace_evaluations(&proof, challenges.q_0, &domain.lde_roots_of_unity_coset)
        || !verify_query(
            air,
            &proof.fri_layers_merkle_roots,
            &proof.fri_last_value,
            &challenges.beta_list,
            challenges.q_0,
            &proof.query_list[0],
            domain,
        )
    {
        return false;
    }

    // Verify 1..n layers of FRI
    let mut result = true;
    for proof_i in proof.query_list.iter().skip(1) {
        let q_i = transcript_to_usize(transcript) % (2_usize.pow(domain.lde_root_order));

        // this is done in constant time
        result &= verify_query(
            air,
            &proof.fri_layers_merkle_roots,
            &proof.fri_last_value,
            &challenges.beta_list,
            q_i,
            &proof_i,
            domain,
        );
    }
    result
}

fn step_4_verify_deep_composition_polynomial<F: IsFFTField>(
    proof: &StarkProof<F>,
    domain: &Domain<F>,
    challenges: &Challenges<F>,
) -> bool {
    //
    // DEEP consistency check
    // Verify that Deep(x) is constructed correctly
    let deep_poly_evaluation =
        reconstruct_deep_composition_poly_evaluation(proof, domain, challenges);
    let deep_poly_claimed_evaluation = &proof.query_list[0].first_layer_evaluation;

    deep_poly_claimed_evaluation == &deep_poly_evaluation
}

fn verify_query<F: IsField + IsFFTField, A: AIR<Field = F>>(
    air: &A,
    fri_layers_merkle_roots: &[FieldElement<F>],
    fri_last_value: &FieldElement<F>,
    beta_list: &[FieldElement<F>],
    iota: usize,
    fri_decommitment: &FriDecommitment<F>,
    domain: &Domain<F>,
) -> bool
where
    FieldElement<F>: ByteConversion,
{
    let lde_primitive_root = F::get_primitive_root_of_unity(domain.lde_root_order as u64).unwrap();
    let offset = FieldElement::from(air.options().coset_offset);
    // evaluation point = offset * w ^ i in the Stark literature
    let mut evaluation_point = offset * lde_primitive_root.pow(iota);

    let mut v = fri_decommitment.first_layer_evaluation.clone();
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
    for (layer_number, (layer_merkle_root, (auth_path, evaluation_sym))) in fri_layers_merkle_roots
        .iter()
        .zip(
            fri_decommitment
                .layers_auth_paths_sym
                .iter()
                .zip(fri_decommitment.layers_evaluations_sym.iter()),
        )
        .enumerate()
    // Since we always derive the current layer from the previous layer
    // We start with the second one, skipping the first, so previous is layer is the first one
    {
        // This is the current layer's evaluation domain length. We need it to know what the decommitment index for the current
        // layer is, so we can check the merkle paths at the right index.
        let domain_length = 1 << domain.lde_root_order - layer_number as u32;
        let layer_evaluation_index_sym = (iota + domain_length / 2) % domain_length;
        if !auth_path.verify(
            layer_merkle_root,
            layer_evaluation_index_sym,
            evaluation_sym,
            &HASHER,
        ) {
            return false;
        }

        let beta = &beta_list[layer_number];
        // v is the calculated element for the co linearity check
        let two = &FieldElement::from(2);
        v = (&v + evaluation_sym) / two + beta * (&v - evaluation_sym) / (two * &evaluation_point);
        evaluation_point = evaluation_point.pow(2_u64);
    }
    v == *fri_last_value
}

// Reconstruct Deep(\upsilon_0) off the values in the proof
fn reconstruct_deep_composition_poly_evaluation<F: IsFFTField>(
    proof: &StarkProof<F>,
    domain: &Domain<F>,
    challenges: &Challenges<F>,
) -> FieldElement<F> {
    let primitive_root = &F::get_primitive_root_of_unity(domain.root_order as u64).unwrap();
    let upsilon_0 = &domain.lde_roots_of_unity_coset[challenges.q_0];

    let mut trace_terms = FieldElement::zero();

    for (col_idx, coeff_row) in
        (0..proof.trace_ood_frame_evaluations.num_columns()).zip(&challenges.trace_term_coeffs)
    {
        for (row_idx, coeff) in (0..proof.trace_ood_frame_evaluations.num_rows()).zip(coeff_row) {
            let poly_evaluation = (proof.deep_poly_openings.lde_trace_evaluations[col_idx].clone()
                - proof.trace_ood_frame_evaluations.get_row(row_idx)[col_idx].clone())
                / (upsilon_0 - &challenges.z * primitive_root.pow(row_idx as u64));

            trace_terms += poly_evaluation * coeff.clone();
        }
    }

    let z_squared = &(&challenges.z * &challenges.z);
    let h_1_upsilon_0 = &proof
        .deep_poly_openings
        .lde_composition_poly_even_evaluation;
    let h_1_zsquared = &proof.composition_poly_even_ood_evaluation;
    let h_2_upsilon_0 = &proof.deep_poly_openings.lde_composition_poly_odd_evaluation;
    let h_2_zsquared = &proof.composition_poly_odd_ood_evaluation;

    let h_1_term = (h_1_upsilon_0 - h_1_zsquared) / (upsilon_0 - z_squared);
    let h_2_term = (h_2_upsilon_0 - h_2_zsquared) / (upsilon_0 - z_squared);

    trace_terms + h_1_term * &challenges.gamma_even + h_2_term * &challenges.gamma_odd
}

// Verifies that t(x_0) is a trace evaluation
fn verify_trace_evaluations<F: IsField + IsFFTField>(
    proof: &StarkProof<F>,
    q_i: usize,
    domain: &[FieldElement<F>],
) -> bool
where
    FieldElement<F>: ByteConversion,
{
    for ((merkle_root, merkle_proof), evaluation) in proof
        .lde_trace_merkle_roots
        .iter()
        .zip(&proof.deep_poly_openings.lde_trace_merkle_proofs)
        .zip(&proof.deep_poly_openings.lde_trace_evaluations)
    {
        let index = q_i % domain.len();

        if !merkle_proof.verify(merkle_root, index, evaluation, &HASHER) {
            return false;
        }
    }

    true
}

pub fn verify<F, A>(proof: &StarkProof<F>, air: &A) -> bool
where
    F: IsFFTField,
    A: AIR<Field = F>,
    FieldElement<F>: ByteConversion,
{
    let mut transcript = step_1_transcript_initialization();
    let domain = Domain::new(air);

    let challenges =
        step_1_replay_rounds_and_recover_challenges(air, proof, &domain, &mut transcript);

    if !step_2_verify_claimed_composition_polynomial(air, proof, &domain, &challenges) {
        return false;
    }

    if !step_3_verify_fri(air, proof, &domain, &challenges, &mut transcript) {
        return false;
    }

    step_4_verify_deep_composition_polynomial(proof, &domain, &challenges)
}
