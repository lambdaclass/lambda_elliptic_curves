use super::{
    air::{constraints::evaluator::ConstraintEvaluator, AIR},
    fri::fri_decommit::FriDecommitment,
    sample_z_ood,
};
use crate::{
    air::frame::Frame,
    fri::HASHER,
    proof::{DeepConsistencyCheck, StarkProof},
    transcript_to_field, transcript_to_usize,
};
#[cfg(not(feature = "test_fiat_shamir"))]
use lambdaworks_crypto::fiat_shamir::default_transcript::DefaultTranscript;
use lambdaworks_crypto::fiat_shamir::transcript::Transcript;
#[cfg(feature = "test_fiat_shamir")]
use lambdaworks_crypto::fiat_shamir::transcript::Transcript;
use lambdaworks_fft::roots_of_unity::get_powers_of_primitive_root_coset;
use lambdaworks_math::{
    field::{
        element::FieldElement,
        traits::{IsField, IsTwoAdicField},
    },
    helpers,
    polynomial::Polynomial,
    traits::ByteConversion,
};

struct DeepCompositionPolyArgs<'a, F: IsTwoAdicField> {
    root_order: u32,
    trace_term_coeffs: &'a [Vec<FieldElement<F>>],
    gamma_even: &'a FieldElement<F>,
    gamma_odd: &'a FieldElement<F>,
    d_evaluation_point: &'a FieldElement<F>,
    ood_evaluation_point: &'a FieldElement<F>,
    trace_poly_ood_evaluations: &'a Frame<F>,
    composition_poly_ood_evaluations: &'a [FieldElement<F>],
    deep_consistency_check: &'a DeepConsistencyCheck<F>,
}

pub fn verify<F: IsTwoAdicField, A: AIR<Field = F>>(proof: &StarkProof<F>, air: &A) -> bool
where
    FieldElement<F>: ByteConversion,
{
    #[cfg(not(feature = "test_fiat_shamir"))]
    let transcript = &mut DefaultTranscript::new();
    #[cfg(feature = "test_fiat_shamir")]
    let transcript = &mut TestTranscript::new();

    // BEGIN TRACE <-> Composition poly consistency evaluation check

    let trace_poly_ood_evaluations = &proof.trace_ood_frame_evaluations;

    // These are H_1(z^2) and H_2(z^2)
    let composition_poly_ood_evaluations = &proof.composition_poly_ood_evaluations;

    let root_order = air.context().trace_length.trailing_zeros();
    let trace_primitive_root = F::get_primitive_root_of_unity(root_order as u64).unwrap();

    let trace_roots_of_unity = get_powers_of_primitive_root_coset(
        root_order as u64,
        air.context().trace_length,
        &FieldElement::<F>::one(),
    )
    .unwrap();

    let boundary_constraints = air.boundary_constraints();

    let n_trace_cols = air.context().trace_columns;

    let boundary_constraint_domains =
        boundary_constraints.generate_roots_of_unity(&trace_primitive_root, n_trace_cols);
    let values = boundary_constraints.values(n_trace_cols);

    let lde_root_order =
        (air.context().trace_length * air.options().blowup_factor as usize).trailing_zeros();
    let lde_roots_of_unity_coset = get_powers_of_primitive_root_coset(
        lde_root_order as u64,
        air.context().trace_length * air.options().blowup_factor as usize,
        &FieldElement::<F>::from(air.options().coset_offset),
    )
    .unwrap();

    // Fiat-Shamir
    // we have to make sure that the result is not either
    // a root of unity or an element of the lde coset.
    let z = sample_z_ood(&lde_roots_of_unity_coset, &trace_roots_of_unity, transcript);

    let boundary_coeffs: Vec<(FieldElement<F>, FieldElement<F>)> = (0..n_trace_cols)
        .map(|_| {
            (
                transcript_to_field(transcript),
                transcript_to_field(transcript),
            )
        })
        .collect();

    let transition_coeffs: Vec<(FieldElement<F>, FieldElement<F>)> =
        (0..air.context().num_transition_constraints)
            .map(|_| {
                (
                    transcript_to_field(transcript),
                    transcript_to_field(transcript),
                )
            })
            .collect();

    // Following naming conventions from https://www.notamonadtutorial.com/diving-deep-fri/
    let mut boundary_c_i_evaluations = Vec::with_capacity(n_trace_cols);
    let mut boundary_quotient_degrees = Vec::with_capacity(n_trace_cols);

    for trace_idx in 0..n_trace_cols {
        let trace_evaluation = &trace_poly_ood_evaluations.get_row(0)[trace_idx];
        let boundary_constraints_domain = boundary_constraint_domains[trace_idx].clone();
        let boundary_interpolating_polynomial =
            &Polynomial::interpolate(&boundary_constraints_domain, &values[trace_idx]);

        let boundary_zerofier =
            boundary_constraints.compute_zerofier(&trace_primitive_root, trace_idx);

        let boundary_quotient_ood_evaluation = (trace_evaluation
            - boundary_interpolating_polynomial.evaluate(&z))
            / boundary_zerofier.evaluate(&z);

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
        .zip(boundary_coeffs)
        .map(|((poly_eval, poly_degree), (alpha, beta))| {
            poly_eval * (&alpha * z.pow(max_degree_power_of_two - poly_degree as u64) + &beta)
        })
        .collect();

    let boundary_quotient_ood_evaluation = boundary_quotient_ood_evaluations
        .iter()
        .fold(FieldElement::<F>::zero(), |acc, x| acc + x);

    let transition_ood_frame_evaluations = air.compute_transition(trace_poly_ood_evaluations);

    let transition_c_i_evaluations =
        ConstraintEvaluator::compute_constraint_composition_poly_evaluations(
            air,
            &transition_ood_frame_evaluations,
            &transition_coeffs,
            max_degree_power_of_two,
            &z,
        );

    let composition_poly_ood_evaluation = &boundary_quotient_ood_evaluation
        + transition_c_i_evaluations
            .iter()
            .fold(FieldElement::<F>::zero(), |acc, evaluation| {
                acc + evaluation
            });

    let composition_poly_claimed_ood_evaluation =
        &composition_poly_ood_evaluations[0] + &z * &composition_poly_ood_evaluations[1];

    if composition_poly_claimed_ood_evaluation != composition_poly_ood_evaluation {
        return false;
    }

    // // END TRACE <-> Composition poly consistency evaluation check

    let lde_root_order =
        (air.context().trace_length * air.options().blowup_factor as usize).trailing_zeros();

    // Get the number of trace terms the DEEP composition poly will have.
    // One coefficient will be sampled for each of them.
    // TODO: try remove this, call transcript inside for and move gamma declarations
    let trace_term_coeffs = &(0..trace_poly_ood_evaluations.num_columns())
        .map(|_| {
            (0..trace_poly_ood_evaluations.num_rows())
                .map(|_| transcript_to_field(transcript))
                .collect()
        })
        .collect::<Vec<Vec<FieldElement<F>>>>();

    // Get coefficients for even and odd terms of the composition polynomial H(x)
    let gamma_even = &transcript_to_field::<F, _>(transcript);
    let gamma_odd = &transcript_to_field::<F, _>(transcript);

    // construct vector of betas
    let mut beta_list = Vec::new();
    let count_betas = proof.fri_layers_merkle_roots.len() - 1;

    for (i, merkle_roots) in proof.fri_layers_merkle_roots.iter().enumerate() {
        let root = merkle_roots.clone();
        let root_bytes = root.to_bytes_be();
        transcript.append(&root_bytes);

        if i < count_betas {
            let beta = transcript_to_field(transcript);
            beta_list.push(beta);
        }
    }

    // DEEP consistency check
    // 1. Verify that Deep(x) is constructed correctly
    let last_evaluation = &proof.query_list[0].fri_decommitment.last_layer_evaluation;
    let last_evaluation_bytes = last_evaluation.to_bytes_be();
    transcript.append(&last_evaluation_bytes);

    let q_0 = transcript_to_usize(transcript) % (2_usize.pow(lde_root_order));
    transcript.append(&q_0.to_be_bytes());

    let deep_composition_poly_args = &mut DeepCompositionPolyArgs {
        root_order,
        trace_term_coeffs,
        gamma_even,
        gamma_odd,
        d_evaluation_point: &lde_roots_of_unity_coset[q_0],
        ood_evaluation_point: &z,
        trace_poly_ood_evaluations,
        composition_poly_ood_evaluations,
        deep_consistency_check: &proof.deep_consistency_check,
    };

    let deep_poly_evaluation = compare_deep_composition_poly(deep_composition_poly_args);
    let deep_poly_claimed_evaluation = &proof.query_list[0].fri_decommitment.layer_evaluations[0].0;

    if deep_poly_claimed_evaluation != &deep_poly_evaluation {
        return false;
    }

    // 2. Verify that t(x_0) is a trace evaluation
    // 3. Verify first layer of FRI
    if !verify_trace_evaluations(
        &proof.deep_consistency_check,
        q_0,
        &lde_roots_of_unity_coset,
    ) || !verify_query(
        air,
        &proof.fri_layers_merkle_roots,
        &beta_list,
        q_0,
        &proof.query_list[0].fri_decommitment,
        lde_root_order,
    ) {
        return false;
    }

    // Verify 1..n layers of FRI
    let mut result = true;
    for proof_i in proof.query_list.iter().skip(1) {
        let q_i = transcript_to_usize(transcript) % (2_usize.pow(lde_root_order));
        transcript.append(&q_i.to_be_bytes());

        // this is done in constant time
        result &= verify_query(
            air,
            &proof.fri_layers_merkle_roots,
            &beta_list,
            q_i,
            &proof_i.fri_decommitment,
            lde_root_order,
        );
    }
    result
}

fn verify_query<F: IsField + IsTwoAdicField, A: AIR<Field = F>>(
    air: &A,
    fri_layers_merkle_roots: &[FieldElement<F>],
    beta_list: &[FieldElement<F>],
    q_i: usize,
    fri_decommitment: &FriDecommitment<F>,
    lde_root_order: u32,
) -> bool
where
    FieldElement<F>: ByteConversion,
{
    let mut lde_primitive_root = F::get_primitive_root_of_unity(lde_root_order as u64).unwrap();
    let mut offset = FieldElement::<F>::from(air.options().coset_offset);

    // For each fri layer merkle proof check:
    // That each merkle path verifies

    // Sample beta with fiat shamir
    // Compute v = [P_i(z_i) + P_i(-z_i)] / 2 + beta * [P_i(z_i) - P_i(-z_i)] / (2 * z_i)
    // Where P_i is the folded polynomial of the i-th fiat shamir round
    // z_i is obtained from the first z (that was derived through fiat-shamir) through a known calculation
    // The calculation is, given the index, index % length_of_evaluation_domain

    // Check that v = P_{i+1}(z_i)

    // For each (merkle_root, merkle_auth_path) / fold
    // With the auth path containining the element that the
    // path proves it's existance
    for (
        index,
        (
            layer_number,
            (
                fri_layer_merkle_root,
                (
                    (fri_layer_auth_path, fri_layer_auth_path_symmetric),
                    (auth_path_evaluation, auth_path_evaluation_symmetric),
                ),
            ),
        ),
    ) in fri_layers_merkle_roots
        .iter()
        .zip(
            fri_decommitment
                .layer_merkle_paths
                .iter()
                .zip(fri_decommitment.layer_evaluations.iter()),
        )
        .enumerate()
        // Since we always derive the current layer from the previous layer
        // We start with the second one, skipping the first, so previous is layer is the first one
        .skip(1)
        .enumerate()
    {
        // This is the current layer's evaluation domain length. We need it to know what the decommitment index for the current
        // layer is, so we can check the merkle paths at the right index.
        let current_layer_domain_length = 2_u64.pow(lde_root_order) as usize >> layer_number;

        let layer_evaluation_index = q_i % current_layer_domain_length;

        if !fri_layer_auth_path.verify(
            fri_layer_merkle_root,
            layer_evaluation_index,
            auth_path_evaluation,
            &HASHER,
        ) {
            return false;
        }

        let layer_evaluation_index_symmetric =
            (q_i + current_layer_domain_length / 2) % current_layer_domain_length;

        if !fri_layer_auth_path_symmetric.verify(
            fri_layer_merkle_root,
            layer_evaluation_index_symmetric,
            auth_path_evaluation_symmetric,
            &HASHER,
        ) {
            return false;
        }

        let beta = beta_list[index].clone();

        let (previous_auth_path_evaluation, previous_path_evaluation_symmetric) = fri_decommitment
            .layer_evaluations
            .get(layer_number - 1)
            // TODO: Check at the start of the FRI operation
            // if layer_merkle_paths has the right amount of elements
            .unwrap();

        // evaluation point = offset * w ^ i in the Stark literature
        let evaluation_point = &offset * lde_primitive_root.pow(q_i);

        // v is the calculated element for the
        // co linearity check
        let two = &FieldElement::<F>::from(2);
        let v = (previous_auth_path_evaluation + previous_path_evaluation_symmetric) / two
            + &beta * (previous_auth_path_evaluation - previous_path_evaluation_symmetric)
                / (two * evaluation_point);

        lde_primitive_root = lde_primitive_root.pow(2_usize);
        offset = offset.pow(2_usize);

        if v != *auth_path_evaluation {
            return false;
        }

        // On the last iteration, also check the provided last evaluation point.
        if layer_number == fri_layers_merkle_roots.len() - 1 {
            let last_evaluation_point = &offset * lde_primitive_root.pow(q_i);

            let last_v = (auth_path_evaluation + auth_path_evaluation_symmetric) / two
                + &beta * (auth_path_evaluation - auth_path_evaluation_symmetric)
                    / (two * &last_evaluation_point);

            if last_v != fri_decommitment.last_layer_evaluation {
                return false;
            }
        }
    }

    true
}

// Verify that Deep(x) has been built correctly
fn compare_deep_composition_poly<F: IsTwoAdicField>(
    args: &mut DeepCompositionPolyArgs<F>,
) -> FieldElement<F> {
    let primitive_root = &F::get_primitive_root_of_unity(args.root_order as u64).unwrap();

    let deep_consistency_check = args.deep_consistency_check;

    let mut trace_terms = FieldElement::zero();

    for (col_idx, coeff_row) in
        (0..args.trace_poly_ood_evaluations.num_columns()).zip(args.trace_term_coeffs)
    {
        for (row_idx, coeff) in (0..args.trace_poly_ood_evaluations.num_rows()).zip(coeff_row) {
            let poly_evaluation = (deep_consistency_check.lde_trace_evaluations[col_idx].clone()
                - args.trace_poly_ood_evaluations.get_row(row_idx)[col_idx].clone())
                / (args.d_evaluation_point
                    - args.ood_evaluation_point * primitive_root.pow(row_idx as u64));

            trace_terms += poly_evaluation * coeff.clone();
        }
    }

    let ood_point_squared = &(args.ood_evaluation_point * args.ood_evaluation_point);

    let even_composition_poly_evaluation = (&deep_consistency_check.composition_poly_evaluations
        [0]
        - &args.composition_poly_ood_evaluations[0])
        / (args.d_evaluation_point - ood_point_squared);

    let odd_composition_poly_evaluation = (&deep_consistency_check.composition_poly_evaluations[1]
        - &args.composition_poly_ood_evaluations[1])
        / (args.d_evaluation_point - ood_point_squared);

    trace_terms
        + even_composition_poly_evaluation * args.gamma_even
        + odd_composition_poly_evaluation * args.gamma_odd
}

// Verifies that t(x_0) is a trace evaluation
fn verify_trace_evaluations<F: IsField + IsTwoAdicField>(
    deep_consistency_check: &DeepConsistencyCheck<F>,
    q_i: usize,
    domain: &[FieldElement<F>],
) -> bool
where
    FieldElement<F>: ByteConversion,
{
    for ((merkle_root, merkle_proof), evaluation) in deep_consistency_check
        .lde_trace_merkle_roots
        .iter()
        .zip(&deep_consistency_check.lde_trace_merkle_proofs)
        .zip(&deep_consistency_check.lde_trace_evaluations)
    {
        let index = q_i % domain.len();

        if !merkle_proof.verify(merkle_root, index, evaluation, &HASHER) {
            return false;
        }
    }

    true
}
