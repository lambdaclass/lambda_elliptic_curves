use lambdaworks_crypto::fiat_shamir::transcript::Transcript;
use lambdaworks_math::{
    field::{
        element::FieldElement,
        traits::{IsField, IsTwoAdicField},
    },
    polynomial::Polynomial,
    traits::ByteConversion,
};

use crate::{transcript_to_field, transcript_to_usize, StarkProof};

use super::{
    air::{
        constraints::{evaluator::ConstraintEvaluator, helpers},
        AIR,
    },
    fri::fri_decommit::FriDecommitment,
    COSET_OFFSET,
};

pub fn verify<F: IsField + IsTwoAdicField, A: AIR + AIR<Field = F>>(
    proof: &StarkProof<F>,
    air: &A,
) -> bool
where
    FieldElement<F>: ByteConversion,
{
    let transcript = &mut Transcript::new();

    // BEGIN TRACE <-> Composition poly consistency evaluation check

    let trace_poly_ood_frame_evaluations = &proof.trace_ood_frame_evaluations;

    // These are H_1(z^2) and H_2(z^2)
    let composition_poly_evaluations = &proof.composition_poly_evaluations;

    let root_order = air.context().trace_length.trailing_zeros();
    let trace_primitive_root = F::get_primitive_root_of_unity(root_order as u64).unwrap();

    let boundary_constraints = air.compute_boundary_constraints();

    // TODO: Fiat-Shamir
    let z = FieldElement::<F>::from(2);
    // TODO: The reason this is commented is we can't just call this function, we have to make sure that the result
    // is not either a root of unity or an element of the lde coset.
    // let z = transcript_to_field(transcript);

    let domain = boundary_constraints.generate_roots_of_unity(&trace_primitive_root);
    // TODO: this assumes one column
    let values = boundary_constraints.values(0);

    // The boundary constraint polynomial is trace - this polynomial below.
    let boundary_interpolating_polynomial = &Polynomial::interpolate(&domain, &values);
    let boundary_zerofier = boundary_constraints.compute_zerofier(&trace_primitive_root);

    let boundary_alpha = transcript_to_field(transcript);
    let boundary_beta = transcript_to_field(transcript);
    // TODO: these are hardcoded to one column, there should be one alpha and beta per column
    let alpha = transcript_to_field(transcript);
    let beta = transcript_to_field(transcript);

    let max_degree =
        air.context().trace_length * air.context().transition_degrees().iter().max().unwrap();

    let max_degree_power_of_two = helpers::next_power_of_two(max_degree as u64);

    // TODO: This is assuming one column
    let mut boundary_quotient_ood_evaluation = &trace_poly_ood_frame_evaluations.get_row(0)[0]
        - boundary_interpolating_polynomial.evaluate(&z);

    boundary_quotient_ood_evaluation = boundary_quotient_ood_evaluation
        * (&boundary_alpha
            * z.pow(max_degree_power_of_two - (air.context().trace_length as u64 - 1))
            + &boundary_beta);

    boundary_quotient_ood_evaluation =
        boundary_quotient_ood_evaluation / boundary_zerofier.evaluate(&z);

    let transition_ood_frame_evaluations = air.compute_transition(trace_poly_ood_frame_evaluations);

    let alpha_and_beta_transition_coefficients = vec![(alpha, beta)];

    let c_i_evaluations = ConstraintEvaluator::compute_constraint_composition_poly_evaluations(
        air,
        &transition_ood_frame_evaluations,
        &alpha_and_beta_transition_coefficients,
        max_degree_power_of_two,
        &z,
    );

    let composition_poly_ood_evaluation = &boundary_quotient_ood_evaluation
        + c_i_evaluations
            .iter()
            .fold(FieldElement::<F>::zero(), |acc, evaluation| {
                acc + evaluation
            });

    let composition_poly_claimed_ood_evaluation =
        &composition_poly_evaluations[0] + &z * &composition_poly_evaluations[1];

    if composition_poly_claimed_ood_evaluation != composition_poly_ood_evaluation {
        return false;
    }

    // // END TRACE <-> Composition poly consistency evaluation check

    let lde_root_order =
        (air.context().trace_length * air.options().blowup_factor as usize).trailing_zeros();

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

    let mut result = true;
    for proof_i in &proof.query_list {
        let last_evaluation = &proof_i.fri_decommitment.last_layer_evaluation;
        let last_evaluation_bytes = last_evaluation.to_bytes_be();
        transcript.append(&last_evaluation_bytes);

        let q_i: usize = transcript_to_usize(transcript) % (2_usize.pow(lde_root_order));
        transcript.append(&q_i.to_be_bytes());

        let fri_decommitment = &proof_i.fri_decommitment;

        // this is done in constant time
        result &= verify_query(
            &proof.fri_layers_merkle_roots,
            &beta_list,
            q_i,
            fri_decommitment,
            lde_root_order,
        );
    }
    result
}

pub fn verify_query<F: IsField + IsTwoAdicField>(
    fri_layers_merkle_roots: &[FieldElement<F>],
    beta_list: &[FieldElement<F>],
    q_i: usize,
    fri_decommitment: &FriDecommitment<F>,
    lde_root_order: u32,
) -> bool {
    let mut lde_primitive_root = F::get_primitive_root_of_unity(lde_root_order as u64).unwrap();
    let mut offset = FieldElement::<F>::from(COSET_OFFSET);

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
        ) {
            return false;
        }

        let layer_evaluation_index_symmetric =
            (q_i + current_layer_domain_length) % current_layer_domain_length;

        if !fri_layer_auth_path_symmetric.verify(
            fri_layer_merkle_root,
            layer_evaluation_index_symmetric,
            auth_path_evaluation_symmetric,
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
