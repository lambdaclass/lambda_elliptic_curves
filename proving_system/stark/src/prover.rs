use lambdaworks_crypto::fiat_shamir::transcript::Transcript;
use lambdaworks_math::{
    field::{
        element::FieldElement,
        traits::{IsField, IsTwoAdicField},
    },
    polynomial::{self, Polynomial},
    traits::ByteConversion,
};

use crate::{transcript_to_field, transcript_to_usize, StarkProof};

use super::{
    air::{constraints::evaluator::ConstraintEvaluator, frame::Frame, trace::TraceTable, AIR},
    fri::{fri, fri_decommit::fri_decommit_layers},
    sample_z_ood, StarkQueryProof,
};

// FIXME remove unwrap() calls and return errors
pub fn prove<F: IsField + IsTwoAdicField, A: AIR + AIR<Field = F>>(
    trace: &[FieldElement<F>],
    air: &A,
) -> StarkProof<F>
where
    FieldElement<F>: ByteConversion,
{
    let transcript = &mut Transcript::new();
    let mut query_list = Vec::<StarkQueryProof<F>>::new();

    let root_order = air.context().trace_length.trailing_zeros();
    // * Generate Coset
    let trace_primitive_root = F::get_primitive_root_of_unity(root_order as u64).unwrap();

    let trace_roots_of_unity = F::get_powers_of_primitive_root_coset(
        root_order as u64,
        air.context().trace_length,
        &FieldElement::<F>::one(),
    )
    .unwrap();

    let lde_root_order =
        (air.context().trace_length * air.options().blowup_factor as usize).trailing_zeros();
    let lde_roots_of_unity_coset = F::get_powers_of_primitive_root_coset(
        lde_root_order as u64,
        air.context().trace_length * air.options().blowup_factor as usize,
        &FieldElement::<F>::from(air.options().coset_offset),
    )
    .unwrap();

    let trace_poly = Polynomial::interpolate(&trace_roots_of_unity, trace);
    let lde_trace = trace_poly.evaluate_slice(&lde_roots_of_unity_coset);

    // Fiat-Shamir
    // z is the Out of domain evaluation point used in Deep FRI. It needs to be a point outside
    // of both the roots of unity and its corresponding coset used for the lde commitment.
    let z = sample_z_ood(&lde_roots_of_unity_coset, &trace_roots_of_unity, transcript);

    let z_squared = &z * &z;

    let lde_trace = TraceTable::new(lde_trace, 1);

    // Create evaluation table
    let evaluator = ConstraintEvaluator::new(air, &trace_poly, &trace_primitive_root);

    let alpha_boundary = transcript_to_field(transcript);
    let beta_boundary = transcript_to_field(transcript);
    let alpha = transcript_to_field(transcript);
    let beta = transcript_to_field(transcript);

    let alpha_and_beta_transition_coefficients = vec![(alpha, beta)];
    let constraint_evaluations = evaluator.evaluate(
        &lde_trace,
        &lde_roots_of_unity_coset,
        &alpha_and_beta_transition_coefficients,
        (&alpha_boundary, &beta_boundary),
    );

    // Get composition poly
    let composition_poly =
        constraint_evaluations.compute_composition_poly(&lde_roots_of_unity_coset);

    let (composition_poly_even, composition_poly_odd) = composition_poly.even_odd_decomposition();
    // Evaluate H_1 and H_2 in z^2.
    let composition_poly_evaluations = vec![
        composition_poly_even.evaluate(&z_squared),
        composition_poly_odd.evaluate(&z_squared),
    ];

    let trace_ood_frame_evaluations = Frame::<F>::construct_ood_frame(
        &[trace_poly.clone()],
        &z,
        &air.context().transition_offsets,
        &trace_primitive_root,
    );

    // END EVALUATION BLOCK

    // Compute DEEP composition polynomial so we can commit to it using FRI.
    let mut deep_composition_poly = compute_deep_composition_poly(
        &trace_poly,
        &composition_poly_even,
        &composition_poly_odd,
        &z,
        &trace_primitive_root,
    );

    // * Do FRI on the composition polynomials
    let lde_fri_commitment = fri(
        &mut deep_composition_poly,
        &lde_roots_of_unity_coset,
        transcript,
    );

    let fri_layers_merkle_roots: Vec<FieldElement<F>> = lde_fri_commitment
        .iter()
        .map(|fri_commitment| fri_commitment.merkle_tree.root.clone())
        .collect();

    for _i in 0..air.context().options.fri_number_of_queries {
        // * Sample q_1, ..., q_m using Fiat-Shamir
        let q_i: usize = transcript_to_usize(transcript) % 2_usize.pow(lde_root_order);
        transcript.append(&q_i.to_be_bytes());

        // * For every q_i, do FRI decommitment
        let fri_decommitment = fri_decommit_layers(&lde_fri_commitment, q_i);

        query_list.push(StarkQueryProof {
            fri_layers_merkle_roots: fri_layers_merkle_roots.clone(),
            fri_decommitment,
        });
    }

    let fri_layers_merkle_roots: Vec<FieldElement<F>> = lde_fri_commitment
        .iter()
        .map(|fri_commitment| fri_commitment.merkle_tree.root.clone())
        .collect();

    StarkProof {
        fri_layers_merkle_roots,
        trace_ood_frame_evaluations,
        composition_poly_evaluations,
        query_list,
    }
}

/// Returns the DEEP composition polynomial that the prover then commits to using
/// FRI. This polynomial is a linear combination of the trace polynomial and the
/// composition polynomial, with coefficients sampled by the verifier (i.e. using Fiat-Shamir).
fn compute_deep_composition_poly<F: IsField>(
    trace_poly: &Polynomial<FieldElement<F>>,
    even_composition_poly: &Polynomial<FieldElement<F>>,
    odd_composition_poly: &Polynomial<FieldElement<F>>,
    ood_evaluation_point: &FieldElement<F>,
    primitive_root: &FieldElement<F>,
) -> Polynomial<FieldElement<F>> {
    // TODO: Fiat-Shamir
    let gamma_1 = FieldElement::one();
    let gamma_2 = FieldElement::one();
    let gamma_3 = FieldElement::one();
    let gamma_4 = FieldElement::one();

    let first_term = (trace_poly.clone()
        - Polynomial::new_monomial(trace_poly.evaluate(ood_evaluation_point), 0))
        / (Polynomial::new_monomial(FieldElement::one(), 1)
            - Polynomial::new_monomial(ood_evaluation_point.clone(), 0));
    let second_term = (trace_poly.clone()
        - Polynomial::new_monomial(
            trace_poly.evaluate(&(ood_evaluation_point * primitive_root)),
            0,
        ))
        / (Polynomial::new_monomial(FieldElement::one(), 1)
            - Polynomial::new_monomial(ood_evaluation_point * primitive_root, 0));

    // Evaluate in X^2
    let even_composition_poly = polynomial::compose(
        even_composition_poly,
        &Polynomial::new_monomial(FieldElement::one(), 2),
    );
    let odd_composition_poly = polynomial::compose(
        odd_composition_poly,
        &Polynomial::new_monomial(FieldElement::one(), 2),
    );

    let third_term = (even_composition_poly.clone()
        - Polynomial::new_monomial(
            even_composition_poly.evaluate(&ood_evaluation_point.clone()),
            0,
        ))
        / (Polynomial::new_monomial(FieldElement::one(), 1)
            - Polynomial::new_monomial(ood_evaluation_point * ood_evaluation_point, 0));
    let fourth_term = (odd_composition_poly.clone()
        - Polynomial::new_monomial(odd_composition_poly.evaluate(ood_evaluation_point), 0))
        / (Polynomial::new_monomial(FieldElement::one(), 1)
            - Polynomial::new_monomial(ood_evaluation_point * ood_evaluation_point, 0));

    first_term * gamma_1 + second_term * gamma_2 + third_term * gamma_3 + fourth_term * gamma_4
}
