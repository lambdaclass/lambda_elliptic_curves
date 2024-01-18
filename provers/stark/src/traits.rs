use itertools::Itertools;
use lambdaworks_math::{
    fft::cpu::roots_of_unity::get_powers_of_primitive_root_coset,
    field::{
        element::FieldElement,
        traits::{IsFFTField, IsField, IsSubFieldOf},
    },
    polynomial::Polynomial,
};

use crate::transcript::IsStarkTranscript;

use super::{
    constraints::boundary::BoundaryConstraints, context::AirContext, frame::Frame,
    proof::options::ProofOptions, trace::TraceTable,
};

/// AIR is a representation of the Constraints
pub trait AIR {
    type Field: IsFFTField + IsSubFieldOf<Self::FieldExtension>;
    type FieldExtension: IsField;
    type RAPChallenges;
    type PublicInputs;

    const STEP_SIZE: usize;

    fn new(
        trace_length: usize,
        pub_inputs: &Self::PublicInputs,
        proof_options: &ProofOptions,
    ) -> Self;

    fn build_auxiliary_trace(
        &self,
        main_trace: &TraceTable<Self::Field>,
        rap_challenges: &Self::RAPChallenges,
    ) -> TraceTable<Self::FieldExtension>;

    fn build_rap_challenges(
        &self,
        transcript: &mut impl IsStarkTranscript<Self::FieldExtension>,
    ) -> Self::RAPChallenges;

    fn number_auxiliary_rap_columns(&self) -> usize;

    fn composition_poly_degree_bound(&self) -> usize;

    /// The method called by the prover to evaluate the transitions corresponding to an evaluation frame.
    /// In the case of the prover, the main evaluation table of the frame takes values in
    /// `Self::Field`, since they are the evaluations of the main trace at the LDE domain.
    fn compute_transition_prover(
        &self,
        frame: &Frame<Self::Field, Self::FieldExtension>,
        periodic_values: &[FieldElement<Self::Field>],
        rap_challenges: &Self::RAPChallenges,
    ) -> Vec<FieldElement<Self::FieldExtension>>;

    /// The method called by the verifier to evaluate the transitions at the out of domain frame.
    /// In the case of the verifier, both main and auxiliary tables of the evaluation frame take
    /// values in `Self::FieldExtension`, since they are the evaluations of the trace polynomials
    /// at the out of domain challenge.
    /// In case `Self::Field` coincides with `Self::FieldExtension`, this method and
    /// `compute_transition_prover` should return the same values.
    fn compute_transition_verifier(
        &self,
        frame: &Frame<Self::FieldExtension, Self::FieldExtension>,
        periodic_values: &[FieldElement<Self::FieldExtension>],
        rap_challenges: &Self::RAPChallenges,
    ) -> Vec<FieldElement<Self::FieldExtension>>;

    fn boundary_constraints(
        &self,
        rap_challenges: &Self::RAPChallenges,
    ) -> BoundaryConstraints<Self::FieldExtension>;

    fn transition_exemptions(&self) -> Vec<Polynomial<FieldElement<Self::FieldExtension>>> {
        let trace_length = self.trace_length();
        let roots_of_unity_order = trace_length.trailing_zeros();
        let roots_of_unity = get_powers_of_primitive_root_coset(
            roots_of_unity_order as u64,
            self.trace_length(),
            &FieldElement::<Self::Field>::one(),
        )
        .unwrap();
        let root_of_unity_len = roots_of_unity.len();

        let x = Polynomial::new_monomial(FieldElement::one(), 1);

        self.context()
            .transition_exemptions
            .iter()
            .unique_by(|elem| *elem)
            .filter(|v| *v > &0_usize)
            .map(|cant_take| {
                roots_of_unity
                    .iter()
                    .take(root_of_unity_len)
                    .rev()
                    .take(*cant_take)
                    .fold(
                        Polynomial::new_monomial(FieldElement::one(), 0),
                        |acc, root| acc * (&x - root),
                    )
            })
            .collect()
    }
    fn context(&self) -> &AirContext;

    fn trace_length(&self) -> usize;

    fn options(&self) -> &ProofOptions {
        &self.context().proof_options
    }

    fn blowup_factor(&self) -> u8 {
        self.options().blowup_factor
    }

    fn num_transition_constraints(&self) -> usize {
        self.context().num_transition_constraints
    }

    fn pub_inputs(&self) -> &Self::PublicInputs;

    fn transition_exemptions_verifier(
        &self,
        root: &FieldElement<Self::Field>,
    ) -> Vec<Polynomial<FieldElement<Self::FieldExtension>>> {
        let x =
            Polynomial::<FieldElement<Self::FieldExtension>>::new_monomial(FieldElement::one(), 1);

        let max = self
            .context()
            .transition_exemptions
            .iter()
            .max()
            .expect("has maximum");
        (1..=*max)
            .map(|index| {
                (1..=index).fold(
                    Polynomial::new_monomial(FieldElement::one(), 0),
                    |acc, k| acc * (&x - root.pow(k).to_extension()),
                )
            })
            .collect()
    }

    fn get_periodic_column_values(&self) -> Vec<Vec<FieldElement<Self::Field>>> {
        vec![]
    }

    fn get_periodic_column_polynomials(&self) -> Vec<Polynomial<FieldElement<Self::Field>>> {
        let mut result = Vec::new();
        for periodic_column in self.get_periodic_column_values() {
            let values: Vec<_> = periodic_column
                .iter()
                .cycle()
                .take(self.trace_length())
                .cloned()
                .collect();
            let poly =
                Polynomial::<FieldElement<Self::Field>>::interpolate_fft::<Self::Field>(&values)
                    .unwrap();
            result.push(poly);
        }
        result
    }
}
