use std::marker::PhantomData;

use crate::{
    constraints::boundary::{BoundaryConstraint, BoundaryConstraints},
    traits::AIR,
};
use lambdaworks_math::field::{
    element::FieldElement, fields::fft_friendly::stark_252_prime_field::Stark252PrimeField,
};
use winterfell::{Air, EvaluationFrame, FieldExtension, ProofOptions, TraceInfo, TraceTable, Trace, AuxTraceRandElements, TraceLayout};

#[derive(Clone)]
pub struct AirAdapterPublicInputs<A>
where
    A: Air<BaseField = FieldElement<Stark252PrimeField>>,
    A::PublicInputs: Clone,
{
    winterfell_public_inputs: A::PublicInputs,
    transition_degrees: Vec<usize>,
    transition_exemptions: Vec<usize>,
    transition_offsets: Vec<usize>,
    trace_info: TraceInfo,
    composition_poly_degree_bound: usize,
}

pub trait FromColumns<A> {
    fn from_cols(columns: Vec<Vec<A>>) -> Self;
}

impl FromColumns<FieldElement<Stark252PrimeField>> for TraceTable<FieldElement<Stark252PrimeField>> {
    fn from_cols(columns: Vec<Vec<FieldElement<Stark252PrimeField>>>) -> Self {
        TraceTable::init(columns)
    }
}

#[derive(Clone)]
pub struct AirAdapter<A, T>
where
    A: Air<BaseField = FieldElement<Stark252PrimeField>>,
    A::PublicInputs: Clone,
    T: Trace<BaseField=FieldElement<Stark252PrimeField>> + Clone + FromColumns<FieldElement<Stark252PrimeField>>,
{
    winterfell_air: A,
    public_inputs: AirAdapterPublicInputs<A>,
    air_context: crate::context::AirContext,
    phantom: PhantomData<T>
}

impl<A, T> AirAdapter<A, T>
where
    A: Air<BaseField = FieldElement<Stark252PrimeField>> + Clone,
    A::PublicInputs: Clone,
    T: Trace<BaseField=FieldElement<Stark252PrimeField>> + Clone + FromColumns<FieldElement<Stark252PrimeField>>,
{
    pub fn convert_winterfell_trace_table(
        trace: TraceTable<FieldElement<Stark252PrimeField>>,
    ) -> crate::trace::TraceTable<Stark252PrimeField> {
        let mut columns = Vec::new();
        for i in 0..trace.width() {
            columns.push(trace.get_column(i).to_owned());
        }

        crate::trace::TraceTable::from_columns(&columns)
    }
}

impl<A, T> AIR for AirAdapter<A, T>
where
    A: Air<BaseField = FieldElement<Stark252PrimeField>> + Clone,
    A::PublicInputs: Clone,
    T: Trace<BaseField=FieldElement<Stark252PrimeField>> + Clone + FromColumns<FieldElement<Stark252PrimeField>>,
{
    type Field = Stark252PrimeField;
    type RAPChallenges = Vec<FieldElement<Stark252PrimeField>>;
    type PublicInputs = AirAdapterPublicInputs<A>;

    fn new(
        trace_length: usize,
        pub_inputs: &Self::PublicInputs,
        lambda_proof_options: &crate::proof::options::ProofOptions,
    ) -> Self {
        let winter_proof_options = ProofOptions::new(
            lambda_proof_options.fri_number_of_queries,
            lambda_proof_options.blowup_factor as usize,
            lambda_proof_options.grinding_factor as u32,
            FieldExtension::None,
            2,
            0,
        );

        let winterfell_air = A::new(
            pub_inputs.trace_info.clone(),
            pub_inputs.winterfell_public_inputs.clone(),
            winter_proof_options,
        );
        let winterfell_context = winterfell_air.context();

        let lambda_context = crate::context::AirContext {
            proof_options: lambda_proof_options.clone(),
            transition_degrees: pub_inputs.transition_degrees.to_owned(),
            transition_exemptions: pub_inputs.transition_exemptions.to_owned(),
            transition_offsets: pub_inputs.transition_offsets.to_owned(),
            num_transition_constraints: winterfell_context.num_transition_constraints(),
            trace_columns: pub_inputs.trace_info.width(),
            num_transition_exemptions: winterfell_context.num_transition_exemptions(),
        };

        Self {
            winterfell_air,
            public_inputs: pub_inputs.clone(),
            air_context: lambda_context,
            phantom: PhantomData
        }
    }

    fn build_auxiliary_trace(
        &self,
        main_trace: &crate::trace::TraceTable<Self::Field>,
        rap_challenges: &Self::RAPChallenges,
    ) -> crate::trace::TraceTable<Self::Field> {
        // We only support one-stage RAP.
        if let Some(winter_trace) = T::from_cols(main_trace.columns()).build_aux_segment(&[], rap_challenges) {
            let mut columns = Vec::new();
            for i in 0..winter_trace.num_cols() {
                columns.push(winter_trace.get_column(i).to_owned());
            }
            crate::trace::TraceTable::from_columns(&columns)
        } else {
            crate::trace::TraceTable::empty()
        }
    }

    fn build_rap_challenges(
        &self,
        transcript: &mut impl crate::transcript::IsStarkTranscript<Self::Field>,
    ) -> Self::RAPChallenges {
        let trace_layout = self.winterfell_air.trace_layout();
        let num_segments = trace_layout.num_aux_segments();

        if num_segments == 1 {
            let mut result = Vec::new();
            for _ in 0..trace_layout.get_aux_segment_rand_elements(0) {
                result.push(transcript.sample_field_element());
            }
            result
        } else if num_segments == 0 {
            Vec::new()
        } else {
            panic!("The winterfell adapter does not support AIR's with more than one auxiliary segment");
        }
    }

    fn number_auxiliary_rap_columns(&self) -> usize {
        self.winterfell_air.trace_layout().aux_trace_width()
    }

    fn composition_poly_degree_bound(&self) -> usize {
        self.public_inputs.composition_poly_degree_bound
    }

    fn compute_transition(
        &self,
        frame: &crate::frame::Frame<Self::Field>,
        rap_challenges: &Self::RAPChallenges,
    ) -> Vec<FieldElement<Self::Field>> {
        let num_aux_columns = self.number_auxiliary_rap_columns();
        let num_main_columns = self.context().trace_columns - num_aux_columns;

        let main_frame = EvaluationFrame::from_rows(
            frame.get_row(0)[..num_main_columns].to_vec(),
            frame.get_row(1)[..num_main_columns].to_vec()
        );

        let mut main_result = vec![FieldElement::zero(); self.winterfell_air.context().num_main_transition_constraints()];
        self.winterfell_air
            .evaluate_transition::<FieldElement<Stark252PrimeField>>(&main_frame, &[], &mut main_result); // Periodic values not supported

        if self.winterfell_air.trace_layout().num_aux_segments() == 1 {
            let mut rand_elements = AuxTraceRandElements::new();
            rand_elements.add_segment_elements(rap_challenges.clone());

            let aux_frame = EvaluationFrame::from_rows(
                frame.get_row(0)[num_main_columns..].to_vec(),
                frame.get_row(1)[num_main_columns..].to_vec()
            );
            
            let mut aux_result = vec![FieldElement::zero(); self.winterfell_air.context().num_aux_transition_constraints()];
            self.winterfell_air.evaluate_aux_transition(
                &main_frame,
                &aux_frame,
                &[],
                &rand_elements,
                &mut aux_result
            );

            main_result.extend_from_slice(&aux_result);
        }
        main_result
    }

    fn boundary_constraints(
        &self,
        rap_challenges: &Self::RAPChallenges,
    ) -> crate::constraints::boundary::BoundaryConstraints<Self::Field> {
        let mut result = Vec::new();
        for assertion in self.winterfell_air.get_assertions() {
            assert!(assertion.is_single());
            result.push(BoundaryConstraint::new(
                assertion.column(),
                assertion.first_step(),
                assertion.values()[0],
            ));
        }

        let mut rand_elements = AuxTraceRandElements::new();
        rand_elements.add_segment_elements(rap_challenges.clone());

        for assertion in self.winterfell_air.get_aux_assertions(&rand_elements) {
            assert!(assertion.is_single());
            result.push(BoundaryConstraint::new(
                assertion.column(),
                assertion.first_step(),
                assertion.values()[0],
            ));
        }

        BoundaryConstraints::from_constraints(result)
    }

    fn context(&self) -> &crate::context::AirContext {
        &self.air_context
    }

    fn trace_length(&self) -> usize {
        self.winterfell_air.context().trace_len()
    }

    fn pub_inputs(&self) -> &Self::PublicInputs {
        &self.public_inputs
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        proof::options::ProofOptions,
        prover::{IsStarkProver, Prover},
        transcript::StoneProverTranscript,
        verifier::{IsStarkVerifier, Verifier},
        winterfell_adapter::examples::{fibonacci_2_terms::{FibAir2Terms, self}, fibonacci_rap::{FibonacciRAP, self, RapTraceTable}},
    };

    #[test]
    fn prove_and_verify_a_winterfell_fibonacci_2_terms_air() {
        let lambda_proof_options = ProofOptions::default_test_options();
        let trace = AirAdapter::<FibAir2Terms, TraceTable<_>>::convert_winterfell_trace_table(fibonacci_2_terms::build_trace(16));
        let pub_inputs = AirAdapterPublicInputs {
            winterfell_public_inputs: trace.columns()[1][7],
            transition_degrees: vec![1, 1],
            transition_exemptions: vec![1, 1],
            transition_offsets: vec![0, 1],
            composition_poly_degree_bound: 8,
            trace_info: TraceInfo::new(2, 8)
        };

        let proof = Prover::prove::<AirAdapter<FibAir2Terms, TraceTable<_>>>(
            &trace,
            &pub_inputs,
            &lambda_proof_options,
            StoneProverTranscript::new(&[]),
        )
        .unwrap();
        assert!(Verifier::verify::<AirAdapter<FibAir2Terms, TraceTable<_>>>(
            &proof,
            &pub_inputs,
            &lambda_proof_options,
            StoneProverTranscript::new(&[]),
        ));
    }

    #[test]
    fn prove_and_verify_a_winterfell_fibonacci_rap_air() {
        let lambda_proof_options = ProofOptions::default_test_options();
        let trace = AirAdapter::<FibonacciRAP, RapTraceTable<_>>::convert_winterfell_trace_table(fibonacci_rap::build_trace(16));
        let trace_layout = TraceLayout::new(3, [1], [1]);
        let trace_info = TraceInfo::new_multi_segment(trace_layout, 16, vec![]);
        let fibonacci_result =  trace.columns()[1][15];
        let pub_inputs = AirAdapterPublicInputs {
            winterfell_public_inputs: fibonacci_result,
            transition_degrees: vec![1, 1, 2],
            transition_exemptions: vec![1, 1, 1],
            transition_offsets: vec![0, 1],
            composition_poly_degree_bound: 32,
            trace_info
        };

        let proof = Prover::prove::<AirAdapter<FibonacciRAP, RapTraceTable<_>>>(
            &trace,
            &pub_inputs,
            &lambda_proof_options,
            StoneProverTranscript::new(&[]),
        )
        .unwrap();
        assert!(Verifier::verify::<AirAdapter<FibonacciRAP, RapTraceTable<_>>>(
            &proof,
            &pub_inputs,
            &lambda_proof_options,
            StoneProverTranscript::new(&[]),
        ));
    }
}
