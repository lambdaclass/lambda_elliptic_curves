use crate::{
    air::{
        self,
        constraints::boundary::{BoundaryConstraint, BoundaryConstraints},
        context::AirContext,
        trace::TraceTable,
        AIR,
    },
    fri::FieldElement,
};
use lambdaworks_crypto::fiat_shamir::transcript::Transcript;
use lambdaworks_math::field::{
    fields::fft_friendly::stark_252_prime_field::Stark252PrimeField, traits::IsField,
};

#[derive(Clone)]
pub struct QuadraticAIR {
    context: AirContext,
}

impl From<AirContext> for QuadraticAIR {
    fn from(context: AirContext) -> Self {
        Self { context }
    }
}

impl AIR for QuadraticAIR {
    type Field = Stark252PrimeField;
    type RawTrace = Vec<FieldElement<Self::Field>>;
    type RAPChallenges = ();

    fn build_main_trace(raw_trace: &Self::RawTrace) -> TraceTable<Self::Field> {
        TraceTable {
            table: raw_trace.clone(),
            n_cols: 1,
        }
    }

    fn build_auxiliary_trace(
        _main_trace: &TraceTable<Self::Field>,
        _rap_challenges: &Self::RAPChallenges,
    ) -> TraceTable<Self::Field> {
        TraceTable::empty()
    }

    fn build_rap_challenges<T: Transcript>(_transcript: &mut T) -> Self::RAPChallenges {}

    fn compute_transition(
        &self,
        frame: &air::frame::Frame<Self::Field>,
        _rap_challenges: &Self::RAPChallenges,
    ) -> Vec<FieldElement<Self::Field>> {
        let first_row = frame.get_row(0);
        let second_row = frame.get_row(1);

        vec![&second_row[0] - &first_row[0] * &first_row[0]]
    }

    fn boundary_constraints(
        &self,
        _rap_challenges: &Self::RAPChallenges,
    ) -> BoundaryConstraints<Self::Field> {
        let a0 = BoundaryConstraint::new_simple(0, FieldElement::<Self::Field>::from(3));

        BoundaryConstraints::from_constraints(vec![a0])
    }

    fn context(&self) -> air::context::AirContext {
        self.context.clone()
    }
}

pub fn quadratic_trace<F: IsField>(
    initial_value: FieldElement<F>,
    trace_length: usize,
) -> Vec<FieldElement<F>> {
    let mut ret: Vec<FieldElement<F>> = vec![];

    ret.push(initial_value);

    for i in 1..(trace_length) {
        ret.push(ret[i - 1].clone() * ret[i - 1].clone());
    }

    ret
}
