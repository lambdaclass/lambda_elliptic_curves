use crate::adapter::air::FromColumns;
use crate::field_element::element::AdapterFieldElement;
use crate::utils::vec_field2adapter;
use lambdaworks_math::field::element::FieldElement;
use rand::seq::SliceRandom;
use rand::thread_rng;
use winter_utils::{collections::Vec, uninit_vector};
use winterfell::math::FieldElement as IsWinterfellFieldElement;
use winterfell::{math::StarkField, matrix::ColMatrix, Trace, TraceLayout};
use winterfell::{
    Air, AirContext, Assertion, EvaluationFrame, ProofOptions, TraceInfo, TraceTable,
    TransitionConstraintDegree,
};

#[derive(Clone)]
pub struct RapTraceTable<B: StarkField> {
    layout: TraceLayout,
    trace: ColMatrix<B>,
    meta: Vec<u8>,
}

impl<B: StarkField> RapTraceTable<B> {
    pub fn new(width: usize, length: usize) -> Self {
        let columns = unsafe { (0..width).map(|_| uninit_vector(length)).collect() };
        Self {
            layout: TraceLayout::new(width, [3], [3]),
            trace: ColMatrix::new(columns),
            meta: vec![],
        }
    }

    pub fn init(columns: Vec<Vec<B>>) -> Self {
        let trace_length = columns[0].len();

        for column in columns.iter().skip(1) {
            assert_eq!(
                column.len(),
                trace_length,
                "all columns traces must have the same length"
            );
        }

        Self {
            layout: TraceLayout::new(columns.len(), [0], [0]),
            trace: ColMatrix::new(columns),
            meta: vec![],
        }
    }

    pub fn fill<I, U>(&mut self, init: I, update: U)
    where
        I: Fn(&mut [B]),
        U: Fn(usize, &mut [B]),
    {
        let mut state = vec![B::ZERO; self.main_trace_width()];
        init(&mut state);
        self.update_row(0, &state);

        for i in 0..self.length() - 1 {
            update(i, &mut state);
            self.update_row(i + 1, &state);
        }
    }

    pub fn update_row(&mut self, step: usize, state: &[B]) {
        self.trace.update_row(step, state);
    }

    pub fn width(&self) -> usize {
        self.main_trace_width()
    }

    pub fn get(&self, column: usize, step: usize) -> B {
        self.trace.get(column, step)
    }

    pub fn read_row_into(&self, step: usize, target: &mut [B]) {
        self.trace.read_row_into(step, target);
    }
}

impl<B: StarkField> Trace for RapTraceTable<B> {
    type BaseField = B;

    fn layout(&self) -> &TraceLayout {
        &self.layout
    }

    fn length(&self) -> usize {
        self.trace.num_rows()
    }

    fn meta(&self) -> &[u8] {
        &self.meta
    }

    fn read_main_frame(&self, row_idx: usize, frame: &mut EvaluationFrame<Self::BaseField>) {
        let next_row_idx = (row_idx + 1) % self.length();
        self.trace.read_row_into(row_idx, frame.current_mut());
        self.trace.read_row_into(next_row_idx, frame.next_mut());
    }

    fn main_segment(&self) -> &ColMatrix<B> {
        &self.trace
    }

    fn build_aux_segment<E>(
        &mut self,
        aux_segments: &[ColMatrix<E>],
        rand_elements: &[E],
    ) -> Option<ColMatrix<E>>
    where
        E: IsWinterfellFieldElement<BaseField = Self::BaseField>,
    {
        // We only have one auxiliary segment for this example
        if !aux_segments.is_empty() {
            return None;
        }

        let mut rap_column = vec![E::ZERO; self.length()];
        let gamma = rand_elements[0];

        rap_column[0] = (<B as Into<E>>::into(self.get(0, 0)) + gamma)
            / (<B as Into<E>>::into(self.get(2, 0)) + gamma);
        for step in 1..self.length() {
            rap_column[step] = (<B as Into<E>>::into(self.get(0, step)) + gamma)
                / (<B as Into<E>>::into(self.get(2, step)) + gamma)
                * rap_column[step - 1];
        }

        Some(ColMatrix::new(vec![rap_column]))
    }
}

impl FromColumns<AdapterFieldElement> for RapTraceTable<AdapterFieldElement> {
    fn from_cols(columns: Vec<Vec<AdapterFieldElement>>) -> Self {
        RapTraceTable::init(columns)
    }
}

#[derive(Clone)]
pub struct FibonacciRAP {
    context: AirContext<AdapterFieldElement>,
    result: AdapterFieldElement,
}

impl Air for FibonacciRAP {
    type BaseField = AdapterFieldElement;
    type PublicInputs = AdapterFieldElement;

    fn new(trace_info: TraceInfo, pub_inputs: Self::BaseField, options: ProofOptions) -> Self {
        let degrees = vec![
            TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::new(1),
        ];
        let aux_degrees = vec![TransitionConstraintDegree::new(2)];
        FibonacciRAP {
            context: AirContext::new_multi_segment(trace_info, degrees, aux_degrees, 3, 1, options),
            result: pub_inputs,
        }
    }

    fn context(&self) -> &AirContext<Self::BaseField> {
        &self.context
    }

    fn evaluate_transition<E: IsWinterfellFieldElement + From<Self::BaseField>>(
        &self,
        frame: &EvaluationFrame<E>,
        _periodic_values: &[E],
        result: &mut [E],
    ) {
        let current = frame.current();
        let next = frame.next();

        // constraints of Fibonacci sequence (1 aux variable):
        result[0] = next[0] - current[1];
        result[1] = next[1] - (current[1] + current[0]);
    }

    fn evaluate_aux_transition<F, E>(
        &self,
        main_frame: &EvaluationFrame<F>,
        aux_frame: &EvaluationFrame<E>,
        _periodic_values: &[F],
        aux_rand_elements: &winterfell::AuxTraceRandElements<E>,
        result: &mut [E],
    ) where
        F: IsWinterfellFieldElement<BaseField = Self::BaseField>,
        E: IsWinterfellFieldElement<BaseField = Self::BaseField> + winterfell::math::ExtensionOf<F>,
    {
        let gamma = aux_rand_elements.get_segment_elements(0)[0];
        let curr_aux = aux_frame.current();
        let next_aux = aux_frame.next();
        let next_main = main_frame.next();

        // curr_aux[0] * ((next_main[0] + gamma) / (next_main[2] + gamma)) = next_aux[0]
        // curr_aux[0] * (next_main[0] + gamma) - next_aux[0] * (next_main[2] + gamma) == 0
        result[0] = curr_aux[0] * (<F as Into<E>>::into(next_main[0]) + gamma)
            - next_aux[0] * (<F as Into<E>>::into(next_main[2]) + gamma);
    }

    fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
        let last_step = self.trace_length() - 1;
        vec![
            Assertion::single(0, 0, Self::BaseField::ONE),
            Assertion::single(1, 0, Self::BaseField::ONE),
            Assertion::single(1, last_step, self.result),
        ]
    }

    fn get_aux_assertions<E: IsWinterfellFieldElement<BaseField = Self::BaseField>>(
        &self,
        _aux_rand_elements: &winterfell::AuxTraceRandElements<E>,
    ) -> Vec<Assertion<E>> {
        let last_step = self.trace_length() - 1;
        vec![Assertion::single(3, last_step, Self::BaseField::ONE.into())]
    }
}

pub fn build_trace(sequence_length: usize) -> TraceTable<AdapterFieldElement> {
    assert!(
        sequence_length.is_power_of_two(),
        "sequence length must be a power of 2"
    );

    let mut fibonacci = vec![FieldElement::one(), FieldElement::one()];
    for i in 2..(sequence_length + 1) {
        fibonacci.push(fibonacci[i - 2] + fibonacci[i - 1])
    }

    let mut permuted = fibonacci[..fibonacci.len() - 1].to_vec();
    let mut rng = thread_rng();
    permuted.shuffle(&mut rng);

    TraceTable::init(vec![
        vec_field2adapter(&fibonacci[..fibonacci.len() - 1]),
        vec_field2adapter(&fibonacci[1..]),
        vec_field2adapter(&permuted),
    ])
}
