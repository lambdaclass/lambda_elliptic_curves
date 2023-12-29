use crate::table::{EvaluationTable, Table, TableView};
use lambdaworks_math::fft::errors::FFTError;
use lambdaworks_math::field::traits::{IsField, IsSubFieldOf};
use lambdaworks_math::{
    field::{element::FieldElement, traits::IsFFTField},
    polynomial::Polynomial,
};
#[cfg(feature = "parallel")]
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};

/// A two-dimensional representation of an execution trace of the STARK
/// protocol.
///
/// For the moment it is mostly a wrapper around the `Table` struct. It is a
/// layer above the raw two-dimensional table, with functionality relevant to the
/// STARK protocol, such as the step size (number of consecutive rows of the table)
/// of the computation being proven.
#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct TraceTable<F: IsField> {
    pub table: Table<F>,
    pub step_size: usize,
}

impl<F: IsField> TraceTable<F> {
    pub fn new(data: Vec<FieldElement<F>>, n_columns: usize, step_size: usize) -> Self {
        let table = Table::new(data, n_columns);
        Self { table, step_size }
    }

    pub fn from_columns(columns: Vec<Vec<FieldElement<F>>>, step_size: usize) -> Self {
        let table = Table::from_columns(columns);
        Self { table, step_size }
    }

    pub fn empty() -> Self {
        Self::new(Vec::new(), 0, 0)
    }

    pub fn is_empty(&self) -> bool {
        self.table.width == 0
    }

    pub fn n_rows(&self) -> usize {
        self.table.height
    }

    pub fn num_steps(&self) -> usize {
        debug_assert!((self.table.height % self.step_size) == 0);
        self.table.height / self.step_size
    }

    /// Given a particular step of the computation represented on the trace,
    /// returns the row of the underlying table.
    pub fn step_to_row(&self, step: usize) -> usize {
        self.step_size * step
    }

    pub fn n_cols(&self) -> usize {
        self.table.width
    }

    pub fn rows(&self) -> Vec<Vec<FieldElement<F>>> {
        self.table.rows()
    }

    pub fn get_row(&self, row_idx: usize) -> &[FieldElement<F>] {
        self.table.get_row(row_idx)
    }

    pub fn get_row_mut(&mut self, row_idx: usize) -> &mut [FieldElement<F>] {
        self.table.get_row_mut(row_idx)
    }

    pub fn last_row(&self) -> &[FieldElement<F>] {
        self.get_row(self.n_rows() - 1)
    }

    pub fn columns(&self) -> Vec<Vec<FieldElement<F>>> {
        self.table.columns()
    }

    /// Given a slice of integer numbers representing column indexes, merge these columns into
    /// a one-dimensional vector.
    ///
    /// The particular way they are merged is not really important since this function is used to
    /// aggreagate values distributed across various columns with no importance on their ordering,
    /// such as to sort them.
    pub fn merge_columns(&self, column_indexes: &[usize]) -> Vec<FieldElement<F>> {
        let mut data = Vec::with_capacity(self.n_rows() * column_indexes.len());
        for row_index in 0..self.n_rows() {
            for column in column_indexes {
                data.push(self.table.data[row_index * self.n_cols() + column].clone());
            }
        }
        data
    }

    pub fn compute_trace_polys<S: IsFFTField + IsSubFieldOf<F>>(
        &self,
    ) -> Vec<Polynomial<FieldElement<F>>>
    where
        FieldElement<F>: Send + Sync,
    {
        let columns = self.columns();
        #[cfg(feature = "parallel")]
        let iter = columns.par_iter();
        #[cfg(not(feature = "parallel"))]
        let iter = columns.iter();

        iter.map(|col| Polynomial::interpolate_fft::<S>(col))
            .collect::<Result<Vec<Polynomial<FieldElement<F>>>, FFTError>>()
            .unwrap()
    }

    /// Given the padding length, appends the last row of the trace table
    /// that many times.
    /// This is useful for example when the desired trace length should be power
    /// of two, and only the last row is the one that can be appended without affecting
    /// the integrity of the constraints.
    pub fn pad_with_last_row(&mut self, padding_len: usize) {
        let last_row = self.last_row().to_vec();
        (0..padding_len).for_each(|_| {
            self.table.append_row(&last_row);
        })
    }

    /// Given a row index, a column index and a value, tries to set that location
    /// of the trace with the given value.
    /// The row_idx passed as argument may be greater than the max row index by 1. In this case,
    /// last row of the trace is cloned, and the value is set in that cloned row. Then, the row is
    /// appended to the end of the trace.
    pub fn set_or_extend(&mut self, row_idx: usize, col_idx: usize, value: &FieldElement<F>) {
        debug_assert!(col_idx < self.n_cols());
        // NOTE: This is not very nice, but for how the function is being used at the moment,
        // the passed `row_idx` should never be greater than `self.n_rows() + 1`. This is just
        // an integrity check for ease in the developing process, we should think a better alternative
        // in the future.
        debug_assert!(row_idx <= self.n_rows() + 1);
        if row_idx >= self.n_rows() {
            let mut last_row = self.last_row().to_vec();
            last_row[col_idx] = value.clone();
            self.table.append_row(&last_row)
        } else {
            let row = self.get_row_mut(row_idx);
            row[col_idx] = value.clone();
        }
    }
}

/// A view into a step of the trace. In general, a step over the trace
/// can be thought as a fixed size subset of trace rows
///
/// The main purpose of this data structure is to have a way to
/// access the steps in a trace, in order to grab elements to calculate
/// constraint evaluations.
#[derive(Debug, Clone, PartialEq)]
pub struct StepView<'t, F: IsSubFieldOf<E>, E: IsField> {
    pub main_table_view: TableView<'t, F>,
    pub aux_table_view: TableView<'t, E>,
    pub step_idx: usize,
}

impl<'t, F: IsSubFieldOf<E>, E: IsField> StepView<'t, F, E> {
    pub fn new(
        main_table_view: TableView<'t, F>,
        aux_table_view: TableView<'t, E>,
        step_idx: usize,
    ) -> Self {
        StepView {
            main_table_view,
            aux_table_view,
            step_idx,
        }
    }

    /// Gets the evaluation element of the main table specified by `row_idx` and `col_idx` of this step
    pub fn get_main_evaluation_element(&self, row_idx: usize, col_idx: usize) -> &FieldElement<F> {
        self.main_table_view.get(row_idx, col_idx)
    }

    /// Gets the evaluation element of the aux table specified by `row_idx` and `col_idx` of this step
    pub fn get_aux_evaluation_element(&self, row_idx: usize, col_idx: usize) -> &FieldElement<E> {
        self.aux_table_view.get(row_idx, col_idx)
    }

    pub fn get_row_main(&self, row_idx: usize) -> &[FieldElement<F>] {
        self.main_table_view.get_row(row_idx)
    }

    pub fn get_row_aux(&self, row_idx: usize) -> &[FieldElement<E>] {
        self.aux_table_view.get_row(row_idx)
    }
}

/// Given a slice of trace polynomials, an evaluation point `x`, the frame offsets
/// corresponding to the computation of the transitions, and a primitive root,
/// outputs the trace evaluations of each trace polynomial over the values used to
/// compute a transition.
/// Example: For a simple Fibonacci computation, if t(x) is the trace polynomial of
/// the computation, this will output evaluations t(x), t(g * x), t(g^2 * z).
pub(crate) fn get_trace_evaluations<F: IsSubFieldOf<E>, E: IsField>(
    main_trace_polys: &[Polynomial<FieldElement<F>>],
    aux_trace_polys: &[Polynomial<FieldElement<E>>],
    x: &FieldElement<E>,
    frame_offsets: &[usize],
    primitive_root: &FieldElement<F>,
    step_size: usize,
) -> EvaluationTable<E, E> {
    let evaluation_points: Vec<_> = frame_offsets
        .iter()
        .map(|offset| primitive_root.pow(*offset) * x)
        .collect();
    let main_evaluations = main_trace_polys
        .iter()
        .map(|poly| {
            evaluation_points
                .iter()
                .map(|eval_point| poly.evaluate(eval_point))
                .collect()
        })
        .collect();
    let aux_evaluations = aux_trace_polys
        .iter()
        .map(|poly| {
            evaluation_points
                .iter()
                .map(|eval_point| poly.evaluate(eval_point))
                .collect()
        })
        .collect();

    EvaluationTable::from_columns(main_evaluations, aux_evaluations, step_size)
}

#[cfg(test)]
mod test {
    use super::TraceTable;
    use lambdaworks_math::field::{element::FieldElement, fields::u64_prime_field::F17};
    type FE = FieldElement<F17>;

    #[test]
    fn test_cols() {
        let col_1 = vec![FE::from(1), FE::from(2), FE::from(5), FE::from(13)];
        let col_2 = vec![FE::from(1), FE::from(3), FE::from(8), FE::from(21)];

        let trace_table = TraceTable::from_columns(vec![col_1.clone(), col_2.clone()], 1);
        let res_cols = trace_table.columns();

        assert_eq!(res_cols, vec![col_1, col_2]);
    }
}
