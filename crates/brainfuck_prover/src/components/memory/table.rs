use super::component::InteractionClaim;
use crate::components::{MemoryClaim, TraceColumn, TraceError, TraceEval};
use brainfuck_vm::registers::Registers;
use num_traits::One;
use stwo_prover::{
    constraint_framework::{
        logup::{LogupTraceGenerator, LookupElements},
        Relation, RelationEFTraitBound,
    },
    core::{
        backend::{
            simd::{column::BaseColumn, m31::LOG_N_LANES, qm31::PackedSecureField},
            Column,
        },
        channel::Channel,
        fields::m31::BaseField,
        poly::circle::{CanonicCoset, CircleEvaluation},
    },
};

/// Represents a single row in the Memory Table.
///
/// The Memory Table stores:
/// - The clock cycle counter (`clk`),
/// - The memory pointer (`mp`),
/// - The memory value (`mv`),
/// - The dummy column flag (`d`).
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct MemoryTableRow {
    /// Clock cycle counter: the current step.
    clk: BaseField,
    /// Memory pointer: points to a memory cell.
    mp: BaseField,
    /// Memory value: value of the cell pointer by `mp` - values in [0..2^31 - 1)
    mv: BaseField,
    /// Dummy: Flag whether the row is a dummy one or not
    d: BaseField,
}

impl MemoryTableRow {
    /// Creates a row for the [`MemoryTable`] which is considered 'real'.
    ///
    /// A 'real' row, is a row that is part of the execution trace from the Brainfuck program
    /// execution.
    pub fn new(clk: BaseField, mp: BaseField, mv: BaseField) -> Self {
        Self { clk, mp, mv, ..Default::default() }
    }

    /// Creates a row for the [`MemoryTable`] which is considered 'dummy'.
    ///
    /// A 'dummy' row, is a row that is not part of the execution trace from the Brainfuck program
    /// execution.
    /// They are used for padding and filling the `clk` gaps after sorting by `mp`, to enforce the
    /// correct sorting.
    pub fn new_dummy(clk: BaseField, mp: BaseField, mv: BaseField) -> Self {
        Self { clk, mp, mv, d: BaseField::one() }
    }

    /// Getter for the `clk` field.
    pub const fn clk(&self) -> BaseField {
        self.clk
    }

    /// Getter for the `mp` field.
    pub const fn mp(&self) -> BaseField {
        self.mp
    }

    /// Getter for the `mv` field.
    pub const fn mv(&self) -> BaseField {
        self.mv
    }

    /// Getter for the `d` field.
    pub const fn d(&self) -> BaseField {
        self.d
    }
}

impl From<(&Registers, bool)> for MemoryTableRow {
    fn from((registers, is_dummy): (&Registers, bool)) -> Self {
        if is_dummy {
            Self::new_dummy(registers.clk, registers.mp, registers.mv)
        } else {
            Self::new(registers.clk, registers.mp, registers.mv)
        }
    }
}

/// Represents the Memory Table, which holds the required registers
/// for the Memory component.
///
/// The Memory Table is constructed by extracting the required fields
/// from the execution trace provided by the Brainfuck Virtual Machine,
/// then sorting by `mp` as a primary key and by `clk` as a secondary key.
///
/// To enforce the sorting on clk, all clk jumped are erased by adding dummy rows.
/// A dummy column flags them.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct MemoryTable {
    /// A vector of [`MemoryTableRow`] representing the table rows.
    table: Vec<MemoryTableRow>,
}

impl MemoryTable {
    /// Creates a new, empty [`MemoryTable`].
    ///
    /// # Returns
    /// A new instance of [`MemoryTable`] with an empty table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Getter for the `table` field.
    pub const fn table(&self) -> &Vec<MemoryTableRow> {
        &self.table
    }

    /// Adds a new row to the Memory Table.
    ///
    /// # Arguments
    /// * `row` - The [`MemoryTableRow`] to add to the table.
    ///
    /// This method pushes a new [`MemoryTableRow`] onto the `table` vector.
    fn add_row(&mut self, row: MemoryTableRow) {
        self.table.push(row);
    }

    /// Adds multiple rows to the Memory Table.
    ///
    /// # Arguments
    /// * `rows` - A vector of [`MemoryTableRow`] to add to the table.
    ///
    /// This method extends the `table` vector with the provided rows.
    fn add_rows(&mut self, rows: Vec<MemoryTableRow>) {
        self.table.extend(rows);
    }

    /// Sorts in-place the existing [`MemoryTableRow`] rows in the Memory Table by `mp`, then `clk`.
    ///
    /// Having the rows sorted is required to ensure a correct proof generation (such that the
    /// constraints can be verified).
    fn sort(&mut self) {
        self.table.sort_by_key(|x| (x.mp, x.clk));
    }

    /// Fills the jumps in `clk` with dummy rows.
    ///
    /// Required to ensure the correct sorting of the [`MemoryTable`] in the constraints.
    ///
    /// Does nothing if the table is empty.
    fn complete_with_dummy_rows(&mut self) {
        let mut new_table = Vec::with_capacity(self.table.len());
        if let Some(mut prev_row) = self.table.first() {
            for row in &self.table {
                let next_clk = prev_row.clk + BaseField::one();
                if row.mp == prev_row.mp && row.clk > next_clk {
                    let mut clk = next_clk;
                    while clk < row.clk {
                        new_table.push(MemoryTableRow::new_dummy(clk, prev_row.mp, prev_row.mv));
                        clk += BaseField::one();
                    }
                }
                new_table.push(row.clone());
                prev_row = row;
            }
            new_table.shrink_to_fit();
            self.table = new_table;
        }
    }

    /// Pads the memory table with dummy rows up to the next power of two length.
    ///
    /// Each dummy row preserves the last memory pointer and value while incrementing the clock.
    ///
    /// Does nothing if the table is empty.
    fn pad(&mut self) {
        if let Some(last_row) = self.table.last().cloned() {
            let trace_len = self.table.len();
            let padding_offset = (trace_len.next_power_of_two() - trace_len) as u32;
            for i in 1..=padding_offset {
                self.add_row(MemoryTableRow::new_dummy(
                    last_row.clk + BaseField::from(i),
                    last_row.mp,
                    last_row.mv,
                ));
            }
        }
    }

    /// Transforms the [`MemoryTable`] into [`super::super::TraceEval`], to be commited when
    /// generating a STARK proof.
    ///
    /// The [`MemoryTable`] is transformed from an array of rows (one element = one step of all
    /// registers) to an array of columns (one element = all steps of one register).
    /// It is then evaluated on the circle domain.
    ///
    /// # Arguments
    /// * memory - The [`MemoryTable`] containing the sorted and padded trace as an array of rows.
    ///
    /// # Returns
    /// A tuple containing the evaluated trace and claim for STARK proof.
    ///
    /// # Errors
    /// Returns [`TraceError::EmptyTrace`] if the table is empty.
    pub fn trace_evaluation(&self) -> Result<(TraceEval, MemoryClaim), TraceError> {
        let n_rows = self.table.len() as u32;
        if n_rows == 0 {
            return Err(TraceError::EmptyTrace);
        }
        let log_n_rows = n_rows.ilog2();
        // TODO: Confirm that the log_size used for evaluation on Circle domain is the log_size of
        // the table plus the SIMD lanes
        let log_size = log_n_rows + LOG_N_LANES;
        let mut trace = vec![BaseColumn::zeros(1 << log_size); MemoryColumn::count()];

        for (vec_row, row) in self.table.iter().enumerate().take(1 << log_n_rows) {
            trace[MemoryColumn::Clk.index()].data[vec_row] = row.clk().into();
            trace[MemoryColumn::Mp.index()].data[vec_row] = row.mp().into();
            trace[MemoryColumn::Mv.index()].data[vec_row] = row.mv().into();
            trace[MemoryColumn::D.index()].data[vec_row] = row.d().into();
        }

        let domain = CanonicCoset::new(log_size).circle_domain();
        let trace = trace.into_iter().map(|col| CircleEvaluation::new(domain, col)).collect();

        // TODO: Confirm that the log_size in `Claim` is `log_size`, including the SIMD lanes
        Ok((trace, MemoryClaim::new(log_size)))
    }
}

impl From<Vec<Registers>> for MemoryTable {
    fn from(registers: Vec<Registers>) -> Self {
        let mut memory_table = Self::new();

        let memory_rows = registers.iter().map(|reg| (reg, false).into()).collect();
        memory_table.add_rows(memory_rows);

        memory_table.sort();
        memory_table.complete_with_dummy_rows();
        memory_table.pad();

        memory_table
    }
}

/// Enum representing the column indices in the Memory trace
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryColumn {
    /// Index of the `clk` register column in the Memory trace.
    Clk,
    /// Index of the `mp` register column in the Memory trace.
    Mp,
    /// Index of the `mv` register column in the Memory trace.
    Mv,
    /// Index of the `d` register column in the Memory trace.
    D,
}

impl MemoryColumn {
    /// Returns the index of the column in the Memory table
    pub const fn index(self) -> usize {
        match self {
            Self::Clk => 0,
            Self::Mp => 1,
            Self::Mv => 2,
            Self::D => 3,
        }
    }

    /// Returns the total number of columns in the Memory table
    pub const fn column_count() -> usize {
        4
    }
}

impl TraceColumn for MemoryColumn {
    fn count() -> usize {
        Self::column_count()
    }
}

/// The interaction elements drawn for the extension column of the Memory component.
///
/// The logUp protocol uses these elements to combine the values of the different
/// registers of the main trace to create a random linear combination
/// of them, and use it in the denominator of the fractions in the logUp protocol.
///
/// There are 3 lookup elements in the Memory component, as only the 'real' registers
/// are used: `clk`, `mp` and `mv`. `d` is used to eventually nullify the numerator.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MemoryElements(LookupElements<{ MemoryColumn::column_count() - 1 }>);

impl MemoryElements {
    /// Provides dummy lookup elements.
    pub fn dummy() -> Self {
        Self(LookupElements::dummy())
    }

    /// Draw random elements from the Fiat-Shamir [`Channel`].
    ///
    /// These elements are randomly secured, and will be use
    /// to generate the interaction trace with the logUp protocol.
    pub fn draw(channel: &mut impl Channel) -> Self {
        Self(LookupElements::draw(channel))
    }
}

impl<F: Clone, EF: RelationEFTraitBound<F>> Relation<F, EF> for MemoryElements {
    /// Combine multiple values from a basefield (e.g. [`BaseField`])
    /// and combine them to a value from an extension field (e.g. [`PackedSecureField`])
    ///
    /// This is used when computing the interaction values from the main trace values.
    fn combine(&self, values: &[F]) -> EF {
        values
            .iter()
            .zip(self.0.alpha_powers)
            .fold(EF::zero(), |acc, (value, power)| acc + EF::from(power) * value.clone()) -
            self.0.z.into()
    }

    /// Returns the name of the struct.
    fn get_name(&self) -> &str {
        stringify!(MemoryElements)
    }

    /// Returns the number interaction elements.
    fn get_size(&self) -> usize {
        MemoryColumn::count() - 1
    }
}

/// Creates the interaction trace from the main trace evaluation
/// and the interaction elements for the Memory component.
///
/// The Processor component uses the other components:
/// The Processor component multiplicities are then positive,
/// and the Memory component multiplicities are negative
/// in the logUp protocol.
///
/// Only the 'real' rows are impacting the logUp sum.
/// Dummy rows are padded rows and rows filling the `clk` gaps
/// which does not appear in the Processor main trace.
///
///
/// # Returns
/// - Interaction trace evaluation, to be commited.
/// - Interaction claim: the total sum from the logUp protocol,
/// to be mixed into the Fiat-Shamir [`Channel`].
pub fn interaction_trace_evaluation(
    main_trace_eval: &TraceEval,
    lookup_elements: &MemoryElements,
) -> (TraceEval, InteractionClaim) {
    let log_size = main_trace_eval[0].domain.log_size();

    let mut logup_gen = LogupTraceGenerator::new(log_size);
    let mut col_gen = logup_gen.new_col();

    let clk_col = &main_trace_eval[MemoryColumn::Clk.index()].data;
    let mp_col = &main_trace_eval[MemoryColumn::Mp.index()].data;
    let mv_column = &main_trace_eval[MemoryColumn::Mv.index()].data;
    let d_col = &main_trace_eval[MemoryColumn::D.index()].data;
    for vec_row in 0..1 << (log_size - LOG_N_LANES) {
        let clk = clk_col[vec_row];
        let mp = mp_col[vec_row];
        let mv = mv_column[vec_row];
        // Set the fraction numerator to 0 if it is a dummy row (d = 1), otherwise set it to -1.
        let is_dummy_num = PackedSecureField::from(d_col[vec_row]) - PackedSecureField::one();
        // Only the common registers with the processor table are part of the extension column.
        let denom: PackedSecureField = lookup_elements.combine(&[clk, mp, mv]);
        col_gen.write_frac(vec_row, is_dummy_num, denom);
    }

    col_gen.finalize_col();

    let (trace, claimed_sum) = logup_gen.finalize_last();

    (trace, InteractionClaim { claimed_sum })
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Zero;

    #[test]
    fn test_memory_row_new() {
        let row = MemoryTableRow::new(BaseField::zero(), BaseField::from(43), BaseField::from(91));
        let expected_row = MemoryTableRow {
            clk: BaseField::zero(),
            mp: BaseField::from(43),
            mv: BaseField::from(91),
            d: BaseField::zero(),
        };
        assert_eq!(row, expected_row);
    }

    #[test]
    fn test_memory_row_new_dummy() {
        let row =
            MemoryTableRow::new_dummy(BaseField::zero(), BaseField::from(43), BaseField::from(91));
        let expected_row = MemoryTableRow {
            clk: BaseField::zero(),
            mp: BaseField::from(43),
            mv: BaseField::from(91),
            d: BaseField::one(),
        };
        assert_eq!(row, expected_row);
    }

    #[test]
    fn test_memory_table_new() {
        let memory_table = MemoryTable::new();
        assert!(memory_table.table.is_empty(), "Memory table should be empty upon initialization.");
    }

    #[test]
    fn test_add_row() {
        let mut memory_table = MemoryTable::new();
        // Create a row to add to the table
        let row = MemoryTableRow::new(BaseField::zero(), BaseField::from(43), BaseField::from(91));
        // Add the row to the table
        memory_table.add_row(row.clone());
        // Check that the table contains the added row
        assert_eq!(memory_table.table, vec![row], "Added row should match the expected row.");
    }

    #[test]
    fn test_add_dummy_row() {
        let mut memory_table = MemoryTable::new();
        // Create a row to add to the table
        let row =
            MemoryTableRow::new_dummy(BaseField::zero(), BaseField::from(43), BaseField::from(91));
        // Add the row to the table
        memory_table.add_row(row.clone());
        // Check that the table contains the added row
        assert_eq!(memory_table.table, vec![row], "Added row should match the expected row.");
    }

    #[test]
    fn test_add_multiple_rows() {
        let mut memory_table = MemoryTable::new();
        // Create a vector of rows to add to the table
        let rows = vec![
            MemoryTableRow::new(BaseField::zero(), BaseField::from(43), BaseField::from(91)),
            MemoryTableRow::new(BaseField::one(), BaseField::from(91), BaseField::from(9)),
            MemoryTableRow::new(BaseField::from(43), BaseField::from(62), BaseField::from(43)),
        ];
        // Add the rows to the table
        memory_table.add_rows(rows.clone());
        // Check that the table contains the added rows
        assert_eq!(memory_table, MemoryTable { table: rows });
    }

    #[test]
    fn test_sort() {
        let mut memory_table = MemoryTable::new();
        let row1 = MemoryTableRow::new(BaseField::zero(), BaseField::zero(), BaseField::zero());
        let row2 = MemoryTableRow::new(BaseField::one(), BaseField::zero(), BaseField::zero());
        let row3 = MemoryTableRow::new(BaseField::zero(), BaseField::one(), BaseField::zero());
        memory_table.add_rows(vec![row3.clone(), row1.clone(), row2.clone()]);

        let mut expected_memory_table = MemoryTable::new();
        expected_memory_table.add_rows(vec![row1, row2, row3]);

        memory_table.sort();

        assert_eq!(memory_table, expected_memory_table);
    }

    #[test]
    fn test_empty_complete_wih_dummy_rows() {
        let mut memory_table = MemoryTable::new();
        memory_table.complete_with_dummy_rows();

        assert_eq!(memory_table, MemoryTable::new());
    }

    #[test]
    fn test_complete_wih_dummy_rows() {
        let mut memory_table = MemoryTable::new();
        let row1 = MemoryTableRow::new(BaseField::zero(), BaseField::zero(), BaseField::zero());
        let row2 = MemoryTableRow::new(BaseField::zero(), BaseField::one(), BaseField::zero());
        let row3 = MemoryTableRow::new(BaseField::from(5), BaseField::one(), BaseField::one());
        memory_table.add_rows(vec![row3.clone(), row1.clone(), row2.clone()]);
        memory_table.sort();
        memory_table.complete_with_dummy_rows();

        let mut expected_memory_table = MemoryTable::new();
        expected_memory_table.add_rows(vec![
            row1,
            row2,
            MemoryTableRow::new_dummy(BaseField::one(), BaseField::one(), BaseField::zero()),
            MemoryTableRow::new_dummy(BaseField::from(2), BaseField::one(), BaseField::zero()),
            MemoryTableRow::new_dummy(BaseField::from(3), BaseField::one(), BaseField::zero()),
            MemoryTableRow::new_dummy(BaseField::from(4), BaseField::one(), BaseField::zero()),
            row3,
        ]);

        assert_eq!(memory_table, expected_memory_table);
    }

    #[test]
    fn test_pad_empty() {
        let mut memory_table = MemoryTable::new();
        memory_table.pad();
        assert_eq!(memory_table, MemoryTable::new());
    }

    #[test]
    fn test_pad() {
        let mut memory_table = MemoryTable::new();
        let row1 = MemoryTableRow::new(BaseField::zero(), BaseField::zero(), BaseField::zero());
        let row2 = MemoryTableRow::new(BaseField::one(), BaseField::one(), BaseField::zero());
        let row3 = MemoryTableRow::new(BaseField::from(2), BaseField::one(), BaseField::one());
        memory_table.add_rows(vec![row1.clone(), row2.clone(), row3.clone()]);

        memory_table.pad();

        let dummy_row =
            MemoryTableRow::new_dummy(BaseField::from(3), BaseField::one(), BaseField::one());
        let mut expected_memory_table = MemoryTable::new();
        expected_memory_table.add_rows(vec![row1, row2, row3, dummy_row]);

        assert_eq!(memory_table, expected_memory_table);
    }

    #[test]
    fn test_from_registers() {
        let reg1 = Registers::default();
        let reg2 = Registers { clk: BaseField::one(), mp: BaseField::one(), ..Default::default() };
        let reg3 = Registers {
            clk: BaseField::from(5),
            mp: BaseField::one(),
            mv: BaseField::one(),
            ..Default::default()
        };
        let registers: Vec<Registers> = vec![reg3, reg1, reg2];

        let row1 = MemoryTableRow::default();
        let row2 = MemoryTableRow::new(BaseField::one(), BaseField::one(), BaseField::zero());
        let row3 = MemoryTableRow::new(BaseField::from(5), BaseField::one(), BaseField::one());

        let dummy_row1 =
            MemoryTableRow::new_dummy(BaseField::from(6), BaseField::one(), BaseField::one());
        let dummy_row2 =
            MemoryTableRow::new_dummy(BaseField::from(7), BaseField::one(), BaseField::one());
        let mut expected_memory_table = MemoryTable::new();
        expected_memory_table.add_rows(vec![
            row1,
            row2,
            MemoryTableRow::new_dummy(BaseField::from(2), BaseField::one(), BaseField::zero()),
            MemoryTableRow::new_dummy(BaseField::from(3), BaseField::one(), BaseField::zero()),
            MemoryTableRow::new_dummy(BaseField::from(4), BaseField::one(), BaseField::zero()),
            row3,
            dummy_row1,
            dummy_row2,
        ]);

        assert_eq!(MemoryTable::from(registers), expected_memory_table);
    }

    #[test]
    fn test_trace_evaluation() {
        let mut memory_table = MemoryTable::new();
        let rows = vec![
            MemoryTableRow::new(BaseField::zero(), BaseField::from(43), BaseField::from(91)),
            MemoryTableRow::new(BaseField::one(), BaseField::from(91), BaseField::from(9)),
        ];
        memory_table.add_rows(rows);

        let (trace, claim) = memory_table.trace_evaluation().unwrap();

        let expected_log_n_rows: u32 = 1;
        let expected_log_size = expected_log_n_rows + LOG_N_LANES;
        let expected_size = 1 << expected_log_size;
        let mut clk_column = BaseColumn::zeros(expected_size);
        let mut mp_column = BaseColumn::zeros(expected_size);
        let mut mv_col = BaseColumn::zeros(expected_size);
        let mut d_column = BaseColumn::zeros(expected_size);

        clk_column.data[0] = BaseField::zero().into();
        clk_column.data[1] = BaseField::one().into();

        mp_column.data[0] = BaseField::from(43).into();
        mp_column.data[1] = BaseField::from(91).into();

        mv_col.data[0] = BaseField::from(91).into();
        mv_col.data[1] = BaseField::from(9).into();

        d_column.data[0] = BaseField::zero().into();
        d_column.data[1] = BaseField::zero().into();

        let domain = CanonicCoset::new(expected_log_size).circle_domain();
        let expected_trace: TraceEval = vec![clk_column, mp_column, mv_col, d_column]
            .into_iter()
            .map(|col| CircleEvaluation::new(domain, col))
            .collect();
        let expected_claim = MemoryClaim::new(expected_log_size);

        assert_eq!(claim, expected_claim);
        for col_index in 0..expected_trace.len() {
            assert_eq!(trace[col_index].domain, expected_trace[col_index].domain);
            assert_eq!(trace[col_index].to_cpu().values, expected_trace[col_index].to_cpu().values);
        }
    }

    #[test]
    fn test_evaluate_empty_trace() {
        let memory_table = MemoryTable::new();
        let run = memory_table.trace_evaluation();

        assert!(matches!(run, Err(TraceError::EmptyTrace)));
    }

    #[test]
    fn test_interaction_trace_evaluation() {
        let mut memory_table = MemoryTable::new();
        // Trace rows are:
        // - Real row
        // - Dummy row (filling the `clk` value)
        // - Real row
        // - Dummy row (padding to power of 2)
        let rows = vec![
            MemoryTableRow::new(BaseField::zero(), BaseField::from(43), BaseField::from(91)),
            MemoryTableRow::new_dummy(BaseField::one(), BaseField::from(43), BaseField::from(91)),
            MemoryTableRow::new(BaseField::from(2), BaseField::from(91), BaseField::from(9)),
            MemoryTableRow::new_dummy(BaseField::from(2), BaseField::from(91), BaseField::from(9)),
        ];
        memory_table.add_rows(rows);

        let (trace_eval, claim) = memory_table.trace_evaluation().unwrap();

        let lookup_elements = MemoryElements::dummy();

        let (interaction_trace_eval, interaction_claim) =
            interaction_trace_evaluation(&trace_eval, &lookup_elements);

        let log_size = trace_eval[0].domain.log_size();
        let mut logup_gen = LogupTraceGenerator::new(log_size);
        let mut col_gen = logup_gen.new_col();

        let mut denoms = [PackedSecureField::zero(); 4];
        let clk_col = &trace_eval[MemoryColumn::Clk.index()].data;
        let mp_col = &trace_eval[MemoryColumn::Mp.index()].data;
        let mv_column = &trace_eval[MemoryColumn::Mv.index()].data;
        // Construct the denominator for each row of the logUp column, from the main trace
        // evaluation.
        for vec_row in 0..1 << (log_size - LOG_N_LANES) {
            let clk = clk_col[vec_row];
            let mp = mp_col[vec_row];
            let mv = mv_column[vec_row];
            let denom: PackedSecureField = lookup_elements.combine(&[clk, mp, mv]);
            denoms[vec_row] = denom;
        }

        let num_1 = -PackedSecureField::one();
        let num_2 = PackedSecureField::zero();
        let num_3 = -PackedSecureField::one();
        let num_4 = PackedSecureField::zero();

        col_gen.write_frac(0, num_1, denoms[0]);
        col_gen.write_frac(1, num_2, denoms[1]);
        col_gen.write_frac(2, num_3, denoms[2]);
        col_gen.write_frac(3, num_4, denoms[3]);

        col_gen.finalize_col();
        let (expected_interaction_trace_eval, expected_claimed_sum) = logup_gen.finalize_last();

        assert_eq!(claim.log_size, log_size,);
        for col_index in 0..expected_interaction_trace_eval.len() {
            assert_eq!(
                interaction_trace_eval[col_index].domain,
                expected_interaction_trace_eval[col_index].domain
            );
            assert_eq!(
                interaction_trace_eval[col_index].to_cpu().values,
                expected_interaction_trace_eval[col_index].to_cpu().values
            );
        }
        assert_eq!(interaction_claim.claimed_sum, expected_claimed_sum);
    }

    // This test verifies that the dummy rows have no impact
    // on the total sum of the logUp protocol in the Memory component.
    // Indeed, the total sum computed by the Processor component won't
    // have the exact same dummy rows (the Memory component) adds extra
    // dummy rows to fill the `clk` jumps and enforce the sorting.
    #[test]
    fn test_dummy_rows_impact_on_interaction_trace_evaluation() {
        let mut memory_table = MemoryTable::new();
        let mut real_memory_table = MemoryTable::new();

        // Trace rows are:
        // - Real row
        // - Dummy row (filling the `clk` value)
        // - Real row
        // - Dummy row (padding to power of 2)
        let rows = vec![
            MemoryTableRow::new(BaseField::zero(), BaseField::from(43), BaseField::from(91)),
            MemoryTableRow::new_dummy(BaseField::one(), BaseField::from(43), BaseField::from(91)),
            MemoryTableRow::new(BaseField::from(2), BaseField::from(91), BaseField::from(9)),
            MemoryTableRow::new_dummy(BaseField::from(2), BaseField::from(91), BaseField::from(9)),
        ];
        memory_table.add_rows(rows);

        // Trace rows are:
        // - Real row
        // - Real row
        let real_rows = vec![
            MemoryTableRow::new(BaseField::zero(), BaseField::from(43), BaseField::from(91)),
            MemoryTableRow::new(BaseField::from(2), BaseField::from(91), BaseField::from(9)),
        ];
        real_memory_table.add_rows(real_rows);

        let (trace_eval, _) = memory_table.trace_evaluation().unwrap();
        let (new_trace_eval, _) = real_memory_table.trace_evaluation().unwrap();

        let lookup_elements = MemoryElements::dummy();

        let (_, interaction_claim) = interaction_trace_evaluation(&trace_eval, &lookup_elements);

        let (_, new_interaction_claim) =
            interaction_trace_evaluation(&new_trace_eval, &lookup_elements);

        assert_eq!(interaction_claim, new_interaction_claim,);
    }
}
