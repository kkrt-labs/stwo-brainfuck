use crate::components::{
    io::component::InteractionClaim, IoClaim, TraceColumn, TraceError, TraceEval,
};
use brainfuck_vm::{instruction::InstructionType, registers::Registers};
use num_traits::{One, Zero};
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

/// Represents a single row in the I/O Table.
///
/// The I/O Table stores:
/// - The clock cycle counter (`clk`),
/// - The current instruction (`ci`),
/// - The memory value (`mv`),
/// - The dummy flag (`d`),
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct IOTableRow {
    /// Clock cycle counter: the current step.
    clk: BaseField,
    /// Current instruction: the opcode at the current instruction pointer.
    ci: BaseField,
    /// Memory value: value of the cell pointer by `mp` - values in [0..2^31 - 1)
    pub mv: BaseField,
    /// Dummy: Flag whether the current entry is a dummy one or not
    pub d: BaseField,
}

impl IOTableRow {
    /// Creates a row for the [`IOTable`] which is considered 'real'.
    ///
    /// A 'real' row, is a row that is part of the execution trace from the Brainfuck program
    /// execution.
    pub fn new(clk: BaseField, ci: BaseField, mv: BaseField) -> Self {
        Self { clk, ci, mv, d: BaseField::zero() }
    }

    /// Creates an entry for the [`IOTable`] which is considered 'dummy'.
    ///
    /// A 'dummy' row, is a row that is not part of the execution trace from the Brainfuck
    /// program execution.
    /// They are used for padding.
    pub fn new_dummy(clk: BaseField) -> Self {
        Self { clk, d: BaseField::one(), ..Default::default() }
    }
}

/// Represents the I/O Table, which holds the required register
/// for the Input and Output components.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct IOTable<const N: u32> {
    /// A vector of [`IOTableRow`] representing the table rows.
    pub table: Vec<IOTableRow>,
}

impl<const N: u32> IOTable<N> {
    /// Creates a new, empty [`IOTable`].
    ///
    /// # Returns
    /// A new instance of [`IOTable`] with an empty table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a new row to the I/O Table from the provided register.
    ///
    /// # Arguments
    /// * `mv` - The memory value for the new row.
    ///
    /// This method pushes a new [`IOTableRow`] onto the `table` vector.
    pub fn add_row_from_register(&mut self, clk: BaseField, ci: BaseField, mv: BaseField) {
        self.table.push(IOTableRow::new(clk, ci, mv));
    }

    /// Adds a new row to the I/O Table.
    ///
    /// # Arguments
    /// * `row` - The [`IOTableRow`] to add to the table.
    ///
    /// This method pushes a new [`IOTableRow`] onto the `table` vector.
    pub fn add_row(&mut self, row: IOTableRow) {
        self.table.push(row);
    }

    /// Adds multiple rows to the I/O Table.
    ///
    /// # Arguments
    /// * `rows` - A vector of [`IOTableRow`] to add to the table.
    ///
    /// This method extends the `table` vector with the provided rows.
    pub fn add_rows(&mut self, rows: Vec<IOTableRow>) {
        self.table.extend(rows);
    }

    /// Pads the I/O table with dummy rows up to the next power of two length.
    ///
    /// Each dummy row is flagged by `d` to one,
    /// the registers `ci` and `mv` are set to zero.
    /// `clk` is increased by one, even though it is not constrained.
    ///
    /// Does nothing if the table is empty.
    fn pad(&mut self) {
        let trace_len = self.table.len();
        let last_clk =
            if trace_len == 0 { BaseField::zero() } else { self.table.last().unwrap().clk };
        let padding_offset = (trace_len.next_power_of_two() - trace_len) as u32;
        for i in 0..padding_offset {
            let dummy_row = IOTableRow::new_dummy(last_clk + BaseField::from(i));
            self.add_row(dummy_row);
        }
    }

    /// Transforms the [`IOTable`] into a [`TraceEval`], to be committed when
    /// generating a STARK proof.
    ///
    /// The [`IOTable`] is transformed from an array of rows (one element = one step
    /// of all registers) to an array of columns (one element = all steps of one register).
    /// It is then evaluated on the circle domain.
    ///
    /// # Returns
    /// A tuple containing the evaluated trace and claim for STARK proof.
    /// If the table is empty, returns an empty trace and a claim with a log size of 0.
    pub fn trace_evaluation(&self) -> (TraceEval, IoClaim) {
        let n_rows = self.table.len() as u32;

        // It is possible that the table is empty because the program has no input or output.
        if n_rows == 0 {
            return (TraceEval::new(), IoClaim::new(0));
        }

        // Compute `log_n_rows`, the base-2 logarithm of the number of rows.
        let log_n_rows = n_rows.ilog2();

        // Add `LOG_N_LANES` to account for SIMD optimization.
        let log_size = log_n_rows + LOG_N_LANES;

        // Initialize a trace with 4 columns (`clk`, `ci`, `mv`, `d`), each column containing
        // `2^log_size` entries initialized to zero.
        let mut trace = vec![BaseColumn::zeros(1 << log_size); 4];

        // Populate the column with data from the table rows.
        for (index, row) in self.table.iter().enumerate().take(1 << log_n_rows) {
            trace[IoColumn::Clk.index()].data[index] = row.clk.into();
            trace[IoColumn::Ci.index()].data[index] = row.ci.into();
            trace[IoColumn::Mv.index()].data[index] = row.mv.into();
            trace[IoColumn::D.index()].data[index] = row.d.into();
        }

        // Create a circle domain using a canonical coset.
        let domain = CanonicCoset::new(log_size).circle_domain();

        // Map the column into the circle domain.
        let trace = trace.into_iter().map(|col| CircleEvaluation::new(domain, col)).collect();

        // Return the evaluated trace and a claim containing the log size of the domain.
        (trace, IoClaim::new(log_size))
    }
}

impl<const N: u32> From<&Vec<Registers>> for IOTable<N> {
    fn from(registers: &Vec<Registers>) -> Self {
        let mut io_table = Self::new();
        let rows = registers
            .iter()
            .filter(|register| register.ci == BaseField::from_u32_unchecked(N))
            .map(|x| IOTableRow::new(x.clk, x.ci, x.mv))
            .collect();
        io_table.add_rows(rows);

        io_table.pad();

        io_table
    }
}

/// Input table (trace) for the Input component.
///
/// This table is made of the I/O registers (`clk`, `ci`, `mv` and `d`) corresponding to
/// inputs (when the current instruction `ci` equals ',').
pub type InputTable = IOTable<{ InstructionType::ReadChar.to_u32() }>;

/// Output table (trace) for the Output component.
///
/// This table is made of the I/O registers (`clk`, `ci`, `mv` and `d`) corresponding to
/// outputs (when the current instruction `ci` equals '.').
pub type OutputTable = IOTable<{ InstructionType::PutChar.to_u32() }>;

/// Enum representing the column indices in the IO trace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IoColumn {
    /// Index of the `clk` register column in the I/O trace.
    Clk,
    /// Index of the `ci` register column in the I/O trace.
    Ci,
    /// Index of the `mv` register column in the I/O trace.
    Mv,
    /// Index of the `d` register column in the I/O trace.
    D,
}

impl IoColumn {
    /// Returns the index of the column in the IO table.
    pub const fn index(self) -> usize {
        match self {
            Self::Clk => 0,
            Self::Ci => 1,
            Self::Mv => 2,
            Self::D => 3,
        }
    }
}

impl TraceColumn for IoColumn {
    fn count() -> (usize, usize) {
        (4, 1)
    }
}

/// The number of random elements necessary for the I/O lookup arguments.
const IO_LOOKUP_ELEMENTS: usize = 3;

/// The interaction elements are drawn for the extension column of the I/O components.
///
/// The logUp protocol uses these elements to combine the values of the different
/// registers of the main trace to create a random linear combination
/// of them, and use it in the denominator of the fractions in the logUp protocol.
///
/// There are three lookup elements in the I/O components: `clk`, `ci` and `mv`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IoElements(LookupElements<IO_LOOKUP_ELEMENTS>);

impl IoElements {
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

impl<F: Clone, EF: RelationEFTraitBound<F>> Relation<F, EF> for IoElements {
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
        stringify!(IoElements)
    }

    /// Returns the number interaction elements.
    fn get_size(&self) -> usize {
        IO_LOOKUP_ELEMENTS
    }
}

/// Creates the interaction trace from the main trace evaluation
/// and the interaction elements for the I/O components.
///
/// The Processor component uses the other components:
/// The Processor component multiplicities are then positive,
/// and the I/O components' multiplicities are negative
/// in the logUp protocol.
///
/// # Returns
/// - Interaction trace evaluation, to be committed.
/// - Interaction claim: the total sum from the logUp protocol,
/// to be mixed into the Fiat-Shamir [`Channel`].
#[allow(clippy::similar_names)]
pub fn interaction_trace_evaluation(
    main_trace_eval: &TraceEval,
    lookup_elements: &IoElements,
) -> Result<(TraceEval, InteractionClaim), TraceError> {
    // If the main trace of the I/O components is empty, then we claimed that it's log size is zero.
    let log_size =
        if main_trace_eval.is_empty() { 0 } else { main_trace_eval[0].domain.log_size() };

    let mut logup_gen = LogupTraceGenerator::new(log_size);
    let mut col_gen = logup_gen.new_col();

    let clk_col = &main_trace_eval[IoColumn::Clk.index()].data;
    let ci_col = &main_trace_eval[IoColumn::Ci.index()].data;
    let mv_col = &main_trace_eval[IoColumn::Mv.index()].data;
    let d_col = &main_trace_eval[IoColumn::D.index()].data;
    for vec_row in 0..1 << (log_size - LOG_N_LANES) {
        let clk = clk_col[vec_row];
        let ci = ci_col[vec_row];
        let mv = mv_col[vec_row];
        let d = d_col[vec_row];
        // We want to prove that the I/O table is a sublist (ordered set inclusion)
        // of the Processor table.
        // To do so we make a permutation argument with a register which contains the order
        // of the row in the execution (`clk`).
        let num = PackedSecureField::from(d) - PackedSecureField::one();
        let denom: PackedSecureField = lookup_elements.combine(&[clk, ci, mv]);
        col_gen.write_frac(vec_row, num, denom);
    }

    col_gen.finalize_col();

    let (trace, claimed_sum) = logup_gen.finalize_last();

    Ok((trace, InteractionClaim { claimed_sum }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::{One, Zero};

    #[test]
    fn test_row_new() {
        let row = IOTableRow::new(
            BaseField::zero(),
            InstructionType::PutChar.to_base_field(),
            BaseField::from(91),
        );
        let expected_row = IOTableRow {
            clk: BaseField::zero(),
            ci: InstructionType::PutChar.to_base_field(),
            mv: BaseField::from(91),
            d: BaseField::zero(),
        };
        assert_eq!(row, expected_row);
    }

    #[test]
    fn test_row_new_dummy() {
        let row = IOTableRow::new_dummy(BaseField::from(5));
        let expected_row = IOTableRow {
            clk: BaseField::from(5),
            ci: BaseField::zero(),
            mv: BaseField::zero(),
            d: BaseField::one(),
        };
        assert_eq!(row, expected_row);
    }

    #[test]
    fn test_table_new() {
        let io_table = InputTable::new();
        assert!(io_table.table.is_empty(), "I/O Table should be empty upon initialization.");
    }

    #[test]
    fn test_table_add_row_from_register() {
        let mut io_table = OutputTable::new();
        // Create a row to add to the table
        let row = IOTableRow::new(
            BaseField::zero(),
            InstructionType::PutChar.to_base_field(),
            BaseField::from(91),
        );
        // Add the row to the table
        io_table.add_row_from_register(
            BaseField::zero(),
            InstructionType::PutChar.to_base_field(),
            BaseField::from(91),
        );
        // Check that the table contains the added row
        assert_eq!(io_table.table, vec![row], "Added row should match the expected row.");
    }

    #[test]
    fn test_table_add_row() {
        let mut io_table = InputTable::new();
        // Create a row to add to the table
        let row = IOTableRow::new(
            BaseField::zero(),
            InstructionType::PutChar.to_base_field(),
            BaseField::from(91),
        );
        // Add the row to the table
        io_table.add_row(row.clone());
        // Check that the table contains the added row
        assert_eq!(io_table.table, vec![row], "Added row should match the expected row.");
    }

    #[test]
    fn test_table_add_multiple_rows() {
        let mut io_table = OutputTable::new();
        // Create a vector of rows to add to the table
        let rows = vec![
            IOTableRow::new(
                BaseField::zero(),
                InstructionType::PutChar.to_base_field(),
                BaseField::from(91),
            ),
            IOTableRow::new(
                BaseField::one(),
                InstructionType::PutChar.to_base_field(),
                BaseField::from(9),
            ),
            IOTableRow::new(
                BaseField::from(4),
                InstructionType::PutChar.to_base_field(),
                BaseField::from(43),
            ),
        ];
        // Add the rows to the table
        io_table.add_rows(rows.clone());
        // Check that the table contains the added rows
        assert_eq!(io_table, IOTable { table: rows });
    }

    #[test]
    fn test_input_table_from_registers() {
        let reg1 = Registers::default();
        let reg2 = Registers {
            mv: BaseField::one(),
            ci: BaseField::from(InstructionType::ReadChar.to_base_field()),
            ..Default::default()
        };
        let reg3 = Registers {
            mv: BaseField::from(5),
            ci: BaseField::from(InstructionType::PutChar.to_base_field()),
            ..Default::default()
        };
        let registers: Vec<Registers> = vec![reg3, reg1, reg2];

        let row = IOTableRow::new(
            BaseField::zero(),
            BaseField::from(InstructionType::ReadChar.to_base_field()),
            BaseField::one(),
        );

        let mut expected_io_table: InputTable = IOTable::new();
        expected_io_table.add_row(row);

        assert_eq!(IOTable::from(&registers), expected_io_table);
    }

    #[test]
    fn test_output_table_from_registers() {
        let reg1 = Registers::default();
        let reg2 = Registers {
            mv: BaseField::one(),
            ci: BaseField::from(InstructionType::ReadChar.to_base_field()),
            ..Default::default()
        };
        let reg3 = Registers {
            mv: BaseField::from(5),
            ci: BaseField::from(InstructionType::PutChar.to_base_field()),
            ..Default::default()
        };
        let registers: Vec<Registers> = vec![reg3, reg1, reg2];

        let row = IOTableRow::new(
            BaseField::zero(),
            InstructionType::PutChar.to_base_field(),
            BaseField::from(5),
        );

        let mut expected_io_table: OutputTable = IOTable::new();
        expected_io_table.add_row(row);

        assert_eq!(IOTable::from(&registers), expected_io_table);
    }

    #[test]
    fn test_trace_evaluation_empty_table() {
        let io_table = InputTable::new();

        // Perform the trace evaluation.
        let (trace, claim) = io_table.trace_evaluation();

        // Verify the claim log size is 0.
        assert_eq!(claim.log_size, 0, "The log size should be 0 for an empty table.");

        // Verify the trace is empty.
        assert!(trace.is_empty(), "The trace should be empty when the table has no rows.");
    }

    #[test]
    fn test_trace_evaluation_single_row() {
        let mut io_table = InputTable::new();
        io_table.add_row(IOTableRow::new(
            BaseField::one(),
            BaseField::from(44),
            BaseField::from(42),
        ));

        let (trace, claim) = io_table.trace_evaluation();

        assert_eq!(claim.log_size, LOG_N_LANES, "Log size should include SIMD lanes.");
        assert_eq!(
            trace.len(),
            IoColumn::count().0,
            "Trace should contain one column per register."
        );

        // Expected values for the single row
        let expected_clk_column = vec![BaseField::one(); 1 << LOG_N_LANES];
        let expected_ci_column = vec![BaseField::from(44); 1 << LOG_N_LANES];
        let expected_mv_column = vec![BaseField::from(42); 1 << LOG_N_LANES];
        let expected_d_column = vec![BaseField::zero(); 1 << LOG_N_LANES];

        // Check that the entire column matches expected values
        assert_eq!(
            trace[IoColumn::Clk.index()].to_cpu().values,
            expected_clk_column,
            "Clk column should match expected values."
        );
        assert_eq!(
            trace[IoColumn::Ci.index()].to_cpu().values,
            expected_ci_column,
            "Ci column should match expected values."
        );
        assert_eq!(
            trace[IoColumn::Mv.index()].to_cpu().values,
            expected_mv_column,
            "Mv column should match expected values."
        );
        assert_eq!(
            trace[IoColumn::D.index()].to_cpu().values,
            expected_d_column,
            "D column should match expected values."
        );
    }

    #[test]
    fn test_io_table_trace_evaluation() {
        let mut io_table = InputTable::new();

        // Add rows to the I/O table.
        let rows = vec![
            IOTableRow::new(BaseField::zero(), BaseField::from(44), BaseField::one()),
            IOTableRow::new(BaseField::one(), BaseField::from(44), BaseField::from(2)),
            IOTableRow::new_dummy(BaseField::from(2)),
            IOTableRow::new_dummy(BaseField::from(3)),
        ];
        io_table.add_rows(rows);

        // Perform the trace evaluation.
        let (trace, claim) = io_table.trace_evaluation();

        // Calculate the expected parameters.
        let expected_log_n_rows: u32 = 2; // log2(2 rows)
        let expected_log_size = expected_log_n_rows + LOG_N_LANES;
        let expected_size = 1 << expected_log_size;

        // Construct the expected trace column for `mv`.
        let mut expected_columns = vec![BaseColumn::zeros(expected_size); IoColumn::count().0];

        // Populate the `clk` column with row data and padding.
        expected_columns[IoColumn::Clk.index()].data[0] = BaseField::zero().into();
        expected_columns[IoColumn::Clk.index()].data[1] = BaseField::one().into();
        expected_columns[IoColumn::Clk.index()].data[2] = BaseField::from(2).into();
        expected_columns[IoColumn::Clk.index()].data[3] = BaseField::from(3).into();

        // Populate the `ci` column with row data and padding.
        expected_columns[IoColumn::Ci.index()].data[0] = BaseField::from(44).into();
        expected_columns[IoColumn::Ci.index()].data[1] = BaseField::from(44).into();
        expected_columns[IoColumn::Ci.index()].data[2] = BaseField::zero().into();
        expected_columns[IoColumn::Ci.index()].data[3] = BaseField::zero().into();

        // Populate the `mv` column with row data and padding.
        expected_columns[IoColumn::Mv.index()].data[0] = BaseField::one().into();
        expected_columns[IoColumn::Mv.index()].data[1] = BaseField::from(2).into();
        expected_columns[IoColumn::Mv.index()].data[2] = BaseField::zero().into();
        expected_columns[IoColumn::Mv.index()].data[3] = BaseField::zero().into();

        // Populate the `d` column with row data and padding.
        expected_columns[IoColumn::D.index()].data[0] = BaseField::zero().into();
        expected_columns[IoColumn::D.index()].data[1] = BaseField::zero().into();
        expected_columns[IoColumn::D.index()].data[2] = BaseField::one().into();
        expected_columns[IoColumn::D.index()].data[3] = BaseField::one().into();

        // Create the expected domain for evaluation.
        let domain = CanonicCoset::new(expected_log_size).circle_domain();

        // Transform expected columns into CircleEvaluation.
        let expected_trace: TraceEval =
            expected_columns.into_iter().map(|col| CircleEvaluation::new(domain, col)).collect();

        // Create the expected claim.
        let expected_claim = IoClaim::new(expected_log_size);

        // Assert equality of the claim.
        assert_eq!(claim, expected_claim, "The claim should match the expected claim.");

        // Assert equality of the trace for all columns.
        for (actual, expected) in trace.iter().zip(expected_trace.iter()) {
            assert_eq!(
                actual.domain, expected.domain,
                "The domain of the trace column should match the expected domain."
            );
            assert_eq!(
                actual.to_cpu().values,
                expected.to_cpu().values,
                "The values of the trace column should match the expected values."
            );
        }
    }

    #[test]
    fn test_trace_evaluation_circle_domain() {
        let mut io_table = InputTable::new();
        io_table.add_rows(vec![
            IOTableRow::new(
                BaseField::zero(),
                InstructionType::ReadChar.to_base_field(),
                BaseField::one(),
            ),
            IOTableRow::new(
                BaseField::one(),
                InstructionType::ReadChar.to_base_field(),
                BaseField::from(2),
            ),
            IOTableRow::new(
                BaseField::from(3),
                InstructionType::ReadChar.to_base_field(),
                BaseField::from(7),
            ),
        ]);

        let (trace, claim) = io_table.trace_evaluation();

        // Verify the domain of the trace matches the expected circle domain.
        let domain = CanonicCoset::new(claim.log_size).circle_domain();
        for column in trace {
            assert_eq!(
                column.domain, domain,
                "Trace column domain should match the expected circle domain."
            );
        }
    }

    #[test]
    fn test_interaction_trace_evaluation() {
        let mut io_table = InputTable::new();
        // Trace rows are:
        // - Real row
        // - Real row
        // - Real row
        // - Dummy row (padding to the power of 2)
        let rows = vec![
            IOTableRow::new(
                BaseField::zero(),
                InstructionType::ReadChar.to_base_field(),
                BaseField::one(),
            ),
            IOTableRow::new(
                BaseField::one(),
                InstructionType::ReadChar.to_base_field(),
                BaseField::from(2),
            ),
            IOTableRow::new(
                BaseField::from(3),
                InstructionType::ReadChar.to_base_field(),
                BaseField::from(7),
            ),
            IOTableRow::new_dummy(BaseField::from(4)),
        ];
        io_table.add_rows(rows);

        let (trace_eval, claim) = io_table.trace_evaluation();

        let lookup_elements = IoElements::dummy();

        let (interaction_trace_eval, interaction_claim) =
            interaction_trace_evaluation(&trace_eval, &lookup_elements).unwrap();

        let log_size = trace_eval[0].domain.log_size();
        let mut logup_gen = LogupTraceGenerator::new(log_size);
        let mut col_gen = logup_gen.new_col();

        let mut denoms = [PackedSecureField::zero(); 4];
        let clk_col = &trace_eval[IoColumn::Clk.index()].data;
        let ci_col = &trace_eval[IoColumn::Ci.index()].data;
        let mv_col = &trace_eval[IoColumn::Mv.index()].data;
        // Construct the denominator for each row of the logUp column, from the main trace
        // evaluation.
        for vec_row in 0..1 << (log_size - LOG_N_LANES) {
            let clk = clk_col[vec_row];
            let ci = ci_col[vec_row];
            let mv = mv_col[vec_row];
            let denom: PackedSecureField = lookup_elements.combine(&[clk, ci, mv]);
            denoms[vec_row] = denom;
        }

        let num_0 = -PackedSecureField::one();
        let num_1 = -PackedSecureField::one();
        let num_2 = -PackedSecureField::one();
        let num_3 = PackedSecureField::zero();

        col_gen.write_frac(0, num_0, denoms[0]);
        col_gen.write_frac(1, num_1, denoms[1]);
        col_gen.write_frac(2, num_2, denoms[2]);
        col_gen.write_frac(3, num_3, denoms[3]);

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
}
