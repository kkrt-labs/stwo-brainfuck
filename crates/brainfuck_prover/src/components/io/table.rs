use crate::components::{Claim, Trace, TraceEval};
use brainfuck_vm::{instruction::InstructionType, registers::Registers};
use stwo_prover::core::{
    backend::{
        simd::{column::BaseColumn, m31::LOG_N_LANES},
        Column,
    },
    fields::m31::BaseField,
    poly::circle::{CanonicCoset, CircleEvaluation},
};

/// Represents a single row in the I/O Table.
///
/// The I/O Table stores:
/// - The memory value (`mv`),
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct IOTableRow {
    /// Memory value: value of the cell pointer by `mp` - values in [0..2^31 - 1)
    pub mv: BaseField,
}

impl IOTableRow {
    pub const fn new(mv: BaseField) -> Self {
        Self { mv }
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
    pub fn add_row_from_register(&mut self, mv: BaseField) {
        self.table.push(IOTableRow { mv });
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
    /// Each dummy row sets the memory value register `mv` to zero.
    ///
    /// Does nothing if the table is empty.
    fn pad(&mut self) {
        let trace_len = self.table.len();
        let padding_offset = (trace_len.next_power_of_two() - trace_len) as u32;
        for _ in 0..padding_offset {
            let dummy_row = IOTableRow::default();
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
    pub fn trace_evaluation(&self) -> (TraceEval, Claim) {
        let n_rows = self.table.len() as u32;

        // It is possible that the table is empty because the program has no input or output.
        if n_rows == 0 {
            return (TraceEval::new(), Claim { log_size: 0, trace: Trace::Io });
        }

        // Compute `log_n_rows`, the base-2 logarithm of the number of rows.
        let log_n_rows = n_rows.ilog2();

        // Add `LOG_N_LANES` to account for SIMD optimization.
        let log_size = log_n_rows + LOG_N_LANES;

        // Initialize a trace with 1 column (`mv`), each column containing `2^log_size` entries
        // initialized to zero.
        let mut trace = vec![BaseColumn::zeros(1 << log_size)];

        // Populate the column with data from the table rows.
        for (index, row) in self.table.iter().enumerate().take(1 << log_n_rows) {
            trace[IoColumn::Io.index()].data[index] = row.mv.into();
        }

        // Create a circle domain using a canonical coset.
        let domain = CanonicCoset::new(log_size).circle_domain();

        // Map the column into the circle domain.
        let trace = trace.into_iter().map(|col| CircleEvaluation::new(domain, col)).collect();

        // Return the evaluated trace and a claim containing the log size of the domain.
        (trace, Claim { log_size, trace: Trace::Io })
    }
}

impl<const N: u32> From<Vec<Registers>> for IOTable<N> {
    fn from(registers: Vec<Registers>) -> Self {
        let mut io_table = Self::new();
        let rows = registers
            .into_iter()
            .filter(|register| register.ci == BaseField::from_u32_unchecked(N))
            .map(|x| IOTableRow { mv: x.mv })
            .collect();
        io_table.add_rows(rows);

        io_table.pad();

        io_table
    }
}

/// Input table (trace) for the Input component.
///
/// This table is made of the memory values (`mv` register) corresponding to
/// inputs (when the current instruction `ci` equals ',').
pub type InputTable = IOTable<{ InstructionType::ReadChar.to_u32() }>;

/// Output table (trace) for the Output component.
///
/// This table is made of the memory values (`mv` register) corresponding to
/// outputs (when the current instruction `ci` equals '.').
pub type OutputTable = IOTable<{ InstructionType::PutChar.to_u32() }>;

/// Enum representing the column indices in the IO trace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IoColumn {
    /// Column representing the input/output operations.
    Io,
}

impl IoColumn {
    /// Returns the index of the column in the IO table.
    pub const fn index(self) -> usize {
        match self {
            Self::Io => 0,
        }
    }

    /// Returns the total number of columns in the IO table.
    pub const fn count() -> usize {
        1
    }
}

#[cfg(test)]
mod tests {
    use crate::components::Trace;

    use super::*;
    use num_traits::One;

    type TestIOTable = IOTable<10>;

    #[test]
    fn test_io_row_new() {
        let row = IOTableRow::new(BaseField::from(91));
        let expected_row = IOTableRow { mv: BaseField::from(91) };
        assert_eq!(row, expected_row);
    }

    #[test]
    fn test_table_new() {
        let io_table = TestIOTable::new();
        assert!(io_table.table.is_empty(), "I/O Table should be empty upon initialization.");
    }

    #[test]
    fn test_table_add_row_from_register() {
        let mut io_table = TestIOTable::new();
        // Create a row to add to the table
        let row = IOTableRow::new(BaseField::from(91));
        // Add the row to the table
        io_table.add_row_from_register(BaseField::from(91));
        // Check that the table contains the added row
        assert_eq!(io_table.table, vec![row], "Added row should match the expected row.");
    }

    #[test]
    fn test_table_add_row() {
        let mut io_table = TestIOTable::new();
        // Create a row to add to the table
        let row = IOTableRow::new(BaseField::from(91));
        // Add the row to the table
        io_table.add_row(row.clone());
        // Check that the table contains the added row
        assert_eq!(io_table.table, vec![row], "Added row should match the expected row.");
    }

    #[test]
    fn test_table_add_multiple_rows() {
        let mut io_table = TestIOTable::new();
        // Create a vector of rows to add to the table
        let rows = vec![
            IOTableRow::new(BaseField::from(91)),
            IOTableRow::new(BaseField::from(9)),
            IOTableRow::new(BaseField::from(43)),
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

        let row = IOTableRow::new(BaseField::one());
        // let row = IOTableRow::new(BaseField::from(5));

        let mut expected_io_table: InputTable = IOTable::new();
        expected_io_table.add_row(row);

        assert_eq!(IOTable::from(registers), expected_io_table);
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

        let row = IOTableRow::new(BaseField::from(5));

        let mut expected_io_table: OutputTable = IOTable::new();
        expected_io_table.add_row(row);

        assert_eq!(IOTable::from(registers), expected_io_table);
    }

    #[test]
    fn test_trace_evaluation_empty_table() {
        let io_table = TestIOTable::new();

        // Perform the trace evaluation.
        let (trace, claim) = io_table.trace_evaluation();

        // Verify the claim log size is 0.
        assert_eq!(claim.log_size, 0, "The log size should be 0 for an empty table.");

        // Verify the trace is empty.
        assert!(trace.is_empty(), "The trace should be empty when the table has no rows.");
    }

    #[test]
    fn test_trace_evaluation_single_row() {
        let mut io_table = TestIOTable::new();
        io_table.add_row(IOTableRow::new(BaseField::from(42)));

        let (trace, claim) = io_table.trace_evaluation();

        // Verify the log size includes SIMD lanes.
        assert!(claim.log_size >= LOG_N_LANES, "Claim log size should include SIMD lanes.");

        // Verify the trace has one column (`mv`).
        assert_eq!(trace.len(), 1, "Trace should contain one column for 'mv'.");

        // Verify the content of the column.
        let expected_mv_column = vec![BaseField::from(42); 16];
        assert_eq!(
            trace[0].to_cpu().values,
            expected_mv_column,
            "'mv' column should match expected values."
        );
    }

    #[test]
    fn test_io_table_trace_evaluation() {
        let mut io_table = TestIOTable::new();

        // Add rows to the I/O table.
        let rows = vec![IOTableRow::new(BaseField::from(1)), IOTableRow::new(BaseField::from(2))];
        io_table.add_rows(rows);

        // Perform the trace evaluation.
        let (trace, claim) = io_table.trace_evaluation();

        // Calculate the expected parameters.
        let expected_log_n_rows: u32 = 1; // log2(2 rows)
        let expected_log_size = expected_log_n_rows + LOG_N_LANES;
        let expected_size = 1 << expected_log_size;

        // Construct the expected trace column for `mv`.
        let mut expected_columns = vec![BaseColumn::zeros(expected_size)];

        // Populate the `mv` column with row data and padding.
        expected_columns[0].data[0] = BaseField::from(1).into();
        expected_columns[0].data[1] = BaseField::from(2).into();

        // Create the expected domain for evaluation.
        let domain = CanonicCoset::new(expected_log_size).circle_domain();

        // Transform expected columns into CircleEvaluation.
        let expected_trace: TraceEval =
            expected_columns.into_iter().map(|col| CircleEvaluation::new(domain, col)).collect();

        // Create the expected claim.
        let expected_claim = Claim { log_size: expected_log_size, trace: Trace::Io };

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
        let mut io_table = TestIOTable::new();
        io_table.add_rows(vec![
            IOTableRow::new(BaseField::from(1)),
            IOTableRow::new(BaseField::from(2)),
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
}
