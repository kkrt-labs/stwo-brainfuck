use brainfuck_vm::registers::Registers;
use num_traits::One;
use stwo_prover::core::{
    backend::{
        simd::{column::BaseColumn, m31::LOG_N_LANES},
        Column,
    },
    fields::m31::BaseField,
    poly::circle::{CanonicCoset, CircleEvaluation},
};

use crate::components::{ProgramClaim, TraceColumn, TraceError, TraceEval};

/// Represents a single row in the Program Table.
///
/// The Program Table stores:
/// - The instruction pointer (`ip`),
/// - The current instruction (`ci`),
/// - The next instruction (`ni`),
/// - The dummy flag (`d`),
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct ProgramTableRow {
    /// Instruction pointer: points to the current instruction in the program.
    ip: BaseField,
    /// Current instruction: the instruction at the current instruction pointer.
    ci: BaseField,
    /// Next instruction:
    /// - The instruction that follows `ci` in the program,
    /// - 0 if out of bounds.
    ni: BaseField,
    /// Dummy: Flag whether the entry is a dummy one or not.
    d: BaseField,
}

impl ProgramTableRow {
    /// Creates an entry for the [`ProgramTable`] which is considered 'real'.
    ///
    /// A 'real' entry, is an entry that is part of the execution trace from the Brainfuck program
    /// execution.
    pub fn new(ip: BaseField, ci: BaseField, ni: BaseField) -> Self {
        Self { ip, ci, ni, ..Default::default() }
    }

    /// Creates an entry for the [`ProgramTable`] which is considered 'dummy'.
    ///
    /// A 'dummy' entry, is an entry that is not part of the execution trace from the Brainfuck
    /// program execution.
    /// They are used to flag padding rows.
    pub fn new_dummy(ip: BaseField) -> Self {
        Self { ip, d: BaseField::one(), ..Default::default() }
    }
}

/// Represents the Program Table, which holds the required register for the Program component.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct ProgramTable {
    /// A vector of [`ProgramTableRow`] representing the table rows.
    pub table: Vec<ProgramTableRow>,
}

impl ProgramTable {
    /// Creates a new, empty [`ProgramTable`].
    ///
    /// # Returns
    /// A new instance of [`ProgramTable`] with an empty table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a new row to the [`ProgramTable`].
    ///
    /// # Arguments
    /// * `row` - The [`ProgramTableRow`] to add to the table.
    ///
    /// This method pushes a new [`ProgramTableRow`] onto the `table` vector.
    pub fn add_row(&mut self, row: ProgramTableRow) {
        self.table.push(row);
    }

    /// Adds multiple rows to the [`ProgramTable`].
    ///
    /// # Arguments
    /// * `rows` - A vector of [`ProgramTableRow`] to add to the table.
    ///
    /// This method extends the `table` vector with the provided rows.
    pub fn add_rows(&mut self, rows: Vec<ProgramTableRow>) {
        self.table.extend(rows);
    }

    /// Pads the [`ProgramTable`] with dummy entries up to the next power of two length.
    ///
    /// Each dummy entry preserves the last instruction pointer
    /// with current and next instructions `ci` and `ni` set to zero.
    ///
    /// Does nothing if the table is empty.
    fn pad(&mut self) {
        if let Some(last_entry) = self.table.last().cloned() {
            let trace_len = self.table.len();
            let padding_offset = (trace_len.next_power_of_two() - trace_len) as u32;
            for _ in 1..=padding_offset {
                self.add_row(ProgramTableRow::new_dummy(last_entry.ip));
            }
        }
    }

    /// Transforms the [`ProgramTable`] into a [`TraceEval`], to be committed when
    /// generating a STARK proof.
    ///
    /// The [`ProgramTable`] is transformed from an array of rows (one element = one step
    /// of all registers) to an array of columns (one element = all steps of one register).
    /// It is then evaluated on the circle domain.
    ///
    /// # Returns
    /// A tuple containing the evaluated trace and claim for STARK proof.
    ///
    /// # Errors
    /// Returns [`TraceError::EmptyTrace`] if the table is empty.
    pub fn trace_evaluation(&self) -> Result<(TraceEval, ProgramClaim), TraceError> {
        let n_rows = self.table.len() as u32;

        // If the table is empty, there is no data to evaluate, so return an error.
        if n_rows == 0 {
            return Err(TraceError::EmptyTrace);
        }

        // Compute `log_n_rows`, the base-2 logarithm of the number of rows.
        let log_n_rows = n_rows.ilog2();

        // Add `LOG_N_LANES` to account for SIMD optimization.
        let log_size = log_n_rows + LOG_N_LANES;

        // Initialize a trace with 4 columns (`ip`, `ci`, `ni`, `d`), each column containing
        // `2^log_size` entries initialized to zero.
        let mut trace = vec![BaseColumn::zeros(1 << log_size); 4];

        // Populate the column with data from the table rows.
        for (index, row) in self.table.iter().enumerate().take(1 << log_n_rows) {
            trace[ProgramColumn::Ip.index()].data[index] = row.ip.into();
            trace[ProgramColumn::Ci.index()].data[index] = row.ci.into();
            trace[ProgramColumn::Ni.index()].data[index] = row.ni.into();
            trace[ProgramColumn::D.index()].data[index] = row.d.into();
        }

        // Create a circle domain using a canonical coset.
        let domain = CanonicCoset::new(log_size).circle_domain();

        // Map the column into the circle domain.
        let trace = trace.into_iter().map(|col| CircleEvaluation::new(domain, col)).collect();

        // Return the evaluated trace and a claim containing the log size of the domain.
        Ok((trace, ProgramClaim::new(log_size)))
    }
}

impl From<&Vec<Registers>> for ProgramTable {
    fn from(registers: &Vec<Registers>) -> Self {
        let mut program_table = Self::new();

        let rows = registers.iter().map(|x| ProgramTableRow::new(x.ip, x.ci, x.ni)).collect();
        program_table.add_rows(rows);

        program_table.pad();

        program_table
    }
}

/// Enum representing the column indices in the Program trace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProgramColumn {
    /// Index of the `ip` register column in the Program trace.
    Ip,
    /// Index of the `ci` register column in the Program trace.
    Ci,
    /// Index of the `ni` register column in the Program trace.
    Ni,
    /// Index of the `d` register column in the Program trace.
    D,
}

impl ProgramColumn {
    /// Returns the index of the column in the Program table.
    pub const fn index(self) -> usize {
        match self {
            Self::Ip => 0,
            Self::Ci => 1,
            Self::Ni => 2,
            Self::D => 3,
        }
    }
}

impl TraceColumn for ProgramColumn {
    fn count() -> (usize, usize) {
        (4, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use brainfuck_vm::{
        compiler::Compiler, instruction::InstructionType, test_helper::create_test_machine,
    };
    use num_traits::{One, Zero};

    #[test]
    fn test_row_new() {
        let row = ProgramTableRow::new(
            BaseField::zero(),
            InstructionType::PutChar.to_base_field(),
            BaseField::from(91),
        );
        let expected_row = ProgramTableRow {
            ip: BaseField::zero(),
            ci: InstructionType::PutChar.to_base_field(),
            ni: BaseField::from(91),
            d: BaseField::zero(),
        };
        assert_eq!(row, expected_row);
    }

    #[test]
    fn test_row_new_dummy() {
        let row = ProgramTableRow::new_dummy(BaseField::from(5));
        let expected_row = ProgramTableRow {
            ip: BaseField::from(5),
            ci: BaseField::zero(),
            ni: BaseField::zero(),
            d: BaseField::one(),
        };
        assert_eq!(row, expected_row);
    }

    #[test]
    fn test_table_new() {
        let program_table = ProgramTable::new();
        assert!(
            program_table.table.is_empty(),
            "Program Table should be empty upon initialization."
        );
    }

    #[test]
    fn test_table_add_row() {
        let mut program_table = ProgramTable::new();
        // Create a row to add to the table
        let row = ProgramTableRow::new(
            BaseField::zero(),
            InstructionType::PutChar.to_base_field(),
            BaseField::from(91),
        );
        // Add the row to the table
        program_table.add_row(row.clone());
        // Check that the table contains the added row
        assert_eq!(program_table.table, vec![row], "Added row should match the expected row.");
    }

    #[test]
    fn test_table_add_multiple_rows() {
        let mut program_table = ProgramTable::new();
        // Create a vector of rows to add to the table
        let rows = vec![
            ProgramTableRow::new(
                BaseField::zero(),
                InstructionType::PutChar.to_base_field(),
                BaseField::from(91),
            ),
            ProgramTableRow::new(
                BaseField::one(),
                InstructionType::PutChar.to_base_field(),
                BaseField::from(9),
            ),
            ProgramTableRow::new(
                BaseField::from(4),
                InstructionType::PutChar.to_base_field(),
                BaseField::from(43),
            ),
        ];
        // Add the rows to the table
        program_table.add_rows(rows.clone());
        // Check that the table contains the added rows
        assert_eq!(program_table, ProgramTable { table: rows });
    }

    #[test]
    fn test_program_table_from_program_memory() {
        let code = "+>";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        // Create a machine and execute the program
        let (mut machine, _) = create_test_machine(&instructions, &[1]);
        let () = machine.execute().expect("Failed to execute machine");

        // Get the trace of the executed program
        let trace = machine.trace();

        let ins_0 = InstructionType::Plus.to_base_field();
        let ins_1 = InstructionType::Right.to_base_field();

        let row_0 = ProgramTableRow::new(BaseField::zero(), ins_0, ins_1);
        let row_1 = ProgramTableRow::new(BaseField::one(), ins_1, BaseField::zero());
        let row_2 = ProgramTableRow::new(2.into(), BaseField::zero(), BaseField::zero());
        let padded_row = ProgramTableRow::new_dummy(2.into());

        let mut expected_program_table = ProgramTable::new();
        expected_program_table.add_rows(vec![row_0, row_1, row_2, padded_row]);

        assert_eq!(ProgramTable::from(&trace), expected_program_table);
    }

    #[test]
    fn test_trace_evaluation_empty_table() {
        let program_table = ProgramTable::new();

        let result = program_table.trace_evaluation();

        assert!(matches!(result, Err(TraceError::EmptyTrace)));
    }

    #[allow(clippy::similar_names)]
    #[test]
    fn test_trace_evaluation_single_row() {
        let mut program_table = ProgramTable::new();
        program_table.add_row(ProgramTableRow::new(
            BaseField::one(),
            BaseField::from(44),
            BaseField::from(42),
        ));

        let (trace, claim) = program_table.trace_evaluation().unwrap();

        assert_eq!(claim.log_size, LOG_N_LANES, "Log size should include SIMD lanes.");
        assert_eq!(
            trace.len(),
            ProgramColumn::count().0,
            "Trace should contain one column per register."
        );

        // Expected values for the single row
        let expected_ip_column = vec![BaseField::one(); 1 << LOG_N_LANES];
        let expected_ci_column = vec![BaseField::from(44); 1 << LOG_N_LANES];
        let expected_ni_column = vec![BaseField::from(42); 1 << LOG_N_LANES];
        let expected_d_column = vec![BaseField::zero(); 1 << LOG_N_LANES];

        // Check that the entire column matches expected values
        assert_eq!(
            trace[ProgramColumn::Ip.index()].to_cpu().values,
            expected_ip_column,
            "Ip column should match expected values."
        );
        assert_eq!(
            trace[ProgramColumn::Ci.index()].to_cpu().values,
            expected_ci_column,
            "Ci column should match expected values."
        );
        assert_eq!(
            trace[ProgramColumn::Ni.index()].to_cpu().values,
            expected_ni_column,
            "Ni column should match expected values."
        );
        assert_eq!(
            trace[ProgramColumn::D.index()].to_cpu().values,
            expected_d_column,
            "D column should match expected values."
        );
    }

    #[test]
    fn test_program_table_trace_evaluation() {
        let mut program_table = ProgramTable::new();

        // Add rows to the Program table.
        let rows = vec![
            ProgramTableRow::new(BaseField::zero(), BaseField::from(44), BaseField::one()),
            ProgramTableRow::new(BaseField::one(), BaseField::from(44), BaseField::from(2)),
            ProgramTableRow::new_dummy(BaseField::from(2)),
            ProgramTableRow::new_dummy(BaseField::from(3)),
        ];
        program_table.add_rows(rows);

        // Perform the trace evaluation.
        let (trace, claim) = program_table.trace_evaluation().unwrap();

        // Calculate the expected parameters.
        let expected_log_n_rows: u32 = 2; // log2(2 rows)
        let expected_log_size = expected_log_n_rows + LOG_N_LANES;
        let expected_size = 1 << expected_log_size;

        // Construct the expected trace column for `ip`, `ci`, `ni` and `d`.
        let mut expected_columns = vec![BaseColumn::zeros(expected_size); ProgramColumn::count().0];

        // Populate the `ip` column with row data and padding.
        expected_columns[ProgramColumn::Ip.index()].data[0] = BaseField::zero().into();
        expected_columns[ProgramColumn::Ip.index()].data[1] = BaseField::one().into();
        expected_columns[ProgramColumn::Ip.index()].data[2] = BaseField::from(2).into();
        expected_columns[ProgramColumn::Ip.index()].data[3] = BaseField::from(3).into();

        // Populate the `ci` column with row data and padding.
        expected_columns[ProgramColumn::Ci.index()].data[0] = BaseField::from(44).into();
        expected_columns[ProgramColumn::Ci.index()].data[1] = BaseField::from(44).into();
        expected_columns[ProgramColumn::Ci.index()].data[2] = BaseField::zero().into();
        expected_columns[ProgramColumn::Ci.index()].data[3] = BaseField::zero().into();

        // Populate the `ni` column with row data and padding.
        expected_columns[ProgramColumn::Ni.index()].data[0] = BaseField::one().into();
        expected_columns[ProgramColumn::Ni.index()].data[1] = BaseField::from(2).into();
        expected_columns[ProgramColumn::Ni.index()].data[2] = BaseField::zero().into();
        expected_columns[ProgramColumn::Ni.index()].data[3] = BaseField::zero().into();

        // Populate the `d` column with row data and padding.
        expected_columns[ProgramColumn::D.index()].data[0] = BaseField::zero().into();
        expected_columns[ProgramColumn::D.index()].data[1] = BaseField::zero().into();
        expected_columns[ProgramColumn::D.index()].data[2] = BaseField::one().into();
        expected_columns[ProgramColumn::D.index()].data[3] = BaseField::one().into();

        // Create the expected domain for evaluation.
        let domain = CanonicCoset::new(expected_log_size).circle_domain();

        // Transform expected columns into CircleEvaluation.
        let expected_trace: TraceEval =
            expected_columns.into_iter().map(|col| CircleEvaluation::new(domain, col)).collect();

        // Create the expected claim.
        let expected_claim = ProgramClaim::new(expected_log_size);

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
        let mut program_table = ProgramTable::new();
        program_table.add_rows(vec![
            ProgramTableRow::new(
                BaseField::zero(),
                InstructionType::ReadChar.to_base_field(),
                BaseField::one(),
            ),
            ProgramTableRow::new(
                BaseField::one(),
                InstructionType::ReadChar.to_base_field(),
                BaseField::from(2),
            ),
            ProgramTableRow::new(
                BaseField::from(3),
                InstructionType::ReadChar.to_base_field(),
                BaseField::from(7),
            ),
        ]);

        let (trace, claim) = program_table.trace_evaluation().unwrap();

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
