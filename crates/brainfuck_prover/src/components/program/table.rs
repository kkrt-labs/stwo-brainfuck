use brainfuck_vm::registers::Registers;
use num_traits::One;
use stwo_prover::core::fields::m31::BaseField;

use crate::components::TraceColumn;

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

/// Enum representing the column indices in the IO trace.
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
}
