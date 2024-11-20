use brainfuck_vm::registers::Registers;
use stwo_prover::core::fields::m31::BaseField;

/// Represents a single row in the Processor Table.
///
/// The Processor Table ensures consistency for the part of the execution that
/// relates to the registers of the Brainfuck virtual machine. It records all
/// register values for each cycle that the program ran.
///
/// Each row contains the values for the following registers:
/// - `clk`: The clock cycle counter, represents the current step.
/// - `ip`: The instruction pointer.
/// - `ci`: The current instruction.
/// - `ni`: The next instruction.
/// - `mp`: The memory pointer.
/// - `mv`: The memory value.
/// - `mvi`: The memory value inverse.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct ProcessorTableRow {
    /// Clock cycle counter: the current step.
    clk: BaseField,
    /// Instruction pointer: the pointer to the current instruction.
    ip: BaseField,
    /// Current instruction: the opcode at the current instruction pointer.
    ci: BaseField,
    /// Next instruction: the opcode that follows `ci`, or 0 if out of bounds.
    ni: BaseField,
    /// Memory pointer: points to the current cell in the memory array.
    mp: BaseField,
    /// Memory value: the value at the current memory cell.
    mv: BaseField,
    /// Memory value inverse: the modular inverse of `mv` on the cell values' range (over
    /// [`BaseField`])
    mvi: BaseField,
}

impl From<&Registers> for ProcessorTableRow {
    fn from(registers: &Registers) -> Self {
        Self {
            clk: registers.clk,
            ip: registers.ip,
            ci: registers.ci,
            ni: registers.ni,
            mp: registers.mp,
            mv: registers.mv,
            mvi: registers.mvi,
        }
    }
}

/// Represents the Processor Table, which records the register values for
/// each cycle that the program ran.
///
/// The Processor Table is used to verify the consistency of the execution,
/// ensuring that all instructions mutate the state correctly according to
/// the Brainfuck instruction set.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct ProcessorTable {
    /// A vector of [`ProcessorTableRow`] representing the rows of the table.
    table: Vec<ProcessorTableRow>,
}

impl ProcessorTable {
    /// Creates a new, empty [`ProcessorTable`].
    ///
    /// # Returns
    /// A new instance of [`ProcessorTable`] with an empty table.
    pub const fn new() -> Self {
        Self { table: Vec::new() }
    }

    /// Adds a new row to the Processor Table.
    ///
    /// # Arguments
    /// * `row` - The [`ProcessorTableRow`] to add to the table.
    ///
    /// This method pushes a new [`ProcessorTableRow`] onto the `table` vector.
    pub fn add_row(&mut self, row: ProcessorTableRow) {
        self.table.push(row);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use brainfuck_vm::registers::Registers;
    use num_traits::{One, Zero};

    #[test]
    fn test_processor_table_row_from_registers() {
        let registers = Registers {
            clk: BaseField::one(),
            ip: BaseField::from(5),
            ci: BaseField::from(43),
            ni: BaseField::from(91),
            mp: BaseField::from(2),
            mv: BaseField::from(7),
            mvi: BaseField::zero(),
        };

        let row = ProcessorTableRow::from(&registers);

        let expected_row = ProcessorTableRow {
            clk: BaseField::one(),
            ip: BaseField::from(5),
            ci: BaseField::from(43),
            ni: BaseField::from(91),
            mp: BaseField::from(2),
            mv: BaseField::from(7),
            mvi: BaseField::zero(),
        };

        assert_eq!(row, expected_row);
    }

    #[test]
    fn test_processor_table_new() {
        let processor_table = ProcessorTable::new();

        assert!(processor_table.table.is_empty());
    }

    #[test]
    fn test_add_row() {
        let mut processor_table = ProcessorTable::new();

        let row = ProcessorTableRow {
            clk: BaseField::from(10),
            ip: BaseField::from(15),
            ci: BaseField::from(43),
            ni: BaseField::from(91),
            mp: BaseField::from(20),
            mv: BaseField::from(25),
            mvi: BaseField::one(),
        };

        processor_table.add_row(row.clone());

        assert_eq!(processor_table.table, vec![row]);
    }

    #[test]
    fn test_add_multiple_rows() {
        let mut processor_table = ProcessorTable::new();

        let rows = vec![
            ProcessorTableRow {
                clk: BaseField::from(1),
                ip: BaseField::from(5),
                ci: BaseField::from(43),
                ni: BaseField::from(91),
                mp: BaseField::from(10),
                mv: BaseField::from(15),
                mvi: BaseField::zero(),
            },
            ProcessorTableRow {
                clk: BaseField::from(2),
                ip: BaseField::from(6),
                ci: BaseField::from(44),
                ni: BaseField::from(92),
                mp: BaseField::from(11),
                mv: BaseField::from(16),
                mvi: BaseField::one(),
            },
            ProcessorTableRow {
                clk: BaseField::from(3),
                ip: BaseField::from(7),
                ci: BaseField::from(45),
                ni: BaseField::from(93),
                mp: BaseField::from(12),
                mv: BaseField::from(17),
                mvi: BaseField::zero(),
            },
        ];

        for row in &rows {
            processor_table.add_row(row.clone());
        }

        assert_eq!(processor_table.table, rows,);
    }
}
