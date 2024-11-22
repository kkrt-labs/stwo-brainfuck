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

    /// Adds multiple rows to the Processor Table.
    ///
    /// # Arguments
    /// * `rows` - A vector of [`ProcessorTableRow`] to add to the table.
    ///
    /// This method extends the `table` vector with the provided rows.
    fn add_rows(&mut self, rows: Vec<ProcessorTableRow>) {
        self.table.extend(rows);
    }

    /// Pads the Processor table with dummy rows up to the next power of two length.
    ///
    /// Each dummy row increase clk, copy the others from the last step
    ///
    /// Does nothing if the table is empty.
    fn pad(&mut self) {
        if let Some(last_row) = self.table.last().cloned() {
            let trace_len = self.table.len();
            let padding_offset = (trace_len.next_power_of_two() - trace_len) as u32;
            for i in 1..=padding_offset {
                self.add_row(ProcessorTableRow {
                    clk: last_row.clk + BaseField::from(i),
                    ip: last_row.ip,
                    ..Default::default()
                });
            }
        }
    }
}

impl From<Vec<Registers>> for ProcessorTable {
    fn from(registers: Vec<Registers>) -> Self {
        let mut processor_table = Self::new();

        let rows = registers.iter().map(Into::into).collect();
        processor_table.add_rows(rows);
        processor_table.pad();

        processor_table
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use brainfuck_vm::{
        compiler::Compiler, registers::Registers, test_helper::create_test_machine,
    };
    use num_traits::{One, Zero};
    use stwo_prover::core::fields::FieldExpOps;

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

    #[test]
    fn test_processor_table_from_registers_example_program() {
        // Create a small program and compile it
        let code = "+>,<[>+.<-]";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        // Create a machine and execute the program
        let (mut machine, _) = create_test_machine(&instructions, &[1]);
        let () = machine.execute().expect("Failed to execute machine");

        // Get the trace of the executed program
        let trace = machine.trace();

        // Convert the trace to an `ProcessorTable`
        let processor_table: ProcessorTable = trace.into();

        // Create the expected `ProcessorTable`
        let process_0 = ProcessorTableRow {
            clk: BaseField::zero(),
            ip: BaseField::zero(),
            ci: BaseField::from(43),
            ni: BaseField::from(62),
            mp: BaseField::zero(),
            mv: BaseField::zero(),
            mvi: BaseField::zero(),
        };

        let process_1 = ProcessorTableRow {
            clk: BaseField::one(),
            ip: BaseField::one(),
            ci: BaseField::from(62),
            ni: BaseField::from(44),
            mp: BaseField::zero(),
            mv: BaseField::one(),
            mvi: BaseField::one(),
        };

        let process_2 = ProcessorTableRow {
            clk: BaseField::from(2),
            ip: BaseField::from(2),
            ci: BaseField::from(44),
            ni: BaseField::from(60),
            mp: BaseField::one(),
            mv: BaseField::zero(),
            mvi: BaseField::zero(),
        };

        let process_3 = ProcessorTableRow {
            clk: BaseField::from(3),
            ip: BaseField::from(3),
            ci: BaseField::from(60),
            ni: BaseField::from(91),
            mp: BaseField::one(),
            mv: BaseField::one(),
            mvi: BaseField::one(),
        };

        let process_4 = ProcessorTableRow {
            clk: BaseField::from(4),
            ip: BaseField::from(4),
            ci: BaseField::from(91),
            ni: BaseField::from(12),
            mp: BaseField::zero(),
            mv: BaseField::one(),
            mvi: BaseField::one(),
        };

        let process_5 = ProcessorTableRow {
            clk: BaseField::from(5),
            ip: BaseField::from(6),
            ci: BaseField::from(62),
            ni: BaseField::from(43),
            mp: BaseField::zero(),
            mv: BaseField::one(),
            mvi: BaseField::one(),
        };

        let process_6 = ProcessorTableRow {
            clk: BaseField::from(6),
            ip: BaseField::from(7),
            ci: BaseField::from(43),
            ni: BaseField::from(46),
            mp: BaseField::one(),
            mv: BaseField::one(),
            mvi: BaseField::one(),
        };

        let process_7 = ProcessorTableRow {
            clk: BaseField::from(7),
            ip: BaseField::from(8),
            ci: BaseField::from(46),
            ni: BaseField::from(60),
            mp: BaseField::one(),
            mv: BaseField::from(2),
            mvi: BaseField::from(2).inverse(),
        };

        let process_8 = ProcessorTableRow {
            clk: BaseField::from(8),
            ip: BaseField::from(9),
            ci: BaseField::from(60),
            ni: BaseField::from(45),
            mp: BaseField::one(),
            mv: BaseField::from(2),
            mvi: BaseField::from(2).inverse(),
        };

        let process_9 = ProcessorTableRow {
            clk: BaseField::from(9),
            ip: BaseField::from(10),
            ci: BaseField::from(45),
            ni: BaseField::from(93),
            mp: BaseField::zero(),
            mv: BaseField::one(),
            mvi: BaseField::one(),
        };

        let process_10 = ProcessorTableRow {
            clk: BaseField::from(10),
            ip: BaseField::from(11),
            ci: BaseField::from(93),
            ni: BaseField::from(6),
            mp: BaseField::zero(),
            mv: BaseField::zero(),
            mvi: BaseField::zero(),
        };

        let process_11 = ProcessorTableRow {
            clk: BaseField::from(11),
            ip: BaseField::from(13),
            ci: BaseField::zero(),
            ni: BaseField::zero(),
            mp: BaseField::zero(),
            mv: BaseField::zero(),
            mvi: BaseField::zero(),
        };

        let mut expected_processor_table = ProcessorTable {
            table: vec![
                process_0, process_1, process_2, process_3, process_4, process_5, process_6,
                process_7, process_8, process_9, process_10, process_11,
            ],
        };

        expected_processor_table.pad();

        // Verify that the processor table is correct
        assert_eq!(processor_table, expected_processor_table);
    }
}
