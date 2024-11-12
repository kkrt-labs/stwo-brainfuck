use brainfuck_vm::{machine::ProgramMemory, registers::Registers};
use num_traits::Zero;
use stwo_prover::core::fields::m31::BaseField;

/// Represents a single row in the Instruction Table.
///
/// The Instruction Table stores:
/// - The instruction pointer (`ip`),
/// - The current instruction (`ci`),
/// - The next instruction (`ni`).
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct InstructionTableRow {
    /// Instruction pointer: points to the current instruction in the program.
    pub ip: BaseField,
    /// Current instruction: the instruction at the current instruction pointer.
    pub ci: BaseField,
    /// Next instruction:
    /// - The instruction that follows `ci` in the program,
    /// - 0 if out of bounds.
    pub ni: BaseField,
}

/// Represents the Instruction Table, which holds the instruction sequence
/// for the Brainfuck virtual machine.
///
/// The Instruction Table is constructed by concatenating the program's list of
/// instructions with the execution trace, and then sorting by instruction
/// pointer and cycle. It is used to verify that the program being executed
/// matches the correct instruction sequence.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct InstructionTable {
    /// A vector of [`InstructionTableRow`] representing the table rows.
    pub table: Vec<InstructionTableRow>,
}

impl InstructionTable {
    /// Creates a new, empty [`InstructionTable`].
    ///
    /// # Returns
    /// A new instance of [`InstructionTable`] with an empty table.
    pub const fn new() -> Self {
        Self { table: Vec::new() }
    }

    /// Adds a new row to the Instruction Table from the provided registers.
    ///
    /// # Arguments
    /// * `ip` - The instruction pointer for the new row.
    /// * `ci` - The current instruction for the new row.
    /// * `ni` - The next instruction for the new row.
    ///
    /// This method pushes a new [`InstructionTableRow`] onto the `table` vector.
    pub fn add_row_from_registers(&mut self, ip: BaseField, ci: BaseField, ni: BaseField) {
        self.table.push(InstructionTableRow { ip, ci, ni });
    }

    /// Adds a new row to the Instruction Table.
    ///
    /// # Arguments
    /// * `row` - The [`InstructionTableRow`] to add to the table.
    ///
    /// This method pushes a new [`InstructionTableRow`] onto the `table` vector.
    pub fn add_row(&mut self, row: InstructionTableRow) {
        self.table.push(row);
    }

    /// Adds multiple rows to the Instruction Table.
    ///
    /// # Arguments
    /// * `rows` - A vector of [`InstructionTableRow`] to add to the table.
    ///
    /// This method extends the `table` vector with the provided rows.
    pub fn add_rows(&mut self, rows: Vec<InstructionTableRow>) {
        self.table.extend(rows);
    }

    /// Retrieves a reference to a specific row in the Instruction Table.
    ///
    /// # Arguments
    /// * `row` - The [`InstructionTableRow`] to search for in the table.
    ///
    /// # Returns
    /// An `Option` containing a reference to the matching row if found,
    /// or `None` if the row does not exist in the table.
    pub fn get_row(&self, row: &InstructionTableRow) -> Option<&InstructionTableRow> {
        self.table.iter().find(|r| *r == row)
    }

    /// Retrieves the last row in the Instruction Table.
    ///
    /// # Returns
    /// An `Option` containing a reference to the last [`InstructionTableRow`] in the table,
    /// or `None` if the table is empty.
    pub fn last_row(&self) -> Option<&InstructionTableRow> {
        self.table.last()
    }
}

impl From<(Vec<Registers>, &ProgramMemory)> for InstructionTable {
    fn from(input: (Vec<Registers>, &ProgramMemory)) -> Self {
        // Create an empty vector to store the program instructions.
        let mut program = Vec::new();

        // Extract the program's code from the `ProgramMemory`.
        let code = input.1.code();

        // Define valid Brainfuck instructions to process.
        // TODO: to be moved somewhere else in a follow-up PR.
        let valid_instructions = [
            BaseField::from(b'>' as u32),
            BaseField::from(b'<' as u32),
            BaseField::from(b'+' as u32),
            BaseField::from(b'-' as u32),
            BaseField::from(b'.' as u32),
            BaseField::from(b',' as u32),
            BaseField::from(b'[' as u32),
            BaseField::from(b']' as u32),
        ];

        // Iterate over the code and collect valid instructions.
        for (index, ci) in code.iter().enumerate() {
            // Skip invalid instructions.
            if !valid_instructions.contains(ci) {
                continue;
            }

            // Create a `Registers` object for each valid instruction and its next instruction.
            program.push(Registers {
                ip: BaseField::from(index as u32),
                ci: *ci,
                ni: if index == code.len() - 1 {
                    BaseField::zero()
                } else {
                    BaseField::from(code[index + 1])
                },
                ..Default::default()
            });
        }

        // Concatenate the program's instructions with the provided execution trace.
        let mut sorted_registers = [program, input.0].concat();
        // Sort the registers by:
        // 1. `ip` (instruction pointer)
        // 2. `clk` (clock cycle)
        sorted_registers.sort_by(|a, b| a.ip.cmp(&b.ip).then_with(|| a.clk.cmp(&b.clk)));

        // Initialize a new instruction table to store the sorted and processed rows.
        let mut instruction_table = Self::new();

        for register in &sorted_registers {
            // Add the current register to the instruction table.
            instruction_table.add_row(InstructionTableRow {
                ip: register.ip,
                ci: register.ci,
                ni: register.ni,
            });
        }

        // If the last row marks the end of the program, remove it:
        // - `ci` = 0 and `ni` = 0
        if let Some(last_row) = instruction_table.last_row() {
            if last_row.ci == BaseField::zero() && last_row.ni == BaseField::zero() {
                instruction_table.table.pop();
            }
        }

        // Return the fully constructed and populated instruction table.
        instruction_table
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use brainfuck_vm::{compiler::Compiler, test_helper::create_test_machine};
    use num_traits::Zero;

    #[test]
    fn test_instruction_table_new() {
        let instruction_table = InstructionTable::new();
        assert!(
            instruction_table.table.is_empty(),
            "Instruction table should be empty upon initialization."
        );
    }

    #[test]
    fn test_add_row_front_registers() {
        let mut instruction_table = InstructionTable::new();
        // Create a row to add to the table
        let row = InstructionTableRow {
            ip: BaseField::zero(),
            ci: BaseField::from(43),
            ni: BaseField::from(91),
        };
        // Add the row to the table
        instruction_table.add_row_from_registers(
            BaseField::zero(),
            BaseField::from(43),
            BaseField::from(91),
        );
        // Check that the table contains the added row
        assert_eq!(instruction_table.table, vec![row], "Added row should match the expected row.");
    }

    #[test]
    fn test_add_row() {
        let mut instruction_table = InstructionTable::new();
        // Create a row to add to the table
        let row = InstructionTableRow {
            ip: BaseField::zero(),
            ci: BaseField::from(43),
            ni: BaseField::from(91),
        };
        // Add the row to the table
        instruction_table.add_row(row.clone());
        // Check that the table contains the added row
        assert_eq!(instruction_table.table, vec![row], "Added row should match the expected row.");
    }

    #[test]
    fn test_add_multiple_rows() {
        let mut instruction_table = InstructionTable::new();
        // Create a vector of rows to add to the table
        let rows = vec![
            InstructionTableRow {
                ip: BaseField::from(0),
                ci: BaseField::from(43),
                ni: BaseField::from(91),
            },
            InstructionTableRow {
                ip: BaseField::from(1),
                ci: BaseField::from(91),
                ni: BaseField::from(9),
            },
            InstructionTableRow {
                ip: BaseField::from(2),
                ci: BaseField::from(62),
                ni: BaseField::from(43),
            },
        ];
        // Add the rows to the table
        instruction_table.add_rows(rows.clone());
        // Check that the table contains the added rows
        assert_eq!(instruction_table, InstructionTable { table: rows });
    }

    #[test]
    fn test_get_existing_row() {
        let mut instruction_table = InstructionTable::new();
        // Create a row to add to the table
        let row = InstructionTableRow {
            ip: BaseField::from(0),
            ci: BaseField::from(43),
            ni: BaseField::from(91),
        };
        // Add the row to the table
        instruction_table.add_row(row.clone());
        // Retrieve the row from the table
        let retrieved = instruction_table.get_row(&row);
        // Check that the retrieved row matches the added row
        assert_eq!(retrieved.unwrap(), &row, "Retrieved row should match the added row.");
    }

    #[test]
    fn test_get_non_existing_row() {
        let instruction_table = InstructionTable::new();
        // Create a row to search for in the table
        let row = InstructionTableRow {
            ip: BaseField::from(0),
            ci: BaseField::from(43),
            ni: BaseField::from(91),
        };
        // Try to retrieve the non-existing row from the table
        let retrieved = instruction_table.get_row(&row);
        // Check that the retrieved row is None
        assert!(retrieved.is_none(), "Should return None for a non-existing row.");
    }

    #[test]
    fn test_instruction_table_last_row() {
        let mut instruction_table = InstructionTable::new();

        // Initially, the table should be empty, so last_row should return None
        assert!(instruction_table.last_row().is_none(), "The table should be empty initially.");

        // Add a row to the table
        let row = InstructionTableRow {
            ip: BaseField::from(1),
            ci: BaseField::from(2),
            ni: BaseField::from(3),
        };
        instruction_table.add_row(row.clone());

        // Now, last_row should return a reference to the added row
        assert_eq!(
            instruction_table.last_row(),
            Some(&row),
            "The last row should match the added row."
        );

        // Add another row
        let second_row = InstructionTableRow {
            ip: BaseField::from(4),
            ci: BaseField::from(5),
            ni: BaseField::from(6),
        };
        instruction_table.add_row(second_row.clone());

        // Now, last_row should return a reference to the second row
        assert_eq!(
            instruction_table.last_row(),
            Some(&second_row),
            "The last row should match the second added row."
        );
    }

    #[test]
    fn test_instruction_table_from_registers_empty() {
        // Create an empty vector of registers
        let registers = vec![];

        // Convert to InstructionTable and ensure sorting
        let instruction_table = InstructionTable::from((registers, &Default::default()));

        // Check that the table is empty
        assert!(instruction_table.table.is_empty());
    }

    #[test]
    #[allow(clippy::cast_lossless, clippy::too_many_lines)]
    fn test_instruction_table_from_registers_example_program() {
        // Create a small program and compile it
        // Reference: https://neptune.cash/learn/brainfuck-tutorial/
        let code = "++>,<[>+.<-]";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        // Create a machine and execute the program
        let (mut machine, _) = create_test_machine(&instructions, &[1]);
        let () = machine.execute().expect("Failed to execute machine");

        // Get the trace of the executed program
        let trace = machine.get_trace();

        // Convert the trace to an `InstructionTable`
        let instruction_table: InstructionTable = (trace, machine.program()).into();

        // Create the expected `InstructionTable`
        let expected_instruction_table = InstructionTable {
            table: vec![
                InstructionTableRow {
                    ip: BaseField::from(0),
                    ci: BaseField::from(b'+' as u32),
                    ni: BaseField::from(b'+' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(0),
                    ci: BaseField::from(b'+' as u32),
                    ni: BaseField::from(b'+' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(1),
                    ci: BaseField::from(b'+' as u32),
                    ni: BaseField::from(b'>' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(1),
                    ci: BaseField::from(b'+' as u32),
                    ni: BaseField::from(b'>' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(2),
                    ci: BaseField::from(b'>' as u32),
                    ni: BaseField::from(b',' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(2),
                    ci: BaseField::from(b'>' as u32),
                    ni: BaseField::from(b',' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(3),
                    ci: BaseField::from(b',' as u32),
                    ni: BaseField::from(b'<' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(3),
                    ci: BaseField::from(b',' as u32),
                    ni: BaseField::from(b'<' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(4),
                    ci: BaseField::from(b'<' as u32),
                    ni: BaseField::from(b'[' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(4),
                    ci: BaseField::from(b'<' as u32),
                    ni: BaseField::from(b'[' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(5),
                    ci: BaseField::from(b'[' as u32),
                    ni: BaseField::from(13),
                },
                InstructionTableRow {
                    ip: BaseField::from(5),
                    ci: BaseField::from(b'[' as u32),
                    ni: BaseField::from(13),
                },
                InstructionTableRow {
                    ip: BaseField::from(7),
                    ci: BaseField::from(b'>' as u32),
                    ni: BaseField::from(b'+' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(7),
                    ci: BaseField::from(b'>' as u32),
                    ni: BaseField::from(b'+' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(7),
                    ci: BaseField::from(b'>' as u32),
                    ni: BaseField::from(b'+' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(8),
                    ci: BaseField::from(b'+' as u32),
                    ni: BaseField::from(b'.' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(8),
                    ci: BaseField::from(b'+' as u32),
                    ni: BaseField::from(b'.' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(8),
                    ci: BaseField::from(b'+' as u32),
                    ni: BaseField::from(b'.' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(9),
                    ci: BaseField::from(b'.' as u32),
                    ni: BaseField::from(b'<' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(9),
                    ci: BaseField::from(b'.' as u32),
                    ni: BaseField::from(b'<' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(9),
                    ci: BaseField::from(b'.' as u32),
                    ni: BaseField::from(b'<' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(10),
                    ci: BaseField::from(b'<' as u32),
                    ni: BaseField::from(b'-' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(10),
                    ci: BaseField::from(b'<' as u32),
                    ni: BaseField::from(b'-' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(10),
                    ci: BaseField::from(b'<' as u32),
                    ni: BaseField::from(b'-' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(11),
                    ci: BaseField::from(b'-' as u32),
                    ni: BaseField::from(b']' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(11),
                    ci: BaseField::from(b'-' as u32),
                    ni: BaseField::from(b']' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(11),
                    ci: BaseField::from(b'-' as u32),
                    ni: BaseField::from(b']' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(12),
                    ci: BaseField::from(b']' as u32),
                    ni: BaseField::from(7),
                },
                InstructionTableRow {
                    ip: BaseField::from(12),
                    ci: BaseField::from(b']' as u32),
                    ni: BaseField::from(7),
                },
                InstructionTableRow {
                    ip: BaseField::from(12),
                    ci: BaseField::from(b']' as u32),
                    ni: BaseField::from(7),
                },
            ],
        };

        // Verify that the instruction table is correct
        assert_eq!(instruction_table, expected_instruction_table);
    }

    #[test]
    #[allow(clippy::cast_lossless)]
    fn test_instruction_table_program_unused_instruction() {
        // We chose a simple program that has unused instructions
        // The goal is to verify that the merge between the trace and the program is correct
        let code = "[-]";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        // Create a machine and execute the program
        let (mut machine, _) = create_test_machine(&instructions, &[]);
        let () = machine.execute().expect("Failed to execute machine");

        // Get the trace of the executed program
        let trace = machine.get_trace();

        // Convert the trace to an `InstructionTable`
        let instruction_table: InstructionTable = (trace.clone(), machine.program()).into();

        println!("trace: {:?}", trace);
        println!("program {:?}", machine.program());
        println!("instruction_table: {:?}", instruction_table);

        let expected_instruction_table = InstructionTable {
            table: vec![
                InstructionTableRow {
                    ip: BaseField::from(0),
                    ci: BaseField::from(b'[' as u32),
                    ni: BaseField::from(4),
                },
                InstructionTableRow {
                    ip: BaseField::from(0),
                    ci: BaseField::from(b'[' as u32),
                    ni: BaseField::from(4),
                },
                InstructionTableRow {
                    ip: BaseField::from(2),
                    ci: BaseField::from(b'-' as u32),
                    ni: BaseField::from(b']' as u32),
                },
                InstructionTableRow {
                    ip: BaseField::from(3),
                    ci: BaseField::from(b']' as u32),
                    ni: BaseField::from(2),
                },
            ],
        };

        // Verify that the instruction table is correct
        assert_eq!(instruction_table, expected_instruction_table);
    }
}
