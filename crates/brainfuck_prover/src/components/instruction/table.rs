use brainfuck_vm::{machine::ProgramMemory, registers::Registers};
use num_traits::Zero;
use stwo_prover::core::fields::m31::BaseField;

use crate::utils::VALID_INSTRUCTIONS;

/// Represents a single row in the Instruction Table.
///
/// The Instruction Table stores:
/// - The instruction pointer (`ip`),
/// - The current instruction (`ci`),
/// - The next instruction (`ni`).
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct InstructionTableRow {
    /// Instruction pointer: points to the current instruction in the program.
    ip: BaseField,
    /// Current instruction: the instruction at the current instruction pointer.
    ci: BaseField,
    /// Next instruction:
    /// - The instruction that follows `ci` in the program,
    /// - 0 if out of bounds.
    ni: BaseField,
}

impl From<&Registers> for InstructionTableRow {
    fn from(registers: &Registers) -> Self {
        Self { ip: registers.ip, ci: registers.ci, ni: registers.ni }
    }
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
    table: Vec<InstructionTableRow>,
}

impl InstructionTable {
    /// Creates a new, empty [`InstructionTable`].
    ///
    /// # Returns
    /// A new instance of [`InstructionTable`] with an empty table.
    pub const fn new() -> Self {
        Self { table: Vec::new() }
    }

    /// Adds a new row to the Instruction Table.
    ///
    /// # Arguments
    /// * `row` - The [`InstructionTableRow`] to add to the table.
    ///
    /// This method pushes a new [`InstructionTableRow`] onto the `table` vector.
    fn add_row(&mut self, row: InstructionTableRow) {
        self.table.push(row);
    }

    /// Adds multiple rows to the Instruction Table.
    ///
    /// # Arguments
    /// * `rows` - A vector of [`InstructionTableRow`] to add to the table.
    ///
    /// This method extends the `table` vector with the provided rows.
    fn add_rows(&mut self, rows: Vec<InstructionTableRow>) {
        self.table.extend(rows);
    }

    /// Pads the instruction table with dummy rows up to the next power of two length.
    ///
    /// Each dummy row preserves the last instruction pointer
    /// with current and next instructions `ci` and `ni` set to zero.
    ///
    /// Does nothing if the table is empty.
    fn pad(&mut self) {
        if let Some(last_row) = self.table.last().cloned() {
            let trace_len = self.table.len();
            let padding_offset = (trace_len.next_power_of_two() - trace_len) as u32;
            for _ in 1..=padding_offset {
                self.add_row(InstructionTableRow { ip: last_row.ip, ..Default::default() });
            }
        }
    }
}

impl From<(Vec<Registers>, &ProgramMemory)> for InstructionTable {
    fn from((execution_trace, program_memory): (Vec<Registers>, &ProgramMemory)) -> Self {
        let mut program = Vec::new();

        let code = program_memory.code();

        for (index, ci) in code.iter().enumerate() {
            if !VALID_INSTRUCTIONS.contains(ci) {
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

        let mut sorted_registers = [program, execution_trace].concat();
        sorted_registers.sort_by_key(|r| (r.ip, r.clk));

        let instruction_rows = sorted_registers.iter().map(Into::into).collect();

        let mut instruction_table = Self::new();
        instruction_table.add_rows(instruction_rows);

        instruction_table.pad();

        instruction_table
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::{
        DECREMENT_INSTRUCTION_BF, INCREMENT_INSTRUCTION_BF, INPUT_INSTRUCTION_BF,
        JUMP_IF_NON_ZERO_INSTRUCTION_BF, JUMP_IF_ZERO_INSTRUCTION_BF, OUTPUT_INSTRUCTION_BF,
        SHIFT_LEFT_INSTRUCTION_BF, SHIFT_RIGHT_INSTRUCTION_BF,
    };
    use brainfuck_vm::{compiler::Compiler, test_helper::create_test_machine};
    use num_traits::{One, Zero};

    #[test]
    fn test_instruction_table_new() {
        let instruction_table = InstructionTable::new();
        assert!(
            instruction_table.table.is_empty(),
            "Instruction table should be empty upon initialization."
        );
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
                ip: BaseField::zero(),
                ci: BaseField::from(43),
                ni: BaseField::from(91),
            },
            InstructionTableRow {
                ip: BaseField::one(),
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
    fn test_instruction_table_from_registers_empty() {
        // Create an empty vector of registers
        let registers = vec![];

        // Convert to InstructionTable and ensure sorting
        let instruction_table = InstructionTable::from((registers, &Default::default()));

        // Check that the table is empty
        assert!(instruction_table.table.is_empty());
    }

    #[test]
    fn test_instruction_table_from_registers_example_program() {
        // Create a small program and compile it
        let code = "+>,<[>+.<-]";
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
        let ins_0 = InstructionTableRow {
            ip: BaseField::zero(),
            ci: INCREMENT_INSTRUCTION_BF,
            ni: SHIFT_RIGHT_INSTRUCTION_BF,
        };

        let ins_1 = InstructionTableRow {
            ip: BaseField::one(),
            ci: SHIFT_RIGHT_INSTRUCTION_BF,
            ni: INPUT_INSTRUCTION_BF,
        };

        let ins_2 = InstructionTableRow {
            ip: BaseField::from(2),
            ci: INPUT_INSTRUCTION_BF,
            ni: SHIFT_LEFT_INSTRUCTION_BF,
        };

        let ins_3 = InstructionTableRow {
            ip: BaseField::from(3),
            ci: SHIFT_LEFT_INSTRUCTION_BF,
            ni: JUMP_IF_ZERO_INSTRUCTION_BF,
        };
        let ins_4 = InstructionTableRow {
            ip: BaseField::from(4),
            ci: JUMP_IF_ZERO_INSTRUCTION_BF,
            ni: BaseField::from(12),
        };
        let ins_6 = InstructionTableRow {
            ip: BaseField::from(6),
            ci: SHIFT_RIGHT_INSTRUCTION_BF,
            ni: INCREMENT_INSTRUCTION_BF,
        };
        let ins_7 = InstructionTableRow {
            ip: BaseField::from(7),
            ci: INCREMENT_INSTRUCTION_BF,
            ni: OUTPUT_INSTRUCTION_BF,
        };
        let ins_8 = InstructionTableRow {
            ip: BaseField::from(8),
            ci: OUTPUT_INSTRUCTION_BF,
            ni: SHIFT_LEFT_INSTRUCTION_BF,
        };
        let ins_9 = InstructionTableRow {
            ip: BaseField::from(9),
            ci: SHIFT_LEFT_INSTRUCTION_BF,
            ni: DECREMENT_INSTRUCTION_BF,
        };
        let inst_10 = InstructionTableRow {
            ip: BaseField::from(10),
            ci: DECREMENT_INSTRUCTION_BF,
            ni: JUMP_IF_NON_ZERO_INSTRUCTION_BF,
        };
        let ins_11 = InstructionTableRow {
            ip: BaseField::from(11),
            ci: JUMP_IF_NON_ZERO_INSTRUCTION_BF,
            ni: BaseField::from(6),
        };

        let padded_rows = vec![
            InstructionTableRow {
                ip: BaseField::from(13),
                ci: BaseField::zero(),
                ni: BaseField::zero(),
            };
            10
        ];

        let mut expected_instruction_table = InstructionTable {
            table: vec![
                ins_0.clone(),
                ins_0,
                ins_1.clone(),
                ins_1,
                ins_2.clone(),
                ins_2,
                ins_3.clone(),
                ins_3,
                ins_4.clone(),
                ins_4,
                ins_6.clone(),
                ins_6,
                ins_7.clone(),
                ins_7,
                ins_8.clone(),
                ins_8,
                ins_9.clone(),
                ins_9,
                inst_10.clone(),
                inst_10,
                ins_11.clone(),
                ins_11,
            ],
        };

        expected_instruction_table.add_rows(padded_rows);

        // Verify that the instruction table is correct
        assert_eq!(instruction_table, expected_instruction_table);
    }

    #[test]
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
        let instruction_table: InstructionTable = (trace, machine.program()).into();

        let ins_0 = InstructionTableRow {
            ip: BaseField::zero(),
            ci: JUMP_IF_ZERO_INSTRUCTION_BF,
            ni: BaseField::from(4),
        };

        let ins_2 = InstructionTableRow {
            ip: BaseField::from(2),
            ci: DECREMENT_INSTRUCTION_BF,
            ni: JUMP_IF_NON_ZERO_INSTRUCTION_BF,
        };

        let ins_3 = InstructionTableRow {
            ip: BaseField::from(3),
            ci: JUMP_IF_NON_ZERO_INSTRUCTION_BF,
            ni: BaseField::from(2),
        };

        let padded_rows = vec![
            InstructionTableRow {
                ip: BaseField::from(5),
                ci: BaseField::zero(),
                ni: BaseField::zero(),
            };
            4
        ];
        let mut expected_instruction_table =
            InstructionTable { table: vec![ins_0.clone(), ins_0, ins_2, ins_3] };

        expected_instruction_table.add_rows(padded_rows);

        // Verify that the instruction table is correct
        assert_eq!(instruction_table, expected_instruction_table);
    }
}
