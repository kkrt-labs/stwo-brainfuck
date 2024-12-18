use crate::components::{ProcessorClaim, TraceColumn, TraceError, TraceEval};
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

/// Represents the Processor Table, which holds the required registers
/// for the Processor component.
///
/// The Processor Table ensures consistency for the part of the execution that
/// relates to the registers of the Brainfuck virtual machine. It records all
/// register values for each cycle that the program ran.
///
///
/// To ease constraints evaluation, each row of the Processor component
/// contains the current row and the next row in natural order.
/// This is done to avoid having to do costly bit-reversals, as constraints
/// are evaluated on the evaluation of the trace which is ordered in
/// a bit-reversed manner over the circle domain once the polynomials are interpolated.
///
/// The preliminary work to extract the fields from the execution trace,
/// the sorting and the padding is done through the [`ProcessorIntermediateTable`] struct.
///
/// Once done, we can build the Processor table from it, by pairing the consecutive
/// [`ProcessorTableEntry`] in [`ProcessorTableRow`].
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct ProcessorTable {
    /// A vector of [`ProcessorTableRow`] representing the table rows.
    table: Vec<ProcessorTableRow>,
}

impl ProcessorTable {
    /// Creates a new, empty [`ProcessorTable`].
    ///
    /// # Returns
    /// A new instance of [`ProcessorTable`] with an empty table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a new row to the Processor Table.
    ///
    /// # Arguments
    /// * `row` - The [`ProcessorTableRow`] to add to the table.
    ///
    /// This method pushes a new [`ProcessorTableRow`] onto the `table` vector.
    fn add_row(&mut self, row: ProcessorTableRow) {
        self.table.push(row);
    }

    /// Transforms the [`ProcessorTable`] into a [`TraceEval`], to be committed when
    /// generating a STARK proof.
    ///
    /// Converts the entry-based table into columnar format and evaluates it over
    /// the circle domain.
    ///
    /// # Returns
    /// A tuple containing the evaluated trace and claim for STARK proof.
    ///
    /// # Errors
    /// Returns `TraceError::EmptyTrace` if the table is empty.
    pub fn trace_evaluation(&self) -> Result<(TraceEval, ProcessorClaim), TraceError> {
        let n_rows = self.table.len() as u32;
        if n_rows == 0 {
            return Err(TraceError::EmptyTrace);
        }

        // Compute log size and adjust for SIMD lanes
        let log_n_rows = n_rows.ilog2();
        let log_size = log_n_rows + LOG_N_LANES;

        // Initialize trace columns
        let mut trace = vec![BaseColumn::zeros(1 << log_size); ProcessorColumn::count().0];

        // Fill columns with table data
        for (index, row) in self.table.iter().enumerate().take(1 << log_n_rows) {
            trace[ProcessorColumn::Clk.index()].data[index] = row.clk.into();
            trace[ProcessorColumn::Ip.index()].data[index] = row.ip.into();
            trace[ProcessorColumn::Ci.index()].data[index] = row.ci.into();
            trace[ProcessorColumn::Ni.index()].data[index] = row.ni.into();
            trace[ProcessorColumn::Mp.index()].data[index] = row.mp.into();
            trace[ProcessorColumn::Mv.index()].data[index] = row.mv.into();
            trace[ProcessorColumn::Mvi.index()].data[index] = row.mvi.into();
            trace[ProcessorColumn::NextClk.index()].data[index] = row.next_clk.into();
            trace[ProcessorColumn::NextIp.index()].data[index] = row.next_ip.into();
            trace[ProcessorColumn::NextCi.index()].data[index] = row.next_ci.into();
            trace[ProcessorColumn::NextNi.index()].data[index] = row.next_ni.into();
            trace[ProcessorColumn::NextMp.index()].data[index] = row.next_mp.into();
            trace[ProcessorColumn::NextMv.index()].data[index] = row.next_mv.into();
            trace[ProcessorColumn::NextMvi.index()].data[index] = row.next_mvi.into();
        }

        // Evaluate columns on the circle domain
        let domain = CanonicCoset::new(log_size).circle_domain();
        let trace = trace.into_iter().map(|col| CircleEvaluation::new(domain, col)).collect();

        // Return the evaluated trace and claim
        Ok((trace, ProcessorClaim::new(log_size)))
    }
}

impl From<Vec<Registers>> for ProcessorTable {
    fn from(registers: Vec<Registers>) -> Self {
        ProcessorIntermediateTable::from(registers).into()
    }
}

// Separated from `Vec<Registers> for ProcessorTable` to facilitate tests.
// It is assumed that [`ProcessorIntermediateTable`] is sorted and padded to the next power of two.
impl From<ProcessorIntermediateTable> for ProcessorTable {
    fn from(mut intermediate_table: ProcessorIntermediateTable) -> Self {
        let mut processor_table = Self::new();

        if intermediate_table.table.is_empty() {
            return processor_table;
        }

        let last_entry = intermediate_table.table.last().unwrap();
        let next_dummy_entry =
            ProcessorTableEntry { clk: last_entry.clk + BaseField::one(), ..last_entry.clone() };

        intermediate_table.add_entry(next_dummy_entry);

        for window in intermediate_table.table.windows(2) {
            match window {
                [entry_1, entry_2] => {
                    let row = ProcessorTableRow::new(entry_1, entry_2);
                    processor_table.add_row(row);
                }
                _ => panic!("Empty window"),
            }
        }
        processor_table
    }
}

/// Represents a single row in the Processor Table.
///
/// Two consecutive entries [`ProcessorTableEntry`] flattened.
///
/// To avoid bit-reversals when evaluating transition constraints,
/// the two consecutives rows on which transition constraints are evaluated
/// are flattened into a single row.
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
    /// Next Clock cycle counter
    next_clk: BaseField,
    /// Next Instruction pointer
    next_ip: BaseField,
    /// Next Current instruction
    next_ci: BaseField,
    /// Next Next instruction
    next_ni: BaseField,
    /// Next Memory pointer
    next_mp: BaseField,
    /// Next Memory value
    next_mv: BaseField,
    /// Next Memory value inverse
    next_mvi: BaseField,
}

impl ProcessorTableRow {
    /// Creates a row for the [`ProcessorIntermediateTable`] which is considered 'real'.
    ///
    /// A 'real' row, is a row that is part of the execution trace from the Brainfuck program
    /// execution.
    pub const fn new(entry_1: &ProcessorTableEntry, entry_2: &ProcessorTableEntry) -> Self {
        Self {
            clk: entry_1.clk,
            ip: entry_1.ip,
            ci: entry_1.ci,
            ni: entry_1.ni,
            mp: entry_1.mp,
            mv: entry_1.mv,
            mvi: entry_1.mvi,
            next_clk: entry_2.clk,
            next_ip: entry_2.ip,
            next_ci: entry_2.ci,
            next_ni: entry_2.ni,
            next_mp: entry_2.mp,
            next_mv: entry_2.mv,
            next_mvi: entry_2.mvi,
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
pub struct ProcessorIntermediateTable {
    /// A vector of [`ProcessorTableEntry`] representing the entries of the table.
    table: Vec<ProcessorTableEntry>,
}

impl ProcessorIntermediateTable {
    /// Creates a new, empty [`ProcessorIntermediateTable`].
    ///
    /// # Returns
    /// A new instance of [`ProcessorIntermediateTable`] with an empty table.
    pub const fn new() -> Self {
        Self { table: Vec::new() }
    }

    /// Adds a new entry to the Processor Table.
    ///
    /// # Arguments
    /// * `entry` - The [`ProcessorTableEntry`] to add to the table.
    ///
    /// This method pushes a new [`ProcessorTableEntry`] onto the `table` vector.
    pub fn add_entry(&mut self, entry: ProcessorTableEntry) {
        self.table.push(entry);
    }

    /// Adds multiple entries to the Processor Table.
    ///
    /// # Arguments
    /// * `entries` - A vector of [`ProcessorTableEntry`] to add to the table.
    ///
    /// This method extends the `table` vector with the provided entries.
    fn add_entries(&mut self, entries: Vec<ProcessorTableEntry>) {
        self.table.extend(entries);
    }

    /// Pads the Processor table with dummy entries up to the next power of two length.
    ///
    /// Each dummy entry increase clk, copy the others from the last step
    ///
    /// Does nothing if the table is empty.
    fn pad(&mut self) {
        if let Some(last_entry) = self.table.last().cloned() {
            let trace_len = self.table.len();
            let padding_offset = (trace_len.next_power_of_two() - trace_len) as u32;
            for i in 1..=padding_offset {
                self.add_entry(ProcessorTableEntry {
                    clk: last_entry.clk + BaseField::from(i),
                    ..last_entry.clone()
                });
            }
        }
    }
}

impl From<Vec<Registers>> for ProcessorIntermediateTable {
    fn from(registers: Vec<Registers>) -> Self {
        let mut processor_table = Self::new();

        let entries = registers.iter().map(Into::into).collect();
        processor_table.add_entries(entries);
        processor_table.pad();

        processor_table
    }
}

/// Represents a single entry in the Processor Table.
///
/// The Processor Table ensures consistency for the part of the execution that
/// relates to the registers of the Brainfuck virtual machine. It records all
/// register values for each cycle that the program ran.
///
/// Each entry contains the values for the following registers:
/// - `clk`: The clock cycle counter, represents the current step.
/// - `ip`: The instruction pointer.
/// - `ci`: The current instruction.
/// - `ni`: The next instruction.
/// - `mp`: The memory pointer.
/// - `mv`: The memory value.
/// - `mvi`: The memory value inverse.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct ProcessorTableEntry {
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

impl From<&Registers> for ProcessorTableEntry {
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

/// Enum representing the column indices in the Processor trace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProcessorColumn {
    Clk,
    Ip,
    Ci,
    Ni,
    Mp,
    Mv,
    Mvi,
    NextClk,
    NextIp,
    NextCi,
    NextNi,
    NextMp,
    NextMv,
    NextMvi,
}

impl ProcessorColumn {
    /// Returns the index of the column in the Processor trace.
    pub const fn index(self) -> usize {
        match self {
            Self::Clk => 0,
            Self::Ip => 1,
            Self::Ci => 2,
            Self::Ni => 3,
            Self::Mp => 4,
            Self::Mv => 5,
            Self::Mvi => 6,
            Self::NextClk => 7,
            Self::NextIp => 8,
            Self::NextCi => 9,
            Self::NextNi => 10,
            Self::NextMp => 11,
            Self::NextMv => 12,
            Self::NextMvi => 13,
        }
    }
}

impl TraceColumn for ProcessorColumn {
    fn count() -> (usize, usize) {
        (14, 4)
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
    fn test_processor_table_entry_from_registers() {
        let registers = Registers {
            clk: BaseField::one(),
            ip: BaseField::from(5),
            ci: BaseField::from(43),
            ni: BaseField::from(91),
            mp: BaseField::from(2),
            mv: BaseField::from(7),
            mvi: BaseField::zero(),
        };

        let entry = ProcessorTableEntry::from(&registers);

        let expected_entry = ProcessorTableEntry {
            clk: BaseField::one(),
            ip: BaseField::from(5),
            ci: BaseField::from(43),
            ni: BaseField::from(91),
            mp: BaseField::from(2),
            mv: BaseField::from(7),
            mvi: BaseField::zero(),
        };

        assert_eq!(entry, expected_entry);
    }

    #[test]
    fn test_processor_table_row() {
        let entry_1 = ProcessorTableEntry {
            clk: BaseField::one(),
            ip: BaseField::from(5),
            ci: BaseField::from(43),
            ni: BaseField::from(91),
            mp: BaseField::from(2),
            mv: BaseField::from(7),
            mvi: BaseField::zero(),
        };

        let entry_2 = ProcessorTableEntry {
            clk: BaseField::one(),
            ip: BaseField::from(5),
            ci: BaseField::from(63),
            ni: BaseField::from(42),
            mp: BaseField::from(2),
            mv: BaseField::one(),
            mvi: BaseField::zero(),
        };

        let row = ProcessorTableRow::new(&entry_1, &entry_2);

        let expected_row = ProcessorTableRow {
            clk: BaseField::one(),
            ip: BaseField::from(5),
            ci: BaseField::from(43),
            ni: BaseField::from(91),
            mp: BaseField::from(2),
            mv: BaseField::from(7),
            mvi: BaseField::zero(),
            next_clk: BaseField::one(),
            next_ip: BaseField::from(5),
            next_ci: BaseField::from(63),
            next_ni: BaseField::from(42),
            next_mp: BaseField::from(2),
            next_mv: BaseField::one(),
            next_mvi: BaseField::zero(),
        };

        assert_eq!(row, expected_row);
    }

    #[test]
    fn test_processor_intermediate_table_new() {
        let processor_intermediate_table = ProcessorIntermediateTable::new();

        assert!(processor_intermediate_table.table.is_empty());
    }

    #[test]
    fn test_processor_table_new() {
        let processor_table = ProcessorTable::new();

        assert!(processor_table.table.is_empty());
    }

    #[test]
    fn test_add_entry() {
        let mut processor_table = ProcessorIntermediateTable::new();

        let entry = ProcessorTableEntry {
            clk: BaseField::from(10),
            ip: BaseField::from(15),
            ci: BaseField::from(43),
            ni: BaseField::from(91),
            mp: BaseField::from(20),
            mv: BaseField::from(25),
            mvi: BaseField::one(),
        };

        processor_table.add_entry(entry.clone());

        assert_eq!(processor_table.table, vec![entry]);
    }

    #[test]
    fn test_add_multiple_entries() {
        let mut processor_table = ProcessorIntermediateTable::new();

        let entries = vec![
            ProcessorTableEntry {
                clk: BaseField::one(),
                ip: BaseField::from(5),
                ci: BaseField::from(43),
                ni: BaseField::from(91),
                mp: BaseField::from(10),
                mv: BaseField::from(15),
                mvi: BaseField::zero(),
            },
            ProcessorTableEntry {
                clk: BaseField::from(2),
                ip: BaseField::from(6),
                ci: BaseField::from(44),
                ni: BaseField::from(92),
                mp: BaseField::from(11),
                mv: BaseField::from(16),
                mvi: BaseField::one(),
            },
            ProcessorTableEntry {
                clk: BaseField::from(3),
                ip: BaseField::from(7),
                ci: BaseField::from(45),
                ni: BaseField::from(93),
                mp: BaseField::from(12),
                mv: BaseField::from(17),
                mvi: BaseField::zero(),
            },
        ];

        for entry in &entries {
            processor_table.add_entry(entry.clone());
        }

        assert_eq!(processor_table.table, entries,);
    }

    #[allow(clippy::similar_names)]
    #[allow(clippy::too_many_lines)]
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

        // Convert the trace to an `ProcessorIntermediateTable`
        let processor_intermediate_table: ProcessorIntermediateTable = trace.into();

        let processor_table = ProcessorTable::from(processor_intermediate_table.clone());

        // Create the expected `ProcessorIntermediateTable`
        let process_0 = ProcessorTableEntry {
            clk: BaseField::zero(),
            ip: BaseField::zero(),
            ci: BaseField::from(43),
            ni: BaseField::from(62),
            mp: BaseField::zero(),
            mv: BaseField::zero(),
            mvi: BaseField::zero(),
        };

        let process_1 = ProcessorTableEntry {
            clk: BaseField::one(),
            ip: BaseField::one(),
            ci: BaseField::from(62),
            ni: BaseField::from(44),
            mp: BaseField::zero(),
            mv: BaseField::one(),
            mvi: BaseField::one(),
        };

        let process_2 = ProcessorTableEntry {
            clk: BaseField::from(2),
            ip: BaseField::from(2),
            ci: BaseField::from(44),
            ni: BaseField::from(60),
            mp: BaseField::one(),
            mv: BaseField::zero(),
            mvi: BaseField::zero(),
        };

        let process_3 = ProcessorTableEntry {
            clk: BaseField::from(3),
            ip: BaseField::from(3),
            ci: BaseField::from(60),
            ni: BaseField::from(91),
            mp: BaseField::one(),
            mv: BaseField::one(),
            mvi: BaseField::one(),
        };

        let process_4 = ProcessorTableEntry {
            clk: BaseField::from(4),
            ip: BaseField::from(4),
            ci: BaseField::from(91),
            ni: BaseField::from(12),
            mp: BaseField::zero(),
            mv: BaseField::one(),
            mvi: BaseField::one(),
        };

        let process_5 = ProcessorTableEntry {
            clk: BaseField::from(5),
            ip: BaseField::from(6),
            ci: BaseField::from(62),
            ni: BaseField::from(43),
            mp: BaseField::zero(),
            mv: BaseField::one(),
            mvi: BaseField::one(),
        };

        let process_6 = ProcessorTableEntry {
            clk: BaseField::from(6),
            ip: BaseField::from(7),
            ci: BaseField::from(43),
            ni: BaseField::from(46),
            mp: BaseField::one(),
            mv: BaseField::one(),
            mvi: BaseField::one(),
        };

        let process_7 = ProcessorTableEntry {
            clk: BaseField::from(7),
            ip: BaseField::from(8),
            ci: BaseField::from(46),
            ni: BaseField::from(60),
            mp: BaseField::one(),
            mv: BaseField::from(2),
            mvi: BaseField::from(2).inverse(),
        };

        let process_8 = ProcessorTableEntry {
            clk: BaseField::from(8),
            ip: BaseField::from(9),
            ci: BaseField::from(60),
            ni: BaseField::from(45),
            mp: BaseField::one(),
            mv: BaseField::from(2),
            mvi: BaseField::from(2).inverse(),
        };

        let process_9 = ProcessorTableEntry {
            clk: BaseField::from(9),
            ip: BaseField::from(10),
            ci: BaseField::from(45),
            ni: BaseField::from(93),
            mp: BaseField::zero(),
            mv: BaseField::one(),
            mvi: BaseField::one(),
        };

        let process_10 = ProcessorTableEntry {
            clk: BaseField::from(10),
            ip: BaseField::from(11),
            ci: BaseField::from(93),
            ni: BaseField::from(6),
            mp: BaseField::zero(),
            mv: BaseField::zero(),
            mvi: BaseField::zero(),
        };

        let process_11 = ProcessorTableEntry {
            clk: BaseField::from(11),
            ip: BaseField::from(13),
            ci: BaseField::zero(),
            ni: BaseField::zero(),
            mp: BaseField::zero(),
            mv: BaseField::zero(),
            mvi: BaseField::zero(),
        };

        let dummy_12 = ProcessorTableEntry { clk: process_11.clk + BaseField::one(), ..process_11 };
        let dummy_13 = ProcessorTableEntry { clk: dummy_12.clk + BaseField::one(), ..process_11 };
        let dummy_14 = ProcessorTableEntry { clk: dummy_13.clk + BaseField::one(), ..process_11 };
        let dummy_15 = ProcessorTableEntry { clk: dummy_14.clk + BaseField::one(), ..process_11 };
        let dummy_16 = ProcessorTableEntry { clk: dummy_15.clk + BaseField::one(), ..process_11 };

        let mut expected_processor_intermediate_table = ProcessorIntermediateTable {
            table: vec![
                process_0.clone(),
                process_1.clone(),
                process_2.clone(),
                process_3.clone(),
                process_4.clone(),
                process_5.clone(),
                process_6.clone(),
                process_7.clone(),
                process_8.clone(),
                process_9.clone(),
                process_10.clone(),
                process_11.clone(),
            ],
        };

        expected_processor_intermediate_table.pad();

        let mut expected_processor_table = ProcessorTable::new();

        let row_0 = ProcessorTableRow::new(&process_0, &process_1);
        let row_1 = ProcessorTableRow::new(&process_1, &process_2);
        let row_2 = ProcessorTableRow::new(&process_2, &process_3);
        let row_3 = ProcessorTableRow::new(&process_3, &process_4);
        let row_4 = ProcessorTableRow::new(&process_4, &process_5);
        let row_5 = ProcessorTableRow::new(&process_5, &process_6);
        let row_6 = ProcessorTableRow::new(&process_6, &process_7);
        let row_7 = ProcessorTableRow::new(&process_7, &process_8);
        let row_8 = ProcessorTableRow::new(&process_8, &process_9);
        let row_9 = ProcessorTableRow::new(&process_9, &process_10);
        let row_10 = ProcessorTableRow::new(&process_10, &process_11);
        let row_11 = ProcessorTableRow::new(&process_11, &dummy_12);
        let row_12 = ProcessorTableRow::new(&dummy_12, &dummy_13);
        let row_13 = ProcessorTableRow::new(&dummy_13, &dummy_14);
        let row_14 = ProcessorTableRow::new(&dummy_14, &dummy_15);
        let row_15 = ProcessorTableRow::new(&dummy_15, &dummy_16);

        // TODO: Eventually add a `add_rows` method for test purposes..
        expected_processor_table.add_row(row_0);
        expected_processor_table.add_row(row_1);
        expected_processor_table.add_row(row_2);
        expected_processor_table.add_row(row_3);
        expected_processor_table.add_row(row_4);
        expected_processor_table.add_row(row_5);
        expected_processor_table.add_row(row_6);
        expected_processor_table.add_row(row_7);
        expected_processor_table.add_row(row_8);
        expected_processor_table.add_row(row_9);
        expected_processor_table.add_row(row_10);
        expected_processor_table.add_row(row_11);
        expected_processor_table.add_row(row_12);
        expected_processor_table.add_row(row_13);
        expected_processor_table.add_row(row_14);
        expected_processor_table.add_row(row_15);

        // Verify that the processor table is correct
        assert_eq!(processor_intermediate_table, expected_processor_intermediate_table);
        assert_eq!(processor_table, expected_processor_table);
    }

    #[test]
    fn test_trace_evaluation_empty_processor_table() {
        let processor_table = ProcessorTable::new();
        let result = processor_table.trace_evaluation();

        assert!(matches!(result, Err(TraceError::EmptyTrace)));
    }

    #[test]
    #[allow(clippy::similar_names)]
    fn test_trace_evaluation_single_row_processor_table() {
        let mut processor_intermediate_table = ProcessorIntermediateTable::new();
        processor_intermediate_table.add_entry(ProcessorTableEntry {
            clk: BaseField::one(),
            ip: BaseField::from(2),
            ci: BaseField::from(3),
            ni: BaseField::from(4),
            mp: BaseField::from(5),
            mv: BaseField::from(6),
            mvi: BaseField::from(7),
        });

        let processor_table = ProcessorTable::from(processor_intermediate_table);

        let (trace, claim) = processor_table.trace_evaluation().unwrap();

        assert_eq!(claim.log_size, LOG_N_LANES, "Log size should include SIMD lanes.");
        assert_eq!(
            trace.len(),
            ProcessorColumn::count().0,
            "Trace should contain one column per register."
        );

        let expected_clk_column = vec![BaseField::one(); 1 << LOG_N_LANES];
        let expected_ip_column = vec![BaseField::from(2); 1 << LOG_N_LANES];
        let expected_ci_column = vec![BaseField::from(3); 1 << LOG_N_LANES];
        let expected_ni_column = vec![BaseField::from(4); 1 << LOG_N_LANES];
        let expected_mp_column = vec![BaseField::from(5); 1 << LOG_N_LANES];
        let expected_mv_column = vec![BaseField::from(6); 1 << LOG_N_LANES];
        let expected_mvi_column = vec![BaseField::from(7); 1 << LOG_N_LANES];

        assert_eq!(trace[ProcessorColumn::Clk.index()].to_cpu().values, expected_clk_column);
        assert_eq!(trace[ProcessorColumn::Ip.index()].to_cpu().values, expected_ip_column);
        assert_eq!(trace[ProcessorColumn::Ci.index()].to_cpu().values, expected_ci_column);
        assert_eq!(trace[ProcessorColumn::Ni.index()].to_cpu().values, expected_ni_column);
        assert_eq!(trace[ProcessorColumn::Mp.index()].to_cpu().values, expected_mp_column);
        assert_eq!(trace[ProcessorColumn::Mv.index()].to_cpu().values, expected_mv_column);
        assert_eq!(trace[ProcessorColumn::Mvi.index()].to_cpu().values, expected_mvi_column);
    }

    #[test]
    #[allow(clippy::similar_names)]
    fn test_trace_evaluation_processor_table_with_multiple_rows() {
        let mut processor_intermediate_table = ProcessorIntermediateTable::new();

        // Add entries to the processor table
        let entries = vec![
            ProcessorTableEntry {
                clk: BaseField::zero(),
                ip: BaseField::one(),
                ci: BaseField::from(2),
                ni: BaseField::from(3),
                mp: BaseField::from(4),
                mv: BaseField::from(5),
                mvi: BaseField::from(6),
            },
            ProcessorTableEntry {
                clk: BaseField::one(),
                ip: BaseField::from(2),
                ci: BaseField::from(3),
                ni: BaseField::from(4),
                mp: BaseField::from(5),
                mv: BaseField::from(6),
                mvi: BaseField::from(7),
            },
        ];

        processor_intermediate_table.add_entries(entries);

        let processor_table = ProcessorTable::from(processor_intermediate_table);

        // Perform the trace evaluation
        let (trace, claim) = processor_table.trace_evaluation().unwrap();

        // Calculate the expected parameters
        let expected_log_n_rows: u32 = 1; // log2(2 rows)
        let expected_log_size = expected_log_n_rows + LOG_N_LANES;
        let expected_size = 1 << expected_log_size;

        // Construct the expected trace columns
        let mut clk_column = BaseColumn::zeros(expected_size);
        let mut ip_column = BaseColumn::zeros(expected_size);
        let mut ci_column = BaseColumn::zeros(expected_size);
        let mut ni_column = BaseColumn::zeros(expected_size);
        let mut mp_column = BaseColumn::zeros(expected_size);
        let mut mv_column = BaseColumn::zeros(expected_size);
        let mut mvi_column = BaseColumn::zeros(expected_size);

        clk_column.data[0] = BaseField::zero().into();
        clk_column.data[1] = BaseField::one().into();

        ip_column.data[0] = BaseField::one().into();
        ip_column.data[1] = BaseField::from(2).into();

        ci_column.data[0] = BaseField::from(2).into();
        ci_column.data[1] = BaseField::from(3).into();

        ni_column.data[0] = BaseField::from(3).into();
        ni_column.data[1] = BaseField::from(4).into();

        mp_column.data[0] = BaseField::from(4).into();
        mp_column.data[1] = BaseField::from(5).into();

        mv_column.data[0] = BaseField::from(5).into();
        mv_column.data[1] = BaseField::from(6).into();

        mvi_column.data[0] = BaseField::from(6).into();
        mvi_column.data[1] = BaseField::from(7).into();

        // Create the expected domain for evaluation
        let domain = CanonicCoset::new(expected_log_size).circle_domain();

        // Transform expected columns into CircleEvaluation
        let expected_trace: TraceEval =
            vec![clk_column, ip_column, ci_column, ni_column, mp_column, mv_column, mvi_column]
                .into_iter()
                .map(|col| CircleEvaluation::new(domain, col))
                .collect();

        // Create the expected claim
        let expected_claim = ProcessorClaim::new(expected_log_size);

        // Assert equality of the claim
        assert_eq!(claim, expected_claim, "Claims should match the expected values.");

        // Assert equality of the trace
        for col_index in 0..expected_trace.len() {
            assert_eq!(
                trace[col_index].domain, expected_trace[col_index].domain,
                "Domains of trace columns should match."
            );
            assert_eq!(
                trace[col_index].to_cpu().values,
                expected_trace[col_index].to_cpu().values,
                "Values of trace columns should match."
            );
        }
    }
}
