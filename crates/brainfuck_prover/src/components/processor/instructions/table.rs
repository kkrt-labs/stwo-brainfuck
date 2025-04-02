use crate::components::{
    processor::table::ProcessorElements, InteractionClaim, ProcessorInstructionClaim, TraceColumn,
    TraceError, TraceEval,
};
use brainfuck_vm::{instruction::InstructionType, registers::Registers};
use num_traits::{One, Zero};
use stwo_prover::{
    constraint_framework::{logup::LogupTraceGenerator, Relation},
    core::{
        backend::{
            simd::{column::BaseColumn, m31::LOG_N_LANES, qm31::PackedSecureField},
            Column,
        },
        fields::m31::BaseField,
        poly::circle::{CanonicCoset, CircleEvaluation},
    },
};

/// Table of the shift left instruction `<` sub-component.
pub type LeftInstructionTable = ProcessorInstructionTable<{ InstructionType::Left.to_u32() }>;

/// Table of the shift right instruction `>` sub-component.
pub type RightInstructionTable = ProcessorInstructionTable<{ InstructionType::Right.to_u32() }>;

/// Table of the plus instruction `+` sub-component.
pub type PlusInstructionTable = ProcessorInstructionTable<{ InstructionType::Plus.to_u32() }>;

/// Table of the minus instruction `-` sub-component.
pub type MinusInstructionTable = ProcessorInstructionTable<{ InstructionType::Minus.to_u32() }>;

/// Table  of the input instruction `,` sub-component.
pub type InputInstructionTable = ProcessorInstructionTable<{ InstructionType::ReadChar.to_u32() }>;

/// Table of the output instruction `.` sub-component.
pub type OutputInstructionTable = ProcessorInstructionTable<{ InstructionType::PutChar.to_u32() }>;

/// Represents the table for the Processor sub-components of the instructions `>`, `<`, `+`, `-`,
/// `,` and `.`, containing the required registers for their constraints.
///
/// To ease constraints evaluation, each row of the sub-components
/// contains the current row and the next row in natural order.
/// This is done to avoid having to do costly bit-reversals, as constraints
/// are evaluated on the evaluation of the trace which is ordered in
/// a bit-reversed manner over the circle domain once the polynomials are interpolated.
///
/// The preliminary work to extract the fields from the execution trace,
/// the sorting and the padding is done through the [`ProcessorInstructionIntermediateTable`]
/// struct.
///
/// Once done, we can build the Processor table from it, by pairing the consecutive
/// [`ProcessorInstructionEntry`] in [`ProcessorInstructionRow`].
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct ProcessorInstructionTable<const N: u32> {
    /// A vector of [`ProcessorInstructionRow`] representing the table rows.
    table: Vec<ProcessorInstructionRow>,
}

impl<const N: u32> ProcessorInstructionTable<N> {
    /// Creates a new, empty [`ProcessorInstructionTable`].
    ///
    /// # Returns
    /// A new instance of [`ProcessorInstructionTable`] with an empty table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a new row to the [`ProcessorInstructionTable`].
    ///
    /// # Arguments
    /// * `row` - The [`ProcessorInstructionRow`] to add to the table.
    ///
    /// This method pushes a new [`ProcessorInstructionRow`] onto the `table` vector.
    fn add_row(&mut self, row: ProcessorInstructionRow) {
        self.table.push(row);
    }

    /// Transforms the [`ProcessorInstructionTable`] into a [`TraceEval`], to be committed when
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
    pub fn trace_evaluation(&self) -> Result<(TraceEval, ProcessorInstructionClaim), TraceError> {
        let n_rows = self.table.len() as u32;
        // It is possible that the table is empty because the program has no jump instruction.
        if n_rows == 0 {
            return Ok((TraceEval::new(), ProcessorInstructionClaim::new(0)));
        }
        if !n_rows.is_power_of_two() {
            return Err(TraceError::InvalidTraceLength);
        }

        let log_n_rows = n_rows.ilog2();
        let log_size = log_n_rows + LOG_N_LANES;
        let mut trace =
            vec![BaseColumn::zeros(1 << log_size); ProcessorInstructionColumn::count().0];

        for (index, row) in self.table.iter().enumerate() {
            trace[ProcessorInstructionColumn::Clk.index()].data[index] = row.clk.into();
            trace[ProcessorInstructionColumn::Ip.index()].data[index] = row.ip.into();
            trace[ProcessorInstructionColumn::Ci.index()].data[index] = row.ci.into();
            trace[ProcessorInstructionColumn::Ni.index()].data[index] = row.ni.into();
            trace[ProcessorInstructionColumn::Mp.index()].data[index] = row.mp.into();
            trace[ProcessorInstructionColumn::Mv.index()].data[index] = row.mv.into();
            trace[ProcessorInstructionColumn::Mvi.index()].data[index] = row.mvi.into();
            trace[ProcessorInstructionColumn::D.index()].data[index] = row.d.into();
            trace[ProcessorInstructionColumn::NextIp.index()].data[index] = row.next_ip.into();
            trace[ProcessorInstructionColumn::NextMp.index()].data[index] = row.next_mp.into();
            trace[ProcessorInstructionColumn::NextMv.index()].data[index] = row.next_mv.into();
        }

        let domain = CanonicCoset::new(log_size).circle_domain();
        let trace = trace.into_iter().map(|col| CircleEvaluation::new(domain, col)).collect();

        Ok((trace, ProcessorInstructionClaim::new(log_size)))
    }
}

impl<const N: u32> From<&Vec<Registers>> for ProcessorInstructionTable<N> {
    fn from(registers: &Vec<Registers>) -> Self {
        ProcessorInstructionIntermediateTable::<N>::from(registers).into()
    }
}

// Separated from `From<&Vec<Registers>> for ProcessorInstructionTable` to facilitate tests.
// It is assumed that [`ProcessorInstructionIntermediateTable`] is sorted and padded to the next
// power of two.
impl<const N: u32> From<ProcessorInstructionIntermediateTable<N>> for ProcessorInstructionTable<N> {
    fn from(intermediate_table: ProcessorInstructionIntermediateTable<N>) -> Self {
        let mut processor_instruction_table = Self::new();

        if intermediate_table.table.is_empty() {
            return processor_instruction_table;
        }

        for window in intermediate_table.table.chunks(2) {
            match window {
                [entry_1, entry_2] => {
                    let row = ProcessorInstructionRow::new(entry_1, entry_2);
                    processor_instruction_table.add_row(row);
                }
                [entry] => {
                    let next_dummy = ProcessorInstructionEntry::new_dummy(
                        entry.clk + BaseField::one(),
                        entry.ip,
                    );
                    let row = ProcessorInstructionRow::new(entry, &next_dummy);
                    processor_instruction_table.add_row(row);
                }
                _ => panic!("Empty window"),
            }
        }
        processor_instruction_table
    }
}

/// Represents a single row in the [`ProcessorInstructionTable`].
///
/// Two consecutive entries [`ProcessorInstructionEntry`] flattened.
///
/// To avoid bit-reversals when evaluating transition constraints,
/// the two consecutives rows on which transition constraints are evaluated
/// are flattened into a single row.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct ProcessorInstructionRow {
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
    /// Dummy: Flag whether the current entry is a dummy one or not.
    d: BaseField,
    /// Next Instruction pointer
    next_ip: BaseField,
    /// Next Memory pointer
    next_mp: BaseField,
    /// Next Memory value
    next_mv: BaseField,
}

impl ProcessorInstructionRow {
    /// Creates a row for the [`ProcessorInstructionIntermediateTable`] which is considered 'real'.
    ///
    /// A 'real' row, is a row that is part of the execution trace from the Brainfuck program
    /// execution.
    pub const fn new(
        entry_1: &ProcessorInstructionEntry,
        entry_2: &ProcessorInstructionEntry,
    ) -> Self {
        Self {
            clk: entry_1.clk,
            ip: entry_1.ip,
            ci: entry_1.ci,
            ni: entry_1.ni,
            mp: entry_1.mp,
            mv: entry_1.mv,
            mvi: entry_1.mvi,
            d: entry_1.d,
            next_ip: entry_2.ip,
            next_mp: entry_2.mp,
            next_mv: entry_2.mv,
        }
    }
}

#[cfg(test)]
pub type LeftIntermediateTable =
    ProcessorInstructionIntermediateTable<{ InstructionType::Left.to_u32() }>;

#[cfg(test)]
pub type RightIntermediateTable =
    ProcessorInstructionIntermediateTable<{ InstructionType::Right.to_u32() }>;

#[cfg(test)]
pub type PlusIntermediateTable =
    ProcessorInstructionIntermediateTable<{ InstructionType::Plus.to_u32() }>;

#[cfg(test)]
pub type MinusIntermediateTable =
    ProcessorInstructionIntermediateTable<{ InstructionType::Minus.to_u32() }>;

#[cfg(test)]
pub type InputInstructionIntermediateTable =
    ProcessorInstructionIntermediateTable<{ InstructionType::ReadChar.to_u32() }>;
#[cfg(test)]
pub type OutputIntermediateTable =
    ProcessorInstructionIntermediateTable<{ InstructionType::PutChar.to_u32() }>;

/// Represents the intermediary tables for the sub-components of the Processor Table.
/// It records the register values for each cycle that the program ran the corresponding
/// instruction.
///
/// The Sub-component tables are used to verify the consistency of the execution,
/// ensuring that all instructions mutate the state correctly according to
/// the Brainfuck instruction set.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct ProcessorInstructionIntermediateTable<const N: u32> {
    /// A vector of [`ProcessorInstructionEntry`] representing the entries of the table.
    table: Vec<ProcessorInstructionEntry>,
}

impl<const N: u32> ProcessorInstructionIntermediateTable<N> {
    /// Creates a new, empty [`ProcessorInstructionIntermediateTable`].
    ///
    /// # Returns
    /// A new instance of [`ProcessorInstructionIntermediateTable`] with an empty table.
    pub const fn new() -> Self {
        Self { table: Vec::new() }
    }

    /// Adds a new entry to the [`ProcessorInstructionIntermediateTable`].
    ///
    /// # Arguments
    /// * `entry` - The [`ProcessorInstructionEntry`] to add to the table.
    ///
    /// This method pushes a new [`ProcessorInstructionEntry`] onto the `table` vector.
    pub fn add_entry(&mut self, entry: ProcessorInstructionEntry) {
        self.table.push(entry);
    }

    /// Adds multiple entries to the [`ProcessorInstructionIntermediateTable`].
    ///
    /// # Arguments
    /// * `entries` - A vector of [`ProcessorInstructionEntry`] to add to the table.
    ///
    /// This method extends the `table` vector with the provided entries.
    fn add_entries(&mut self, entries: Vec<ProcessorInstructionEntry>) {
        self.table.extend(entries);
    }

    /// Pads the [`ProcessorInstructionIntermediateTable`] with dummy entries up to the next power
    /// of two length.
    ///
    /// Each dummy entry increase `clk`, copy `ip` from the last step, and set to zero the others.
    ///
    /// Does nothing if the table is empty.
    fn pad(&mut self) {
        let trace_len = self.table.len();
        let (last_clk, last_ip) = if trace_len == 0 {
            (BaseField::zero(), BaseField::zero())
        } else {
            let last_entry = self.table.last().unwrap();
            (last_entry.clk, last_entry.ip)
        };
        let padding_offset = (trace_len.next_power_of_two() - trace_len) as u32;
        for i in 0..padding_offset {
            let dummy_entry =
                ProcessorInstructionEntry::new_dummy(last_clk + BaseField::from(i), last_ip);
            self.add_entry(dummy_entry);
        }
    }
}

impl<const N: u32> From<&Vec<Registers>> for ProcessorInstructionIntermediateTable<N> {
    fn from(registers: &Vec<Registers>) -> Self {
        let mut processor_instruction_intermediate_table = Self::new();

        let entries = registers
            .iter()
            .zip(registers.iter().skip(1))
            .filter(|(reg, _)| reg.ci == InstructionType::try_from(N).unwrap().to_base_field())
            .flat_map(|(reg_0, reg_1)| {
                [ProcessorInstructionEntry::from(reg_0), ProcessorInstructionEntry::from(reg_1)]
            })
            .collect();

        processor_instruction_intermediate_table.add_entries(entries);
        processor_instruction_intermediate_table.pad();

        processor_instruction_intermediate_table
    }
}

/// Represents a single entry in the [`ProcessorInstructionIntermediateTable`].
///
/// The [`ProcessorInstructionIntermediateTable`] ensures consistency for the part of the execution
/// that relates to the registers of the Brainfuck virtual machine. It records all
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
pub struct ProcessorInstructionEntry {
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
    /// Dummy: Flag whether the current entry is a dummy one or not.
    d: BaseField,
}

impl ProcessorInstructionEntry {
    /// Creates an entry for the [`ProcessorInstructionIntermediateTable`] which is considered
    /// 'real'.
    ///
    /// A 'real' entry, is an entry that is part of the execution trace from the Brainfuck program
    /// execution.
    pub fn new(
        clk: BaseField,
        ip: BaseField,
        ci: BaseField,
        ni: BaseField,
        mp: BaseField,
        mv: BaseField,
        mvi: BaseField,
    ) -> Self {
        Self { clk, ip, ci, ni, mp, mv, mvi, d: BaseField::zero() }
    }

    /// Creates an entry for the [`ProcessorInstructionIntermediateTable`] which is considered
    /// 'dummy'.
    ///
    /// A 'dummy' entry, is an entry that is not part of the execution trace from the Brainfuck
    /// program execution.
    /// They are used to flag padding rows.
    pub fn new_dummy(clk: BaseField, ip: BaseField) -> Self {
        Self { clk, ip, d: BaseField::one(), ..Default::default() }
    }
}

impl From<&Registers> for ProcessorInstructionEntry {
    fn from(registers: &Registers) -> Self {
        Self::new(
            registers.clk,
            registers.ip,
            registers.ci,
            registers.ni,
            registers.mp,
            registers.mv,
            registers.mvi,
        )
    }
}

/// Enum representing the column indices in the `ProcessorInstruction` trace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProcessorInstructionColumn {
    Clk,
    Ip,
    Ci,
    Ni,
    Mp,
    Mv,
    Mvi,
    D,
    NextIp,
    NextMp,
    NextMv,
}

impl ProcessorInstructionColumn {
    /// Returns the index of the column in the `ProcessorInstruction` trace.
    pub const fn index(self) -> usize {
        match self {
            Self::Clk => 0,
            Self::Ip => 1,
            Self::Ci => 2,
            Self::Ni => 3,
            Self::Mp => 4,
            Self::Mv => 5,
            Self::Mvi => 6,
            Self::D => 7,
            Self::NextIp => 8,
            Self::NextMp => 9,
            Self::NextMv => 10,
        }
    }
}

impl TraceColumn for ProcessorInstructionColumn {
    fn count() -> (usize, usize) {
        (11, 1)
    }
}

/// Creates the interaction trace from the main trace evaluation
/// and the interaction elements for the Processor sub-components.
///
/// The [`ProcessorInstructionTable`] represents the execution trace of a single instruction, among
/// the valid instruction set of the Brainfuck ISA.
///
/// Only the 'real' rows are impacting the logUp sum.
/// Dummy rows are padding rows.
///
/// Here, the logUp has four extension columns, which uses
/// the Input, Output, Instruction and Memory components.
///
/// # Returns
/// - Interaction trace evaluation, to be committed.
/// - Interaction claim: the total sum from the logUp protocol, to be mixed into the Fiat-Shamir
///   [`Channel`].
#[allow(clippy::similar_names)]
pub fn interaction_trace_evaluation(
    main_trace_eval: &TraceEval,
    processor_lookup_elements: &ProcessorElements,
) -> Result<(TraceEval, InteractionClaim), TraceError> {
    // If the main trace of the Jump components is empty, then we claimed that it's log
    // size is zero.
    let log_size = main_trace_eval[0].domain.log_size();

    let clk_col = &main_trace_eval[ProcessorInstructionColumn::Clk.index()].data;
    let ip_col = &main_trace_eval[ProcessorInstructionColumn::Ip.index()].data;
    let ci_col = &main_trace_eval[ProcessorInstructionColumn::Ci.index()].data;
    let ni_col = &main_trace_eval[ProcessorInstructionColumn::Ni.index()].data;
    let mp_col = &main_trace_eval[ProcessorInstructionColumn::Mp.index()].data;
    let mv_col = &main_trace_eval[ProcessorInstructionColumn::Mv.index()].data;
    let mvi_col = &main_trace_eval[ProcessorInstructionColumn::Mvi.index()].data;
    let d_col = &main_trace_eval[ProcessorInstructionColumn::D.index()].data;

    let mut logup_gen = LogupTraceGenerator::new(log_size);

    let mut col_gen = logup_gen.new_col();
    for vec_row in 0..1 << (log_size - LOG_N_LANES) {
        let clk = clk_col[vec_row];
        let ip = ip_col[vec_row];
        let ci = ci_col[vec_row];
        let ni = ni_col[vec_row];
        let mp = mp_col[vec_row];
        let mv = mv_col[vec_row];
        let mvi = mvi_col[vec_row];
        let d = d_col[vec_row];

        let num = PackedSecureField::from(d) - PackedSecureField::one();

        let denom: PackedSecureField =
            processor_lookup_elements.combine(&[clk, ip, ci, ni, mp, mv, mvi]);
        col_gen.write_frac(vec_row, num, denom);
    }
    col_gen.finalize_col();

    let (trace, claimed_sum) = logup_gen.finalize_last();

    Ok((trace, InteractionClaim { claimed_sum }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use brainfuck_vm::{
        compiler::Compiler, registers::Registers, test_helper::create_test_machine,
    };
    use num_traits::{One, Zero};

    #[test]
    fn test_processor_instruction_table_entry_from_registers() {
        let registers = Registers {
            clk: BaseField::one(),
            ip: BaseField::from(5),
            ci: BaseField::from(43),
            ni: BaseField::from(91),
            mp: BaseField::from(2),
            mv: BaseField::from(7),
            mvi: BaseField::zero(),
        };

        let entry = ProcessorInstructionEntry::from(&registers);

        let expected_entry = ProcessorInstructionEntry::new(
            BaseField::one(),
            BaseField::from(5),
            BaseField::from(43),
            BaseField::from(91),
            BaseField::from(2),
            BaseField::from(7),
            BaseField::zero(),
        );

        assert_eq!(entry, expected_entry);
    }

    #[test]
    fn test_processor_instruction_table_row() {
        let entry_1 = ProcessorInstructionEntry::new(
            BaseField::one(),
            BaseField::from(5),
            BaseField::from(43),
            BaseField::from(91),
            BaseField::from(2),
            BaseField::from(7),
            BaseField::zero(),
        );

        let entry_2 = ProcessorInstructionEntry::new_dummy(BaseField::one(), entry_1.ip);

        let row = ProcessorInstructionRow::new(&entry_1, &entry_2);

        let expected_row = ProcessorInstructionRow {
            clk: BaseField::one(),
            ip: BaseField::from(5),
            ci: BaseField::from(43),
            ni: BaseField::from(91),
            mp: BaseField::from(2),
            mv: BaseField::from(7),
            mvi: BaseField::zero(),
            d: BaseField::zero(),
            next_ip: BaseField::from(5),
            ..Default::default()
        };

        assert_eq!(row, expected_row);
    }

    #[test]
    fn test_left_intermediate_table_new() {
        let left_intermediate_table = LeftIntermediateTable::new();

        assert!(left_intermediate_table.table.is_empty());
    }

    #[test]
    fn test_left_table_new() {
        let left_table = LeftInstructionTable::new();

        assert!(left_table.table.is_empty());
    }

    #[test]
    fn test_add_entry() {
        let mut left_table = LeftIntermediateTable::new();

        let entry = ProcessorInstructionEntry::new(
            BaseField::from(10),
            BaseField::from(15),
            BaseField::from(43),
            BaseField::from(91),
            BaseField::from(20),
            BaseField::from(25),
            BaseField::one(),
        );

        left_table.add_entry(entry.clone());

        assert_eq!(left_table.table, vec![entry]);
    }

    #[test]
    fn test_add_multiple_entries() {
        let mut left_table = LeftIntermediateTable::new();

        let entries = vec![
            ProcessorInstructionEntry::new(
                BaseField::one(),
                BaseField::from(5),
                BaseField::from(43),
                BaseField::from(91),
                BaseField::from(10),
                BaseField::from(15),
                BaseField::zero(),
            ),
            ProcessorInstructionEntry::new(
                BaseField::from(2),
                BaseField::from(6),
                BaseField::from(44),
                BaseField::from(92),
                BaseField::from(11),
                BaseField::from(16),
                BaseField::one(),
            ),
            ProcessorInstructionEntry::new(
                BaseField::from(3),
                BaseField::from(7),
                BaseField::from(45),
                BaseField::from(93),
                BaseField::from(12),
                BaseField::from(17),
                BaseField::zero(),
            ),
        ];

        for entry in &entries {
            left_table.add_entry(entry.clone());
        }

        assert_eq!(left_table.table, entries,);
    }

    #[allow(clippy::similar_names)]
    #[allow(clippy::too_many_lines)]
    #[test]
    fn test_left_table_from_registers_example_program() {
        // Create a small program and compile it
        let code = "+>,<[>+.<-]";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        // Create a machine and execute the program
        let (mut machine, _) = create_test_machine(&instructions, &[1]);
        let () = machine.execute().expect("Failed to execute machine");

        // Get the trace of the executed program
        let trace = &machine.trace();

        // Convert the trace to an `ProcessorInstructionIntermediateTable`
        let left_intermediate_table: LeftIntermediateTable = trace.into();

        let left_table = LeftInstructionTable::from(left_intermediate_table.clone());

        // Create the expected `ProcessorInstructionIntermediateTable`
        let process_0 = ProcessorInstructionEntry::new(
            BaseField::from(3),
            BaseField::from(3),
            InstructionType::Left.to_base_field(),
            InstructionType::JumpIfZero.to_base_field(),
            BaseField::one(),
            BaseField::one(),
            BaseField::one(),
        );

        let process_1 = ProcessorInstructionEntry::new(
            BaseField::from(4),
            BaseField::from(4),
            InstructionType::JumpIfZero.to_base_field(),
            BaseField::from(12),
            BaseField::zero(),
            BaseField::one(),
            BaseField::one(),
        );

        let process_2 = ProcessorInstructionEntry::new(
            BaseField::from(8),
            BaseField::from(9),
            InstructionType::Left.to_base_field(),
            InstructionType::Minus.to_base_field(),
            BaseField::one(),
            BaseField::from(2),
            BaseField::from(2).inverse(),
        );

        let process_3 = ProcessorInstructionEntry::new(
            BaseField::from(9),
            BaseField::from(10),
            InstructionType::Minus.to_base_field(),
            InstructionType::JumpIfNotZero.to_base_field(),
            BaseField::zero(),
            BaseField::one(),
            BaseField::one(),
        );

        let mut expected_left_intermediate_table = ProcessorInstructionIntermediateTable {
            table: vec![process_0.clone(), process_1.clone(), process_2.clone(), process_3.clone()],
        };

        expected_left_intermediate_table.pad();

        let mut expected_processor_instruction_table = ProcessorInstructionTable::new();

        let row_0 = ProcessorInstructionRow::new(&process_0, &process_1);
        let row_1 = ProcessorInstructionRow::new(&process_2, &process_3);

        expected_processor_instruction_table.add_row(row_0);
        expected_processor_instruction_table.add_row(row_1);

        // Verify that the processor table is correct
        assert_eq!(left_intermediate_table, expected_left_intermediate_table);
        assert_eq!(left_table, expected_processor_instruction_table);
    }

    #[test]
    fn test_trace_evaluation_empty_processor_instruction_table() {
        let left_table = LeftInstructionTable::new();
        let (trace, claim) = left_table.trace_evaluation().unwrap();

        assert_eq!(trace.len(), 0);
        assert_eq!(claim.log_size, 0);
    }

    #[test]
    #[allow(clippy::similar_names)]
    fn test_trace_evaluation_single_row_processor_instruction_table() {
        let mut left_intermediate_table = LeftIntermediateTable::new();
        left_intermediate_table.add_entry(ProcessorInstructionEntry::new(
            BaseField::one(),
            BaseField::from(2),
            BaseField::from(3),
            BaseField::from(4),
            BaseField::from(5),
            BaseField::from(6),
            BaseField::from(7),
        ));

        let processor_instruction_table = ProcessorInstructionTable::from(left_intermediate_table);

        let (trace, claim) = processor_instruction_table.trace_evaluation().unwrap();

        assert_eq!(claim.log_size, LOG_N_LANES, "Log size should include SIMD lanes.");
        assert_eq!(
            trace.len(),
            ProcessorInstructionColumn::count().0,
            "Trace should contain one column per register."
        );

        let expected_clk_col = vec![BaseField::one(); 1 << LOG_N_LANES];
        let expected_ip_col = vec![BaseField::from(2); 1 << LOG_N_LANES];
        let expected_ci_col = vec![BaseField::from(3); 1 << LOG_N_LANES];
        let expected_ni_col = vec![BaseField::from(4); 1 << LOG_N_LANES];
        let expected_mp_col = vec![BaseField::from(5); 1 << LOG_N_LANES];
        let expected_mv_col = vec![BaseField::from(6); 1 << LOG_N_LANES];
        let expected_mvi_col = vec![BaseField::from(7); 1 << LOG_N_LANES];

        assert_eq!(
            trace[ProcessorInstructionColumn::Clk.index()].to_cpu().values,
            expected_clk_col
        );
        assert_eq!(trace[ProcessorInstructionColumn::Ip.index()].to_cpu().values, expected_ip_col);
        assert_eq!(trace[ProcessorInstructionColumn::Ci.index()].to_cpu().values, expected_ci_col);
        assert_eq!(trace[ProcessorInstructionColumn::Ni.index()].to_cpu().values, expected_ni_col);
        assert_eq!(trace[ProcessorInstructionColumn::Mp.index()].to_cpu().values, expected_mp_col);
        assert_eq!(trace[ProcessorInstructionColumn::Mv.index()].to_cpu().values, expected_mv_col);
        assert_eq!(
            trace[ProcessorInstructionColumn::Mvi.index()].to_cpu().values,
            expected_mvi_col
        );
    }

    #[test]
    #[allow(clippy::similar_names)]
    #[allow(clippy::too_many_lines)]
    fn test_trace_evaluation_processor_instruction_table_with_multiple_rows() {
        let mut left_intermediate_table = LeftIntermediateTable::new();

        // Add entries to the processor table
        let entries = vec![
            ProcessorInstructionEntry::new(
                BaseField::zero(),
                BaseField::zero(),
                InstructionType::Left.to_base_field(),
                InstructionType::Plus.to_base_field(),
                BaseField::from(4),
                BaseField::from(5),
                BaseField::from(6),
            ),
            ProcessorInstructionEntry::new(
                BaseField::one(),
                BaseField::one(),
                InstructionType::Plus.to_base_field(),
                InstructionType::Left.to_base_field(),
                BaseField::one(),
                BaseField::from(2),
                BaseField::from(3),
            ),
            ProcessorInstructionEntry::new(
                BaseField::from(2),
                BaseField::from(2),
                InstructionType::Left.to_base_field(),
                InstructionType::Minus.to_base_field(),
                BaseField::from(4),
                BaseField::from(5),
                BaseField::from(6),
            ),
            ProcessorInstructionEntry::new(
                BaseField::from(3),
                BaseField::from(3),
                InstructionType::Minus.to_base_field(),
                BaseField::zero(),
                BaseField::one(),
                BaseField::from(2),
                BaseField::from(3),
            ),
        ];

        left_intermediate_table.add_entries(entries);

        let left_table = ProcessorInstructionTable::from(left_intermediate_table);

        // Perform the trace evaluation
        let (trace, claim) = left_table.trace_evaluation().unwrap();

        // Calculate the expected parameters
        let expected_log_n_rows: u32 = 1; // log2(2 rows)
        let expected_log_size = expected_log_n_rows + LOG_N_LANES;
        let expected_size = 1 << expected_log_size;

        // Construct the expected trace columns
        let mut clk_col = BaseColumn::zeros(expected_size);
        let mut ip_col = BaseColumn::zeros(expected_size);
        let mut ci_col = BaseColumn::zeros(expected_size);
        let mut ni_col = BaseColumn::zeros(expected_size);
        let mut mp_col = BaseColumn::zeros(expected_size);
        let mut mv_col = BaseColumn::zeros(expected_size);
        let mut mvi_col = BaseColumn::zeros(expected_size);
        let mut d_col = BaseColumn::zeros(expected_size);
        let mut next_ip_col = BaseColumn::zeros(expected_size);
        let mut next_mp_col = BaseColumn::zeros(expected_size);
        let mut next_mv_col = BaseColumn::zeros(expected_size);

        clk_col.data[0] = BaseField::zero().into();
        clk_col.data[1] = BaseField::from(2).into();

        ip_col.data[0] = BaseField::zero().into();
        ip_col.data[1] = BaseField::from(2).into();

        ci_col.data[0] = InstructionType::Left.to_base_field().into();
        ci_col.data[1] = InstructionType::Left.to_base_field().into();

        ni_col.data[0] = InstructionType::Plus.to_base_field().into();
        ni_col.data[1] = InstructionType::Minus.to_base_field().into();

        mp_col.data[0] = BaseField::from(4).into();
        mp_col.data[1] = BaseField::from(4).into();

        mv_col.data[0] = BaseField::from(5).into();
        mv_col.data[1] = BaseField::from(5).into();

        mvi_col.data[0] = BaseField::from(6).into();
        mvi_col.data[1] = BaseField::from(6).into();

        d_col.data[0] = BaseField::zero().into();
        d_col.data[1] = BaseField::zero().into();

        next_ip_col.data[0] = BaseField::one().into();
        next_ip_col.data[1] = BaseField::from(3).into();

        next_mp_col.data[0] = BaseField::one().into();
        next_mp_col.data[1] = BaseField::one().into();

        next_mv_col.data[0] = BaseField::from(2).into();
        next_mv_col.data[1] = BaseField::from(2).into();

        // Create the expected domain for evaluation
        let domain = CanonicCoset::new(expected_log_size).circle_domain();

        // Transform expected columns into CircleEvaluation
        let expected_trace: TraceEval =
            vec![clk_col, ip_col, ci_col, ni_col, mp_col, mv_col, mvi_col]
                .into_iter()
                .map(|col| CircleEvaluation::new(domain, col))
                .collect();

        // Create the expected claim
        let expected_claim = ProcessorInstructionClaim::new(expected_log_size);

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

    #[allow(clippy::similar_names)]
    #[allow(clippy::too_many_lines)]
    #[test]
    fn test_interaction_trace_evaluation() {
        // Get an execution trace from a valid Brainfuck program
        let code = "+>>><,<.<";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        let (mut machine, _) = create_test_machine(&instructions, &[1]);
        let () = machine.execute().expect("Failed to execute machine");

        let left_table = LeftInstructionTable::from(&machine.trace());

        let (trace_eval, claim) = left_table.trace_evaluation().unwrap();

        let processor_lookup_elements = ProcessorElements::dummy();

        let (interaction_trace_eval, interaction_claim) =
            interaction_trace_evaluation(&trace_eval, &processor_lookup_elements).unwrap();

        let log_size = trace_eval[0].domain.log_size();

        let mut denoms = [PackedSecureField::zero(); 4];

        let clk_col = &trace_eval[ProcessorInstructionColumn::Clk.index()].data;
        let ip_col = &trace_eval[ProcessorInstructionColumn::Ip.index()].data;
        let ci_col = &trace_eval[ProcessorInstructionColumn::Ci.index()].data;
        let ni_col = &trace_eval[ProcessorInstructionColumn::Ni.index()].data;
        let mp_col = &trace_eval[ProcessorInstructionColumn::Mp.index()].data;
        let mv_col = &trace_eval[ProcessorInstructionColumn::Mv.index()].data;
        let mvi_col = &trace_eval[ProcessorInstructionColumn::Mvi.index()].data;

        // Construct the denominator for each row of the logUp column, from the main trace
        // evaluation.
        for vec_row in 0..1 << (log_size - LOG_N_LANES) {
            let clk = clk_col[vec_row];
            let ip = ip_col[vec_row];
            let ci = ci_col[vec_row];
            let ni = ni_col[vec_row];
            let mp = mp_col[vec_row];
            let mv = mv_col[vec_row];
            let mvi = mvi_col[vec_row];

            // Sub-component lookup argument
            let denom: PackedSecureField =
                processor_lookup_elements.combine(&[clk, ip, ci, ni, mp, mv, mvi]);

            denoms[vec_row] = denom;
        }

        let num_0 = -PackedSecureField::one();
        let num_1 = -PackedSecureField::one();
        let num_2 = -PackedSecureField::one();
        let num_3 = PackedSecureField::zero();

        let mut logup_gen = LogupTraceGenerator::new(log_size);

        // Sub Component Lookup
        let mut col_gen = logup_gen.new_col();
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
