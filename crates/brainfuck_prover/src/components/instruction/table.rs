use crate::components::{InstructionClaim, InteractionClaim, TraceColumn, TraceError, TraceEval};
use brainfuck_vm::{machine::ProgramMemory, registers::Registers};
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

/// Represents the Instruction Table, which holds the required registers
/// for the Instruction component.
///
/// To ease constraints evaluation, each row of the Instruction component
/// contains the current row and the next row in natural order.
/// This is done to avoid having to do costly bit-reversals, as constraints
/// are evaluated on the evaluation of the trace which is ordered in
/// a bit-reversed manner over the circle domain once the polynomials are interpolated.
///
/// The preliminary work to extract the fields from the execution trace,
/// the sorting and the padding is done through the [`InstructionIntermediateTable`] struct.
///
/// Once done, we can build the Instruction table from it, by pairing the consecutive
/// [`InstructionTableEntry`] in [`InstructionTableRow`].
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
    pub fn new() -> Self {
        Self::default()
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

    /// Transforms the [`InstructionIntermediateTable`] into a [`TraceEval`], to be committed when
    /// generating a STARK proof.
    ///
    /// The [`InstructionIntermediateTable`] is transformed from an array of rows (one element = one
    /// step of all registers) to an array of columns (one element = all steps of one register).
    /// It is then evaluated on the circle domain.
    ///
    /// # Returns
    /// A tuple containing the evaluated trace and claim for STARK proof.
    ///
    /// # Errors
    /// Returns [`TraceError::EmptyTrace`] if the table is empty.
    pub fn trace_evaluation(&self) -> Result<(TraceEval, InstructionClaim), TraceError> {
        let n_rows = self.table.len() as u32;
        // If the table is empty, there is no data to evaluate, so return an error.
        if n_rows == 0 {
            return Err(TraceError::EmptyTrace);
        }

        // Compute `log_n_rows`, the base-2 logarithm of the number of rows.
        // This determines the smallest power of two greater than or equal to `n_rows`
        //
        // The result is rounded down (i.e. (17 as u32).ilog2() = 4).
        let log_n_rows = n_rows.ilog2();

        // Add `LOG_N_LANES` to account for SIMD optimization. This ensures that
        // the domain size is aligned for parallel processing.
        let log_size = log_n_rows + LOG_N_LANES;

        // Initialize a trace with 3 columns (for `ip`, `ci`, and `ni` registers),
        // each column containing `2^log_size` entries initialized to zero.
        let mut trace = vec![BaseColumn::zeros(1 << log_size); InstructionColumn::count().0];

        // Populate the columns with data from the table rows.
        // We iterate over the table rows and, for each row:
        // - Map the `ip` value to the first column.
        // - Map the `ci` value to the second column.
        // - Map the `ni` value to the third column.
        // - Map the `d` value to the fourth column.
        // - Map the `next_ip` value to the fourth column.
        // - Map the `next_ci` value to the fifth column.
        // - Map the `next_ni` value to the sixth column.
        // - Map the `next_d` value to the seventh column.
        for (index, row) in self.table.iter().enumerate().take(1 << log_n_rows) {
            trace[InstructionColumn::Ip.index()].data[index] = row.ip.into();
            trace[InstructionColumn::Ci.index()].data[index] = row.ci.into();
            trace[InstructionColumn::Ni.index()].data[index] = row.ni.into();
            trace[InstructionColumn::D.index()].data[index] = row.d.into();
            trace[InstructionColumn::NextIp.index()].data[index] = row.next_ip.into();
            trace[InstructionColumn::NextCi.index()].data[index] = row.next_ci.into();
            trace[InstructionColumn::NextNi.index()].data[index] = row.next_ni.into();
            trace[InstructionColumn::NextD.index()].data[index] = row.next_d.into();
        }

        // Create a circle domain using a canonical coset.
        // This domain provides the mathematical structure required for FFT-based evaluation.
        let domain = CanonicCoset::new(log_size).circle_domain();

        // Map each column into the circle domain.
        //
        // This converts the columnar data into polynomial evaluations over the domain, enabling
        // constraint verification in STARK proofs.
        let trace = trace.into_iter().map(|col| CircleEvaluation::new(domain, col)).collect();

        // Return the evaluated trace and a claim containing the log size of the domain.
        Ok((trace, InstructionClaim::new(log_size)))
    }
}

impl From<(&Vec<Registers>, &ProgramMemory)> for InstructionTable {
    fn from((registers, program): (&Vec<Registers>, &ProgramMemory)) -> Self {
        InstructionIntermediateTable::from((registers, program)).into()
    }
}

// Separated from `Vec<Registers> for InstructionTable` to facilitate tests.
// It is assumed that [`InstructionIntermediateTable`] is sorted and padded to the next power of
// two.
impl From<InstructionIntermediateTable> for InstructionTable {
    fn from(mut intermediate_table: InstructionIntermediateTable) -> Self {
        let mut instruction_table = Self::new();

        if intermediate_table.table.is_empty() {
            return instruction_table;
        }

        let last_entry = intermediate_table.table.last().unwrap();
        let next_dummy_entry = InstructionTableEntry::new_dummy(last_entry.ip);

        intermediate_table.add_entry(next_dummy_entry);

        for window in intermediate_table.table.windows(2) {
            match window {
                [entry_1, entry_2] => {
                    let row = InstructionTableRow::new(entry_1, entry_2);
                    instruction_table.add_row(row);
                }
                _ => panic!("Empty window"),
            }
        }
        instruction_table
    }
}

/// Represents a single row of the [`InstructionTable`]
///
/// Two consecutive [`InstructionTableEntry`] flattened.
///
/// To avoid bit-reversals when evaluating transition constraints,
/// the two consecutive rows on which transition constraints are evaluated
/// are flattened into a single row.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct InstructionTableRow {
    /// Instruction pointer: points to the current instruction in the program.
    ip: BaseField,
    /// Current instruction: the instruction at the current instruction pointer.
    ci: BaseField,
    /// Next instruction
    ni: BaseField,
    /// Dummy: Flag whether the current entry is a dummy one or not.
    d: BaseField,
    /// Next Instruction pointer.
    next_ip: BaseField,
    /// Next Current instruction.
    next_ci: BaseField,
    /// Next Next instruction.
    next_ni: BaseField,
    /// Next Dummy.
    next_d: BaseField,
}

impl InstructionTableRow {
    /// Creates a row for the [`InstructionIntermediateTable`] which is considered 'real'.
    ///
    /// A 'real' row, is a row that is part of the execution trace from the Brainfuck program
    /// execution.
    pub const fn new(entry_1: &InstructionTableEntry, entry_2: &InstructionTableEntry) -> Self {
        Self {
            ip: entry_1.ip,
            ci: entry_1.ci,
            ni: entry_1.ni,
            d: entry_1.d,
            next_ip: entry_2.ip,
            next_ci: entry_2.ci,
            next_ni: entry_2.ni,
            next_d: entry_2.d,
        }
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
pub struct InstructionIntermediateTable {
    /// A vector of [`InstructionTableEntry`] representing the table entries.
    table: Vec<InstructionTableEntry>,
}

impl InstructionIntermediateTable {
    /// Creates a new, empty [`InstructionIntermediateTable`].
    ///
    /// # Returns
    /// A new instance of [`InstructionIntermediateTable`] with an empty table.
    const fn new() -> Self {
        Self { table: Vec::new() }
    }

    /// Adds a new entry to the Instruction Table.
    ///
    /// # Arguments
    /// * `entry` - The [`InstructionTableEntry`] to add to the table.
    ///
    /// This method pushes a new [`InstructionTableEntry`] onto the `table` vector.
    fn add_entry(&mut self, entry: InstructionTableEntry) {
        self.table.push(entry);
    }

    /// Adds multiple entries to the Instruction Table.
    ///
    /// # Arguments
    /// * `entries` - A vector of [`InstructionTableEntry`] to add to the table.
    ///
    /// This method extends the `table` vector with the provided entries.
    fn add_entries(&mut self, entries: Vec<InstructionTableEntry>) {
        self.table.extend(entries);
    }

    /// Pads the instruction table with dummy entries up to the next power of two length.
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
                self.add_entry(InstructionTableEntry::new_dummy(last_entry.ip));
            }
        }
    }
}

impl From<(&Vec<Registers>, &ProgramMemory)> for InstructionIntermediateTable {
    fn from((execution_trace, program_memory): (&Vec<Registers>, &ProgramMemory)) -> Self {
        let mut program = Vec::new();

        let code = program_memory.code();

        for (index, ci) in code.iter().enumerate() {
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

        let mut sorted_registers = [program, execution_trace.clone()].concat();
        sorted_registers.sort_by_key(|r| (r.ip, r.clk));

        let instruction_rows = sorted_registers.iter().map(|reg| (reg, false).into()).collect();

        let mut instruction_table = Self::new();
        instruction_table.add_entries(instruction_rows);

        instruction_table.pad();

        instruction_table
    }
}

/// Represents a single entry of the [`InstructionIntermediateTable`].
///
/// Represents the registers used by the Instruction Table of a single step from the execution
/// trace.
///
/// The Instruction Table stores:
/// - The instruction pointer (`ip`),
/// - The current instruction (`ci`),
/// - The next instruction (`ni`).
/// - The dummy flag (`d`).
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct InstructionTableEntry {
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

impl InstructionTableEntry {
    /// Creates an entry for the [`InstructionIntermediateTable`] which is considered 'real'.
    ///
    /// A 'real' entry, is an entry that is part of the execution trace from the Brainfuck program
    /// execution.
    pub fn new(ip: BaseField, ci: BaseField, ni: BaseField) -> Self {
        Self { ip, ci, ni, ..Default::default() }
    }

    /// Creates an entry for the [`InstructionIntermediateTable`] which is considered 'dummy'.
    ///
    /// A 'dummy' entry, is an entry that is not part of the execution trace from the Brainfuck
    /// program execution.
    /// They are used to flag padding rows.
    pub fn new_dummy(ip: BaseField) -> Self {
        Self { ip, d: BaseField::one(), ..Default::default() }
    }
}

impl From<(&Registers, bool)> for InstructionTableEntry {
    fn from((registers, is_dummy): (&Registers, bool)) -> Self {
        if is_dummy {
            Self::new_dummy(registers.ip)
        } else {
            Self::new(registers.ip, registers.ci, registers.ni)
        }
    }
}

/// Enum representing the column indices in the Instruction trace
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstructionColumn {
    /// Index of the `ip` register column in the Instruction trace.
    Ip,
    /// Index of the `ci` register column in the Instruction trace.
    Ci,
    /// Index of the `ni` register column in the Instruction trace.
    Ni,
    /// Index of the `d` register column in the Memory trace.
    D,
    /// Index of the `next_ip` register column in the Instruction trace.
    NextIp,
    /// Index of the `next_ci` register column in the Instruction trace.
    NextCi,
    /// Index of the `next_ni` register column in the Instruction trace.
    NextNi,
    /// Index of the `next_d` register column in the Memory trace.
    NextD,
}

impl InstructionColumn {
    /// Returns the index of the column in the Instruction trace
    pub const fn index(self) -> usize {
        match self {
            Self::Ip => 0,
            Self::Ci => 1,
            Self::Ni => 2,
            Self::D => 3,
            Self::NextIp => 4,
            Self::NextCi => 5,
            Self::NextNi => 6,
            Self::NextD => 7,
        }
    }
}

impl TraceColumn for InstructionColumn {
    fn count() -> (usize, usize) {
        (8, 1)
    }
}

/// The number of random elements necessary for the Instruction lookup argument.
const INSTRUCTION_LOOKUP_ELEMENTS: usize = 3;

/// The interaction elements are drawn for the extension column of the Instruction component.
///
/// The logUp protocol uses these elements to combine the values of the different
/// registers of the main trace to create a random linear combination
/// of them, and use it in the denominator of the fractions in the logUp protocol.
///
/// There are 3 lookup elements in the Instruction component: `ip`, `ci` and `ni`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InstructionElements(LookupElements<INSTRUCTION_LOOKUP_ELEMENTS>);

impl InstructionElements {
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

impl<F: Clone, EF: RelationEFTraitBound<F>> Relation<F, EF> for InstructionElements {
    /// Combine multiple values from a base field (e.g. [`BaseField`])
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
        stringify!(InstructionElements)
    }

    /// Returns the number interaction elements.
    fn get_size(&self) -> usize {
        INSTRUCTION_LOOKUP_ELEMENTS
    }
}

/// Creates the interaction trace from the main trace evaluation
/// and the interaction elements for the Instruction component.
///
/// The Instruction table is the concatenation of the execution trace
/// and the compiled program, sorted by `ip`.
///
/// We want to prove that the Instruction table is a permutation of the Processor table
/// and a sub list of the Program table (as two disjoint subset whose union is the Instruction
/// table). To do so we make a lookup argument which yields for the Processor and the
/// Instruction. Here, each fraction have a multiplicity of -1, while the counterpart in the
/// Processor and Program components will have a multiplicity of 1.
/// The order is kept by having the `ip` register in the denominator.
///
/// Only the 'real' rows are impacting the logUp sum.
/// Dummy rows are padding rows.
///
/// Here, the logUp has a single extension column, which will be used
/// by both the Processor and the Program components.
///
/// # Returns
/// - Interaction trace evaluation, to be committed.
/// - Interaction claim: the total sum from the logUp protocol,
/// to be mixed into the Fiat-Shamir [`Channel`].
#[allow(clippy::similar_names)]
pub fn interaction_trace_evaluation(
    main_trace_eval: &TraceEval,
    lookup_elements: &InstructionElements,
) -> Result<(TraceEval, InteractionClaim), TraceError> {
    if main_trace_eval.is_empty() {
        return Err(TraceError::EmptyTrace)
    }

    let log_size = main_trace_eval[0].domain.log_size();

    let mut logup_gen = LogupTraceGenerator::new(log_size);
    let mut col_gen = logup_gen.new_col();

    let ip_col = &main_trace_eval[InstructionColumn::Ip.index()].data;
    let ci_col = &main_trace_eval[InstructionColumn::Ci.index()].data;
    let ni_col = &main_trace_eval[InstructionColumn::Ni.index()].data;
    let d_col = &main_trace_eval[InstructionColumn::D.index()].data;

    for vec_row in 0..1 << (log_size - LOG_N_LANES) {
        let ip = ip_col[vec_row];
        let ci = ci_col[vec_row];
        let ni = ni_col[vec_row];
        let d = d_col[vec_row];

        let num = PackedSecureField::from(d) - PackedSecureField::one();
        let denom: PackedSecureField = lookup_elements.combine(&[ip, ci, ni]);
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
        compiler::Compiler, instruction::InstructionType, test_helper::create_test_machine,
    };
    use num_traits::{One, Zero};

    #[test]
    fn test_instruction_intermediate_table_new() {
        let instruction_intermediate_table = InstructionIntermediateTable::new();
        assert!(
            instruction_intermediate_table.table.is_empty(),
            "Instruction table should be empty upon initialization."
        );
    }

    #[test]
    fn test_new_instruction_entry() {
        let entry =
            InstructionTableEntry::new(BaseField::one(), BaseField::from(43), BaseField::from(45));

        let expected_entry = InstructionTableEntry {
            ip: BaseField::one(),
            ci: BaseField::from(43),
            ni: BaseField::from(45),
            d: BaseField::zero(),
        };

        assert_eq!(entry, expected_entry);
    }

    #[test]
    fn test_new_dummy_instruction_entry() {
        let entry = InstructionTableEntry::new_dummy(BaseField::one());

        let expected_entry = InstructionTableEntry {
            ip: BaseField::one(),
            ci: BaseField::zero(),
            ni: BaseField::zero(),
            d: BaseField::one(),
        };

        assert_eq!(entry, expected_entry);
    }

    #[test]
    fn test_instruction_row_new() {
        let entry_1 =
            InstructionTableEntry::new(BaseField::zero(), BaseField::from(43), BaseField::from(45));
        let entry_2 = InstructionTableEntry::new_dummy(BaseField::one());

        let row = InstructionTableRow::new(&entry_1, &entry_2);

        let expected_row = InstructionTableRow {
            ip: BaseField::zero(),
            ci: BaseField::from(43),
            ni: BaseField::from(45),
            d: BaseField::zero(),
            next_ip: BaseField::one(),
            next_ci: BaseField::zero(),
            next_ni: BaseField::zero(),
            next_d: BaseField::one(),
        };
        assert_eq!(row, expected_row);
    }

    #[test]
    fn test_add_entry() {
        let mut instruction_intermediate_table = InstructionIntermediateTable::new();
        // Create a entry to add to the table
        let entry =
            InstructionTableEntry::new(BaseField::zero(), BaseField::from(43), BaseField::from(91));
        // Add the entry to the table
        instruction_intermediate_table.add_entry(entry.clone());
        // Check that the table contains the added entry
        assert_eq!(
            instruction_intermediate_table.table,
            vec![entry],
            "Added entry should match the expected entry."
        );
    }

    #[test]
    fn test_add_multiple_entries() {
        let mut instruction_intermediate_table = InstructionIntermediateTable::new();
        // Create a vector of entries to add to the table
        let entries = vec![
            InstructionTableEntry::new(BaseField::zero(), BaseField::from(43), BaseField::from(91)),
            InstructionTableEntry::new(BaseField::one(), BaseField::from(91), BaseField::from(9)),
            InstructionTableEntry::new(
                BaseField::from(2),
                BaseField::from(62),
                BaseField::from(43),
            ),
        ];
        // Add the entries to the table
        instruction_intermediate_table.add_entries(entries.clone());
        // Check that the table contains the added entries
        assert_eq!(instruction_intermediate_table, InstructionIntermediateTable { table: entries });
    }

    #[test]
    fn test_instruction_table_from_registers_empty() {
        // Create an empty vector of registers
        let registers = vec![];

        // Convert to InstructionIntermediateTable and ensure sorting
        let instruction_intermediate_table =
            InstructionIntermediateTable::from((&registers, &Default::default()));

        // Check that the table is empty
        assert!(instruction_intermediate_table.table.is_empty());
    }

    #[allow(clippy::similar_names)]
    #[allow(clippy::too_many_lines)]
    #[test]
    fn test_instruction_intermediate_table_from_registers_example_program() {
        // Create a small program and compile it
        let code = "+>,<[>+.<-]";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        // Create a machine and execute the program
        let (mut machine, _) = create_test_machine(&instructions, &[1]);
        let () = machine.execute().expect("Failed to execute machine");

        // Get the trace of the executed program
        let trace = machine.trace();

        // Convert the trace to an `InstructionIntermediateTable`
        let instruction_intermediate_table: InstructionIntermediateTable =
            (&trace, machine.program()).into();

        // Create the expected `InstructionIntermediateTable`
        let ins_0 = InstructionTableEntry::new(
            BaseField::zero(),
            InstructionType::Plus.to_base_field(),
            InstructionType::Right.to_base_field(),
        );

        let ins_1 = InstructionTableEntry::new(
            BaseField::one(),
            InstructionType::Right.to_base_field(),
            InstructionType::ReadChar.to_base_field(),
        );

        let ins_2 = InstructionTableEntry::new(
            BaseField::from(2),
            InstructionType::ReadChar.to_base_field(),
            InstructionType::Left.to_base_field(),
        );

        let ins_3 = InstructionTableEntry::new(
            BaseField::from(3),
            InstructionType::Left.to_base_field(),
            InstructionType::JumpIfZero.to_base_field(),
        );
        let ins_4 = InstructionTableEntry::new(
            BaseField::from(4),
            InstructionType::JumpIfZero.to_base_field(),
            BaseField::from(12),
        );
        let ins_5 = InstructionTableEntry::new(
            BaseField::from(5),
            BaseField::from(12),
            InstructionType::Right.to_base_field(),
        );
        let ins_6 = InstructionTableEntry::new(
            BaseField::from(6),
            InstructionType::Right.to_base_field(),
            InstructionType::Plus.to_base_field(),
        );
        let ins_7 = InstructionTableEntry::new(
            BaseField::from(7),
            InstructionType::Plus.to_base_field(),
            InstructionType::PutChar.to_base_field(),
        );
        let ins_8 = InstructionTableEntry::new(
            BaseField::from(8),
            InstructionType::PutChar.to_base_field(),
            InstructionType::Left.to_base_field(),
        );
        let ins_9 = InstructionTableEntry::new(
            BaseField::from(9),
            InstructionType::Left.to_base_field(),
            InstructionType::Minus.to_base_field(),
        );
        let inst_10 = InstructionTableEntry::new(
            BaseField::from(10),
            InstructionType::Minus.to_base_field(),
            InstructionType::JumpIfNotZero.to_base_field(),
        );
        let ins_11 = InstructionTableEntry::new(
            BaseField::from(11),
            InstructionType::JumpIfNotZero.to_base_field(),
            BaseField::from(6),
        );
        let ins_12 =
            InstructionTableEntry::new(BaseField::from(12), BaseField::from(6), BaseField::zero());
        let ins_13 =
            InstructionTableEntry::new(BaseField::from(13), BaseField::zero(), BaseField::zero());

        let padded_entry = InstructionTableEntry::new_dummy(BaseField::from(13));
        let padded_entries = vec![padded_entry; 7];

        let mut expected_instruction_intermediate_table = InstructionIntermediateTable {
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
                ins_5,
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
                ins_12,
                ins_13,
            ],
        };

        expected_instruction_intermediate_table.add_entries(padded_entries);

        // Verify that the instruction table is correct
        assert_eq!(instruction_intermediate_table, expected_instruction_intermediate_table);
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
        let trace = machine.trace();

        // Convert the trace to an `InstructionIntermediateTable`
        let instruction_intermediate_table: InstructionIntermediateTable =
            (&trace, machine.program()).into();

        let ins_0 = InstructionTableEntry::new(
            BaseField::zero(),
            InstructionType::JumpIfZero.to_base_field(),
            BaseField::from(4),
        );

        let ins_1 = InstructionTableEntry::new(
            BaseField::one(),
            BaseField::from(4),
            InstructionType::Minus.to_base_field(),
        );

        let ins_2 = InstructionTableEntry::new(
            BaseField::from(2),
            InstructionType::Minus.to_base_field(),
            InstructionType::JumpIfNotZero.to_base_field(),
        );

        let ins_3 = InstructionTableEntry::new(
            BaseField::from(3),
            InstructionType::JumpIfNotZero.to_base_field(),
            BaseField::from(2),
        );

        let ins_4 =
            InstructionTableEntry::new(BaseField::from(4), BaseField::from(2), BaseField::zero());

        let ins_5 =
            InstructionTableEntry::new(BaseField::from(5), BaseField::zero(), BaseField::zero());

        let padded_entry = InstructionTableEntry::new_dummy(BaseField::from(5));
        let padded_entries = vec![padded_entry; 1];
        let mut expected_instruction_intermediate_table = InstructionIntermediateTable {
            table: vec![ins_0.clone(), ins_0, ins_1, ins_2, ins_3, ins_4, ins_5],
        };

        expected_instruction_intermediate_table.add_entries(padded_entries);

        // Verify that the instruction intermediate table is correct
        assert_eq!(instruction_intermediate_table, expected_instruction_intermediate_table);
    }

    #[test]
    fn test_trace_evaluation_empty_table() {
        let instruction_intermediate_table = InstructionIntermediateTable::new();
        let instruction_table = InstructionTable::from(instruction_intermediate_table);
        let result = instruction_table.trace_evaluation();

        assert!(matches!(result, Err(TraceError::EmptyTrace)));
    }

    #[test]
    #[allow(clippy::similar_names)]
    fn test_trace_evaluation_single_row() {
        let mut instruction_intermediate_table = InstructionIntermediateTable::new();
        instruction_intermediate_table.add_entry(InstructionTableEntry::new(
            BaseField::one(),
            BaseField::from(43),
            BaseField::from(91),
        ));

        let instruction_table = InstructionTable::from(instruction_intermediate_table);

        let (trace, claim) = instruction_table.trace_evaluation().unwrap();

        assert_eq!(claim.log_size, LOG_N_LANES, "Log size should include SIMD lanes.");
        assert_eq!(
            trace.len(),
            InstructionColumn::count().0,
            "Trace should contain one column per register."
        );

        // Expected values for the single row
        let expected_ip_column = vec![BaseField::one(); 1 << LOG_N_LANES];
        let expected_ci_column = vec![BaseField::from(43); 1 << LOG_N_LANES];
        let expected_ni_column = vec![BaseField::from(91); 1 << LOG_N_LANES];
        let expected_d_column = vec![BaseField::zero(); 1 << LOG_N_LANES];
        let expected_next_ip_column = vec![BaseField::one(); 1 << LOG_N_LANES];
        let expected_next_ci_column = vec![BaseField::zero(); 1 << LOG_N_LANES];
        let expected_next_ni_column = vec![BaseField::zero(); 1 << LOG_N_LANES];
        let expected_next_d_column = vec![BaseField::one(); 1 << LOG_N_LANES];

        // Check that the entire column matches expected values
        assert_eq!(
            trace[InstructionColumn::Ip.index()].to_cpu().values,
            expected_ip_column,
            "IP column should match expected values."
        );
        assert_eq!(
            trace[InstructionColumn::Ci.index()].to_cpu().values,
            expected_ci_column,
            "CI column should match expected values."
        );
        assert_eq!(
            trace[InstructionColumn::Ni.index()].to_cpu().values,
            expected_ni_column,
            "NI column should match expected values."
        );
        assert_eq!(
            trace[InstructionColumn::D.index()].to_cpu().values,
            expected_d_column,
            "D column should match expected values."
        );

        // Check that the entire column matches expected values
        assert_eq!(
            trace[InstructionColumn::NextIp.index()].to_cpu().values,
            expected_next_ip_column,
            "Next IP column should match expected values."
        );
        assert_eq!(
            trace[InstructionColumn::NextCi.index()].to_cpu().values,
            expected_next_ci_column,
            "Next CI column should match expected values."
        );
        assert_eq!(
            trace[InstructionColumn::NextNi.index()].to_cpu().values,
            expected_next_ni_column,
            "Next NI column should match expected values."
        );
        assert_eq!(
            trace[InstructionColumn::NextD.index()].to_cpu().values,
            expected_next_d_column,
            "Next D column should match expected values."
        );
    }

    #[test]
    #[allow(clippy::similar_names)]
    fn test_instruction_trace_evaluation() {
        let mut instruction_intermediate_table = InstructionIntermediateTable::new();

        // Add entries to the instruction table.
        let entries = vec![
            InstructionTableEntry::new(BaseField::zero(), BaseField::from(43), BaseField::from(91)),
            InstructionTableEntry::new(BaseField::one(), BaseField::from(91), BaseField::from(9)),
        ];
        instruction_intermediate_table.add_entries(entries);

        let instruction_table = InstructionTable::from(instruction_intermediate_table);

        // Perform the trace evaluation.
        let (trace, claim) = instruction_table.trace_evaluation().unwrap();

        // Calculate the expected parameters.
        let expected_log_n_rows: u32 = 1; // log2(2 rows)
        let expected_log_size = expected_log_n_rows + LOG_N_LANES;
        let expected_size = 1 << expected_log_size;

        // Construct the expected trace columns.
        let mut ip_column = BaseColumn::zeros(expected_size);
        let mut ci_column = BaseColumn::zeros(expected_size);
        let mut ni_column = BaseColumn::zeros(expected_size);

        ip_column.data[0] = BaseField::zero().into();
        ip_column.data[1] = BaseField::one().into();

        ci_column.data[0] = BaseField::from(43).into();
        ci_column.data[1] = BaseField::from(91).into();

        ni_column.data[0] = BaseField::from(91).into();
        ni_column.data[1] = BaseField::from(9).into();

        // Create the expected domain for evaluation.
        let domain = CanonicCoset::new(expected_log_size).circle_domain();

        // Transform expected columns into CircleEvaluation.
        let expected_trace: TraceEval = vec![ip_column, ci_column, ni_column]
            .into_iter()
            .map(|col| CircleEvaluation::new(domain, col))
            .collect();

        // Create the expected claim.
        let expected_claim = InstructionClaim::new(expected_log_size);

        // Assert equality of the claim.
        assert_eq!(claim, expected_claim);

        // Assert equality of the trace.
        for col_index in 0..expected_trace.len() {
            assert_eq!(trace[col_index].domain, expected_trace[col_index].domain);
            assert_eq!(trace[col_index].to_cpu().values, expected_trace[col_index].to_cpu().values);
        }
    }

    #[test]
    fn test_trace_evaluation_circle_domain() {
        let mut instruction_intermediate_table = InstructionIntermediateTable::new();
        instruction_intermediate_table.add_entries(vec![
            InstructionTableEntry::new(BaseField::zero(), BaseField::from(43), BaseField::from(91)),
            InstructionTableEntry::new(BaseField::one(), BaseField::from(91), BaseField::from(9)),
        ]);

        let instruction_table = InstructionTable::from(instruction_intermediate_table);

        let (trace, claim) = instruction_table.trace_evaluation().unwrap();

        let log_size = claim.log_size;
        let domain = CanonicCoset::new(log_size).circle_domain();

        // Check that each column is evaluated over the correct domain
        for column in trace {
            assert_eq!(
                column.domain, domain,
                "Trace column domain should match expected circle domain."
            );
        }
    }

    #[test]
    fn test_empty_interaction_trace_evaluation() {
        let empty_eval = vec![];
        let lookup_elements = InstructionElements::dummy();
        let interaction_trace_eval = interaction_trace_evaluation(&empty_eval, &lookup_elements);

        assert!(matches!(interaction_trace_eval, Err(TraceError::EmptyTrace)));
    }

    #[allow(clippy::similar_names)]
    #[test]
    fn test_interaction_trace_evaluation() {
        let code = "+->[-]";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        let (mut machine, _) = create_test_machine(&instructions, &[]);
        let () = machine.execute().expect("Failed to execute machine");

        let trace = machine.trace();
        let intermediate_table = InstructionIntermediateTable::from((&trace, machine.program()));
        let instruction_table = InstructionTable::from(intermediate_table);

        let (trace_eval, claim) = instruction_table.trace_evaluation().unwrap();

        let lookup_elements = InstructionElements::dummy();
        let (interaction_trace_eval, interaction_claim) =
            interaction_trace_evaluation(&trace_eval, &lookup_elements).unwrap();

        let log_size = trace_eval[0].domain.log_size();

        let mut denoms = [PackedSecureField::zero(); 16];
        let ip_col = &trace_eval[InstructionColumn::Ip.index()].data;
        let ci_col = &trace_eval[InstructionColumn::Ci.index()].data;
        let ni_col = &trace_eval[InstructionColumn::Ni.index()].data;

        // Construct the denominator for each row of the logUp column, from the main trace
        // evaluation.
        for vec_row in 0..1 << (log_size - LOG_N_LANES) {
            let ip = ip_col[vec_row];
            let ci = ci_col[vec_row];
            let ni = ni_col[vec_row];
            let denom: PackedSecureField = lookup_elements.combine(&[ip, ci, ni]);
            denoms[vec_row] = denom;
        }

        let mut logup_gen = LogupTraceGenerator::new(log_size);

        let mut col_gen = logup_gen.new_col();

        col_gen.write_frac(0, -PackedSecureField::one(), denoms[0]);
        col_gen.write_frac(1, -PackedSecureField::one(), denoms[1]);
        col_gen.write_frac(2, -PackedSecureField::one(), denoms[2]);
        col_gen.write_frac(3, -PackedSecureField::one(), denoms[3]);
        col_gen.write_frac(4, -PackedSecureField::one(), denoms[4]);
        col_gen.write_frac(5, -PackedSecureField::one(), denoms[5]);
        col_gen.write_frac(6, -PackedSecureField::one(), denoms[6]);
        col_gen.write_frac(7, -PackedSecureField::one(), denoms[7]);
        col_gen.write_frac(8, -PackedSecureField::one(), denoms[8]);
        col_gen.write_frac(9, -PackedSecureField::one(), denoms[9]);
        col_gen.write_frac(10, -PackedSecureField::one(), denoms[10]);
        col_gen.write_frac(11, -PackedSecureField::one(), denoms[11]);
        col_gen.write_frac(12, -PackedSecureField::one(), denoms[12]);
        col_gen.write_frac(13, PackedSecureField::zero(), denoms[13]);
        col_gen.write_frac(14, PackedSecureField::zero(), denoms[14]);
        col_gen.write_frac(15, PackedSecureField::zero(), denoms[15]);

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
