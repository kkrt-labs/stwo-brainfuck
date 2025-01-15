use crate::components::{
    processor::table::ProcessorElements, InteractionClaim, JumpClaim, TraceColumn, TraceError,
    TraceEval,
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

pub type JumpIfNotZeroTable = JumpTable<{ InstructionType::JumpIfNotZero.to_u32() }>;

pub type JumpIfZeroTable = JumpTable<{ InstructionType::JumpIfZero.to_u32() }>;

/// Represents the `Jump` table for the Processor sub-components representing the jump instructions
/// `[` and `]`.
///
/// The table contains the required registers for verifying the correct state
/// transition of a jump instruction.
///
/// The `Jump` tables ensure that the `[` and `]` instruction are correctly executed.
///
/// To ease constraints evaluation, each row of a `Jump` component
/// contains the current row and the next row in natural order.
/// This is done to avoid having to do costly bit-reversals, as constraints
/// are evaluated on the evaluation of the trace which is ordered in
/// a bit-reversed manner over the circle domain once the polynomials are interpolated.
///
/// The preliminary work to extract the fields from the execution trace,
/// the sorting and the padding is done through the [`JumpIntermediateTable`] struct.
///
/// Once done, we can build the `Jump` table from it, by pairing the consecutive
/// [`JumpEntry`] in [`JumpRow`].
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct JumpTable<const N: u32> {
    /// A vector of [`JumpRow`] representing the table rows.
    table: Vec<JumpRow>,
}

impl<const N: u32> JumpTable<N> {
    /// Creates a new, empty [`JumpTable`].
    ///
    /// # Returns
    /// A new instance of [`JumpTable`] with an empty table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a new row to the Jump Table.
    ///
    /// # Arguments
    /// * `row` - The [`JumpRow`] to add to the table.
    ///
    /// This method pushes a new [`JumpRow`] onto the `table` vector.
    fn add_row(&mut self, row: JumpRow) {
        self.table.push(row);
    }

    /// Transforms the [`JumpTable`] into a [`TraceEval`], to be committed when
    /// generating a STARK proof.
    ///
    /// Converts the entry-based table into columnar format and evaluates it over
    /// the circle domain.
    ///
    /// # Returns
    /// A tuple containing the evaluated trace and claim for STARK proof.
    /// If the table is empty, returns an empty trace and a claim with a log size of 0.
    pub fn trace_evaluation(&self) -> (TraceEval, JumpClaim) {
        let n_rows = self.table.len() as u32;
        // It is possible that the table is empty because the program has no jump instruction.
        if n_rows == 0 {
            return (TraceEval::new(), JumpClaim::new(0));
        }

        // Compute log size and adjust for SIMD lanes
        let log_n_rows = n_rows.ilog2();
        let log_size = log_n_rows + LOG_N_LANES;

        // Initialize trace columns
        let mut trace = vec![BaseColumn::zeros(1 << log_size); JumpColumn::count().0];

        // Fill columns with table data
        for (index, row) in self.table.iter().enumerate().take(1 << log_n_rows) {
            trace[JumpColumn::Clk.index()].data[index] = row.clk.into();
            trace[JumpColumn::Ip.index()].data[index] = row.ip.into();
            trace[JumpColumn::Ci.index()].data[index] = row.ci.into();
            trace[JumpColumn::Ni.index()].data[index] = row.ni.into();
            trace[JumpColumn::Mp.index()].data[index] = row.mp.into();
            trace[JumpColumn::Mv.index()].data[index] = row.mv.into();
            trace[JumpColumn::Mvi.index()].data[index] = row.mvi.into();
            trace[JumpColumn::D.index()].data[index] = row.d.into();
            trace[JumpColumn::NextClk.index()].data[index] = row.next_clk.into();
            trace[JumpColumn::NextIp.index()].data[index] = row.next_ip.into();
            trace[JumpColumn::NextMp.index()].data[index] = row.next_mp.into();
            trace[JumpColumn::NextMv.index()].data[index] = row.next_mv.into();
            trace[JumpColumn::IsMvZero.index()].data[index] = row.is_mv_zero.into();
        }

        // Evaluate columns on the circle domain
        let domain = CanonicCoset::new(log_size).circle_domain();
        let trace = trace.into_iter().map(|col| CircleEvaluation::new(domain, col)).collect();

        // Return the evaluated trace and claim
        (trace, JumpClaim::new(log_size))
    }
}

impl<const N: u32> From<&Vec<Registers>> for JumpTable<N> {
    fn from(registers: &Vec<Registers>) -> Self {
        JumpIntermediateTable::<N>::from(registers).into()
    }
}

// Separated from `From<&Vec<Registers>> for JumpTable` to facilitate tests.
// It is assumed that [`JumpIntermediateTable`] is sorted and padded to the next power of
// two.
impl<const N: u32> From<JumpIntermediateTable<N>> for JumpTable<N> {
    fn from(intermediate_table: JumpIntermediateTable<N>) -> Self {
        let mut jump_table = Self::new();

        if intermediate_table.table.is_empty() {
            return jump_table;
        }

        for window in intermediate_table.table.chunks(2) {
            match window {
                [entry_1, entry_2] => {
                    let row = JumpRow::new(entry_1, entry_2);
                    jump_table.add_row(row);
                }
                [entry] => {
                    let next_dummy = JumpEntry::new_dummy(entry.clk + BaseField::one(), entry.ip);
                    let row = JumpRow::new(entry, &next_dummy);
                    jump_table.add_row(row);
                }
                _ => panic!("Empty window"),
            }
        }
        jump_table
    }
}

/// Represents a single row in the Processor Table.
///
/// Two consecutive entries [`JumpEntry`] flattened.
///
/// To avoid bit-reversals when evaluating transition constraints,
/// the two consecutives rows on which transition constraints are evaluated
/// are flattened into a single row.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct JumpRow {
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
    /// Next Clock cycle counter.
    next_clk: BaseField,
    /// Next Instruction pointer
    next_ip: BaseField,
    /// Next Memory pointer
    next_mp: BaseField,
    /// Next Memory value
    next_mv: BaseField,
    /// Dummy: Flag whether the current row is dummy or not.
    d: BaseField,
    /// Flag to indicate whether `mv` equals zero or not.
    is_mv_zero: BaseField,
}

impl JumpRow {
    /// Creates a row for the [`JumpTable`] which is considered 'real'.
    ///
    /// A 'real' row, is a row that is part of the execution trace from the Brainfuck program
    /// execution.
    pub fn new(entry_1: &JumpEntry, entry_2: &JumpEntry) -> Self {
        assert!(entry_1.d == entry_2.d, "Both entries should be either real or dummy.");
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
            next_mp: entry_2.mp,
            next_mv: entry_2.mv,
            d: entry_1.d,
            is_mv_zero: BaseField::one() - entry_1.mv * entry_1.mvi,
        }
    }
}

#[cfg(test)]
pub type JumpIfNotZeroIntermediateTable =
    JumpIntermediateTable<{ InstructionType::JumpIfNotZero.to_u32() }>;

#[cfg(test)]
pub type JumpIfZeroIntermediateTable =
    JumpIntermediateTable<{ InstructionType::JumpIfZero.to_u32() }>;

/// An intermediate representation of the trace, between the execution trace and the trace for the
/// Jump instruction components.
///
/// It allows extracting the required fields from the execution trace provided by the Brainfuck
/// Virtual Machine.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct JumpIntermediateTable<const N: u32> {
    /// A vector of [`JumpEntry`] representing the entries of the table.
    table: Vec<JumpEntry>,
}

impl<const N: u32> JumpIntermediateTable<N> {
    /// Creates a new, empty [`JumpIntermediateTable`].
    ///
    /// # Returns
    /// A new instance of [`JumpIntermediateTable`] with an empty table.
    pub const fn new() -> Self {
        Self { table: Vec::new() }
    }

    /// Adds a new entry to the table.
    ///
    /// # Arguments
    /// * `entry` - The [`JumpEntry`] to add to the table.
    ///
    /// This method pushes a new [`JumpEntry`] onto the `table` vector.
    pub fn add_entry(&mut self, entry: JumpEntry) {
        self.table.push(entry);
    }

    /// Adds multiple entries to the table.
    ///
    /// # Arguments
    /// * `entries` - A vector of [`JumpEntry`] to add to the table.
    ///
    /// This method extends the `table` vector with the provided entries.
    fn add_entries(&mut self, entries: Vec<JumpEntry>) {
        self.table.extend(entries);
    }

    /// Pads the table with dummy entries up to the next power of two length.
    ///
    /// Each dummy entry increase clk, copy the others from the last step
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
            let dummy_entry = JumpEntry::new_dummy(last_clk + BaseField::from(i), last_ip);
            self.add_entry(dummy_entry);
        }
    }
}

impl<const N: u32> From<&Vec<Registers>> for JumpIntermediateTable<N> {
    fn from(registers: &Vec<Registers>) -> Self {
        let mut jump_table = Self::new();

        // We must have the value of the instruction and the following executed instruction.
        let entries = registers
            .iter()
            .zip(registers.iter().skip(1))
            .filter(|(reg, _)| reg.ci == InstructionType::try_from(N).unwrap().to_base_field())
            .flat_map(|(reg_0, reg_1)| [JumpEntry::from(reg_0), JumpEntry::from(reg_1)])
            .collect();

        jump_table.add_entries(entries);
        jump_table.pad();

        jump_table
    }
}

/// Represents a single entry in the [`JumpTable`].
///
/// Each entry contains the values for the following registers:
/// - `clk`: The clock cycle counter, represents the current step.
/// - `ip`: The instruction pointer.
/// - `ci`: The current instruction.
/// - `ni`: The next instruction.
/// - `mp`: The memory pointer.
/// - `mv`: The memory value.
/// - `mvi`: The memory value inverse.
/// - `d`: The dummy entry flag.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct JumpEntry {
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
    /// Dummy: Flag whether the current entry is dummy or not.
    d: BaseField,
}

impl JumpEntry {
    /// Creates an entry for the [`JumpIntermediateTable`] which is considered 'real'.
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

    /// Creates an entry for the [`JumpIntermediateTable`] which is considered 'dummy'.
    ///
    /// A 'dummy' entry, is an entry that is not part of the execution trace from the Brainfuck
    /// program execution.
    /// They are used to flag padding rows.
    pub fn new_dummy(clk: BaseField, ip: BaseField) -> Self {
        Self { clk, ip, d: BaseField::one(), ..Default::default() }
    }
}

impl From<&Registers> for JumpEntry {
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

/// Enum representing the column indices in the Jump trace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JumpColumn {
    Clk,
    Ip,
    Ci,
    Ni,
    Mp,
    Mv,
    Mvi,
    NextClk,
    NextIp,
    NextMp,
    NextMv,
    D,
    IsMvZero,
}

impl JumpColumn {
    /// Returns the index of the column in the Jump trace.
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
            Self::NextMp => 9,
            Self::NextMv => 10,
            Self::D => 11,
            Self::IsMvZero => 12,
        }
    }
}

impl TraceColumn for JumpColumn {
    fn count() -> (usize, usize) {
        (13, 1)
    }
}

/// Creates the interaction trace from the main trace evaluation
/// and the interaction elements for the `Jump` component.
///
/// The [`JumpTable`] represents the trace of the `]` instructions in the execution trace.
///
/// The [`JumpTable`] is a sub-component of the processor component,
/// it yields the Processor to verify the correct execution of the `]` (jnz) instruction.
///
/// Only the 'real' rows are impacting the logUp sum.
/// Dummy rows are padding rows.
///
/// Here, the logUp has a single extension columns, used by the
/// Processor component.
///
/// # Returns
/// - Interaction trace evaluation, to be committed.
/// - Interaction claim: the total sum from the logUp protocol, to be mixed into the Fiat-Shamir
///   channel.
#[allow(clippy::similar_names)]
pub fn interaction_trace_evaluation(
    main_trace_eval: &TraceEval,
    processor_lookup_elements: &ProcessorElements,
) -> Result<(TraceEval, InteractionClaim), TraceError> {
    // If the main trace of the Jump components is empty, then we claimed that it's log
    // size is zero.
    let log_size = main_trace_eval[0].domain.log_size();

    let clk_col = &main_trace_eval[JumpColumn::Clk.index()].data;
    let ip_col = &main_trace_eval[JumpColumn::Ip.index()].data;
    let ci_col = &main_trace_eval[JumpColumn::Ci.index()].data;
    let ni_col = &main_trace_eval[JumpColumn::Ni.index()].data;
    let mp_col = &main_trace_eval[JumpColumn::Mp.index()].data;
    let mv_col = &main_trace_eval[JumpColumn::Mv.index()].data;
    let mvi_col = &main_trace_eval[JumpColumn::Mvi.index()].data;
    let d_col = &main_trace_eval[JumpColumn::D.index()].data;

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
    fn test_jump_entry_from_registers() {
        let registers = Registers {
            clk: BaseField::one(),
            ip: BaseField::from(5),
            ci: BaseField::from(43),
            ni: BaseField::from(91),
            mp: BaseField::from(2),
            mv: BaseField::from(7),
            mvi: BaseField::zero(),
        };

        let entry = JumpEntry::from(&registers);

        let expected_entry = JumpEntry::new(
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
    fn test_jump_row() {
        let entry_1 = JumpEntry::new(
            BaseField::one(),
            BaseField::from(5),
            BaseField::from(43),
            BaseField::from(91),
            BaseField::from(2),
            BaseField::one(),
            BaseField::one(),
        );

        let entry_2 = JumpEntry::new(
            BaseField::from(2),
            BaseField::from(4),
            BaseField::from(91),
            BaseField::from(6),
            BaseField::one(),
            BaseField::zero(),
            BaseField::zero(),
        );

        let row = JumpRow::new(&entry_1, &entry_2);

        let expected_row = JumpRow {
            clk: BaseField::one(),
            ip: BaseField::from(5),
            ci: BaseField::from(43),
            ni: BaseField::from(91),
            mp: BaseField::from(2),
            mv: BaseField::one(),
            mvi: BaseField::one(),
            next_clk: BaseField::from(2),
            next_ip: BaseField::from(4),
            next_mp: BaseField::one(),
            is_mv_zero: BaseField::zero(),
            ..Default::default()
        };

        assert_eq!(row, expected_row);
    }

    #[test]
    fn test_jump_if_not_zero_intermediate_table_new() {
        let jump_if_not_zero_intermediate_table = JumpIfNotZeroIntermediateTable::new();

        assert!(jump_if_not_zero_intermediate_table.table.is_empty());
    }

    #[test]
    fn test_jump_if_zero_intermediate_table_new() {
        let jump_if_zero_intermediate_table = JumpIfZeroIntermediateTable::new();

        assert!(jump_if_zero_intermediate_table.table.is_empty());
    }

    #[test]
    fn test_jump_if_not_zero_table_new() {
        let jump_if_not_zero_table = JumpIfNotZeroTable::new();

        assert!(jump_if_not_zero_table.table.is_empty());
    }

    #[test]
    fn test_jump_if_zero_table_new() {
        let jump_if_zero_table = JumpIfZeroTable::new();

        assert!(jump_if_zero_table.table.is_empty());
    }

    #[test]
    fn test_add_entry_jump_if_not_zero() {
        let mut jump_if_not_zero_table = JumpIfNotZeroIntermediateTable::new();

        let entry = JumpEntry::new(
            BaseField::from(10),
            BaseField::from(15),
            BaseField::from(43),
            BaseField::from(91),
            BaseField::from(20),
            BaseField::from(25),
            BaseField::one(),
        );

        jump_if_not_zero_table.add_entry(entry.clone());

        assert_eq!(jump_if_not_zero_table.table, vec![entry]);
    }

    #[test]
    fn test_add_entry_jump_if_zero() {
        let mut jump_if_zero_table = JumpIfZeroIntermediateTable::new();

        let entry = JumpEntry::new(
            BaseField::from(10),
            BaseField::from(15),
            BaseField::from(45),
            BaseField::from(91),
            BaseField::from(20),
            BaseField::from(25),
            BaseField::one(),
        );

        jump_if_zero_table.add_entry(entry.clone());

        assert_eq!(jump_if_zero_table.table, vec![entry]);
    }

    #[test]
    fn test_add_multiple_entries_jump_if_not_zero() {
        let mut jump_if_not_zero_table = JumpIfNotZeroIntermediateTable::new();

        let entries = vec![
            JumpEntry::new(
                BaseField::one(),
                BaseField::from(5),
                BaseField::from(43),
                BaseField::from(91),
                BaseField::from(10),
                BaseField::from(15),
                BaseField::zero(),
            ),
            JumpEntry::new(
                BaseField::from(2),
                BaseField::from(6),
                BaseField::from(44),
                BaseField::from(92),
                BaseField::from(11),
                BaseField::from(16),
                BaseField::one(),
            ),
            JumpEntry::new(
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
            jump_if_not_zero_table.add_entry(entry.clone());
        }

        assert_eq!(jump_if_not_zero_table.table, entries,);
    }

    #[allow(clippy::similar_names)]
    #[test]
    fn test_jump_if_not_zero_table_from_registers_example_program() {
        // Create a small program and compile it
        let code = "++>,<[>+.<-]";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        // Create a machine and execute the program
        let (mut machine, _) = create_test_machine(&instructions, &[1]);
        let () = machine.execute().expect("Failed to execute machine");

        // Get the trace of the executed program
        let trace = machine.trace();

        // Convert the trace to an `JumpIfNotZeroIntermediateTable`
        let jump_if_not_zero_intermediate_table = JumpIfNotZeroIntermediateTable::from(&trace);

        // Create the `JumpIfNotZeroTable`.
        let jump_if_not_zero_table =
            JumpIfNotZeroTable::from(jump_if_not_zero_intermediate_table.clone());

        // Create the expected `JumpIfNotZeroIntermediateTable`

        let jump_0 = JumpEntry::new(
            BaseField::from(11),
            BaseField::from(12),
            InstructionType::JumpIfNotZero.to_base_field(),
            BaseField::from(7),
            BaseField::zero(),
            BaseField::one(),
            BaseField::one(),
        );

        let next_jump_0 = JumpEntry::new(
            BaseField::from(12),
            BaseField::from(7),
            InstructionType::Right.to_base_field(),
            InstructionType::Plus.to_base_field(),
            BaseField::zero(),
            BaseField::one(),
            BaseField::one(),
        );

        let jump_1 = JumpEntry::new(
            BaseField::from(17),
            BaseField::from(12),
            InstructionType::JumpIfNotZero.to_base_field(),
            BaseField::from(7),
            BaseField::zero(),
            BaseField::zero(),
            BaseField::zero(),
        );

        let next_jump_1 = JumpEntry::new(
            BaseField::from(18),
            BaseField::from(14),
            BaseField::zero(),
            BaseField::zero(),
            BaseField::zero(),
            BaseField::zero(),
            BaseField::zero(),
        );

        let mut expected_jump_if_not_zero_intermediate_table = JumpIfNotZeroIntermediateTable {
            table: vec![jump_0.clone(), next_jump_0.clone(), jump_1.clone(), next_jump_1.clone()],
        };

        expected_jump_if_not_zero_intermediate_table.pad();

        let mut expected_jump_if_not_zero_table = JumpTable::new();

        let row_0 = JumpRow::new(&jump_0, &next_jump_0);
        let row_1 = JumpRow::new(&jump_1, &next_jump_1);

        expected_jump_if_not_zero_table.add_row(row_0);
        expected_jump_if_not_zero_table.add_row(row_1);

        // Verify that the processor table is correct
        assert_eq!(
            jump_if_not_zero_intermediate_table,
            expected_jump_if_not_zero_intermediate_table
        );
        assert_eq!(jump_if_not_zero_table, expected_jump_if_not_zero_table);
    }

    #[test]
    fn test_trace_evaluation_empty_jump_table() {
        let jump_if_not_zero_table = JumpIfNotZeroTable::new();
        let (trace, claim) = jump_if_not_zero_table.trace_evaluation();

        assert_eq!(trace.len(), 0);
        assert_eq!(claim.log_size, 0);
    }

    #[test]
    #[allow(clippy::similar_names)]
    fn test_trace_evaluation_single_row_jump_table() {
        let mut jump_if_not_zero_intermediate_table = JumpIfNotZeroIntermediateTable::new();
        jump_if_not_zero_intermediate_table.add_entry(JumpEntry::new(
            BaseField::one(),
            BaseField::from(2),
            InstructionType::JumpIfNotZero.to_base_field(),
            BaseField::one(),
            BaseField::from(5),
            BaseField::zero(),
            BaseField::zero(),
        ));

        jump_if_not_zero_intermediate_table.add_entry(JumpEntry::new(
            BaseField::from(2),
            BaseField::from(3),
            BaseField::zero(),
            BaseField::zero(),
            BaseField::from(5),
            BaseField::zero(),
            BaseField::zero(),
        ));

        let jump_if_not_zero_table = JumpIfNotZeroTable::from(jump_if_not_zero_intermediate_table);

        let (trace, claim) = jump_if_not_zero_table.trace_evaluation();

        assert_eq!(claim.log_size, LOG_N_LANES, "Log size should include SIMD lanes.");
        assert_eq!(
            trace.len(),
            JumpColumn::count().0,
            "Trace should contain one column per register."
        );

        let expected_clk_col = vec![BaseField::one(); 1 << LOG_N_LANES];
        let expected_ip_col = vec![BaseField::from(2); 1 << LOG_N_LANES];
        let expected_ci_col =
            vec![InstructionType::JumpIfNotZero.to_base_field(); 1 << LOG_N_LANES];
        let expected_ni_col = vec![BaseField::one(); 1 << LOG_N_LANES];
        let expected_mp_col = vec![BaseField::from(5); 1 << LOG_N_LANES];
        let expected_mv_col = vec![BaseField::zero(); 1 << LOG_N_LANES];
        let expected_mvi_col = vec![BaseField::zero(); 1 << LOG_N_LANES];
        let expected_next_clk_col = vec![BaseField::from(2); 1 << LOG_N_LANES];
        let expected_next_ip_col = vec![BaseField::from(3); 1 << LOG_N_LANES];
        let expected_next_mp_col = vec![BaseField::from(5); 1 << LOG_N_LANES];
        let expected_next_mv_col = vec![BaseField::zero(); 1 << LOG_N_LANES];
        let expected_d_col = vec![BaseField::zero(); 1 << LOG_N_LANES];
        let expected_is_mv_zero_col = vec![BaseField::one(); 1 << LOG_N_LANES];

        assert_eq!(trace[JumpColumn::Clk.index()].to_cpu().values, expected_clk_col);
        assert_eq!(trace[JumpColumn::Ip.index()].to_cpu().values, expected_ip_col);
        assert_eq!(trace[JumpColumn::Ci.index()].to_cpu().values, expected_ci_col);
        assert_eq!(trace[JumpColumn::Ni.index()].to_cpu().values, expected_ni_col);
        assert_eq!(trace[JumpColumn::Mp.index()].to_cpu().values, expected_mp_col);
        assert_eq!(trace[JumpColumn::Mv.index()].to_cpu().values, expected_mv_col);
        assert_eq!(trace[JumpColumn::Mvi.index()].to_cpu().values, expected_mvi_col);
        assert_eq!(trace[JumpColumn::NextClk.index()].to_cpu().values, expected_next_clk_col);
        assert_eq!(trace[JumpColumn::NextIp.index()].to_cpu().values, expected_next_ip_col);
        assert_eq!(trace[JumpColumn::NextMp.index()].to_cpu().values, expected_next_mp_col);
        assert_eq!(trace[JumpColumn::NextMv.index()].to_cpu().values, expected_next_mv_col);
        assert_eq!(trace[JumpColumn::D.index()].to_cpu().values, expected_d_col);
        assert_eq!(trace[JumpColumn::IsMvZero.index()].to_cpu().values, expected_is_mv_zero_col);
    }

    #[test]
    #[allow(clippy::similar_names)]
    #[allow(clippy::too_many_lines)]
    fn test_trace_evaluation_jump_table_with_multiple_rows() {
        let mut jump_if_not_zero_intermediate_table = JumpIfNotZeroIntermediateTable::new();

        // Add entries to the processor table
        let entries = vec![
            JumpEntry::new(
                BaseField::from(11),
                BaseField::from(12),
                InstructionType::JumpIfNotZero.to_base_field(),
                BaseField::from(7),
                BaseField::zero(),
                BaseField::one(),
                BaseField::one(),
            ),
            JumpEntry::new(
                BaseField::from(12),
                BaseField::from(7),
                InstructionType::Right.to_base_field(),
                InstructionType::Plus.to_base_field(),
                BaseField::zero(),
                BaseField::one(),
                BaseField::one(),
            ),
            JumpEntry::new(
                BaseField::from(17),
                BaseField::from(12),
                InstructionType::JumpIfNotZero.to_base_field(),
                BaseField::from(7),
                BaseField::zero(),
                BaseField::zero(),
                BaseField::zero(),
            ),
            JumpEntry::new(
                BaseField::from(18),
                BaseField::from(14),
                BaseField::zero(),
                BaseField::zero(),
                BaseField::zero(),
                BaseField::zero(),
                BaseField::zero(),
            ),
        ];

        jump_if_not_zero_intermediate_table.add_entries(entries);

        let jump_if_not_zero_table = JumpIfNotZeroTable::from(jump_if_not_zero_intermediate_table);

        // Perform the trace evaluation
        let (trace, claim) = jump_if_not_zero_table.trace_evaluation();

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
        let mut next_clk_col = BaseColumn::zeros(expected_size);
        let mut next_ip_col = BaseColumn::zeros(expected_size);
        let mut next_mp_col = BaseColumn::zeros(expected_size);
        let mut next_mv_col = BaseColumn::zeros(expected_size);
        let mut d_col = BaseColumn::zeros(expected_size);
        let mut is_mv_zero_col = BaseColumn::zeros(expected_size);

        clk_col.data[0] = BaseField::from(11).into();
        clk_col.data[1] = BaseField::from(17).into();

        ip_col.data[0] = BaseField::from(12).into();
        ip_col.data[1] = BaseField::from(12).into();

        ci_col.data[0] = InstructionType::JumpIfNotZero.to_base_field().into();
        ci_col.data[1] = InstructionType::JumpIfNotZero.to_base_field().into();

        ni_col.data[0] = BaseField::from(7).into();
        ni_col.data[1] = BaseField::from(7).into();

        mp_col.data[0] = BaseField::zero().into();
        mp_col.data[1] = BaseField::zero().into();

        mv_col.data[0] = BaseField::one().into();
        mv_col.data[1] = BaseField::zero().into();

        mvi_col.data[0] = BaseField::one().into();
        mvi_col.data[1] = BaseField::zero().into();

        next_clk_col.data[0] = BaseField::from(12).into();
        next_clk_col.data[1] = BaseField::from(18).into();

        next_ip_col.data[0] = BaseField::from(7).into();
        next_ip_col.data[1] = BaseField::from(14).into();

        next_mp_col.data[0] = BaseField::zero().into();
        next_mp_col.data[1] = BaseField::zero().into();

        next_mv_col.data[0] = BaseField::one().into();
        next_mv_col.data[1] = BaseField::zero().into();

        d_col.data[0] = BaseField::zero().into();
        d_col.data[1] = BaseField::zero().into();

        is_mv_zero_col.data[0] = BaseField::zero().into();
        is_mv_zero_col.data[1] = BaseField::one().into();

        // Create the expected domain for evaluation
        let domain = CanonicCoset::new(expected_log_size).circle_domain();

        // Transform expected columns into CircleEvaluation
        let expected_trace: TraceEval = vec![
            clk_col,
            ip_col,
            ci_col,
            ni_col,
            mp_col,
            mv_col,
            mvi_col,
            next_clk_col,
            next_ip_col,
            next_mp_col,
            next_mv_col,
            d_col,
            is_mv_zero_col,
        ]
        .into_iter()
        .map(|col| CircleEvaluation::new(domain, col))
        .collect();

        // Create the expected claim
        let expected_claim = JumpClaim::new(expected_log_size);

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
        let code = "++>,<[>+.<-]";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        let (mut machine, _) = create_test_machine(&instructions, &[1]);
        let () = machine.execute().expect("Failed to execute machine");

        let jump_if_not_zero_table = JumpIfNotZeroTable::from(&machine.trace());

        let (trace_eval, claim) = jump_if_not_zero_table.trace_evaluation();

        let processor_lookup_elements = ProcessorElements::dummy();

        let (interaction_trace_eval, interaction_claim) =
            interaction_trace_evaluation(&trace_eval, &processor_lookup_elements).unwrap();

        let log_size = trace_eval[0].domain.log_size();

        let mut denoms = [PackedSecureField::zero(); 2];

        let clk_col = &trace_eval[JumpColumn::Clk.index()].data;
        let ip_col = &trace_eval[JumpColumn::Ip.index()].data;
        let ci_col = &trace_eval[JumpColumn::Ci.index()].data;
        let ni_col = &trace_eval[JumpColumn::Ni.index()].data;
        let mp_col = &trace_eval[JumpColumn::Mp.index()].data;
        let mv_col = &trace_eval[JumpColumn::Mv.index()].data;
        let mvi_col = &trace_eval[JumpColumn::Mvi.index()].data;

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

            // Jump lookup argument
            let denom: PackedSecureField =
                processor_lookup_elements.combine(&[clk, ip, ci, ni, mp, mv, mvi]);

            denoms[vec_row] = denom;
        }

        let num_0 = -PackedSecureField::one();
        let num_1 = -PackedSecureField::one();

        let mut logup_gen = LogupTraceGenerator::new(log_size);

        // Instruction Lookup
        let mut col_gen = logup_gen.new_col();
        col_gen.write_frac(0, num_0, denoms[0]);
        col_gen.write_frac(1, num_1, denoms[1]);
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
