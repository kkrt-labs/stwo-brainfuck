use crate::components::{InteractionClaim, MemoryClaim, TraceColumn, TraceError, TraceEval};
use brainfuck_vm::registers::Registers;
use num_traits::One;
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

/// Represents the Memory Table, which holds the required registers
/// for the Memory component.
///
/// The Memory Table is constructed by extracting the required fields
/// from the execution trace provided by the Brainfuck Virtual Machine,
/// then sorting by `mp` as a primary key and by `clk` as a secondary key.
///
/// To enforce the sorting on `clk`, all `clk` jumped are erased by adding dummy rows.
/// A dummy column flags them.
///
/// To ease constraints evaluation, each row of the Memory component
/// contains the current row and the next row in natural order.
/// This is done to avoid having to do costly bit-reversals, as constraints
/// are evaluated on the evaluation of the trace which is ordered in
/// a bit-reversed manner over the circle domain once the polynomials are interpolated.
///
/// The preliminary work to extract the fields from the execution trace,
/// the sorting and the padding is done through the [`MemoryIntermediateTable`] struct.
///
/// Once done, we can build the Memory table from it, by pairing the consecutive
/// [`MemoryTableEntry`] in [`MemoryTableRow`].
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct MemoryTable {
    /// A vector of [`MemoryTableRow`] representing the table rows.
    pub(crate) table: Vec<MemoryTableRow>,
}

impl MemoryTable {
    /// Creates a new, empty [`MemoryTable`].
    ///
    /// # Returns
    /// A new instance of [`MemoryTable`] with an empty table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a new row to the Memory Table.
    ///
    /// # Arguments
    /// * `row` - The [`MemoryTableRow`] to add to the table.
    ///
    /// This method pushes a new [`MemoryTableRow`] onto the `table` vector.
    fn add_row(&mut self, row: MemoryTableRow) {
        self.table.push(row);
    }

    /// Transforms the [`MemoryTable`] into [`super::super::TraceEval`], to be committed
    /// when generating a STARK proof.
    ///
    /// The [`MemoryTable`] is transformed from an array of consecutive rows (one
    /// element = one step of all registers) to an array of columns (one element = all steps of
    /// one register). It is then evaluated on the circle domain.
    ///
    /// # Arguments
    /// * memory - The [`MemoryTable`] containing the sorted and padded trace as an array of
    ///   consecutive rows.
    ///
    /// # Returns
    /// A tuple containing the evaluated trace and claim for STARK proof.
    ///
    /// # Errors
    /// Returns [`TraceError::EmptyTrace`] if the table is empty.
    pub fn trace_evaluation(&self) -> Result<(TraceEval, MemoryClaim), TraceError> {
        let n_rows = self.table.len() as u32;
        if n_rows == 0 {
            return Err(TraceError::EmptyTrace);
        }
        let log_n_rows = n_rows.ilog2();
        let log_size = log_n_rows + LOG_N_LANES;
        let mut trace = vec![BaseColumn::zeros(1 << log_size); MemoryColumn::count().0];

        for (vec_row, row) in self.table.iter().enumerate().take(1 << log_n_rows) {
            trace[MemoryColumn::Clk.index()].data[vec_row] = row.clk.into();
            trace[MemoryColumn::Mp.index()].data[vec_row] = row.mp.into();
            trace[MemoryColumn::Mv.index()].data[vec_row] = row.mv.into();
            trace[MemoryColumn::D.index()].data[vec_row] = row.d.into();
            trace[MemoryColumn::NextClk.index()].data[vec_row] = row.next_clk.into();
            trace[MemoryColumn::NextMp.index()].data[vec_row] = row.next_mp.into();
            trace[MemoryColumn::NextMv.index()].data[vec_row] = row.next_mv.into();
            trace[MemoryColumn::NextD.index()].data[vec_row] = row.next_d.into();
        }

        let domain = CanonicCoset::new(log_size).circle_domain();
        let trace = trace.into_iter().map(|col| CircleEvaluation::new(domain, col)).collect();

        Ok((trace, MemoryClaim::new(log_size)))
    }
}

impl From<&Vec<Registers>> for MemoryTable {
    fn from(registers: &Vec<Registers>) -> Self {
        MemoryIntermediateTable::from(registers).into()
    }
}

// Separated from `Vec<Registers> for MemoryTable` to facilitate tests.
// It is assumed that [`MemoryIntermediateTable`] is sorted and padded to the next power of two.
impl From<MemoryIntermediateTable> for MemoryTable {
    fn from(mut intermediate_table: MemoryIntermediateTable) -> Self {
        let mut memory_table = Self::new();

        if intermediate_table.table.is_empty() {
            return memory_table;
        }

        let last_entry = intermediate_table.table.last().unwrap();
        let next_dummy_entry = MemoryTableEntry::new_dummy(
            last_entry.clk + BaseField::one(),
            last_entry.mp,
            last_entry.mv,
        );

        intermediate_table.add_entry(next_dummy_entry);

        for window in intermediate_table.table.windows(2) {
            match window {
                [entry_1, entry_2] => {
                    let row = MemoryTableRow::new(entry_1, entry_2);
                    memory_table.add_row(row);
                }
                _ => panic!("Empty window"),
            }
        }
        memory_table
    }
}

/// Represents a single row of the [`MemoryTable`]
///
/// Two consecutive [`MemoryTableEntry`] flattened.
///
/// To avoid bit-reversals when evaluating transition constraints,
/// the two consecutive rows on which transition constraints are evaluated
/// are flattened into a single row.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct MemoryTableRow {
    /// Clock cycle counter: the current step.
    clk: BaseField,
    /// Memory pointer: points to a memory cell.
    mp: BaseField,
    /// Memory value: value of the cell pointer by `mp` - values in [0..2^31 - 1)
    mv: BaseField,
    /// Dummy: Flag whether the current entry is a dummy one or not
    pub(crate) d: BaseField,
    /// Next Clock cycle counter.
    next_clk: BaseField,
    /// Next Memory pointer.
    pub(crate) next_mp: BaseField,
    /// Next Memory value.
    pub(crate) next_mv: BaseField,
    /// Next Dummy.
    pub(crate) next_d: BaseField,
}

impl MemoryTableRow {
    /// Creates a row for the [`MemoryIntermediateTable`] which is considered 'real'.
    ///
    /// A 'real' row, is a row that is part of the execution trace from the Brainfuck program
    /// execution.
    pub const fn new(entry_1: &MemoryTableEntry, entry_2: &MemoryTableEntry) -> Self {
        Self {
            clk: entry_1.clk,
            mp: entry_1.mp,
            mv: entry_1.mv,
            d: entry_1.d,
            next_clk: entry_2.clk,
            next_mp: entry_2.mp,
            next_mv: entry_2.mv,
            next_d: entry_2.d,
        }
    }
}

/// An intermediate representation of the trace, between the execution trace and the trace for the
/// Memory component.
///
/// It allows extracting the required fields from the execution trace provided by the Brainfuck
/// Virtual Machine, then sorting by `mp` as a primary key and by `clk` as a secondary key.
///
/// To enforce the sorting on `clk`, all `clk` jumped are erased by adding dummy entries.
/// A dummy column flags these entries.
///
/// To be used by [`MemoryTable`].
#[derive(Debug, Default, PartialEq, Eq, Clone)]
struct MemoryIntermediateTable {
    /// A vector of [`MemoryTableEntry`] representing the table entries.
    table: Vec<MemoryTableEntry>,
}

impl MemoryIntermediateTable {
    /// Creates a new, empty [`MemoryIntermediateTable`].
    ///
    /// # Returns
    /// A new instance of [`MemoryIntermediateTable`] with an empty table.
    fn new() -> Self {
        Self::default()
    }

    /// Adds a new entry to the Memory Table.
    ///
    /// # Arguments
    /// * `entry` - The [`MemoryTableEntry`] to add to the table.
    ///
    /// This method pushes a new [`MemoryTableEntry`] onto the `table` vector.
    fn add_entry(&mut self, entry: MemoryTableEntry) {
        self.table.push(entry);
    }

    /// Adds multiple entries to the Memory Table.
    ///
    /// # Arguments
    /// * `entries` - A vector of [`MemoryTableEntry`] to add to the table.
    ///
    /// This method extends the `table` vector with the provided rows.
    fn add_entries(&mut self, entries: Vec<MemoryTableEntry>) {
        self.table.extend(entries);
    }

    /// Sorts in-place the existing [`MemoryTableEntry`] rows in the Memory Table by `mp`, then
    /// `clk`.
    ///
    /// Having the entries sorted is required to ensure a correct proof generation (such that the
    /// constraints can be verified).
    fn sort(&mut self) {
        self.table.sort_by_key(|x| (x.mp, x.clk));
    }

    /// Fills the jumps in `clk` with dummy entries.
    ///
    /// Required to ensure the correct sorting of the [`MemoryIntermediateTable`] in the
    /// constraints.
    ///
    /// Does nothing if the table is empty.
    fn complete_with_dummy_entries(&mut self) {
        let mut new_table = Vec::with_capacity(self.table.len());
        if let Some(mut prev_entry) = self.table.first() {
            for entry in &self.table {
                let next_clk = prev_entry.clk + BaseField::one();
                if entry.mp == prev_entry.mp && entry.clk > next_clk {
                    let mut clk = next_clk;
                    while clk < entry.clk {
                        new_table.push(MemoryTableEntry::new_dummy(
                            clk,
                            prev_entry.mp,
                            prev_entry.mv,
                        ));
                        clk += BaseField::one();
                    }
                }
                new_table.push(entry.clone());
                prev_entry = entry;
            }
            new_table.shrink_to_fit();
            self.table = new_table;
        }
    }

    /// Pads the memory table with dummy entries up to the next power of two length.
    ///
    /// Each dummy entry preserves the last memory pointer and value, while incrementing the clock.
    ///
    /// Does nothing if the table is empty.
    fn pad(&mut self) {
        if let Some(last_entry) = self.table.last().cloned() {
            let trace_len = self.table.len();
            let padding_offset = (trace_len.next_power_of_two() - trace_len) as u32;
            for i in 1..=padding_offset {
                self.add_entry(MemoryTableEntry::new_dummy(
                    last_entry.clk + BaseField::from(i),
                    last_entry.mp,
                    last_entry.mv,
                ));
            }
        }
    }
}

impl From<&Vec<Registers>> for MemoryIntermediateTable {
    fn from(registers: &Vec<Registers>) -> Self {
        let mut intermediate_table = Self::new();

        let memory_entries = registers.iter().map(|reg| (reg, false).into()).collect();
        intermediate_table.add_entries(memory_entries);

        intermediate_table.sort();
        intermediate_table.complete_with_dummy_entries();
        intermediate_table.pad();

        intermediate_table
    }
}

/// Represents a single entry of the [`MemoryIntermediateTable`].
///
/// Represents the registers used by the Memory Table of a single step from the execution trace.
///
/// The Memory Table Intermediate stores:
/// - The clock cycle counter (`clk`),
/// - The memory pointer (`mp`),
/// - The memory value (`mv`),
/// - The dummy column flag (`d`).
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct MemoryTableEntry {
    /// Clock cycle counter: the current step.
    clk: BaseField,
    /// Memory pointer: points to a memory cell.
    mp: BaseField,
    /// Memory value: value of the cell pointer by `mp` - values in [0..2^31 - 1)
    mv: BaseField,
    /// Dummy: Flag whether the entry is a dummy one or not
    d: BaseField,
}

impl MemoryTableEntry {
    /// Creates an entry for the [`MemoryIntermediateTable`] which is considered 'real'.
    ///
    /// A 'real' entry, is an entry that is part of the execution trace from the Brainfuck program
    /// execution.
    pub fn new(clk: BaseField, mp: BaseField, mv: BaseField) -> Self {
        Self { clk, mp, mv, ..Default::default() }
    }

    /// Creates an entry for the [`MemoryIntermediateTable`] which is considered 'dummy'.
    ///
    /// A 'dummy' entry, is an entry that is not part of the execution trace from the Brainfuck
    /// program execution.
    /// They are used for padding and filling the `clk` gaps after sorting by `mp`, to enforce the
    /// correct sorting.
    pub fn new_dummy(clk: BaseField, mp: BaseField, mv: BaseField) -> Self {
        Self { clk, mp, mv, d: BaseField::one() }
    }
}

impl From<(&Registers, bool)> for MemoryTableEntry {
    fn from((registers, is_dummy): (&Registers, bool)) -> Self {
        if is_dummy {
            Self::new_dummy(registers.clk, registers.mp, registers.mv)
        } else {
            Self::new(registers.clk, registers.mp, registers.mv)
        }
    }
}

/// Enum representing the column indices in the Memory trace
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryColumn {
    /// Index of the `clk` register column in the Memory trace.
    Clk,
    /// Index of the `mp` register column in the Memory trace.
    Mp,
    /// Index of the `mv` register column in the Memory trace.
    Mv,
    /// Index of the `d` register column in the Memory trace.
    D,
    /// Index of the `next_clk` register column in the Memory trace.
    NextClk,
    /// Index of the `next_mp` register column in the Memory trace.
    NextMp,
    /// Index of the `next_mv` register column in the Memory trace.
    NextMv,
    /// Index of the `next_d` register column in the Memory trace.
    NextD,
}

impl MemoryColumn {
    /// Returns the index of the column in the Memory table
    pub const fn index(self) -> usize {
        match self {
            Self::Clk => 0,
            Self::Mp => 1,
            Self::Mv => 2,
            Self::D => 3,
            Self::NextClk => 4,
            Self::NextMp => 5,
            Self::NextMv => 6,
            Self::NextD => 7,
        }
    }
}

impl TraceColumn for MemoryColumn {
    fn count() -> (usize, usize) {
        (8, 1)
    }
}

/// The number of random elements necessary for the Memory lookup argument.
const MEMORY_LOOKUP_ELEMENTS: usize = 3;

/// The interaction elements are drawn for the extension column of the Memory component.
///
/// The logUp protocol uses these elements to combine the values of the different
/// registers of the main trace to create a random linear combination
/// of them, and use it in the denominator of the fractions in the logUp protocol.
///
/// There are 3 lookup elements in the Memory component, as only the 'real' registers
/// are used: `clk`, `mp` and `mv`. `d` is used to eventually nullify the numerator.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MemoryElements(LookupElements<MEMORY_LOOKUP_ELEMENTS>);

impl MemoryElements {
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

impl<F: Clone, EF: RelationEFTraitBound<F>> Relation<F, EF> for MemoryElements {
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
        stringify!(MemoryElements)
    }

    /// Returns the number interaction elements.
    fn get_size(&self) -> usize {
        MEMORY_LOOKUP_ELEMENTS
    }
}

/// Creates the interaction trace from the main trace evaluation
/// and the interaction elements for the Memory component.
///
/// The Processor component uses the other components:
/// The Processor component multiplicities are then positive,
/// and the Memory component multiplicities are negative
/// in the logUp protocol.
///
/// Only the 'real' rows are impacting the logUp sum.
/// Dummy rows are padded rows and rows filling the `clk` gaps
/// which does not appear in the Processor main trace.
///
///
/// # Returns
/// - Interaction trace evaluation, to be committed.
/// - Interaction claim: the total sum from the logUp protocol,
/// to be mixed into the Fiat-Shamir [`Channel`].
#[allow(clippy::similar_names)]
pub fn interaction_trace_evaluation(
    main_trace_eval: &TraceEval,
    lookup_elements: &MemoryElements,
) -> Result<(TraceEval, InteractionClaim), TraceError> {
    if main_trace_eval.is_empty() {
        return Err(TraceError::EmptyTrace)
    }

    let log_size = main_trace_eval[0].domain.log_size();

    let mut logup_gen = LogupTraceGenerator::new(log_size);
    let mut col_gen = logup_gen.new_col();

    let clk_col = &main_trace_eval[MemoryColumn::Clk.index()].data;
    let mp_col = &main_trace_eval[MemoryColumn::Mp.index()].data;
    let mv_column = &main_trace_eval[MemoryColumn::Mv.index()].data;
    let d_col = &main_trace_eval[MemoryColumn::D.index()].data;
    let next_clk_col = &main_trace_eval[MemoryColumn::NextClk.index()].data;
    let next_mp_col = &main_trace_eval[MemoryColumn::NextMp.index()].data;
    let next_mv_col = &main_trace_eval[MemoryColumn::NextMv.index()].data;
    let next_d_col = &main_trace_eval[MemoryColumn::NextD.index()].data;
    for vec_row in 0..1 << (log_size - LOG_N_LANES) {
        let clk = clk_col[vec_row];
        let mp = mp_col[vec_row];
        let mv = mv_column[vec_row];
        let next_clk = next_clk_col[vec_row];
        let next_mp = next_mp_col[vec_row];
        let next_mv = next_mv_col[vec_row];
        // Set the fraction numerator to 0 if it is a dummy row (d = 1), otherwise set it to -1.
        let num_1 = PackedSecureField::from(d_col[vec_row]) - PackedSecureField::one();
        let num_2 = PackedSecureField::from(next_d_col[vec_row]) - PackedSecureField::one();
        // Only the common registers with the processor table are part of the extension column.
        let denom_1: PackedSecureField = lookup_elements.combine(&[clk, mp, mv]);
        let denom_2: PackedSecureField = lookup_elements.combine(&[next_clk, next_mp, next_mv]);
        col_gen.write_frac(vec_row, num_1 * denom_2 + num_2 * denom_1, denom_1 * denom_2);
    }

    col_gen.finalize_col();

    let (trace, claimed_sum) = logup_gen.finalize_last();

    Ok((trace, InteractionClaim { claimed_sum }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Zero;

    #[test]
    fn test_memory_entry_new() {
        let entry =
            MemoryTableEntry::new(BaseField::zero(), BaseField::from(43), BaseField::from(91));
        let expected_entry = MemoryTableEntry {
            clk: BaseField::zero(),
            mp: BaseField::from(43),
            mv: BaseField::from(91),
            d: BaseField::zero(),
        };
        assert_eq!(entry, expected_entry);
    }

    #[test]
    fn test_memory_entry_new_dummy() {
        let entry = MemoryTableEntry::new_dummy(
            BaseField::zero(),
            BaseField::from(43),
            BaseField::from(91),
        );
        let expected_entry = MemoryTableEntry {
            clk: BaseField::zero(),
            mp: BaseField::from(43),
            mv: BaseField::from(91),
            d: BaseField::one(),
        };
        assert_eq!(entry, expected_entry);
    }

    #[test]
    fn test_memory_row_new() {
        let entry_1 =
            MemoryTableEntry::new(BaseField::zero(), BaseField::from(43), BaseField::from(91));
        let entry_2 =
            MemoryTableEntry::new_dummy(BaseField::one(), BaseField::from(3), BaseField::from(9));

        let row = MemoryTableRow::new(&entry_1, &entry_2);

        let expected_row = MemoryTableRow {
            clk: BaseField::zero(),
            mp: BaseField::from(43),
            mv: BaseField::from(91),
            d: BaseField::zero(),
            next_clk: BaseField::one(),
            next_mp: BaseField::from(3),
            next_mv: BaseField::from(9),
            next_d: BaseField::one(),
        };
        assert_eq!(row, expected_row);
    }

    #[test]
    fn test_memory_intermediate_table_new() {
        let intermediate_table = MemoryIntermediateTable::new();
        assert!(
            intermediate_table.table.is_empty(),
            "Memory intermediate table should be empty upon initialization."
        );
    }

    #[test]
    fn test_memory_table_new() {
        let memory_table = MemoryTable::new();
        assert!(memory_table.table.is_empty(), "Memory table should be empty upon initialization.");
    }

    #[test]
    fn test_add_entry() {
        let mut intermediate_table = MemoryIntermediateTable::new();
        // Create a row to add to the table
        let row =
            MemoryTableEntry::new(BaseField::zero(), BaseField::from(43), BaseField::from(91));
        // Add the row to the table
        intermediate_table.add_entry(row.clone());
        // Check that the table contains the added row
        assert_eq!(intermediate_table.table, vec![row], "Added row should match the expected row.");
    }

    #[test]
    fn test_add_dummy_entry() {
        let mut intermediate_table = MemoryIntermediateTable::new();
        // Create a row to add to the table
        let entry = MemoryTableEntry::new_dummy(
            BaseField::zero(),
            BaseField::from(43),
            BaseField::from(91),
        );
        // Add the row to the table
        intermediate_table.add_entry(entry.clone());
        // Check that the table contains the added row
        assert_eq!(
            intermediate_table.table,
            vec![entry],
            "Added row should match the expected row."
        );
    }

    #[test]
    fn test_add_multiple_entries() {
        let mut intermediate_table = MemoryIntermediateTable::new();
        // Create a vector of entries to add to the table
        let entries = vec![
            MemoryTableEntry::new(BaseField::zero(), BaseField::from(43), BaseField::from(91)),
            MemoryTableEntry::new(BaseField::one(), BaseField::from(91), BaseField::from(9)),
            MemoryTableEntry::new(BaseField::from(43), BaseField::from(62), BaseField::from(43)),
        ];
        // Add the entries to the table
        intermediate_table.add_entries(entries.clone());
        // Check that the table contains the added entries
        assert_eq!(intermediate_table, MemoryIntermediateTable { table: entries });
    }

    #[test]
    fn test_sort() {
        let mut intermediate_table = MemoryIntermediateTable::new();
        let entry_1 =
            MemoryTableEntry::new(BaseField::zero(), BaseField::zero(), BaseField::zero());
        let entry_2 = MemoryTableEntry::new(BaseField::one(), BaseField::zero(), BaseField::zero());
        let entry_3 = MemoryTableEntry::new(BaseField::zero(), BaseField::one(), BaseField::zero());
        intermediate_table.add_entries(vec![entry_3.clone(), entry_1.clone(), entry_2.clone()]);

        let mut expected_memory_table = MemoryIntermediateTable::new();
        expected_memory_table.add_entries(vec![entry_1, entry_2, entry_3]);

        intermediate_table.sort();

        assert_eq!(intermediate_table, expected_memory_table);
    }

    #[test]
    fn test_empty_complete_wih_dummy_entries() {
        let mut intermediate_table = MemoryIntermediateTable::new();
        intermediate_table.complete_with_dummy_entries();

        assert_eq!(intermediate_table, MemoryIntermediateTable::new());
    }

    #[test]
    fn test_complete_wih_dummy_entries() {
        let mut intermediate_table = MemoryIntermediateTable::new();
        let entry_1 =
            MemoryTableEntry::new(BaseField::zero(), BaseField::zero(), BaseField::zero());
        let entry_2 = MemoryTableEntry::new(BaseField::zero(), BaseField::one(), BaseField::zero());
        let entry_3 = MemoryTableEntry::new(BaseField::from(5), BaseField::one(), BaseField::one());
        intermediate_table.add_entries(vec![entry_3.clone(), entry_1.clone(), entry_2.clone()]);
        intermediate_table.sort();
        intermediate_table.complete_with_dummy_entries();

        let mut expected_memory_table = MemoryIntermediateTable::new();
        expected_memory_table.add_entries(vec![
            entry_1,
            entry_2,
            MemoryTableEntry::new_dummy(BaseField::one(), BaseField::one(), BaseField::zero()),
            MemoryTableEntry::new_dummy(BaseField::from(2), BaseField::one(), BaseField::zero()),
            MemoryTableEntry::new_dummy(BaseField::from(3), BaseField::one(), BaseField::zero()),
            MemoryTableEntry::new_dummy(BaseField::from(4), BaseField::one(), BaseField::zero()),
            entry_3,
        ]);

        assert_eq!(intermediate_table, expected_memory_table);
    }

    #[test]
    fn test_pad_empty() {
        let mut intermediate_table = MemoryIntermediateTable::new();
        intermediate_table.pad();
        assert_eq!(intermediate_table, MemoryIntermediateTable::new());
    }

    #[test]
    fn test_pad() {
        let mut intermediate_table = MemoryIntermediateTable::new();
        let entry_1 =
            MemoryTableEntry::new(BaseField::zero(), BaseField::zero(), BaseField::zero());
        let entry_2 = MemoryTableEntry::new(BaseField::one(), BaseField::one(), BaseField::zero());
        let entry_3 = MemoryTableEntry::new(BaseField::from(2), BaseField::one(), BaseField::one());
        intermediate_table.add_entries(vec![entry_1.clone(), entry_2.clone(), entry_3.clone()]);

        intermediate_table.pad();

        let dummy_entry =
            MemoryTableEntry::new_dummy(BaseField::from(3), BaseField::one(), BaseField::one());
        let mut expected_memory_table = MemoryIntermediateTable::new();
        expected_memory_table.add_entries(vec![entry_1, entry_2, entry_3, dummy_entry]);

        assert_eq!(intermediate_table, expected_memory_table);
    }

    #[test]
    fn test_memory_intermediate_table_from_registers() {
        let reg_1 = Registers::default();
        let reg_2 = Registers { clk: BaseField::one(), mp: BaseField::one(), ..Default::default() };
        let reg_3 = Registers {
            clk: BaseField::from(5),
            mp: BaseField::one(),
            mv: BaseField::one(),
            ..Default::default()
        };
        let registers = vec![reg_3, reg_1, reg_2];

        let entry_1 = MemoryTableEntry::default();
        let entry_2 = MemoryTableEntry::new(BaseField::one(), BaseField::one(), BaseField::zero());
        let entry_3 = MemoryTableEntry::new(BaseField::from(5), BaseField::one(), BaseField::one());

        let dummy_entry_1 =
            MemoryTableEntry::new_dummy(BaseField::from(6), BaseField::one(), BaseField::one());
        let dummy_entry_2 =
            MemoryTableEntry::new_dummy(BaseField::from(7), BaseField::one(), BaseField::one());
        let mut expected_memory_table = MemoryIntermediateTable::new();
        expected_memory_table.add_entries(vec![
            entry_1,
            entry_2,
            MemoryTableEntry::new_dummy(BaseField::from(2), BaseField::one(), BaseField::zero()),
            MemoryTableEntry::new_dummy(BaseField::from(3), BaseField::one(), BaseField::zero()),
            MemoryTableEntry::new_dummy(BaseField::from(4), BaseField::one(), BaseField::zero()),
            entry_3,
            dummy_entry_1,
            dummy_entry_2,
        ]);

        assert_eq!(MemoryIntermediateTable::from(&registers), expected_memory_table);
    }

    #[test]
    fn test_empty_trace_evaluation() {
        let registers = vec![];
        let trace_eval = MemoryTable::from(&registers).trace_evaluation();

        assert!(matches!(trace_eval, Err(TraceError::EmptyTrace)));
    }

    #[test]
    fn test_trace_evaluation() {
        let mut intermediate_table = MemoryIntermediateTable::new();
        let rows = vec![
            MemoryTableEntry::new(BaseField::zero(), BaseField::from(43), BaseField::from(91)),
            MemoryTableEntry::new(BaseField::one(), BaseField::from(91), BaseField::from(9)),
        ];
        intermediate_table.add_entries(rows);

        let (trace, claim) = MemoryTable::from(intermediate_table).trace_evaluation().unwrap();

        let expected_log_n_rows: u32 = 1;
        let expected_log_size = expected_log_n_rows + LOG_N_LANES;
        let expected_size = 1 << expected_log_size;
        let mut clk_column = BaseColumn::zeros(expected_size);
        let mut mp_column = BaseColumn::zeros(expected_size);
        let mut mv_col = BaseColumn::zeros(expected_size);
        let mut d_column = BaseColumn::zeros(expected_size);

        clk_column.data[0] = BaseField::zero().into();
        clk_column.data[1] = BaseField::one().into();

        mp_column.data[0] = BaseField::from(43).into();
        mp_column.data[1] = BaseField::from(91).into();

        mv_col.data[0] = BaseField::from(91).into();
        mv_col.data[1] = BaseField::from(9).into();

        d_column.data[0] = BaseField::zero().into();
        d_column.data[1] = BaseField::zero().into();

        let domain = CanonicCoset::new(expected_log_size).circle_domain();
        let expected_trace: TraceEval = vec![clk_column, mp_column, mv_col, d_column]
            .into_iter()
            .map(|col| CircleEvaluation::new(domain, col))
            .collect();
        let expected_claim = MemoryClaim::new(expected_log_size);

        assert_eq!(claim, expected_claim);
        for col_index in 0..expected_trace.len() {
            assert_eq!(trace[col_index].domain, expected_trace[col_index].domain);
            assert_eq!(trace[col_index].to_cpu().values, expected_trace[col_index].to_cpu().values);
        }
    }

    #[test]
    fn test_empty_interaction_trace_evaluation() {
        let empty_eval = vec![];
        let lookup_elements = MemoryElements::dummy();
        let interaction_trace_eval = interaction_trace_evaluation(&empty_eval, &lookup_elements);

        assert!(matches!(interaction_trace_eval, Err(TraceError::EmptyTrace)));
    }

    #[test]
    fn test_interaction_trace_evaluation() {
        let mut intermediate_table = MemoryIntermediateTable::new();
        // Trace entries are:
        // - Real entry
        // - Dummy entry (filling the `clk` value)
        // - Real entry
        // - Dummy entry (padding to the power of 2)
        let entries = vec![
            MemoryTableEntry::new(BaseField::zero(), BaseField::zero(), BaseField::zero()),
            MemoryTableEntry::new_dummy(BaseField::one(), BaseField::one(), BaseField::zero()),
            MemoryTableEntry::new(BaseField::from(2), BaseField::one(), BaseField::zero()),
            MemoryTableEntry::new_dummy(BaseField::from(3), BaseField::one(), BaseField::zero()),
        ];
        intermediate_table.add_entries(entries);

        let memory_table = MemoryTable::from(intermediate_table);

        let (trace_eval, claim) = memory_table.trace_evaluation().unwrap();

        let lookup_elements = MemoryElements::dummy();

        let (interaction_trace_eval, interaction_claim) =
            interaction_trace_evaluation(&trace_eval, &lookup_elements).unwrap();

        let log_size = trace_eval[0].domain.log_size();
        let mut logup_gen = LogupTraceGenerator::new(log_size);
        let mut col_gen = logup_gen.new_col();

        let mut denoms = [PackedSecureField::zero(); 4];
        let clk_col = &trace_eval[MemoryColumn::Clk.index()].data;
        let mp_col = &trace_eval[MemoryColumn::Mp.index()].data;
        let mv_column = &trace_eval[MemoryColumn::Mv.index()].data;
        // Construct the denominator for each row of the logUp column, from the main trace
        // evaluation.
        for vec_row in 0..1 << (log_size - LOG_N_LANES) {
            let clk = clk_col[vec_row];
            let mp = mp_col[vec_row];
            let mv = mv_column[vec_row];
            let denom: PackedSecureField = lookup_elements.combine(&[clk, mp, mv]);
            denoms[vec_row] = denom;
        }

        let num_0 = -PackedSecureField::one();
        let num_1 = PackedSecureField::zero();
        let num_2 = -PackedSecureField::one();
        let num_3 = PackedSecureField::zero();

        col_gen.write_frac(0, num_0 * denoms[1] + num_1 * denoms[0], denoms[0] * denoms[1]);
        col_gen.write_frac(1, num_1 * denoms[2] + num_2 * denoms[1], denoms[1] * denoms[2]);
        col_gen.write_frac(2, num_2 * denoms[3] + num_3 * denoms[2], denoms[2] * denoms[3]);
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

    // This test verifies that the dummy entries have no impact
    // on the total sum of the logUp protocol in the Memory component.
    // Indeed, the total sum computed by the Processor component won't
    // have the exact same dummy entries: the Memory component adds extra
    // dummy entries to fill the `clk` jumps and enforce the sorting.
    #[test]
    fn test_interaction_trace_evaluation_dummy_entries_effect() {
        let mut intermediate_table = MemoryIntermediateTable::new();
        let mut real_intermediate_table = MemoryIntermediateTable::new();

        // Trace entries are:
        // - Real entry
        // - Dummy entry (filling the `clk` value)
        // - Real entry
        // - Dummy entry (padding to power of 2)
        let entries = vec![
            MemoryTableEntry::new(BaseField::zero(), BaseField::from(43), BaseField::from(91)),
            MemoryTableEntry::new_dummy(BaseField::one(), BaseField::from(43), BaseField::from(91)),
            MemoryTableEntry::new(BaseField::from(2), BaseField::from(91), BaseField::from(9)),
            MemoryTableEntry::new_dummy(
                BaseField::from(2),
                BaseField::from(91),
                BaseField::from(9),
            ),
        ];
        intermediate_table.add_entries(entries);

        // Trace entries are:
        // - Real entry
        // - Real entry
        let real_entries = vec![
            MemoryTableEntry::new(BaseField::zero(), BaseField::from(43), BaseField::from(91)),
            MemoryTableEntry::new(BaseField::from(2), BaseField::from(91), BaseField::from(9)),
        ];
        real_intermediate_table.add_entries(real_entries);

        let (trace_eval, _) = MemoryTable::from(intermediate_table).trace_evaluation().unwrap();
        let (new_trace_eval, _) =
            MemoryTable::from(real_intermediate_table).trace_evaluation().unwrap();

        let lookup_elements = MemoryElements::dummy();

        let (_, interaction_claim) =
            interaction_trace_evaluation(&trace_eval, &lookup_elements).unwrap();

        let (_, new_interaction_claim) =
            interaction_trace_evaluation(&new_trace_eval, &lookup_elements).unwrap();

        assert_eq!(interaction_claim, new_interaction_claim,);
    }
}
