use super::component::Claim;
use crate::components::{TraceError, TraceEval};
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

/// Represents a single row in the Memory Table.
///
/// The Memory Table stores:
/// - The clock cycle counter (`clk`),
/// - The memory pointer (`mp`),
/// - The memory value (`mv`),
/// - The dummy column flag (`d`).
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct MemoryTableRow {
    /// Clock cycle counter: the current step.
    clk: BaseField,
    /// Memory pointer: points to a memory cell.
    mp: BaseField,
    /// Memory value: value of the cell pointer by `mp` - values in [0..2^31 - 1)
    mv: BaseField,
    /// Dummy: Flag whether the row is a dummy one or not
    d: BaseField,
}

impl MemoryTableRow {
    /// Creates a row for the [`MemoryTable`] which is considered 'real'.
    ///
    /// A 'real' row, is a row that is part of the execution trace from the Brainfuck program
    /// execution.
    pub fn new(clk: BaseField, mp: BaseField, mv: BaseField) -> Self {
        Self { clk, mp, mv, ..Default::default() }
    }

    /// Creates a row for the [`MemoryTable`] which is considered 'dummy'.
    ///
    /// A 'dummy' row, is a row that is not part of the execution trace from the Brainfuck program
    /// execution.
    /// They are used for padding and filling the `clk` gaps after sorting by `mp`, to enforce the
    /// correct sorting.
    pub fn new_dummy(clk: BaseField, mp: BaseField, mv: BaseField) -> Self {
        Self { clk, mp, mv, d: BaseField::one() }
    }

    /// Getter for the `clk` field.
    pub const fn clk(&self) -> BaseField {
        self.clk
    }

    /// Getter for the `mp` field.
    pub const fn mp(&self) -> BaseField {
        self.mp
    }

    /// Getter for the `mv` field.
    pub const fn mv(&self) -> BaseField {
        self.mv
    }

    /// Getter for the `d` field.
    pub const fn d(&self) -> BaseField {
        self.d
    }
}

impl From<(&Registers, bool)> for MemoryTableRow {
    fn from((registers, is_dummy): (&Registers, bool)) -> Self {
        if is_dummy {
            Self::new_dummy(registers.clk, registers.mp, registers.mv)
        } else {
            Self::new(registers.clk, registers.mp, registers.mv)
        }
    }
}

/// Represents the Memory Table, which holds the required registers
/// for the Memory component.
///
/// The Memory Table is constructed by extracting the required fields
/// from the execution trace provided by the Brainfuck Virtual Machine,
/// then sorting by `mp` as a primary key and by `clk` as a secondary key.
///
/// To enforce the sorting on clk, all clk jumped are erased by adding dummy rows.
/// A dummy column flags them.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct MemoryTable {
    /// A vector of [`MemoryTableRow`] representing the table rows.
    table: Vec<MemoryTableRow>,
}

impl MemoryTable {
    /// Creates a new, empty [`MemoryTable`].
    ///
    /// # Returns
    /// A new instance of [`MemoryTable`] with an empty table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Getter for the `table` field.
    pub const fn table(&self) -> &Vec<MemoryTableRow> {
        &self.table
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

    /// Adds multiple rows to the Memory Table.
    ///
    /// # Arguments
    /// * `rows` - A vector of [`MemoryTableRow`] to add to the table.
    ///
    /// This method extends the `table` vector with the provided rows.
    fn add_rows(&mut self, rows: Vec<MemoryTableRow>) {
        self.table.extend(rows);
    }

    /// Sorts in-place the existing [`MemoryTableRow`] rows in the Memory Table by `mp`, then `clk`.
    ///
    /// Having the rows sorted is required to ensure a correct proof generation (such that the
    /// constraints can be verified).
    fn sort(&mut self) {
        self.table.sort_by_key(|x| (x.mp, x.clk));
    }

    /// Fills the jumps in `clk` with dummy rows.
    ///
    /// Required to ensure the correct sorting of the [`MemoryTable`] in the constraints.
    ///
    /// Does nothing if the table is empty.
    fn complete_with_dummy_rows(&mut self) {
        let mut new_table = Vec::with_capacity(self.table.len());
        if let Some(mut prev_row) = self.table.first() {
            for row in &self.table {
                let next_clk = prev_row.clk + BaseField::one();
                if row.mp == prev_row.mp && row.clk > next_clk {
                    let mut clk = next_clk;
                    while clk < row.clk {
                        new_table.push(MemoryTableRow::new_dummy(clk, prev_row.mp, prev_row.mv));
                        clk += BaseField::one();
                    }
                }
                new_table.push(row.clone());
                prev_row = row;
            }
            new_table.shrink_to_fit();
            self.table = new_table;
        }
    }

    /// Pads the memory table with dummy rows up to the next power of two length.
    ///
    /// Each dummy row preserves the last memory pointer and value while incrementing the clock.
    ///
    /// Does nothing if the table is empty.
    fn pad(&mut self) {
        if let Some(last_row) = self.table.last().cloned() {
            let trace_len = self.table.len();
            let padding_offset = (trace_len.next_power_of_two() - trace_len) as u32;
            for i in 1..=padding_offset {
                self.add_row(MemoryTableRow::new_dummy(
                    last_row.clk + BaseField::from(i),
                    last_row.mp,
                    last_row.mv,
                ));
            }
        }
    }

    /// Transforms the [`MemoryTable`] into [`super::super::TraceEval`], to be commited when
    /// generating a STARK proof.
    ///
    /// The [`MemoryTable`] is transformed from an array of rows (one element = one step of all
    /// registers) to an array of columns (one element = all steps of one register).
    /// It is then evaluated on the circle domain.
    ///
    /// # Arguments
    /// * memory - The [`MemoryTable`] containing the sorted and padded trace as an array of rows.
    pub fn trace_evaluation(&self) -> Result<(TraceEval, Claim), TraceError> {
        let n_rows = self.table.len() as u32;
        if n_rows == 0 {
            return Err(TraceError::EmptyTrace);
        }
        let log_n_rows = n_rows.ilog2();
        // TODO: Confirm that the log_size used for evaluation on Circle domain is the log_size of
        // the table plus the SIMD lanes
        let log_size = log_n_rows + LOG_N_LANES;
        let mut trace: Vec<BaseColumn> =
            (0..MemoryColumn::count()).map(|_| BaseColumn::zeros(1 << log_size)).collect();

        for (vec_row, row) in self.table.iter().enumerate().take(1 << log_n_rows) {
            trace[MemoryColumn::Clk.index()].data[vec_row] = row.clk().into();
            trace[MemoryColumn::Mp.index()].data[vec_row] = row.mp().into();
            trace[MemoryColumn::Mv.index()].data[vec_row] = row.mv().into();
            trace[MemoryColumn::D.index()].data[vec_row] = row.d().into();
        }

        let domain = CanonicCoset::new(log_size).circle_domain();
        let trace = trace.into_iter().map(|col| CircleEvaluation::new(domain, col)).collect();

        // TODO: Confirm that the log_size in `Claim` is `log_size`, including the SIMD lanes
        Ok((trace, Claim { log_size }))
    }
}

impl From<Vec<Registers>> for MemoryTable {
    fn from(registers: Vec<Registers>) -> Self {
        let mut memory_table = Self::new();

        let memory_rows = registers.iter().map(|reg| (reg, false).into()).collect();
        memory_table.add_rows(memory_rows);

        memory_table.sort();
        memory_table.complete_with_dummy_rows();
        memory_table.pad();

        memory_table
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
}

impl MemoryColumn {
    /// Returns the index of the column in the Memory table
    pub const fn index(self) -> usize {
        match self {
            MemoryColumn::Clk => 0,
            MemoryColumn::Mp => 1,
            MemoryColumn::Mv => 2,
            MemoryColumn::D => 3,
        }
    }

    /// Returns the total number of columns in the Memory table
    pub const fn count() -> usize {
        4
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Zero;

    #[test]
    fn test_memory_row_new() {
        let row = MemoryTableRow::new(BaseField::zero(), BaseField::from(43), BaseField::from(91));
        let expected_row = MemoryTableRow {
            clk: BaseField::zero(),
            mp: BaseField::from(43),
            mv: BaseField::from(91),
            d: BaseField::zero(),
        };
        assert_eq!(row, expected_row);
    }

    #[test]
    fn test_memory_row_new_dummy() {
        let row =
            MemoryTableRow::new_dummy(BaseField::zero(), BaseField::from(43), BaseField::from(91));
        let expected_row = MemoryTableRow {
            clk: BaseField::zero(),
            mp: BaseField::from(43),
            mv: BaseField::from(91),
            d: BaseField::one(),
        };
        assert_eq!(row, expected_row);
    }

    #[test]
    fn test_memory_table_new() {
        let memory_table = MemoryTable::new();
        assert!(memory_table.table.is_empty(), "Memory table should be empty upon initialization.");
    }

    #[test]
    fn test_add_row() {
        let mut memory_table = MemoryTable::new();
        // Create a row to add to the table
        let row = MemoryTableRow::new(BaseField::zero(), BaseField::from(43), BaseField::from(91));
        // Add the row to the table
        memory_table.add_row(row.clone());
        // Check that the table contains the added row
        assert_eq!(memory_table.table, vec![row], "Added row should match the expected row.");
    }

    #[test]
    fn test_add_dummy_row() {
        let mut memory_table = MemoryTable::new();
        // Create a row to add to the table
        let row =
            MemoryTableRow::new_dummy(BaseField::zero(), BaseField::from(43), BaseField::from(91));
        // Add the row to the table
        memory_table.add_row(row.clone());
        // Check that the table contains the added row
        assert_eq!(memory_table.table, vec![row], "Added row should match the expected row.");
    }

    #[test]
    fn test_add_multiple_rows() {
        let mut memory_table = MemoryTable::new();
        // Create a vector of rows to add to the table
        let rows = vec![
            MemoryTableRow::new(BaseField::zero(), BaseField::from(43), BaseField::from(91)),
            MemoryTableRow::new(BaseField::one(), BaseField::from(91), BaseField::from(9)),
            MemoryTableRow::new(BaseField::from(43), BaseField::from(62), BaseField::from(43)),
        ];
        // Add the rows to the table
        memory_table.add_rows(rows.clone());
        // Check that the table contains the added rows
        assert_eq!(memory_table, MemoryTable { table: rows });
    }

    #[test]
    fn test_sort() {
        let mut memory_table = MemoryTable::new();
        let row1 = MemoryTableRow::new(BaseField::zero(), BaseField::zero(), BaseField::zero());
        let row2 = MemoryTableRow::new(BaseField::one(), BaseField::zero(), BaseField::zero());
        let row3 = MemoryTableRow::new(BaseField::zero(), BaseField::one(), BaseField::zero());
        memory_table.add_rows(vec![row3.clone(), row1.clone(), row2.clone()]);

        let mut expected_memory_table = MemoryTable::new();
        expected_memory_table.add_rows(vec![row1, row2, row3]);

        memory_table.sort();

        assert_eq!(memory_table, expected_memory_table);
    }

    #[test]
    fn test_empty_complete_wih_dummy_rows() {
        let mut memory_table = MemoryTable::new();
        memory_table.complete_with_dummy_rows();

        assert_eq!(memory_table, MemoryTable::new());
    }

    #[test]
    fn test_complete_wih_dummy_rows() {
        let mut memory_table = MemoryTable::new();
        let row1 = MemoryTableRow::new(BaseField::zero(), BaseField::zero(), BaseField::zero());
        let row2 = MemoryTableRow::new(BaseField::zero(), BaseField::one(), BaseField::zero());
        let row3 = MemoryTableRow::new(BaseField::from(5), BaseField::one(), BaseField::one());
        memory_table.add_rows(vec![row3.clone(), row1.clone(), row2.clone()]);
        memory_table.sort();
        memory_table.complete_with_dummy_rows();

        let mut expected_memory_table = MemoryTable::new();
        expected_memory_table.add_rows(vec![
            row1,
            row2,
            MemoryTableRow::new_dummy(BaseField::one(), BaseField::one(), BaseField::zero()),
            MemoryTableRow::new_dummy(BaseField::from(2), BaseField::one(), BaseField::zero()),
            MemoryTableRow::new_dummy(BaseField::from(3), BaseField::one(), BaseField::zero()),
            MemoryTableRow::new_dummy(BaseField::from(4), BaseField::one(), BaseField::zero()),
            row3,
        ]);

        assert_eq!(memory_table, expected_memory_table);
    }

    #[test]
    fn test_pad_empty() {
        let mut memory_table = MemoryTable::new();
        memory_table.pad();
        assert_eq!(memory_table, MemoryTable::new());
    }

    #[test]
    fn test_pad() {
        let mut memory_table = MemoryTable::new();
        let row1 = MemoryTableRow::new(BaseField::zero(), BaseField::zero(), BaseField::zero());
        let row2 = MemoryTableRow::new(BaseField::one(), BaseField::one(), BaseField::zero());
        let row3 = MemoryTableRow::new(BaseField::from(2), BaseField::one(), BaseField::one());
        memory_table.add_rows(vec![row1.clone(), row2.clone(), row3.clone()]);

        memory_table.pad();

        let dummy_row =
            MemoryTableRow::new_dummy(BaseField::from(3), BaseField::one(), BaseField::one());
        let mut expected_memory_table = MemoryTable::new();
        expected_memory_table.add_rows(vec![row1, row2, row3, dummy_row]);

        assert_eq!(memory_table, expected_memory_table);
    }

    #[test]
    fn test_from_registers() {
        let reg1 = Registers::default();
        let reg2 = Registers { clk: BaseField::one(), mp: BaseField::one(), ..Default::default() };
        let reg3 = Registers {
            clk: BaseField::from(5),
            mp: BaseField::one(),
            mv: BaseField::one(),
            ..Default::default()
        };
        let registers: Vec<Registers> = vec![reg3, reg1, reg2];

        let row1 = MemoryTableRow::default();
        let row2 = MemoryTableRow::new(BaseField::one(), BaseField::one(), BaseField::zero());
        let row3 = MemoryTableRow::new(BaseField::from(5), BaseField::one(), BaseField::one());

        let dummy_row1 =
            MemoryTableRow::new_dummy(BaseField::from(6), BaseField::one(), BaseField::one());
        let dummy_row2 =
            MemoryTableRow::new_dummy(BaseField::from(7), BaseField::one(), BaseField::one());
        let mut expected_memory_table = MemoryTable::new();
        expected_memory_table.add_rows(vec![
            row1,
            row2,
            MemoryTableRow::new_dummy(BaseField::from(2), BaseField::one(), BaseField::zero()),
            MemoryTableRow::new_dummy(BaseField::from(3), BaseField::one(), BaseField::zero()),
            MemoryTableRow::new_dummy(BaseField::from(4), BaseField::one(), BaseField::zero()),
            row3,
            dummy_row1,
            dummy_row2,
        ]);

        assert_eq!(MemoryTable::from(registers), expected_memory_table);
    }

    #[test]
    fn test_write_trace() {
        let mut memory_table = MemoryTable::new();
        let rows = vec![
            MemoryTableRow::new(BaseField::zero(), BaseField::from(43), BaseField::from(91)),
            MemoryTableRow::new(BaseField::one(), BaseField::from(91), BaseField::from(9)),
        ];
        memory_table.add_rows(rows);

        let (trace, claim) = memory_table.trace_evaluation().unwrap();

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
        let expected_claim = Claim { log_size: expected_log_size };

        assert_eq!(claim, expected_claim);
        for col_index in 0..expected_trace.len() {
            assert_eq!(trace[col_index].domain, expected_trace[col_index].domain);
            assert_eq!(trace[col_index].to_cpu().values, expected_trace[col_index].to_cpu().values);
        }
    }
    #[test]
    fn test_write_empty_trace() {
        let memory_table = MemoryTable::new();
        let run = memory_table.trace_evaluation();

        assert!(matches!(run, Err(TraceError::EmptyTrace)));
    }
}
