use brainfuck_vm::registers::Registers;
use num_traits::{One, Zero};
use stwo_prover::core::fields::m31::BaseField;

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
    pub clk: BaseField,
    /// Memory pointer: points to a memory cell.
    pub mp: BaseField,
    /// Memory value: value of the cell pointer by `mp` - values in [0..2^31 - 1)
    pub mv: BaseField,
    /// Dummy: Flag whether the row is a dummy one or not
    d: BaseField,
}

impl MemoryTableRow {
    pub fn new(clk: BaseField, mp: BaseField, mv: BaseField) -> Self {
        Self { clk, mp, mv, ..Default::default() }
    }

    pub fn new_dummy(clk: BaseField, mp: BaseField, mv: BaseField) -> Self {
        Self { clk, mp, mv, d: BaseField::one() }
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
    pub table: Vec<MemoryTableRow>,
}

impl MemoryTable {
    /// Creates a new, empty [`MemoryTable`].
    ///
    /// # Returns
    /// A new instance of [`MemoryTable`] with an empty table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a new row to the Memory Table from the provided registers.
    ///
    /// # Arguments
    /// * `clk` - The clock cycle counter for the new row.
    /// * `mp` - The memory pointer for the new row.
    /// * `mv` - The memory value for the new row.
    /// * `is_dummy` - Flag whether the new row is dummy.
    ///
    /// This method pushes a new [`MemoryTableRow`] onto the `table` vector.
    pub fn add_row_from_registers(
        &mut self,
        clk: BaseField,
        mp: BaseField,
        mv: BaseField,
        is_dummy: bool,
    ) {
        let d = if is_dummy { BaseField::one() } else { BaseField::zero() };
        self.table.push(MemoryTableRow { clk, mp, mv, d });
    }

    /// Adds a new row to the Memory Table.
    ///
    /// # Arguments
    /// * `row` - The [`MemoryTableRow`] to add to the table.
    ///
    /// This method pushes a new [`MemoryTableRow`] onto the `table` vector.
    pub fn add_row(&mut self, row: MemoryTableRow) {
        self.table.push(row);
    }

    /// Adds multiple rows to the Memory Table.
    ///
    /// # Arguments
    /// * `rows` - A vector of [`MemoryTableRow`] to add to the table.
    ///
    /// This method extends the `table` vector with the provided rows.
    pub fn add_rows(&mut self, rows: Vec<MemoryTableRow>) {
        self.table.extend(rows);
    }

    /// Retrieves a reference to a specific row in the Memory Table.
    ///
    /// # Arguments
    /// * `row` - The [`MemoryTableRow`] to search for in the table.
    ///
    /// # Returns
    /// An `Option` containing a reference to the matching row if found,
    /// or `None` if the row does not exist in the table.
    pub fn get_row(&self, row: &MemoryTableRow) -> Option<&MemoryTableRow> {
        self.table.iter().find(|r| *r == row)
    }

    /// Returns a reference to a row in the Memory Table given its index.
    ///
    /// # Arguments
    /// * `index` - The [`usize`] index to search for in the table.
    ///
    /// # Returns
    /// An `Option` containing a reference to the matching row if found,
    /// or `None` if the row does not exist in the table.
    pub fn get_row_from_index(&self, index: usize) -> Option<&MemoryTableRow> {
        self.table.get(index)
    }

    /// Sorts in-place the existing [`MemoryTableRow`] rows in the Memory Table by `mp`, then `clk`.
    ///
    /// Having the rows sorted is required to ensure a correct proof generation (such that the
    /// constraints can be verified).
    pub fn sort(&mut self) {
        self.table.sort_by_key(|x| (x.mp, x.clk));
    }

    /// Fills the jumps in `clk` with dummy rows.
    ///
    /// Required to ensure the correct sorting of the [`MemoryTable`] in the constraints.
    fn complete_with_dummy_rows(&mut self) {
        let mut new_table = Vec::with_capacity(self.table.len());
        let mut prev_row = self.get_row_from_index(0).unwrap();

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

impl From<Vec<Registers>> for MemoryTable {
    fn from(registers: Vec<Registers>) -> Self {
        let mut memory_table = Self::new();

        for register in registers {
            memory_table.add_row_from_registers(register.clk, register.mp, register.mv, false);
        }

        memory_table.sort();
        memory_table.complete_with_dummy_rows();

        memory_table
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
    fn test_add_row_from_registers() {
        let mut memory_table = MemoryTable::new();
        // Create a row to add to the table
        let row = MemoryTableRow::new(BaseField::zero(), BaseField::from(43), BaseField::from(91));
        // Add the row to the table
        memory_table.add_row_from_registers(
            BaseField::zero(),
            BaseField::from(43),
            BaseField::from(91),
            false,
        );
        // Check that the table contains the added row
        assert_eq!(memory_table.table, vec![row], "Added row should match the expected row.");
    }

    #[test]
    fn test_add_dummy_row_from_registers() {
        let mut memory_table = MemoryTable::new();
        // Create a row to add to the table
        let row =
            MemoryTableRow::new_dummy(BaseField::zero(), BaseField::from(43), BaseField::from(91));
        // Add the row to the table
        memory_table.add_row_from_registers(
            BaseField::zero(),
            BaseField::from(43),
            BaseField::from(91),
            true,
        );
        // Check that the table contains the added row
        assert_eq!(memory_table.table, vec![row], "Added row should match the expected row.");
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
    fn test_get_existing_row() {
        let mut memory_table = MemoryTable::new();
        // Create a row to add to the table
        let row = MemoryTableRow {
            clk: BaseField::from(0),
            mp: BaseField::from(43),
            mv: BaseField::from(91),
            d: BaseField::zero(),
        };
        // Add the row to the table
        memory_table.add_row(row.clone());
        // Retrieve the row from the table
        let retrieved = memory_table.get_row(&row);
        // Check that the retrieved row matches the added row
        assert_eq!(retrieved.unwrap(), &row, "Retrieved row should match the added row.");
    }

    #[test]
    fn test_get_non_existing_row() {
        let memory_table = MemoryTable::new();
        // Create a row to search for in the table
        let row = MemoryTableRow {
            clk: BaseField::from(0),
            mp: BaseField::from(43),
            mv: BaseField::from(91),
            d: BaseField::zero(),
        };
        // Try to retrieve the non-existing row from the table
        let retrieved = memory_table.get_row(&row);
        // Check that the retrieved row is None
        assert!(retrieved.is_none(), "Should return None for a non-existing row.");
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
            MemoryTableRow::new_dummy(BaseField::from(1), BaseField::one(), BaseField::zero()),
            MemoryTableRow::new_dummy(BaseField::from(2), BaseField::one(), BaseField::zero()),
            MemoryTableRow::new_dummy(BaseField::from(3), BaseField::one(), BaseField::zero()),
            MemoryTableRow::new_dummy(BaseField::from(4), BaseField::one(), BaseField::zero()),
            row3,
        ]);

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

        let mut expected_memory_table = MemoryTable::new();
        expected_memory_table.add_rows(vec![
            row1,
            row2,
            MemoryTableRow::new_dummy(BaseField::from(2), BaseField::one(), BaseField::zero()),
            MemoryTableRow::new_dummy(BaseField::from(3), BaseField::one(), BaseField::zero()),
            MemoryTableRow::new_dummy(BaseField::from(4), BaseField::one(), BaseField::zero()),
            row3,
        ]);

        assert_eq!(MemoryTable::from(registers), expected_memory_table);
    }
}
