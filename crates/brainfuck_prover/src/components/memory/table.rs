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
}
