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
    pub fn new() -> Self {
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
    pub fn get_row(&self, row: InstructionTableRow) -> Option<&InstructionTableRow> {
        self.table.iter().find(|r| *r == &row)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
    fn test_add_row() {
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
        assert_eq!(instruction_table, InstructionTable { table: rows.clone() });
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
        let retrieved = instruction_table.get_row(row.clone());
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
        let retrieved = instruction_table.get_row(row);
        // Check that the retrieved row is None
        assert!(retrieved.is_none(), "Should return None for a non-existing row.");
    }
}
