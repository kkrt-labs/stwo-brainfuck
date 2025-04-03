use crate::components::{
    processor::table::ProcessorElements, EndOfExecutionClaim, InteractionClaim, TraceColumn,
    TraceError, TraceEval,
};
use brainfuck_vm::registers::Registers;
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

/// Represents the table for the end of execution instruction sub-component, containing the required
/// registers for its constraints.
///
/// The end of execution instruction is the last row of the execution trace,
/// which consists of an `ip` value of the size of the compiled program (hence out of bounds),
/// and a `ci` value of 0.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct EndOfExecInstructionTable {
    /// A vector of [`EndOfExecInstructionRow`] representing the rows of the table.
    table: Vec<EndOfExecInstructionRow>,
}

impl EndOfExecInstructionTable {
    /// Creates a new, empty [`EndOfExecInstructionTable`].
    ///
    /// # Returns
    /// A new instance of [`EndOfExecInstructionTable`] with an empty table.
    pub const fn new() -> Self {
        Self { table: Vec::new() }
    }

    /// Adds a new row to the [`EndOfExecInstructionTable`].
    ///
    /// # Arguments
    /// * `row` - The [`EndOfExecInstructionRow`] to add to the table.
    ///
    /// This method pushes a new [`EndOfExecInstructionRow`] onto the `table` vector.
    pub fn add_row(&mut self, row: EndOfExecInstructionRow) {
        self.table.push(row);
    }

    /// Adds multiple rows to the [`EndOfExecInstructionTable`].
    ///
    /// # Arguments
    /// * `rows` - A vector of [`EndOfExecInstructionRow`] to add to the table.
    ///
    /// This method extends the `table` vector with the provided rows.
    fn add_rows(&mut self, rows: Vec<EndOfExecInstructionRow>) {
        self.table.extend(rows);
    }

    /// Transforms the [`EndOfExecInstructionTable`] into a [`TraceEval`], to be committed when
    /// generating a STARK proof.
    ///
    /// Converts the row-based table into columnar format and evaluates it over
    /// the circle domain.
    ///
    /// # Returns
    /// A tuple containing the evaluated trace and claim for STARK proof.
    ///
    /// # Errors
    /// Returns `TraceError::EmptyTrace` if the table is empty.
    pub fn trace_evaluation(&self) -> Result<(TraceEval, EndOfExecutionClaim), TraceError> {
        let n_rows = self.table.len() as u32;
        // If there is no (or more than one) end of execution instruction in the trace, we must
        // raise an error.
        if n_rows != 1 {
            return Err(TraceError::InvalidEndOfExecution);
        }

        let log_size = LOG_N_LANES;

        let mut trace = vec![BaseColumn::zeros(1 << log_size); EndOfExecutionColumn::count().0];

        trace[EndOfExecutionColumn::Clk.index()].data[0] = self.table[0].clk.into();
        trace[EndOfExecutionColumn::Ip.index()].data[0] = self.table[0].ip.into();
        trace[EndOfExecutionColumn::Ci.index()].data[0] = self.table[0].ci.into();
        trace[EndOfExecutionColumn::Ni.index()].data[0] = self.table[0].ni.into();
        trace[EndOfExecutionColumn::Mp.index()].data[0] = self.table[0].mp.into();
        trace[EndOfExecutionColumn::Mv.index()].data[0] = self.table[0].mv.into();
        trace[EndOfExecutionColumn::Mvi.index()].data[0] = self.table[0].mvi.into();

        // Evaluate columns on the circle domain
        let domain = CanonicCoset::new(log_size).circle_domain();
        let trace = trace.into_iter().map(|col| CircleEvaluation::new(domain, col)).collect();

        // Return the evaluated trace and claim
        Ok((trace, EndOfExecutionClaim::new(log_size)))
    }
}

impl From<&Vec<Registers>> for EndOfExecInstructionTable {
    fn from(registers: &Vec<Registers>) -> Self {
        let mut end_of_execution_table = Self::new();

        let rows =
            registers.iter().filter(|reg| reg.ci == BaseField::zero()).map(Into::into).collect();

        end_of_execution_table.add_rows(rows);

        end_of_execution_table
    }
}

/// Represents a row in the [`EndOfExecInstructionTable`].
///
/// The [`EndOfExecInstructionTable`] ensures that the Brainfuck program terminates correctly.
///
/// The row contains the values for the following registers:
/// - `clk`: The clock cycle counter, represents the current step.
/// - `ip`: The instruction pointer.
/// - `ci`: The current instruction.
/// - `ni`: The next instruction.
/// - `mp`: The memory pointer.
/// - `mv`: The memory value.
/// - `mvi`: The memory value inverse.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct EndOfExecInstructionRow {
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

impl EndOfExecInstructionRow {
    /// Creates a row for the [`EndOfExecInstructionTable`].
    pub const fn new(
        clk: BaseField,
        ip: BaseField,
        ci: BaseField,
        ni: BaseField,
        mp: BaseField,
        mv: BaseField,
        mvi: BaseField,
    ) -> Self {
        Self { clk, ip, ci, ni, mp, mv, mvi }
    }
}

impl From<&Registers> for EndOfExecInstructionRow {
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

/// Enum representing the column indices in the `EndOfExecution` trace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EndOfExecutionColumn {
    Clk,
    Ip,
    Ci,
    Ni,
    Mp,
    Mv,
    Mvi,
}

impl EndOfExecutionColumn {
    /// Returns the index of the column in the `EndOfExecution` trace.
    pub const fn index(self) -> usize {
        match self {
            Self::Clk => 0,
            Self::Ip => 1,
            Self::Ci => 2,
            Self::Ni => 3,
            Self::Mp => 4,
            Self::Mv => 5,
            Self::Mvi => 6,
        }
    }
}

impl TraceColumn for EndOfExecutionColumn {
    fn count() -> (usize, usize) {
        (7, 1)
    }
}

/// Creates the interaction trace from the main trace evaluation
/// and the interaction elements for the Processor sub-components.
///
/// The [`EndOfExecInstructionTable`] represents the execution trace of the end of execution
/// instruction.
///
/// Here, the logUp has a single extension column, which yields
/// the Processor lookup elements.
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
    let log_size = main_trace_eval[0].domain.log_size();

    let clk_col = &main_trace_eval[EndOfExecutionColumn::Clk.index()].data;
    let ip_col = &main_trace_eval[EndOfExecutionColumn::Ip.index()].data;
    let ci_col = &main_trace_eval[EndOfExecutionColumn::Ci.index()].data;
    let ni_col = &main_trace_eval[EndOfExecutionColumn::Ni.index()].data;
    let mp_col = &main_trace_eval[EndOfExecutionColumn::Mp.index()].data;
    let mv_col = &main_trace_eval[EndOfExecutionColumn::Mv.index()].data;
    let mvi_col = &main_trace_eval[EndOfExecutionColumn::Mvi.index()].data;

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

        let num = -PackedSecureField::one();

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
    use crate::components::{
        processor::{
            instructions::end_of_execution::table::{
                interaction_trace_evaluation, EndOfExecInstructionRow, EndOfExecInstructionTable,
                EndOfExecutionColumn,
            },
            table::ProcessorElements,
        },
        TraceColumn, TraceError,
    };
    use brainfuck_vm::{
        compiler::Compiler, registers::Registers, test_helper::create_test_machine,
    };
    use num_traits::{One, Zero};
    use stwo_prover::{
        constraint_framework::{logup::LogupTraceGenerator, Relation},
        core::{
            backend::simd::{m31::LOG_N_LANES, qm31::PackedSecureField},
            fields::m31::BaseField,
        },
    };

    #[test]
    fn test_end_of_execution_table_row_from_registers() {
        let registers = Registers {
            clk: BaseField::one(),
            ip: BaseField::from(5),
            ci: BaseField::from(43),
            ni: BaseField::from(91),
            mp: BaseField::from(2),
            mv: BaseField::from(7),
            mvi: BaseField::zero(),
        };

        let row = EndOfExecInstructionRow::from(&registers);

        let expected_row = EndOfExecInstructionRow::new(
            BaseField::one(),
            BaseField::from(5),
            BaseField::from(43),
            BaseField::from(91),
            BaseField::from(2),
            BaseField::from(7),
            BaseField::zero(),
        );

        assert_eq!(row, expected_row);
    }

    #[test]
    fn test_end_of_execution_table_new() {
        let end_of_execution_table = EndOfExecInstructionTable::new();

        assert!(end_of_execution_table.table.is_empty());
    }

    #[test]
    fn test_add_row() {
        let mut end_of_execution_table = EndOfExecInstructionTable::new();

        let row = EndOfExecInstructionRow::new(
            BaseField::from(10),
            BaseField::from(15),
            BaseField::zero(),
            BaseField::from(91),
            BaseField::from(20),
            BaseField::from(25),
            BaseField::one(),
        );

        end_of_execution_table.add_row(row.clone());

        assert_eq!(end_of_execution_table.table, vec![row]);
    }

    #[allow(clippy::similar_names)]
    #[allow(clippy::too_many_lines)]
    #[test]
    fn test_end_of_execution_table_from_registers_example_program() {
        // Create a small program and compile it
        let code = "+>,<[>+.<-]";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        // Create a machine and execute the program
        let (mut machine, _) = create_test_machine(&instructions, &[1]);
        let () = machine.execute().expect("Failed to execute machine");

        // Get the trace of the executed program
        let trace = &machine.trace();

        // Convert the trace to an `EndOfExecInstructionTable`
        let end_of_execution_table: EndOfExecInstructionTable = trace.into();

        // Create the expected `EndOfExecInstructionTable`
        let end_of_exec_row = EndOfExecInstructionRow::new(
            BaseField::from(11),
            BaseField::from(13),
            BaseField::zero(),
            BaseField::zero(),
            BaseField::zero(),
            BaseField::zero(),
            BaseField::zero(),
        );

        let expected_end_of_execution_table =
            EndOfExecInstructionTable { table: vec![end_of_exec_row] };

        // Verify that the end of execution table is correct
        assert_eq!(end_of_execution_table, expected_end_of_execution_table);
    }

    #[test]
    fn test_trace_evaluation_empty_end_of_execution_table() {
        let end_of_execution_table = EndOfExecInstructionTable::new();
        let trace_result = end_of_execution_table.trace_evaluation();

        assert_eq!(trace_result.unwrap_err(), TraceError::InvalidEndOfExecution);
    }

    #[test]
    fn test_trace_evaluation_multiple_rows_end_of_execution_table() {
        let mut end_of_execution_table = EndOfExecInstructionTable::new();

        end_of_execution_table.add_row(EndOfExecInstructionRow::default());
        end_of_execution_table.add_row(EndOfExecInstructionRow::default());

        let trace_result = end_of_execution_table.trace_evaluation();

        assert_eq!(trace_result.unwrap_err(), TraceError::InvalidEndOfExecution);
    }

    #[test]
    #[allow(clippy::similar_names)]
    fn test_trace_evaluation_single_row_end_of_execution_table() {
        let mut end_of_execution_table = EndOfExecInstructionTable::new();
        end_of_execution_table.add_row(EndOfExecInstructionRow {
            clk: BaseField::one(),
            ip: BaseField::from(2),
            ..Default::default()
        });

        let (trace, claim) = end_of_execution_table.trace_evaluation().unwrap();

        assert_eq!(claim.log_size, LOG_N_LANES, "Log size should include SIMD lanes.");
        assert_eq!(
            trace.len(),
            EndOfExecutionColumn::count().0,
            "Trace should contain one column per register."
        );

        let expected_clk_col = vec![BaseField::one(); 1 << LOG_N_LANES];
        let expected_ip_col = vec![BaseField::from(2); 1 << LOG_N_LANES];
        let expected_ci_col = vec![BaseField::zero(); 1 << LOG_N_LANES];
        let expected_ni_col = vec![BaseField::zero(); 1 << LOG_N_LANES];
        let expected_mp_col = vec![BaseField::zero(); 1 << LOG_N_LANES];
        let expected_mv_col = vec![BaseField::zero(); 1 << LOG_N_LANES];
        let expected_mvi_col = vec![BaseField::zero(); 1 << LOG_N_LANES];

        assert_eq!(trace[EndOfExecutionColumn::Clk.index()].to_cpu().values, expected_clk_col);
        assert_eq!(trace[EndOfExecutionColumn::Ip.index()].to_cpu().values, expected_ip_col);
        assert_eq!(trace[EndOfExecutionColumn::Ci.index()].to_cpu().values, expected_ci_col);
        assert_eq!(trace[EndOfExecutionColumn::Ni.index()].to_cpu().values, expected_ni_col);
        assert_eq!(trace[EndOfExecutionColumn::Mp.index()].to_cpu().values, expected_mp_col);
        assert_eq!(trace[EndOfExecutionColumn::Mv.index()].to_cpu().values, expected_mv_col);
        assert_eq!(trace[EndOfExecutionColumn::Mvi.index()].to_cpu().values, expected_mvi_col);
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

        let end_of_execution_table = EndOfExecInstructionTable::from(&machine.trace());

        let (trace_eval, claim) = end_of_execution_table.trace_evaluation().unwrap();

        let processor_lookup_elements = ProcessorElements::dummy();

        let (interaction_trace_eval, interaction_claim) =
            interaction_trace_evaluation(&trace_eval, &processor_lookup_elements).unwrap();

        let log_size = trace_eval[0].domain.log_size();

        let mut denoms = [PackedSecureField::zero(); 1];

        let clk_col = &trace_eval[EndOfExecutionColumn::Clk.index()].data;
        let ip_col = &trace_eval[EndOfExecutionColumn::Ip.index()].data;
        let ci_col = &trace_eval[EndOfExecutionColumn::Ci.index()].data;
        let ni_col = &trace_eval[EndOfExecutionColumn::Ni.index()].data;
        let mp_col = &trace_eval[EndOfExecutionColumn::Mp.index()].data;
        let mv_col = &trace_eval[EndOfExecutionColumn::Mv.index()].data;
        let mvi_col = &trace_eval[EndOfExecutionColumn::Mvi.index()].data;

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

        let num = -PackedSecureField::one();

        let mut logup_gen = LogupTraceGenerator::new(log_size);

        // Sub Component Lookup
        let mut col_gen = logup_gen.new_col();
        col_gen.write_frac(0, num, denoms[0]);
        col_gen.finalize_col();

        let (expected_interaction_trace_eval, expected_claimed_sum) = logup_gen.finalize_last();

        assert_eq!(denoms.len(), 1);
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
