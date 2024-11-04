use crate::machine::Machine;
use std::cell::RefCell;
use std::io::{Cursor, Write};
use std::rc::Rc;
use stwo_prover::core::fields::m31::BaseField;

pub struct TestWriter {
    buffer: Rc<RefCell<Vec<u8>>>,
}

impl TestWriter {
    pub fn new() -> Self {
        TestWriter {
            buffer: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub fn get_output(&self) -> Vec<u8> {
        self.buffer.borrow().clone()
    }
}

impl Default for TestWriter {
    fn default() -> Self {
        Self::new()
    }
}

impl Write for TestWriter {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.buffer.borrow_mut().extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

impl Clone for TestWriter {
    fn clone(&self) -> Self {
        TestWriter {
            buffer: Rc::clone(&self.buffer), // This creates a new reference to the same buffer
        }
    }
}

// Helper function to create a test machine
pub fn create_test_machine(code: Vec<BaseField>, input: &[u8]) -> (Machine, TestWriter) {
    let input = Cursor::new(input.to_vec());
    let output = TestWriter::new();
    let test_output = output.clone();
    let machine = Machine::new(code, input, output);
    (machine, test_output)
}
