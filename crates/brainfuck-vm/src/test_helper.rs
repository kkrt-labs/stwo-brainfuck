use std::cell::RefCell;
use std::io::Write;
use std::rc::Rc;

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
