// Adapted from rkdud007 brainfuck-zkvm https://github.com/rkdud007/brainfuck-zkvm/blob/main/src/compiler.rs

use stwo_prover::core::fields::m31::BaseField;

pub struct Compiler {
    code: Vec<char>,
    instructions: Vec<BaseField>,
}

impl Compiler {
    pub fn new(code: String) -> Self {
        let trimmed_code = code.chars().filter(|c| !c.is_whitespace()).collect();
        Self {
            code: trimmed_code,
            instructions: vec![],
        }
    }

    pub fn compile(&mut self) -> Vec<BaseField> {
        let mut loop_stack = vec![];
        for symbol in &self.code {
            self.instructions.push(BaseField::from(*symbol as u32));

            match *symbol {
                '[' => {
                    self.instructions.push(BaseField::from(0));
                    loop_stack.push(self.instructions.len() - 1);
                }
                ']' => {
                    let start_pos = loop_stack.pop().unwrap();
                    let loop_end_pos = self.instructions.len() + 1;
                    self.instructions[start_pos] = BaseField::from((loop_end_pos - 1) as u32);
                    self.instructions
                        .push(BaseField::from((start_pos + 1) as u32));
                }
                _ => (),
            }
        }

        self.instructions.clone()
    }
}
