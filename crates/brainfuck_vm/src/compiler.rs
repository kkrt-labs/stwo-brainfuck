// Adapted from rkdud007 brainfuck-zkvm https://github.com/rkdud007/brainfuck-zkvm/blob/main/src/compiler.rs

use stwo_prover::core::fields::m31::BaseField;

pub struct Compiler {
    code: Vec<char>,
    instructions: Vec<BaseField>,
}

impl Compiler {
    pub fn new(code: &str) -> Self {
        let trimmed_code = code.chars().filter(|c| !c.is_whitespace()).collect();
        Self { code: trimmed_code, instructions: vec![] }
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
                    self.instructions.push(BaseField::from((start_pos + 1) as u32));
                }
                _ => (),
            }
        }

        self.instructions.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let code = "++>,<[>+.<-]";
        let compiler = Compiler::new(code);
        let expected_trimmed_code =
            vec!['+', '+', '>', ',', '<', '[', '>', '+', '.', '<', '-', ']'];
        assert_eq!(expected_trimmed_code, compiler.code,);
    }

    #[test]
    fn test_compile() {
        let code = "++>,<[>+.<-]";
        let mut compiler = Compiler::new(code);
        let instructions = compiler.compile();
        #[allow(clippy::cast_sign_loss)]
        let expected_ins: Vec<BaseField> =
            vec![43, 43, 62, 44, 60, 91, 13, 62, 43, 46, 60, 45, 93, 7]
                .into_iter()
                .map(|x| BaseField::from(x as u32))
                .collect();
        assert_eq!(instructions, expected_ins);
    }
}
