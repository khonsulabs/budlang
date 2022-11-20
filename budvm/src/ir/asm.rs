#![allow(missing_docs, clippy::missing_panics_doc)]
//! Bud Assembly Language
//!
//! ```budasm
//! fn name @a @b @c
//! // (a * b) * c
//! mul @a @b $tmp
//! mul $tmp @c $
//!
//! fn __init
//! // init function called when module is loaded
//! // name(1, 2, 3) -> 6
//! push 1
//! push 2
//! push 3
//! call name 3
//! ```
//!
// We use the Range type which doesn't allow this, and it's not worth making a
// helper function to appease clippy.
#![allow(clippy::range_plus_one)]

use std::{iter::Peekable, ops::Range, str::CharIndices};

use crate::{
    ir::{
        CodeBlockBuilder, CompareAction, Destination, Function, Instruction, Label, Literal,
        LiteralOrSource, Module,
    },
    lexer_util::{
        decode_numeric_literal, decode_string_literal_contents, DecodeNumericError,
        DecodeStringError, DoublePeekable, Numeric,
    },
    Comparison, Intrinsic, Symbol,
};

#[derive(PartialEq, Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub range: Range<usize>,
}

impl Token {
    fn at_offset(kind: TokenKind, offset: usize) -> Self {
        Self::new(kind, offset..offset + 1)
    }

    fn new(kind: TokenKind, range: Range<usize>) -> Self {
        Self { kind, range }
    }
}

#[derive(Debug, PartialEq)]
pub enum TokenKind {
    Identifier(Symbol),
    EndOfLine,
    Comment,
    Integer(i64),
    Real(f64),
    String(String),
}

pub struct Lexer<'a> {
    chars: DoublePeekable<CharIndices<'a>>,
    source: &'a str,
}

impl<'a> Lexer<'a> {
    #[must_use]
    pub fn new(source: &'a str) -> Self {
        Self {
            chars: DoublePeekable::new(source.char_indices()),
            source,
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token, AsmError>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.chars.next()? {
                (offset, ch) if ch == '$' || ch == '@' || ch == '#' || ch.is_alphabetic() => {
                    let mut end = offset;
                    while self.chars.peek().map_or(false, |(_, ch)| {
                        ch.is_alphanumeric() || *ch == '_' || *ch == '$'
                    }) {
                        end = self.chars.next().expect("just peeked").0;
                    }
                    return Some(Ok(Token {
                        kind: TokenKind::Identifier(Symbol::from(&self.source[offset..=end])),
                        range: offset..end + 1,
                    }));
                }
                (offset, char) if char == '\r' || char == '\n' => {
                    if char == '\r' && matches!(self.chars.peek().map(|(_, ch)| *ch), Some('\n')) {
                        return Some(Ok(Token::new(TokenKind::EndOfLine, offset..offset + 2)));
                    }

                    return Some(Ok(Token::at_offset(TokenKind::EndOfLine, offset)));
                }
                (offset, char) if char == '"' => {
                    let literal = match decode_string_literal_contents(&mut self.chars, offset) {
                        Ok(literal) => literal,
                        Err(err) => return Some(Err(AsmError::from(err))),
                    };

                    return Some(Ok(Token::new(
                        TokenKind::String(literal.contents),
                        offset..literal.end_quote_offset + 1,
                    )));
                }
                (offset, char)
                    if char.is_numeric()
                        || (char == '-'
                            && self.chars.peek().map_or(false, |(_, ch)| ch.is_numeric())) =>
                {
                    let literal = match decode_numeric_literal(&mut self.chars, self.source, offset)
                    {
                        Ok(literal) => literal,
                        Err(err) => return Some(Err(AsmError::from(err))),
                    };

                    return Some(Ok(Token::new(
                        match literal.contents {
                            Numeric::Integer(integer) => TokenKind::Integer(integer),
                            Numeric::Real(real) => TokenKind::Real(real),
                        },
                        offset..literal.last_offset + 1,
                    )));
                }
                (_, ch) if ch.is_ascii_whitespace() => {}
                (offset, character) => {
                    return Some(Err(AsmError::UnexpectedChar { character, offset }))
                }
            }
        }
    }
}

#[derive(PartialEq, Debug)]
pub enum AsmError {
    String(DecodeStringError),
    Numeric(DecodeNumericError),
    UnexpectedChar { character: char, offset: usize },
    Unexpected(Token),
    UnexpectedEof(String),
    LabelAlreadyUsed { label: Symbol, range: Range<usize> },
    UnknownInstruction(Token),
    UnknownArgument(Token),
    InvalidArgumentCount(Token),
    UnknownIntrinsic(Token),
}

impl From<DecodeStringError> for AsmError {
    fn from(err: DecodeStringError) -> Self {
        Self::String(err)
    }
}

impl From<DecodeNumericError> for AsmError {
    fn from(err: DecodeNumericError) -> Self {
        Self::Numeric(err)
    }
}

pub(crate) struct Parser<'a> {
    tokens: Peekable<Lexer<'a>>,
    current_function_name: Option<Symbol>,
    current_function: CodeBlockBuilder,
    module: Module,
}

impl<'a> Parser<'a> {
    pub fn parse(asm: &'a str) -> Result<Module, AsmError> {
        Self {
            tokens: Lexer::new(asm).peekable(),
            current_function_name: None,
            current_function: CodeBlockBuilder::default(),
            module: Module::default(),
        }
        .parse_asm()
    }

    fn parse_asm(mut self) -> Result<Module, AsmError> {
        while let Some(token) = self.tokens.next().transpose()? {
            match &token.kind {
                TokenKind::Identifier(symbol) => {
                    if let Some(label) = symbol.strip_prefix('#') {
                        let label = self.current_function.named_label(label);
                        self.current_function.label(label);
                        self.expect_end_of_line()?;
                    } else {
                        match &**symbol {
                            "function" => self.parse_function()?,
                            "add" | "sub" | "mul" | "div" | "and" | "or" | "xor" | "bitor"
                            | "bitand" | "bitxor" | "shl" | "shr" => self.parse_binop(symbol)?,
                            "eq" | "neq" | "lt" | "lte" | "gt" | "gte" => {
                                self.parse_comparison(symbol)?;
                            }
                            "not" => self.parse_not()?,
                            "ifnot" => self.parse_ifnot()?,
                            "jump" => self.parse_jump()?,
                            "push" => self.parse_push()?,
                            "load" => self.parse_load()?,
                            "call" => self.parse_call()?,
                            "recurse" => self.parse_call_with_name(None)?,
                            "intrinsic" => self.parse_intrinsic()?,
                            "invoke" => self.parse_invoke()?,
                            "return" => {
                                let value = if self.next_is_end_of_line() {
                                    None
                                } else {
                                    Some(self.expect_literal_or_source()?)
                                };
                                self.expect_end_of_line()?;
                                self.current_function.push(Instruction::Return(value));
                            }
                            _ => return Err(AsmError::UnknownInstruction(token)),
                        }
                    }
                }
                TokenKind::EndOfLine | TokenKind::Comment => {}
                _ => return Err(AsmError::Unexpected(token)),
            }
        }

        self.begin_new_function(None);

        Ok(self.module)
    }

    fn parse_binop(&mut self, kind: &Symbol) -> Result<(), AsmError> {
        let left = self.expect_literal_or_source()?;
        let right = self.expect_literal_or_source()?;
        let destination = self.expect_destination()?;

        let instruction = match &**kind {
            "add" => Instruction::Add {
                left,
                right,
                destination,
            },
            "sub" => Instruction::Sub {
                left,
                right,
                destination,
            },
            "mul" => Instruction::Multiply {
                left,
                right,
                destination,
            },
            "div" => Instruction::Divide {
                left,
                right,
                destination,
            },
            "and" => Instruction::LogicalAnd {
                left,
                right,
                destination,
            },
            "or" => Instruction::LogicalOr {
                left,
                right,
                destination,
            },
            "xor" => Instruction::LogicalXor {
                left,
                right,
                destination,
            },
            "bitand" => Instruction::BitwiseAnd {
                left,
                right,
                destination,
            },
            "bitor" => Instruction::BitwiseOr {
                left,
                right,
                destination,
            },
            "bitxor" => Instruction::BitwiseXor {
                left,
                right,
                destination,
            },
            "shl" => Instruction::ShiftLeft {
                left,
                right,
                destination,
            },
            "shr" => Instruction::ShiftRight {
                left,
                right,
                destination,
            },
            _ => unreachable!("this list should match the one found in parse_asm"),
        };
        self.current_function.push(instruction);
        Ok(())
    }

    fn begin_new_function(&mut self, new_function_name: Option<Symbol>) {
        let block = std::mem::take(&mut self.current_function).finish();
        match std::mem::replace(&mut self.current_function_name, new_function_name) {
            Some(name) => self.module.vtable.push(Function::new(name, block)),
            None => {
                self.module.init = Some(Function::new(Symbol::from("__init"), block));
            }
        }
    }

    fn next_is_end_of_line(&mut self) -> bool {
        self.peek_token_kind().map_or(true, |kind| {
            matches!(kind, TokenKind::EndOfLine | TokenKind::Comment)
        })
    }

    fn expect_end_of_line(&mut self) -> Result<(), AsmError> {
        match self.tokens.next().transpose()? {
            Some(token) if token.kind == TokenKind::Comment => {
                // Skip comments
                self.expect_end_of_line()
            }
            Some(token) if token.kind == TokenKind::EndOfLine => Ok(()),
            None => Ok(()),
            Some(token) => Err(AsmError::Unexpected(token)),
        }
    }

    fn expect_next(&mut self, expected: &str) -> Result<Token, AsmError> {
        self.tokens
            .next()
            .ok_or_else(|| AsmError::UnexpectedEof(expected.to_string()))?
    }

    fn expect_identifier(&mut self, expected: &str) -> Result<(Symbol, Range<usize>), AsmError> {
        let token = self.expect_next(expected)?;
        match token.kind {
            TokenKind::Identifier(symbol) => Ok((symbol, token.range)),
            kind => Err(AsmError::Unexpected(Token {
                kind,
                range: token.range,
            })),
        }
    }

    fn expect_label(&mut self) -> Result<Label, AsmError> {
        let (label, range) = self.expect_identifier("label")?;
        if let Some(label) = label.strip_prefix('#') {
            Ok(self.current_function.named_label(label))
        } else {
            Err(AsmError::Unexpected(Token {
                kind: TokenKind::Identifier(label),
                range,
            }))
        }
    }

    fn expect_integer(&mut self, expecting: &str) -> Result<(i64, Range<usize>), AsmError> {
        let token = self.expect_next(expecting)?;
        match token.kind {
            TokenKind::Integer(value) => Ok((value, token.range)),
            kind => Err(AsmError::Unexpected(Token {
                kind,
                range: token.range,
            })),
        }
    }

    fn expect_arg_count(&mut self) -> Result<usize, AsmError> {
        let (value, range) = self.expect_integer("arg count")?;
        match usize::try_from(value) {
            Ok(value) => Ok(value),
            Err(_) => Err(AsmError::InvalidArgumentCount(Token {
                kind: TokenKind::Integer(value),
                range,
            })),
        }
    }

    fn peek_token_kind(&mut self) -> Option<&TokenKind> {
        self.tokens.peek().and_then(|token| {
            if let Ok(token) = token {
                Some(&token.kind)
            } else {
                None
            }
        })
    }

    fn expect_literal_or_source(&mut self) -> Result<LiteralOrSource, AsmError> {
        let token = self.expect_next("literal, argument, or variable")?;
        match token.kind {
            TokenKind::Identifier(symbol) => match &*symbol {
                "void" => Ok(LiteralOrSource::Literal(Literal::Void)),
                "true" => Ok(LiteralOrSource::Literal(Literal::Boolean(true))),
                "false" => Ok(LiteralOrSource::Literal(Literal::Boolean(false))),
                _ => {
                    let (first_char, remaining) = symbol.split_at(1);
                    match first_char {
                        "$" => {
                            let variable = self
                                .current_function
                                .variable_index_from_name(&Symbol::from(remaining));
                            Ok(LiteralOrSource::Variable(variable))
                        }
                        "@" => {
                            if let Some(arg) =
                                self.current_function.argument(&Symbol::from(remaining))
                            {
                                Ok(LiteralOrSource::Argument(arg))
                            } else {
                                Err(AsmError::UnknownArgument(Token {
                                    kind: TokenKind::Identifier(symbol),
                                    range: token.range,
                                }))
                            }
                        }
                        _ => Err(AsmError::Unexpected(Token {
                            kind: TokenKind::Identifier(symbol),
                            range: token.range,
                        })),
                    }
                }
            },
            TokenKind::Integer(value) => Ok(LiteralOrSource::Literal(Literal::Integer(value))),
            TokenKind::Real(value) => Ok(LiteralOrSource::Literal(Literal::Real(value))),
            TokenKind::String(value) => Ok(LiteralOrSource::Literal(Literal::String(value))),
            kind => Err(AsmError::Unexpected(Token {
                kind,
                range: token.range,
            })),
        }
    }

    fn expect_destination(&mut self) -> Result<Destination, AsmError> {
        let token = self.expect_next("variable, stack ($) or return ($$)")?;
        if let TokenKind::Identifier(symbol) = &token.kind {
            if let Some(remaining) = symbol.strip_prefix('$') {
                return match remaining {
                    "" => Ok(Destination::Stack),
                    "$" => Ok(Destination::Return),
                    _ => {
                        let variable = self
                            .current_function
                            .variable_index_from_name(&Symbol::from(remaining));
                        Ok(Destination::Variable(variable))
                    }
                };
            }
        }
        Err(AsmError::Unexpected(token))
    }

    fn parse_function(&mut self) -> Result<(), AsmError> {
        let name = self.expect_next("function name")?;
        if let TokenKind::Identifier(name) = &name.kind {
            self.begin_new_function(Some(name.clone()));
        } else {
            return Err(AsmError::Unexpected(name));
        }

        while let Some(token) = match self.tokens.next().transpose()? {
            Some(token) if token.kind == TokenKind::EndOfLine => None,
            Some(token) => Some(token),
            None => None,
        } {
            if let TokenKind::Identifier(arg_name) = &token.kind {
                if let Some(arg_name) = arg_name.strip_prefix('@') {
                    self.current_function.new_argument(arg_name);
                } else {
                    //
                    return Err(AsmError::Unexpected(token));
                }
            } else {
                return Err(AsmError::Unexpected(token));
            }
        }

        Ok(())
    }

    fn parse_comparison(&mut self, kind: &Symbol) -> Result<(), AsmError> {
        let comparison = match &**kind {
            "eq" => Comparison::Equal,
            "neq" => Comparison::NotEqual,
            "lt" => Comparison::LessThan,
            "lte" => Comparison::LessThanOrEqual,
            "gt" => Comparison::GreaterThan,
            "gte" => Comparison::GreaterThanOrEqual,
            _ => unreachable!("list should match parse_asm"),
        };
        let left = self.expect_literal_or_source()?;
        let right = self.expect_literal_or_source()?;
        match self.peek_token_kind() {
            Some(TokenKind::Identifier(action)) => {
                let action = if action == "jump" {
                    self.tokens.next();

                    let label = self.expect_next("label")?;
                    if let TokenKind::Identifier(label_name) = &label.kind {
                        if let Some(label) = label_name.strip_prefix('#') {
                            let label = self.current_function.named_label(label);
                            CompareAction::JumpIfFalse(label)
                        } else {
                            return Err(AsmError::Unexpected(label));
                        }
                    } else {
                        return Err(AsmError::Unexpected(label));
                    }
                } else {
                    let destination = self.expect_destination()?;
                    CompareAction::Store(destination)
                };

                self.current_function.push(Instruction::Compare {
                    comparison,
                    left,
                    right,
                    action,
                });

                Ok(())
            }
            Some(_) => Err(AsmError::Unexpected(
                self.tokens
                    .next()
                    .expect("just peeked")
                    .expect("just peeked"),
            )),
            // There could be a parse error, so we use expect_next to raise the
            // appropriate error.
            None => self.expect_next("compare action").map(|_| ()),
        }
    }

    fn parse_not(&mut self) -> Result<(), AsmError> {
        let value = self.expect_literal_or_source()?;
        let destination = self.expect_destination()?;
        self.current_function
            .push(Instruction::Not { value, destination });
        Ok(())
    }

    fn parse_ifnot(&mut self) -> Result<(), AsmError> {
        let condition = self.expect_literal_or_source()?;
        let false_jump_to = self.expect_label()?;
        self.current_function.push(Instruction::If {
            condition,
            false_jump_to,
        });
        Ok(())
    }

    fn parse_jump(&mut self) -> Result<(), AsmError> {
        let label = self.expect_label()?;
        self.current_function.push(Instruction::JumpTo(label));
        Ok(())
    }

    fn parse_push(&mut self) -> Result<(), AsmError> {
        let value = self.expect_literal_or_source()?;
        self.current_function.push(Instruction::Push(value));
        Ok(())
    }
    fn parse_load(&mut self) -> Result<(), AsmError> {
        let value = self.expect_literal_or_source()?;
        let (variable, variable_range) = self.expect_identifier("variable")?;
        if let Some(variable) = variable.strip_prefix('$') {
            let variable = self
                .current_function
                .variable_index_from_name(&Symbol::from(variable));
            self.current_function
                .push(Instruction::Load { value, variable });
            Ok(())
        } else {
            Err(AsmError::Unexpected(Token {
                kind: TokenKind::Identifier(variable),
                range: variable_range,
            }))
        }
    }

    fn parse_call(&mut self) -> Result<(), AsmError> {
        let (function, _) = self.expect_identifier("function name")?;
        self.parse_call_with_name(Some(function))
    }

    fn parse_call_with_name(&mut self, function: Option<Symbol>) -> Result<(), AsmError> {
        let arg_count = self.expect_arg_count()?;
        let destination = self.expect_destination()?;

        self.current_function.push(Instruction::Call {
            function,
            arg_count,
            destination,
        });

        Ok(())
    }

    fn parse_intrinsic(&mut self) -> Result<(), AsmError> {
        let (name, range) = self.expect_identifier("intrinsic name")?;
        let intrinsic = match &*name {
            "NewMap" => Intrinsic::NewMap,
            "NewList" => Intrinsic::NewList,
            _ => {
                return Err(AsmError::UnknownIntrinsic(Token {
                    kind: TokenKind::Identifier(name),
                    range,
                }));
            }
        };

        let arg_count = self.expect_arg_count()?;
        let destination = self.expect_destination()?;
        self.current_function.push(Instruction::CallIntrinsic {
            intrinsic,
            arg_count,
            destination,
        });

        Ok(())
    }

    fn parse_invoke(&mut self) -> Result<(), AsmError> {
        let target = if let Some(TokenKind::Identifier(identifier)) = self.peek_token_kind() {
            if identifier == "$" {
                self.tokens.next();
                None
            } else {
                Some(self.expect_literal_or_source()?)
            }
        } else {
            return Err(AsmError::UnexpectedEof(String::from("invoke target")));
        };

        let (name, _) = self.expect_identifier("function name")?;
        let arg_count = self.expect_arg_count()?;
        let destination = self.expect_destination()?;

        self.current_function.push(Instruction::CallInstance {
            target,
            name,
            arg_count,
            destination,
        });

        Ok(())
    }
}

#[test]
fn basic() {
    let block = Parser::parse(
        r#"
            return 42
        "#,
    )
    .unwrap();

    assert_eq!(
        block.init.unwrap().body.code,
        vec![Instruction::Return(Some(
            crate::ir::LiteralOrSource::Literal(crate::ir::Literal::Integer(42))
        ))]
    );
}

#[test]
#[allow(clippy::too_many_lines)]
fn roundtrip_all_instructions() {
    // These instructions don't make any sense. We just need one each
    // instruction, and we need to ensure we try each
    // LiteralOrSource/Destination variant.
    let mut block = CodeBlockBuilder::default();
    block.push(Instruction::Return(None));
    let init = Function::new("__init", block.finish());

    let mut block = CodeBlockBuilder::default();
    let arg1 = block.new_argument("test");
    let var1 = block.variable_index_from_name(&Symbol::from("test"));
    let a_label = block.named_label("a_label");
    block.label(a_label.clone());
    block.push(Instruction::Add {
        left: LiteralOrSource::Argument(arg1),
        right: LiteralOrSource::Variable(var1.clone()),
        destination: Destination::Variable(var1.clone()),
    });
    block.push(Instruction::Sub {
        left: LiteralOrSource::Literal(Literal::Boolean(false)),
        right: LiteralOrSource::Literal(Literal::Boolean(true)),
        destination: Destination::Return,
    });
    block.push(Instruction::Multiply {
        left: LiteralOrSource::Literal(Literal::String(String::from("a string"))),
        right: LiteralOrSource::Literal(Literal::Real(1.0)),
        destination: Destination::Stack,
    });
    block.push(Instruction::Divide {
        left: LiteralOrSource::Literal(Literal::Void),
        right: LiteralOrSource::Literal(Literal::Integer(0)),
        destination: Destination::Stack,
    });
    block.push(Instruction::LogicalAnd {
        left: LiteralOrSource::Literal(Literal::Void),
        right: LiteralOrSource::Literal(Literal::Void),
        destination: Destination::Stack,
    });
    block.push(Instruction::LogicalOr {
        left: LiteralOrSource::Literal(Literal::Void),
        right: LiteralOrSource::Literal(Literal::Void),
        destination: Destination::Stack,
    });
    block.push(Instruction::LogicalXor {
        left: LiteralOrSource::Literal(Literal::Void),
        right: LiteralOrSource::Literal(Literal::Void),
        destination: Destination::Stack,
    });
    block.push(Instruction::BitwiseAnd {
        left: LiteralOrSource::Literal(Literal::Void),
        right: LiteralOrSource::Literal(Literal::Void),
        destination: Destination::Stack,
    });
    block.push(Instruction::BitwiseOr {
        left: LiteralOrSource::Literal(Literal::Void),
        right: LiteralOrSource::Literal(Literal::Void),
        destination: Destination::Stack,
    });
    block.push(Instruction::BitwiseXor {
        left: LiteralOrSource::Literal(Literal::Void),
        right: LiteralOrSource::Literal(Literal::Void),
        destination: Destination::Stack,
    });
    block.push(Instruction::ShiftLeft {
        left: LiteralOrSource::Literal(Literal::Void),
        right: LiteralOrSource::Literal(Literal::Void),
        destination: Destination::Stack,
    });
    block.push(Instruction::ShiftRight {
        left: LiteralOrSource::Literal(Literal::Void),
        right: LiteralOrSource::Literal(Literal::Void),
        destination: Destination::Stack,
    });
    block.push(Instruction::Not {
        value: LiteralOrSource::Literal(Literal::Void),
        destination: Destination::Stack,
    });
    block.push(Instruction::If {
        condition: LiteralOrSource::Literal(Literal::Void),
        false_jump_to: a_label.clone(),
    });
    block.push(Instruction::JumpTo(a_label.clone()));
    block.push(Instruction::Compare {
        comparison: Comparison::Equal,
        left: LiteralOrSource::Literal(Literal::Void),
        right: LiteralOrSource::Literal(Literal::Void),
        action: CompareAction::JumpIfFalse(a_label),
    });
    block.push(Instruction::Compare {
        comparison: Comparison::NotEqual,
        left: LiteralOrSource::Literal(Literal::Void),
        right: LiteralOrSource::Literal(Literal::Void),
        action: CompareAction::Store(Destination::Stack),
    });
    block.push(Instruction::Compare {
        comparison: Comparison::GreaterThan,
        left: LiteralOrSource::Literal(Literal::Void),
        right: LiteralOrSource::Literal(Literal::Void),
        action: CompareAction::Store(Destination::Stack),
    });
    block.push(Instruction::Compare {
        comparison: Comparison::GreaterThanOrEqual,
        left: LiteralOrSource::Literal(Literal::Void),
        right: LiteralOrSource::Literal(Literal::Void),
        action: CompareAction::Store(Destination::Stack),
    });
    block.push(Instruction::Compare {
        comparison: Comparison::LessThan,
        left: LiteralOrSource::Literal(Literal::Void),
        right: LiteralOrSource::Literal(Literal::Void),
        action: CompareAction::Store(Destination::Stack),
    });
    block.push(Instruction::Compare {
        comparison: Comparison::LessThanOrEqual,
        left: LiteralOrSource::Literal(Literal::Void),
        right: LiteralOrSource::Literal(Literal::Void),
        action: CompareAction::Store(Destination::Stack),
    });
    block.push(Instruction::Push(LiteralOrSource::Literal(Literal::Void)));
    block.push(Instruction::Load {
        value: LiteralOrSource::Literal(Literal::Void),
        variable: var1.clone(),
    });
    block.push(Instruction::Return(Some(LiteralOrSource::Literal(
        Literal::Void,
    ))));
    block.push(Instruction::Call {
        function: None,
        arg_count: 1,
        destination: Destination::Stack,
    });
    block.push(Instruction::Call {
        function: Some(Symbol::from("test")),
        arg_count: 1,
        destination: Destination::Stack,
    });
    block.push(Instruction::CallInstance {
        target: None,
        name: Symbol::from("test"),
        arg_count: 1,
        destination: Destination::Stack,
    });
    block.push(Instruction::CallInstance {
        target: Some(LiteralOrSource::Variable(var1)),
        name: Symbol::from("test"),
        arg_count: 1,
        destination: Destination::Stack,
    });
    block.push(Instruction::CallIntrinsic {
        intrinsic: Intrinsic::NewList,
        arg_count: 1,
        destination: Destination::Stack,
    });
    block.push(Instruction::CallIntrinsic {
        intrinsic: Intrinsic::NewMap,
        arg_count: 1,
        destination: Destination::Stack,
    });
    let test_func = Function::new("test", block.finish());

    let manually_built = Module::new(vec![test_func], Vec::new(), Some(init));

    let assembly = manually_built.to_string();
    println!("Source:");
    println!("{assembly}");
    let parsed = Parser::parse(&assembly).unwrap();
    println!("Parsed source:");
    println!("{parsed}");
    assert_eq!(manually_built, parsed);
}
