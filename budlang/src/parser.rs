// TODO docs for parser
#![allow(missing_docs)]
// We use the Range type which doesn't allow this, and it's not worth making a
// helper function to appease clippy.
#![allow(clippy::range_plus_one)]

use std::{
    fmt::{Display, Write},
    ops::Range,
    str::CharIndices,
};

use crate::ast::{
    BinOpKind, Break, Call, CodeUnit, Continue, Function, If, Loop, LoopParameters, Mapping,
    NodeId, SyntaxTreeBuilder,
};

use budvm::{
    lexer_util::{
        decode_numeric_literal, decode_string_literal_contents, DecodeNumericError,
        DecodeStringError, DoublePeekable, Numeric,
    },
    Comparison, Symbol, ValueKind,
};

#[derive(Clone, Debug, PartialEq)]
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

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.kind, f)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum TokenKind {
    Identifier(Symbol),
    Integer(i64),
    Real(f64),
    String(String),
    Assign,
    Comment(String),
    Comparison(Comparison),
    Not,
    Add,
    Sub,
    Multiply,
    Divide,
    ShiftLeft,
    ShiftRight,
    Open(BracketType),
    Close(BracketType),
    EndOfLine,
    Comma,
    Period,
    Colon,
    Hash,
    Ampersand,
    Pipe,
    Caret,
    Tilde,
    Unknown(char),
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenKind::Identifier(value) => Display::fmt(value, f),
            TokenKind::Integer(value) => Display::fmt(value, f),
            TokenKind::Real(value) => Display::fmt(value, f),
            TokenKind::String(value) => Display::fmt(value, f),
            TokenKind::Assign => f.write_str(":="),
            TokenKind::Comparison(value) => Display::fmt(value, f),
            TokenKind::ShiftLeft => f.write_str("<<"),
            TokenKind::ShiftRight => f.write_str(">>"),
            TokenKind::Not => f.write_char('!'),
            TokenKind::Add => f.write_char('+'),
            TokenKind::Sub => f.write_char('-'),
            TokenKind::Multiply => f.write_char('*'),
            TokenKind::Divide => f.write_char('/'),
            TokenKind::Open(value) => match value {
                BracketType::Paren => f.write_char('('),
                BracketType::Square => f.write_char('['),
                BracketType::Curly => f.write_char('{'),
            },
            TokenKind::Close(value) => match value {
                BracketType::Paren => f.write_char(')'),
                BracketType::Square => f.write_char(']'),
                BracketType::Curly => f.write_char('}'),
            },
            TokenKind::EndOfLine => f.write_str("\\n"),
            TokenKind::Comma => f.write_char(','),
            TokenKind::Period => f.write_char('.'),
            TokenKind::Colon => f.write_char(':'),
            TokenKind::Hash => f.write_char('#'),
            TokenKind::Ampersand => f.write_char('&'),
            TokenKind::Pipe => f.write_char('|'),
            TokenKind::Caret => f.write_char('^'),
            TokenKind::Tilde => f.write_char('~'),
            TokenKind::Unknown(token) => Display::fmt(token, f),
            TokenKind::Comment(value) => write!(f, "// {value}"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BracketType {
    Paren,
    Square,
    Curly,
}

pub struct Lexer<'a> {
    source: &'a str,
    chars: DoublePeekable<CharIndices<'a>>,
    peeked_token: Option<Result<Token, ParseError>>,
}

impl<'a> Lexer<'a> {
    #[must_use]
    pub fn new(source: &'a str) -> Self {
        Self {
            source,
            chars: DoublePeekable::new(source.char_indices()),
            peeked_token: None,
        }
    }

    fn peek(&mut self) -> Option<&Result<Token, ParseError>> {
        if self.peeked_token.is_none() {
            self.peeked_token = self.read_token();
        }

        self.peeked_token.as_ref()
    }

    fn peek_token(&mut self) -> Option<&Token> {
        self.peek().and_then(|result| {
            if let Ok(result) = result {
                Some(result)
            } else {
                None
            }
        })
    }

    fn peek_token_kind(&mut self) -> Option<&TokenKind> {
        self.peek_token().map(|token| &token.kind)
    }

    #[allow(clippy::too_many_lines)] // TODO refactor too many lines
    fn read_token(&mut self) -> Option<Result<Token, ParseError>> {
        loop {
            break match self.chars.next() {
                Some((_, char)) if char == ' ' || char == '\t' => {
                    continue;
                }
                Some((offset, char)) if char.is_alphabetic() => {
                    let mut end = offset;
                    while self
                        .chars
                        .peek()
                        .map_or(false, |(_, char)| char.is_alphanumeric() || char == &'_')
                    {
                        end = self.chars.next().expect("just peeked").0;
                    }

                    Some(Ok(Token {
                        kind: TokenKind::Identifier(Symbol::from(&self.source[offset..=end])),
                        range: offset..end + 1,
                    }))
                }
                Some((offset, char))
                    if char.is_numeric()
                        || (char == '-'
                            && self.chars.peek().map_or(false, |(_, ch)| ch.is_numeric())) =>
                {
                    match decode_numeric_literal(&mut self.chars, self.source, offset) {
                        Ok(numeric) => Some(Ok(Token {
                            kind: match numeric.contents {
                                Numeric::Integer(value) => TokenKind::Integer(value),
                                Numeric::Real(value) => TokenKind::Real(value),
                            },
                            range: offset..numeric.last_offset,
                        })),
                        Err(err) => Some(Err(ParseError::from(err))),
                    }
                }
                Some((offset, char)) if char == '+' => {
                    Some(Ok(Token::at_offset(TokenKind::Add, offset)))
                }
                Some((offset, char)) if char == '-' => {
                    Some(Ok(Token::at_offset(TokenKind::Sub, offset)))
                }
                Some((offset, char)) if char == '*' => {
                    Some(Ok(Token::at_offset(TokenKind::Multiply, offset)))
                }
                Some((offset, char)) if char == '/' => {
                    if matches!(self.chars.peek().map(|(_, ch)| *ch), Some('/')) {
                        // Comment
                        let (mut end, _) = self.chars.next().expect("just peeked");

                        // Read until end of line
                        while self
                            .chars
                            .peek()
                            .map_or(false, |(_, char)| *char != '\n' && *char != '\r')
                        {
                            end = self.chars.next().expect("just peeked").0;
                        }

                        Some(Ok(Token::new(
                            TokenKind::Comment(self.source[offset..=end].to_string()),
                            offset..end + 1,
                        )))
                    } else {
                        Some(Ok(Token::at_offset(TokenKind::Divide, offset)))
                    }
                }
                Some((offset, char)) if char == '=' => Some(Ok(Token::at_offset(
                    TokenKind::Comparison(Comparison::Equal),
                    offset,
                ))),
                Some((offset, char)) if char == '!' => {
                    if matches!(self.chars.peek().map(|(_, ch)| *ch), Some('=')) {
                        self.chars.next();

                        Some(Ok(Token::new(
                            TokenKind::Comparison(Comparison::NotEqual),
                            offset..offset + 2,
                        )))
                    } else {
                        Some(Ok(Token::at_offset(TokenKind::Not, offset)))
                    }
                }
                Some((offset, char)) if char == '<' => {
                    Some(Ok(match self.chars.peek().map(|(_, ch)| *ch) {
                        Some('=') => {
                            self.chars.next();
                            Token::new(
                                TokenKind::Comparison(Comparison::LessThanOrEqual),
                                offset..offset + 2,
                            )
                        }
                        Some('<') => {
                            self.chars.next();
                            Token::new(TokenKind::ShiftLeft, offset..offset + 2)
                        }

                        _ => Token::at_offset(TokenKind::Comparison(Comparison::LessThan), offset),
                    }))
                }
                Some((offset, char)) if char == '>' => {
                    Some(Ok(match self.chars.peek().map(|(_, ch)| *ch) {
                        Some('=') => {
                            self.chars.next();
                            Token::new(
                                TokenKind::Comparison(Comparison::GreaterThanOrEqual),
                                offset..offset + 2,
                            )
                        }
                        Some('>') => {
                            self.chars.next();
                            Token::new(TokenKind::ShiftRight, offset..offset + 2)
                        }

                        _ => {
                            Token::at_offset(TokenKind::Comparison(Comparison::GreaterThan), offset)
                        }
                    }))
                }
                Some((offset, char)) if char == ':' => {
                    if matches!(self.chars.peek().map(|(_, ch)| *ch), Some('=')) {
                        self.chars.next();

                        Some(Ok(Token::new(TokenKind::Assign, offset..offset + 2)))
                    } else {
                        Some(Ok(Token::at_offset(TokenKind::Colon, offset)))
                    }
                }
                Some((offset, char)) if char == ',' => {
                    Some(Ok(Token::at_offset(TokenKind::Comma, offset)))
                }
                Some((offset, char)) if char == '.' => {
                    Some(Ok(Token::at_offset(TokenKind::Period, offset)))
                }
                Some((offset, char)) if char == '#' => {
                    Some(Ok(Token::at_offset(TokenKind::Hash, offset)))
                }
                Some((offset, char)) if char == '&' => {
                    Some(Ok(Token::at_offset(TokenKind::Ampersand, offset)))
                }
                Some((offset, char)) if char == '~' => {
                    Some(Ok(Token::at_offset(TokenKind::Tilde, offset)))
                }
                Some((offset, char)) if char == '|' => {
                    Some(Ok(Token::at_offset(TokenKind::Pipe, offset)))
                }
                Some((offset, char)) if char == '^' => {
                    Some(Ok(Token::at_offset(TokenKind::Caret, offset)))
                }
                Some((offset, char)) if char == '(' => Some(Ok(Token::at_offset(
                    TokenKind::Open(BracketType::Paren),
                    offset,
                ))),
                Some((offset, char)) if char == ')' => Some(Ok(Token::at_offset(
                    TokenKind::Close(BracketType::Paren),
                    offset,
                ))),
                Some((offset, char)) if char == '[' => Some(Ok(Token::at_offset(
                    TokenKind::Open(BracketType::Square),
                    offset,
                ))),
                Some((offset, char)) if char == ']' => Some(Ok(Token::at_offset(
                    TokenKind::Close(BracketType::Square),
                    offset,
                ))),
                Some((offset, char)) if char == '{' => Some(Ok(Token::at_offset(
                    TokenKind::Open(BracketType::Curly),
                    offset,
                ))),
                Some((offset, char)) if char == '}' => Some(Ok(Token::at_offset(
                    TokenKind::Close(BracketType::Curly),
                    offset,
                ))),
                Some((offset, char)) if char == '"' => Some(self.read_string(offset)),
                Some((offset, char)) if char == '\r' || char == '\n' => {
                    if char == '\r' && matches!(self.chars.peek().map(|(_, ch)| *ch), Some('\n')) {
                        Some(Ok(Token::new(TokenKind::EndOfLine, offset..offset + 2)))
                    } else {
                        Some(Ok(Token::at_offset(TokenKind::EndOfLine, offset)))
                    }
                }
                Some((offset, char)) => Some(Err(ParseError::Unexpected(Token {
                    kind: TokenKind::Unknown(char),
                    range: offset..offset + 1,
                }))),
                None => None,
            };
        }
    }

    fn expect_end_of_line(&mut self) -> Result<(), ParseError> {
        let end_of_line = self.next().ok_or(ParseError::ExpectedEndOfLine {
            offset: self.source.len(),
            found: None,
        })??;
        match &end_of_line.kind {
            TokenKind::Comment(_) => self.expect_end_of_line(),
            TokenKind::EndOfLine | TokenKind::Close(_) => Ok(()),
            _ => Err(ParseError::ExpectedEndOfLine {
                offset: end_of_line.range.start,
                found: Some(end_of_line),
            }),
        }
    }

    fn expect_end_of_line_or_eof(&mut self) -> Result<(), ParseError> {
        match self.peek_token_kind() {
            Some(TokenKind::Comment(_)) => {
                self.next();
                self.expect_end_of_line_or_eof()?;
            }
            Some(TokenKind::EndOfLine) => {
                self.next();
            }
            Some(TokenKind::Close(_)) | None => {}
            _ => {
                let token = self.next().expect("just peeked")?;
                return Err(ParseError::ExpectedEndOfLine {
                    offset: token.range.start,
                    found: Some(token),
                });
            }
        }
        Ok(())
    }

    fn read_string(&mut self, start_offset: usize) -> Result<Token, ParseError> {
        let literal = decode_string_literal_contents(&mut self.chars, start_offset)?;
        Ok(Token {
            kind: TokenKind::String(literal.contents),
            range: start_offset..literal.end_quote_offset + 1,
        })
    }

    fn expect_next(&mut self, expected: &str) -> Result<Token, ParseError> {
        self.next()
            .ok_or_else(|| ParseError::UnexpectedEof(expected.to_string()))?
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(token) = self.peeked_token.take() {
            Some(token)
        } else {
            self.read_token()
        }
    }
}

pub fn parse(source: &str) -> Result<CodeUnit, ParseError> {
    let mut tokens = Lexer::new(source);
    let mut statements = Vec::new();
    let mut functions = Vec::new();
    let init_tree = SyntaxTreeBuilder::new();
    while let Some(token) = tokens.next().transpose()? {
        match &token.kind {
            TokenKind::Identifier(ident) if ident == "function" => {
                let function = parse_function(&mut tokens)?;
                functions.push(function);
            }

            TokenKind::Comment(_) | TokenKind::EndOfLine => {}
            _ => {
                let expression = parse_expression(token, &init_tree, &mut tokens, None)?;
                statements.push(expression);
            }
        }
    }

    let mut unit = CodeUnit::from_tree(statements, init_tree);
    for function in functions {
        unit = unit.with(function.name().clone(), function);
    }

    Ok(unit)
}

fn parse_function(tokens: &mut Lexer<'_>) -> Result<Function, ParseError> {
    let name = tokens.expect_next("function name")?;
    let name = match name.kind {
        TokenKind::Identifier(name) => name,
        _ => todo!("error non-identifier for function name"),
    };

    // Parameter list
    let open_paren = tokens.expect_next("(")?;
    let mut args = Vec::new();
    if let TokenKind::Open(BracketType::Paren) = open_paren.kind {
        loop {
            match tokens.next() {
                Some(Ok(token)) if matches!(token.kind, TokenKind::Close(BracketType::Paren)) => {
                    break;
                }
                Some(Ok(Token {
                    kind: TokenKind::Identifier(arg_name),
                    ..
                })) => {
                    args.push(arg_name);

                    match tokens.expect_next("comma")? {
                        Token {
                            kind: TokenKind::Comma,
                            ..
                        } => {}
                        Token {
                            kind: TokenKind::Close(BracketType::Paren),
                            ..
                        } => {
                            break;
                        }
                        other => return Err(ParseError::Unexpected(other)),
                    }
                }
                Some(Ok(token)) => todo!("unexpected token {token:?}"),
                Some(Err(err)) => return Err(err),
                None => todo!("expected end paren and function body"),
            }
        }
    }

    tokens.expect_end_of_line()?;

    let body_tree = SyntaxTreeBuilder::new();
    let body_node = parse_statements(&body_tree, tokens, Some(&name))?;

    match tokens.expect_next("end")?.kind {
        TokenKind::Identifier(end) if end == "end" => {}
        other => todo!("unexpected {other:?}"),
    }
    // There needs to be a trailing end of line after end.
    tokens.expect_end_of_line_or_eof()?;

    Ok(Function::new(name, args, body_tree.finish(body_node)))
}

fn parse_statements(
    tree: &SyntaxTreeBuilder,
    tokens: &mut Lexer<'_>,
    owning_function_name: Option<&str>,
) -> Result<NodeId, ParseError> {
    let mut body = Vec::new();
    while let Some(Ok(token)) = tokens.peek() {
        match &token.kind {
            TokenKind::Identifier(ident) if ident == "end" || ident == "else" => {
                // end of function
                break;
            }
            TokenKind::Comment(_) | TokenKind::EndOfLine => {
                tokens.next();
            }
            _ => {
                let first_token = tokens.next().expect("just peeked")?;
                let expression = parse_expression(first_token, tree, tokens, owning_function_name)?;
                body.push(expression);
            }
        }
    }

    let body_node = match body.len() {
        1 => body[0],
        _ => tree.statements(body),
    };
    Ok(body_node)
}

fn parse_expression(
    first_token: Token,
    tree: &SyntaxTreeBuilder,
    tokens: &mut Lexer<'_>,
    owning_function_name: Option<&str>,
) -> Result<NodeId, ParseError> {
    match &first_token.kind {
        TokenKind::Identifier(symbol) if symbol == "if" => {
            let first_token = tokens.expect_next("if condition")?;
            let condition = parse_expression(first_token, tree, tokens, owning_function_name)?;
            tokens.expect_end_of_line()?;
            let if_true = parse_statements(tree, tokens, owning_function_name)?;

            let mut if_op = If::new(condition, if_true);
            let mut expect_end = true;

            match tokens.peek_token_kind() {
                Some(TokenKind::Identifier(sym)) if sym == "else" => {
                    let _else_token = tokens.next();
                    let else_block = match tokens.peek_token_kind() {
                        Some(TokenKind::Identifier(sym)) if sym == "if" => {
                            let if_token =
                                tokens.next().expect("just peeked").expect("just matched");
                            expect_end = false;
                            parse_expression(if_token, tree, tokens, owning_function_name)?
                        }
                        _ => {
                            tokens.expect_end_of_line()?;
                            parse_statements(tree, tokens, owning_function_name)?
                        }
                    };
                    if_op = if_op.with_else(else_block);
                }
                _ => {}
            }

            if expect_end {
                match tokens.expect_next("end")?.kind {
                    TokenKind::Identifier(end) if end == "end" => {}
                    other => todo!("unexpected {other:?}"),
                }
                tokens.expect_end_of_line_or_eof()?;
            }

            Ok(tree.if_node(if_op))
        }
        TokenKind::Identifier(symbol) if symbol == "loop" => {
            parse_loop(tree, tokens, owning_function_name)
        }
        TokenKind::Identifier(symbol) if symbol == "break" || symbol == "continue" => {
            parse_loop_keyword(symbol, tree, tokens, owning_function_name)
        }
        _ => parse_assign_expression(first_token, tree, tokens, owning_function_name),
    }
}

fn parse_loop(
    tree: &SyntaxTreeBuilder,
    tokens: &mut Lexer<'_>,
    owning_function_name: Option<&str>,
) -> Result<NodeId, ParseError> {
    let name = if let Some(TokenKind::Hash) = tokens.peek_token_kind() {
        tokens.next();
        let name = tokens.expect_next("loop name")?;
        match name.kind {
            TokenKind::Identifier(name) => Some(name),
            other => {
                return Err(ParseError::Unexpected(Token {
                    range: name.range,
                    kind: other,
                }))
            }
        }
    } else {
        None
    };

    let next_token = tokens.expect_next("loop condition or end of line")?;
    let parameters = match &next_token.kind {
        TokenKind::Identifier(sym) if sym == "while" => {
            // loop [#label] while <expr>
            Some(LoopParameters::While(parse_expression(
                tokens.expect_next("loop condition")?,
                tree,
                tokens,
                owning_function_name,
            )?))
        }
        TokenKind::Identifier(sym) if sym == "until" => {
            // loop [#label] until <expr>
            Some(LoopParameters::Until(parse_expression(
                tokens.expect_next("loop condition")?,
                tree,
                tokens,
                owning_function_name,
            )?))
        }
        TokenKind::Identifier(sym) if sym == "for" => {
            Some(parse_for_loop(tree, tokens, owning_function_name)?)
        }
        TokenKind::Comment(_) | TokenKind::EndOfLine => {
            // loop [#label]
            None
        }
        _ => return Err(ParseError::Unexpected(next_token)),
    };

    let body = parse_statements(tree, tokens, owning_function_name)?;
    match tokens.expect_next("end")?.kind {
        TokenKind::Identifier(end) if end == "end" => {}
        other => todo!("unexpected {other:?}"),
    }
    tokens.expect_end_of_line_or_eof()?;

    Ok(tree.loop_node(Loop {
        name,
        parameters,
        body,
    }))
}

fn parse_for_loop(
    tree: &SyntaxTreeBuilder,
    tokens: &mut Lexer<'_>,
    owning_function_name: Option<&str>,
) -> Result<LoopParameters, ParseError> {
    // loop [#label] for x := <initial> [down] to <break when equal> [step <amount>]
    let var_name = tokens.expect_next("variable name")?;
    let var_name = match &var_name.kind {
        TokenKind::Identifier(name) => name.clone(),
        _ => return Err(ParseError::Unexpected(var_name)),
    };

    let mut first_token = tokens.expect_next("assigment or keyword")?;

    let initial_value = if let TokenKind::Assign = &first_token.kind {
        first_token = tokens.expect_next("expression")?;
        let expression = parse_expression(first_token, tree, tokens, owning_function_name)?;

        first_token = tokens.expect_next("to or down to")?;

        Some(expression)
    } else {
        None
    };

    let ascending = match &first_token.kind {
        TokenKind::Identifier(keyword) if keyword == "to" => true,
        TokenKind::Identifier(keyword) if keyword == "down" => {
            first_token = tokens.expect_next("to")?;
            match &first_token.kind {
                TokenKind::Identifier(keyword) if keyword == "to" => false,
                _ => return Err(ParseError::Unexpected(first_token)),
            }
        }
        _ => return Err(ParseError::Unexpected(first_token)),
    };

    let stop_value = parse_expression(
        tokens.expect_next("loop end value")?,
        tree,
        tokens,
        owning_function_name,
    )?;

    let inclusive = match tokens.peek_token_kind() {
        Some(TokenKind::Identifier(symbol)) if symbol == "inclusive" => {
            tokens.next();
            true
        }
        _ => false,
    };

    let step = match tokens.peek_token_kind() {
        Some(TokenKind::Identifier(symbol)) if symbol == "step" => {
            tokens.next();
            Some(parse_expression(
                tokens.expect_next("expression")?,
                tree,
                tokens,
                owning_function_name,
            )?)
        }
        _ => None,
    };

    Ok(LoopParameters::For {
        var_name,
        initial_value,
        ascending,
        inclusive,
        stop_value,
        step,
    })
}

fn parse_loop_keyword(
    keyword: &Symbol,
    tree: &SyntaxTreeBuilder,
    tokens: &mut Lexer<'_>,
    owning_function_name: Option<&str>,
) -> Result<NodeId, ParseError> {
    let name = if let Some(TokenKind::Hash) = tokens.peek_token_kind() {
        tokens.next();
        let name = tokens.expect_next("loop name")?;
        match &name.kind {
            TokenKind::Identifier(name) => Some(name.clone()),
            _ => return Err(ParseError::Unexpected(name)),
        }
    } else {
        None
    };

    if keyword == "break" {
        // break [#label] [expr]
        let value = if matches!(
            tokens.peek_token_kind(),
            Some(TokenKind::EndOfLine | TokenKind::Comment(_))
        ) {
            None
        } else {
            let first_token = tokens.expect_next("end of line or expression")?;
            Some(parse_expression(
                first_token,
                tree,
                tokens,
                owning_function_name,
            )?)
        };
        tokens.expect_end_of_line_or_eof()?;
        Ok(tree.break_node(Break { name, value }))
    } else {
        // continue [#label]
        assert_eq!(keyword, "continue");
        tokens.expect_end_of_line_or_eof()?;
        Ok(tree.continue_node(Continue { name }))
    }
}

fn parse_assign_expression(
    first_token: Token,
    tree: &SyntaxTreeBuilder,
    tokens: &mut Lexer<'_>,
    owning_function_name: Option<&str>,
) -> Result<NodeId, ParseError> {
    // This operator groups differently than most of the other operators. a := b
    // := c should result in `(a := (b := c))`, not `((a := b) := c))`.
    let mut left = parse_logic_expression(first_token, tree, tokens, owning_function_name)?;

    let mut stack = Vec::new();
    while let Some(TokenKind::Assign) = tokens.peek_token_kind() {
        tokens.next();
        stack.push(left);
        let first_token = tokens.expect_next("value to assign")?;
        left = parse_logic_expression(first_token, tree, tokens, owning_function_name)?;
    }

    // Perform the assignments.
    let mut right = left;
    while let Some(left) = stack.pop() {
        right = tree.assign_node(left, right);
    }

    Ok(right)
}

fn parse_logic_expression(
    first_token: Token,
    tree: &SyntaxTreeBuilder,
    tokens: &mut Lexer<'_>,
    owning_function_name: Option<&str>,
) -> Result<NodeId, ParseError> {
    let mut left = parse_comparison_expression(first_token, tree, tokens, owning_function_name)?;

    while let Some(binop_kind) = match tokens.peek_token_kind() {
        Some(TokenKind::Identifier(sym)) if sym == "and" => Some(BinOpKind::LogicalAnd),
        Some(TokenKind::Identifier(sym)) if sym == "or" => Some(BinOpKind::LogicalOr),
        Some(TokenKind::Identifier(sym)) if sym == "xor" => Some(BinOpKind::LogicalXor),
        _ => None,
    } {
        let _op_token = tokens.next();
        let next_token = tokens.expect_next("value to compare against")?;
        let right = parse_comparison_expression(next_token, tree, tokens, owning_function_name)?;
        left = tree.binop_node(binop_kind, left, right);
    }

    Ok(left)
}

fn parse_comparison_expression(
    first_token: Token,
    tree: &SyntaxTreeBuilder,
    tokens: &mut Lexer<'_>,
    owning_function_name: Option<&str>,
) -> Result<NodeId, ParseError> {
    let mut left = parse_convert_expression(first_token, tree, tokens, owning_function_name)?;

    while let Some(TokenKind::Comparison(comparison)) = tokens.peek_token_kind() {
        let comparison = *comparison;
        let _op_token = tokens.next();
        let next_token = tokens.expect_next("value to compare against")?;
        let right = parse_convert_expression(next_token, tree, tokens, owning_function_name)?;
        left = tree.compare_node(comparison, left, right);
    }

    Ok(left)
}

fn parse_convert_expression(
    first_token: Token,
    tree: &SyntaxTreeBuilder,
    tokens: &mut Lexer<'_>,
    owning_function_name: Option<&str>,
) -> Result<NodeId, ParseError> {
    let mut expr = parse_bitwise_expression(first_token, tree, tokens, owning_function_name)?;

    while matches!(tokens.peek_token_kind(), Some(TokenKind::Identifier(sym)) if sym == "as") {
        let _op_token = tokens.next();
        let conversion_type = tokens.expect_next("conversion type")?;
        let kind = if let TokenKind::Identifier(kind) = &conversion_type.kind {
            ValueKind::from(kind.clone())
        } else {
            return Err(ParseError::Unexpected(conversion_type));
        };

        expr = tree.convert_node(expr, kind);
    }

    Ok(expr)
}

fn parse_bitwise_expression(
    first_token: Token,
    tree: &SyntaxTreeBuilder,
    tokens: &mut Lexer<'_>,
    owning_function_name: Option<&str>,
) -> Result<NodeId, ParseError> {
    let mut left = parse_add_sub(first_token, tree, tokens, owning_function_name)?;

    while let Some(binop_kind) = match tokens.peek_token_kind() {
        Some(TokenKind::Ampersand) => Some(BinOpKind::BitwiseAnd),
        Some(TokenKind::Pipe) => Some(BinOpKind::BitwiseOr),
        Some(TokenKind::Caret) => Some(BinOpKind::BitwiseXor),
        Some(TokenKind::ShiftLeft) => Some(BinOpKind::ShiftLeft),
        Some(TokenKind::ShiftRight) => Some(BinOpKind::ShiftRight),
        _ => None,
    } {
        let _op_token = tokens.next();
        let next_token = tokens.expect_next("value to compare against")?;
        let right = parse_add_sub(next_token, tree, tokens, owning_function_name)?;
        left = tree.binop_node(binop_kind, left, right);
    }

    Ok(left)
}

fn parse_add_sub(
    first_token: Token,
    tree: &SyntaxTreeBuilder,
    tokens: &mut Lexer<'_>,
    owning_function_name: Option<&str>,
) -> Result<NodeId, ParseError> {
    enum Kind {
        Add,
        Sub,
    }

    let mut left = parse_mul_div(first_token, tree, tokens, owning_function_name)?;

    loop {
        let kind = match tokens.peek() {
            Some(Ok(token)) if matches!(token.kind, TokenKind::Add) => Kind::Add,
            Some(Ok(token)) if matches!(token.kind, TokenKind::Sub) => Kind::Sub,
            _ => break,
        };
        let _op_token = tokens.next();
        let next_token = tokens.expect_next("value to operate against")?;
        let right = parse_mul_div(next_token, tree, tokens, owning_function_name)?;
        left = match kind {
            Kind::Add => tree.binop_node(BinOpKind::Add, left, right),
            Kind::Sub => tree.binop_node(BinOpKind::Sub, left, right),
        };
    }

    Ok(left)
}

fn parse_mul_div(
    first_token: Token,
    tree: &SyntaxTreeBuilder,
    tokens: &mut Lexer<'_>,
    owning_function_name: Option<&str>,
) -> Result<NodeId, ParseError> {
    enum Kind {
        Multiply,
        Divide,
    }

    let mut left = parse_term(first_token, tree, tokens, owning_function_name)?;

    loop {
        let kind = match tokens.peek() {
            Some(Ok(token)) if matches!(token.kind, TokenKind::Multiply) => Kind::Multiply,
            Some(Ok(token)) if matches!(token.kind, TokenKind::Divide) => Kind::Divide,
            _ => break,
        };
        let _op_token = tokens.next();
        let next_token = tokens.expect_next("value to operate against")?;
        let right = parse_term(next_token, tree, tokens, owning_function_name)?;
        left = match kind {
            Kind::Multiply => tree.binop_node(BinOpKind::Multiply, left, right),
            Kind::Divide => tree.binop_node(BinOpKind::Divide, left, right),
        };
    }

    Ok(left)
}

fn parse_term(
    first_token: Token,
    tree: &SyntaxTreeBuilder,
    tokens: &mut Lexer<'_>,
    owning_function_name: Option<&str>,
) -> Result<NodeId, ParseError> {
    match first_token.kind {
        TokenKind::Identifier(lookup_base) => match lookup_base.as_str() {
            "true" => Ok(tree.boolean(true)),
            "false" => Ok(tree.boolean(false)),
            "not" => {
                let expr = parse_term(
                    tokens.expect_next("expression")?,
                    tree,
                    tokens,
                    owning_function_name,
                )?;
                Ok(tree.not_node(expr, false))
            }
            _ => parse_lookup(lookup_base, tree, tokens, owning_function_name),
        },
        TokenKind::Tilde => {
            let expr = parse_term(
                tokens.expect_next("expression")?,
                tree,
                tokens,
                owning_function_name,
            )?;
            Ok(tree.not_node(expr, true))
        }
        TokenKind::Integer(integer) => Ok(tree.integer(integer)),
        TokenKind::Real(integer) => Ok(tree.real(integer)),
        TokenKind::String(string) => Ok(tree.string(string)),
        TokenKind::Open(BracketType::Paren) => {
            let first_token = tokens.expect_next("expression")?;
            let expression = parse_expression(first_token, tree, tokens, owning_function_name)?;
            let close_paren = tokens.expect_next(")")?;
            if !matches!(close_paren.kind, TokenKind::Close(BracketType::Paren)) {
                todo!("error expected close paren")
            }

            Ok(expression)
        }
        TokenKind::Open(BracketType::Curly) => parse_map(tree, tokens, owning_function_name),
        TokenKind::Open(BracketType::Square) => parse_list(tree, tokens, owning_function_name),
        other => Err(ParseError::Unexpected(Token {
            kind: other,
            range: first_token.range,
        })),
    }
}

fn parse_lookup(
    mut symbol: Symbol,
    tree: &SyntaxTreeBuilder,
    tokens: &mut Lexer<'_>,
    owning_function_name: Option<&str>,
) -> Result<NodeId, ParseError> {
    let mut base = None;
    loop {
        base = match tokens.peek_token_kind() {
            Some(TokenKind::Open(BracketType::Paren)) => {
                // Call
                let _open_paren = tokens.next();
                let mut args = Vec::new();
                let mut next_token = tokens.expect_next("argument or )")?;
                if !matches!(next_token.kind, TokenKind::Close(BracketType::Paren)) {
                    loop {
                        args.push(parse_expression(
                            next_token,
                            tree,
                            tokens,
                            owning_function_name,
                        )?);

                        // Expect either end bracket or comma,
                        let comma_or_end = tokens.expect_next(", or )")?;
                        match comma_or_end.kind {
                            TokenKind::Close(BracketType::Paren) => break,
                            TokenKind::Comma => {}
                            other => todo!("error: {other:?}"),
                        }
                        next_token = tokens.expect_next("argument or )")?;
                    }
                }
                if let Some(base) = base {
                    Some(tree.call(Call::on(base, symbol, args)))
                } else if symbol == "this" || owning_function_name == Some(&symbol) {
                    Some(tree.call(Call::recurse(args)))
                } else {
                    Some(tree.call(Call::global(symbol, args)))
                }
            }
            Some(TokenKind::Open(BracketType::Square)) => {
                // Index
                todo!()
            }
            _ if base.is_none() => {
                // Just a solo identifier literal.
                Some(tree.identifier(symbol))
            }
            _ => break,
        };

        if let Some(TokenKind::Period) = tokens.peek_token_kind() {
            let _period = tokens.next();
            match tokens.expect_next("identifier")?.kind {
                TokenKind::Identifier(sym) => symbol = sym,
                _ => todo!("error: invalid lookup"),
            }
        } else {
            break;
        }
    }

    Ok(base.expect("always at least a base lookup"))
}

fn parse_map(
    tree: &SyntaxTreeBuilder,
    tokens: &mut Lexer<'_>,
    owning_function_name: Option<&str>,
) -> Result<NodeId, ParseError> {
    let mut mappings = Vec::new();
    loop {
        let first_token = tokens.expect_next("key")?;
        if matches!(first_token.kind, TokenKind::Close(BracketType::Curly)) {
            break;
        }

        let key = parse_expression(first_token, tree, tokens, owning_function_name)?;
        let colon = tokens.expect_next(":")?;
        assert!(matches!(colon.kind, TokenKind::Colon));
        let first_token = tokens.expect_next("value")?;
        let value = parse_expression(first_token, tree, tokens, owning_function_name)?;
        mappings.push(Mapping { key, value });

        match tokens.peek_token_kind() {
            Some(TokenKind::Comma) => {
                tokens.next();
            }
            Some(TokenKind::Close(BracketType::Curly)) => {
                // let the beginning of the loop handle this.
            }
            _ => todo!("error parsing map, expected comma or close curly"),
        }
    }

    Ok(tree.map_node(mappings))
}

fn parse_list(
    tree: &SyntaxTreeBuilder,
    tokens: &mut Lexer<'_>,
    owning_function_name: Option<&str>,
) -> Result<NodeId, ParseError> {
    let mut values = Vec::new();
    loop {
        let first_token = tokens.expect_next("list element or ]")?;
        if matches!(first_token.kind, TokenKind::Close(BracketType::Square)) {
            break;
        }

        values.push(parse_expression(
            first_token,
            tree,
            tokens,
            owning_function_name,
        )?);

        match tokens.peek_token_kind() {
            Some(TokenKind::Comma) => {
                tokens.next();
            }
            Some(TokenKind::Close(BracketType::Square)) => {
                // let the beginning of the loop handle this.
            }
            _ => todo!("error parsing map, expected comma or close square"),
        }
    }

    Ok(tree.list_node(values))
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParseError {
    Unexpected(Token),
    UnexpectedEof(String),
    MissingEnd {
        kind: char,
        open_offset: usize,
        error_location: usize,
    },
    ExpectedEndOfLine {
        offset: usize,
        found: Option<Token>,
    },
    String(DecodeStringError),
    Numeric(DecodeNumericError),
}

impl ParseError {
    #[must_use]
    pub fn location(&self) -> Option<Range<usize>> {
        match self {
            ParseError::Unexpected(token) => Some(token.range.clone()),
            ParseError::UnexpectedEof(_) => None,
            ParseError::MissingEnd {
                open_offset,
                error_location,
                ..
            } => Some(*open_offset..error_location + 1),
            ParseError::ExpectedEndOfLine { offset, .. } => Some(*offset..*offset),
            ParseError::Numeric(err) => err.location(),
            ParseError::String(err) => err.location(),
        }
    }
}

impl std::error::Error for ParseError {}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unexpected(token) => {
                write!(f, "unexpected '{token}' at offset {}", token.range.start)
            }
            Self::UnexpectedEof(message) => {
                write!(f, "unexpected end of file: {message}")
            }
            Self::MissingEnd {
                kind,
                open_offset,
                error_location,
            } => {
                write!(f, "missing '{kind}' at {open_offset}..{error_location}")
            }
            Self::ExpectedEndOfLine { offset, found } => {
                if let Some(found) = found {
                    write!(f, "expected end of line at {offset}, but found {found}")
                } else {
                    write!(f, "expected end of line at {offset}")
                }
            }
            Self::String(err) => write!(f, "error parsing string literal: {err}"),
            Self::Numeric(err) => write!(f, "error parsing numeric literal: {err}"),
        }
    }
}

impl From<DecodeNumericError> for ParseError {
    fn from(err: DecodeNumericError) -> Self {
        Self::Numeric(err)
    }
}

impl From<DecodeStringError> for ParseError {
    fn from(err: DecodeStringError) -> Self {
        Self::String(err)
    }
}

#[test]
fn string_parsing() {
    use budvm::DynamicValue;
    assert_eq!(
        Lexer::new(r#""hello""#)
            .collect::<Result<Vec<_>, _>>()
            .unwrap(),
        vec![Token::new(TokenKind::String(String::from("hello")), 0..7)]
    );
    let string = String::from("\"\\\t\r\n\u{2764}test");
    let source = string.to_source().unwrap();
    assert_eq!(source, r#""\"\\\t\r\n\u{2764}test""#);
    assert_eq!(
        Lexer::new(source.as_str())
            .collect::<Result<Vec<_>, _>>()
            .unwrap(),
        vec![Token::new(TokenKind::String(string), 0..source.len())]
    );
    assert!(matches!(
        Lexer::new(r#"""#)
            .collect::<Result<Vec<_>, _>>()
            .unwrap_err(),
        ParseError::String(DecodeStringError::EndQuoteNotFound)
    ));
    assert!(matches!(
        Lexer::new(r#""\"#)
            .collect::<Result<Vec<_>, _>>()
            .unwrap_err(),
        ParseError::String(DecodeStringError::EndQuoteNotFound)
    ));
}

#[test]
fn number_parsing() {
    let tokens = Lexer::new(r#"0 0.0 -1 -1.0 1_000 -1_000.000_1"#)
        .collect::<Result<Vec<_>, _>>()
        .unwrap();

    assert_eq!(tokens.len(), 6);
    assert_eq!(tokens[0].kind, TokenKind::Integer(0));
    assert_eq!(tokens[1].kind, TokenKind::Real(0.0));
    assert_eq!(tokens[2].kind, TokenKind::Integer(-1));
    assert_eq!(tokens[3].kind, TokenKind::Real(-1.0));
    assert_eq!(tokens[4].kind, TokenKind::Integer(1_000));
    assert_eq!(tokens[5].kind, TokenKind::Real(-1_000.000_1));
}
