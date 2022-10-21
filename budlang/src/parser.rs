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

use crate::{
    ast::{BinOpKind, Call, CodeUnit, Function, If, Mapping, NodeId, SyntaxTreeBuilder},
    symbol::Symbol,
    vm::Comparison,
};

#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    kind: TokenKind,
    range: Range<usize>,
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
enum TokenKind {
    Identifier(Symbol),
    Integer(i64),
    Real(f64),
    String(String),
    Assign,
    Comparison(Comparison),
    Not,
    Add,
    Sub,
    Multiply,
    Divide,
    Open(BracketType),
    Close(BracketType),
    EndOfLine,
    Comma,
    Period,
    Colon,
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
            TokenKind::Unknown(token) => Display::fmt(token, f),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
enum BracketType {
    Paren,
    Square,
    Curly,
}

struct DoublePeekable<I>
where
    I: Iterator,
{
    iter: I,
    peeked: Peeked<I::Item>,
}

impl<I> DoublePeekable<I>
where
    I: Iterator,
{
    fn peek(&mut self) -> Option<&I::Item> {
        if self.peeked.len() < 1 {
            if let Some(next_value) = self.iter.next() {
                self.peeked = Peeked(Some(PeekedData::One(next_value)));
            } else {
                return None;
            }
        }

        self.peeked.nth(0)
    }

    fn peek_second(&mut self) -> Option<&I::Item> {
        if self.peeked.len() < 2 {
            if let Some(next_value) = self.iter.next() {
                self.peeked.0 = match self.peeked.0.take() {
                    None => match self.iter.next() {
                        Some(second_value) => Some(PeekedData::Two(next_value, second_value)),
                        None => Some(PeekedData::One(next_value)),
                    },
                    Some(PeekedData::One(existing_value)) => {
                        Some(PeekedData::Two(existing_value, next_value))
                    }
                    Some(PeekedData::Two(first, second)) => Some(PeekedData::Two(first, second)),
                }
            }
        }

        self.peeked.nth(1)
    }
}

impl<I> Iterator for DoublePeekable<I>
where
    I: Iterator,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(peeked) = self.peeked.next() {
            Some(peeked)
        } else {
            self.iter.next()
        }
    }
}

struct Peeked<T>(Option<PeekedData<T>>);

enum PeekedData<T> {
    One(T),
    Two(T, T),
}

impl<T> Peeked<T> {
    const fn len(&self) -> usize {
        match &self.0 {
            None => 0,
            Some(PeekedData::One(_)) => 1,
            Some(PeekedData::Two(_, _)) => 2,
        }
    }

    fn nth(&self, index: usize) -> Option<&T> {
        match &self.0 {
            None => None,
            Some(PeekedData::One(value)) => {
                if index == 0 {
                    Some(value)
                } else {
                    None
                }
            }
            Some(PeekedData::Two(first, second)) => {
                if index == 0 {
                    Some(first)
                } else if index == 1 {
                    Some(second)
                } else {
                    None
                }
            }
        }
    }
}

impl<T> Iterator for Peeked<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.0.take() {
            None => None,
            Some(PeekedData::One(value)) => Some(value),
            Some(PeekedData::Two(first, second)) => {
                self.0 = Some(PeekedData::One(second));
                Some(first)
            }
        }
    }
}

struct Lexer<'a> {
    source: &'a str,
    chars: DoublePeekable<CharIndices<'a>>,
    peeked_token: Option<Result<Token, ParseError>>,
}

impl<'a> Lexer<'a> {
    fn new(source: &'a str) -> Self {
        Self {
            source,
            chars: DoublePeekable {
                iter: source.char_indices(),
                peeked: Peeked(None),
            },
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
                    let mut end = offset;
                    while self
                        .chars
                        .peek()
                        .map_or(false, |(_, char)| char.is_numeric())
                    {
                        end = self.chars.next().expect("just peeked").0;
                    }

                    // If we have a period and another numeric, this is a floating point number.
                    if self.chars.peek().map_or(false, |(_, ch)| *ch == '.')
                        && self
                            .chars
                            .peek_second()
                            .map_or(false, |(_, ch)| ch.is_numeric())
                    {
                        // Skip the decimal
                        self.chars.next();
                        while self
                            .chars
                            .peek()
                            .map_or(false, |(_, char)| char.is_numeric())
                        {
                            end = self.chars.next().expect("just peeked").0;
                        }

                        let value = self.source[offset..=end].parse::<f64>().unwrap();

                        return Some(Ok(Token {
                            kind: TokenKind::Real(value),
                            range: offset..end + 1,
                        }));
                    }

                    let value = self.source[offset..=end].parse::<i64>().unwrap();

                    Some(Ok(Token {
                        kind: TokenKind::Integer(value),
                        range: offset..end + 1,
                    }))
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
                    Some(Ok(Token::at_offset(TokenKind::Divide, offset)))
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
                    if matches!(self.chars.peek().map(|(_, ch)| *ch), Some('=')) {
                        self.chars.next();

                        Some(Ok(Token::new(
                            TokenKind::Comparison(Comparison::LessThanOrEqual),
                            offset..offset + 2,
                        )))
                    } else {
                        Some(Ok(Token::at_offset(
                            TokenKind::Comparison(Comparison::LessThan),
                            offset,
                        )))
                    }
                }
                Some((offset, char)) if char == '>' => {
                    if matches!(self.chars.peek().map(|(_, ch)| *ch), Some('=')) {
                        self.chars.next();

                        Some(Ok(Token::new(
                            TokenKind::Comparison(Comparison::GreaterThanOrEqual),
                            offset..offset + 2,
                        )))
                    } else {
                        Some(Ok(Token::at_offset(
                            TokenKind::Comparison(Comparison::GreaterThan),
                            offset,
                        )))
                    }
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
        assert!(matches!(end_of_line.kind, TokenKind::EndOfLine)); // TODO error trailing stuff
        Ok(())
    }

    fn expect_end_of_line_or_eof(&mut self) -> Result<(), ParseError> {
        let end_of_line = match self.next().transpose()? {
            Some(token) => token,
            None => return Ok(()),
        };
        assert!(matches!(end_of_line.kind, TokenKind::EndOfLine)); // TODO error trailing stuff
        Ok(())
    }

    fn read_string(&mut self, start_offset: usize) -> Result<Token, ParseError> {
        let mut string = String::new();
        let mut end_offset = start_offset + 1;
        loop {
            let ch = self.chars.next().map(|r| r.1);
            if ch.is_some() {
                end_offset += 1;
            }

            match ch {
                Some('"') => {
                    // Final quote
                    break;
                }
                Some('\\') => {
                    end_offset += 1;
                    // Escaped character
                    let unescaped = match self.chars.next() {
                        Some((_, 't')) => '\t',
                        Some((_, 'r')) => '\r',
                        Some((_, 'n')) => '\n',
                        Some((_, 'u')) => {
                            end_offset += 1;
                            match self.chars.next().map(|r| r.1) {
                                Some('{') => {}
                                _ => {
                                    todo!("add error")
                                }
                            }

                            let mut codepoint = 0_u32;
                            for (offset, char) in &mut self.chars {
                                end_offset = offset + 1;
                                let nibble_value = match char {
                                    '}' => {
                                        break;
                                    }
                                    ch if ch.is_numeric() => u32::from(ch) - u32::from(b'0'),
                                    ch if ('a'..='f').contains(&ch) => {
                                        u32::from(ch) - u32::from(b'a')
                                    }
                                    ch if ('A'..='F').contains(&ch) => {
                                        u32::from(ch) - u32::from(b'A')
                                    }
                                    _ => {
                                        return Err(ParseError::Unexpected(Token {
                                            kind: TokenKind::Unknown(char),
                                            range: offset..offset + 1,
                                        }))
                                    }
                                };

                                codepoint <<= 4;
                                codepoint |= nibble_value;
                            }

                            if let Some(ch) = char::from_u32(codepoint) {
                                ch
                            } else {
                                todo!("handle invalid unicode")
                            }
                        }
                        Some((_, other)) => other,
                        None => {
                            return Err(ParseError::UnexpectedEof(String::from(
                                "expected escape character",
                            )))
                        }
                    };

                    string.push(unescaped);
                }
                Some(ch) => {
                    string.push(ch);
                }
                None => {
                    return Err(ParseError::MissingEnd {
                        kind: '"',
                        open_offset: start_offset,
                        error_location: end_offset,
                    })
                }
            }
        }

        Ok(Token::new(
            TokenKind::String(string),
            start_offset..end_offset,
        ))
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

            TokenKind::EndOfLine => {}
            _ => {
                let expression = parse_expression(token, &init_tree, &mut tokens, None)?;
                statements.push(expression);
            }
        }
    }

    let mut unit = CodeUnit::from_tree(statements, init_tree);
    for function in functions {
        unit = unit.with(
            function.name().expect("all functions are named").clone(),
            function,
        );
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
            TokenKind::EndOfLine => {
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

            match tokens.peek_token_kind() {
                Some(TokenKind::Identifier(sym)) if sym == "else" => {
                    let _else_token = tokens.next();
                    tokens.expect_end_of_line()?;
                    let else_block = parse_statements(tree, tokens, owning_function_name)?;
                    if_op = if_op.with_else(else_block);
                }
                _ => {}
            }
            match tokens.expect_next("end")?.kind {
                TokenKind::Identifier(end) if end == "end" => {}
                other => todo!("unexpected {other:?}"),
            }
            tokens.expect_end_of_line_or_eof()?;

            Ok(tree.if_node(if_op))
        }
        _ => parse_assign_expression(first_token, tree, tokens, owning_function_name),
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
    let mut left = parse_comparison_expression(first_token, tree, tokens, owning_function_name)?;

    let mut stack = Vec::new();
    while let Some(TokenKind::Assign) = tokens.peek_token_kind() {
        tokens.next();
        stack.push(left);
        let first_token = tokens.expect_next("value to assign")?;
        left = parse_comparison_expression(first_token, tree, tokens, owning_function_name)?;
    }

    // Perform the assignments.
    let mut right = left;
    while let Some(left) = stack.pop() {
        right = tree.assign_node(left, right);
    }

    Ok(right)
}

fn parse_comparison_expression(
    first_token: Token,
    tree: &SyntaxTreeBuilder,
    tokens: &mut Lexer<'_>,
    owning_function_name: Option<&str>,
) -> Result<NodeId, ParseError> {
    let mut left = parse_add_sub(first_token, tree, tokens, owning_function_name)?;

    while let Some(TokenKind::Comparison(comparison)) = tokens.peek_token_kind() {
        let comparison = *comparison;
        let _op_token = tokens.next();
        let next_token = tokens.expect_next("value to compare against")?;
        let right = parse_add_sub(next_token, tree, tokens, owning_function_name)?;
        left = tree.compare_node(comparison, left, right);
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
            _ => parse_lookup(lookup_base, tree, tokens, owning_function_name),
        },
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
        }
    }
}

#[test]
fn string_parsing() {
    use crate::vm::DynamicValue;
    assert_eq!(
        Lexer::new(r#""hello""#)
            .collect::<Result<Vec<_>, _>>()
            .unwrap(),
        vec![Token::new(TokenKind::String(String::from("hello")), 0..7)]
    );
    let string = String::from("\t\r\n\u{2764}test");
    let source = string.to_source().unwrap();
    assert_eq!(source, r#""\t\r\n\u{2764}test""#);
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
        ParseError::MissingEnd {
            kind: '"',
            open_offset: 0,
            error_location: 1,
        }
    ));
    assert!(matches!(
        Lexer::new(r#""\"#)
            .collect::<Result<Vec<_>, _>>()
            .unwrap_err(),
        ParseError::UnexpectedEof(_)
    ));
}
