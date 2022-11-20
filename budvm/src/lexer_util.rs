// We use the Range type which doesn't allow this, and it's not worth making a
// helper function to appease clippy.
#![allow(clippy::range_plus_one)]
//! Utilities shared between Bud Assembly and Bud.
use std::{
    borrow::Cow,
    fmt::Display,
    num::{ParseFloatError, ParseIntError},
    ops::Range,
    str::CharIndices,
};

/// An iterator adapter thatallows peeking up to two positions ahead.
pub struct DoublePeekable<I>
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
    /// Returns a new instance wrapping `iter`.
    pub fn new(iter: I) -> Self {
        Self {
            iter,
            peeked: Peeked(None),
        }
    }

    /// Returns a reference to the next item the iterator will return, if
    /// present.
    pub fn peek(&mut self) -> Option<&I::Item> {
        if self.peeked.len() < 1 {
            if let Some(next_value) = self.iter.next() {
                self.peeked = Peeked(Some(PeekedData::One(next_value)));
            } else {
                return None;
            }
        }

        self.peeked.nth(0)
    }

    /// Reterns a reference to the second item the iterator will return, if
    /// present.
    pub fn peek_second(&mut self) -> Option<&I::Item> {
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

/// An error while decoding the contents of a string literal.
#[derive(Eq, PartialEq, Debug, Clone)]
pub enum DecodeStringError {
    /// An invalid hexadecimal character was encountered at the given offset.
    InvalidHexadecimalCharacter(usize),
    /// An invalid unicode codepoint was encountered.
    InvalidUnicodeCodepoint {
        /// The decoded codepoint.
        codepoint: u32,
        /// The range of the escape sequence.
        range: Range<usize>,
    },
    /// An invalid character was encountered while parsing a unicode escape.
    InvalidUnicodeEscape(usize),
    /// The end double-quote character was not found.
    EndQuoteNotFound,
}

impl DecodeStringError {
    #[must_use]
    /// Returns the location of the error within the original source.
    pub fn location(&self) -> Option<Range<usize>> {
        match self {
            DecodeStringError::InvalidUnicodeEscape(offset)
            | DecodeStringError::InvalidHexadecimalCharacter(offset) => Some(*offset..*offset + 1),
            DecodeStringError::InvalidUnicodeCodepoint { range, .. } => Some(range.clone()),

            DecodeStringError::EndQuoteNotFound => None,
        }
    }
}

impl Display for DecodeStringError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DecodeStringError::InvalidHexadecimalCharacter(_) => {
                f.write_str("invalid hexadecimal character")
            }
            DecodeStringError::InvalidUnicodeCodepoint { codepoint, .. } => {
                write!(f, "{codepoint} is an invalid unicode codepoint")
            }
            DecodeStringError::InvalidUnicodeEscape(_) => {
                f.write_str("invalid unicode escape format. expected \\u{FFEF}")
            }
            DecodeStringError::EndQuoteNotFound => f.write_str("missing end quote"),
        }
    }
}

/// The result of decoding a string literal's contents.
pub struct StringLiteral {
    /// The decoded contents of the literal.
    pub contents: String,
    /// The offset of the end quote in the original string.
    pub end_quote_offset: usize,
}

/// Decodes a string literal with escape sequences used by Bud and Bud Assembly.
pub fn decode_string_literal_contents(
    mut chars: &mut impl Iterator<Item = (usize, char)>,
    start_offset: usize,
) -> Result<StringLiteral, DecodeStringError> {
    let mut string = String::new();
    let mut end_offset = start_offset + 1;
    loop {
        let ch = chars.next().map(|r| r.1);
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
                let unescaped = match chars.next() {
                    Some((_, 't')) => '\t',
                    Some((_, 'r')) => '\r',
                    Some((_, 'n')) => '\n',
                    Some((_, 'u')) => {
                        let escape_start = end_offset;
                        end_offset += 1;
                        match chars.next().map(|r| r.1) {
                            Some('{') => {}
                            _ => return Err(DecodeStringError::InvalidUnicodeEscape(end_offset)),
                        }

                        let mut codepoint = 0_u32;
                        for (offset, char) in &mut chars {
                            end_offset = offset + 1;
                            let nibble_value = match char {
                                '}' => {
                                    break;
                                }
                                ch if ch.is_numeric() => u32::from(ch) - u32::from(b'0'),
                                ch if ('a'..='f').contains(&ch) => u32::from(ch) - u32::from(b'a'),
                                ch if ('A'..='F').contains(&ch) => u32::from(ch) - u32::from(b'A'),
                                _ => {
                                    return Err(DecodeStringError::InvalidHexadecimalCharacter(
                                        offset,
                                    ))
                                }
                            };

                            codepoint <<= 4;
                            codepoint |= nibble_value;
                        }

                        if let Some(ch) = char::from_u32(codepoint) {
                            ch
                        } else {
                            return Err(DecodeStringError::InvalidUnicodeCodepoint {
                                codepoint,
                                range: escape_start..end_offset,
                            });
                        }
                    }
                    Some((_, other)) => other,
                    None => return Err(DecodeStringError::EndQuoteNotFound),
                };

                string.push(unescaped);
            }
            Some(ch) => {
                string.push(ch);
            }
            None => return Err(DecodeStringError::EndQuoteNotFound),
        }
    }

    Ok(StringLiteral {
        contents: string,
        end_quote_offset: end_offset - 1,
    })
}

/// Decodes all valid numeric literal formats supported by Bud and Bud Assembly.
pub fn decode_numeric_literal(
    chars: &mut DoublePeekable<CharIndices<'_>>,
    source: &str,
    start_offset: usize,
) -> Result<NumericLiteral, DecodeNumericError> {
    let mut end = start_offset;
    while chars
        .peek()
        .map_or(false, |(_, char)| char.is_numeric() || *char == '_')
    {
        end = chars.next().expect("just peeked").0;
    }

    // If we have a period and another numeric, this is a floating point number.
    if chars.peek().map_or(false, |(_, ch)| *ch == '.')
        && chars.peek_second().map_or(false, |(_, ch)| ch.is_numeric())
    {
        // Skip the decimal
        chars.next();
        while chars
            .peek()
            .map_or(false, |(_, char)| char.is_numeric() || *char == '_')
        {
            end = chars.next().expect("just peeked").0;
        }

        let source = &source[start_offset..=end];
        let source = if source.find('_').is_some() {
            Cow::Owned(source.replace('_', ""))
        } else {
            Cow::Borrowed(source)
        };

        let value = source.parse::<f64>()?;

        return Ok(NumericLiteral {
            contents: Numeric::Real(value),
            last_offset: end,
        });
    }

    let source = &source[start_offset..=end];
    let source = if source.find('_').is_some() {
        Cow::Owned(source.replace('_', ""))
    } else {
        Cow::Borrowed(source)
    };
    let value = source.parse::<i64>()?;
    Ok(NumericLiteral {
        contents: Numeric::Integer(value),
        last_offset: end,
    })
}

/// A parsed numeric literal.
pub struct NumericLiteral {
    /// The value that was parsed.
    pub contents: Numeric,
    /// The position of the last character that was part of this literal value.
    pub last_offset: usize,
}

/// A numeric literal.
pub enum Numeric {
    /// A signed integer value.
    Integer(i64),
    /// A real number (floating point).
    Real(f64),
}

/// An error while decoding a numeric literal.
#[derive(Eq, PartialEq, Debug, Clone)]
pub enum DecodeNumericError {
    /// An error from parsing a float value.
    Float(ParseFloatError),
    /// An error from parsing an integer value.
    Integer(ParseIntError),
}

impl DecodeNumericError {
    /// Returns the location of the error within the original source.
    #[must_use]
    pub fn location(&self) -> Option<Range<usize>> {
        None // TODO
    }
}

impl Display for DecodeNumericError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DecodeNumericError::Float(err) => Display::fmt(err, f),
            DecodeNumericError::Integer(err) => Display::fmt(err, f),
        }
    }
}

impl From<ParseFloatError> for DecodeNumericError {
    fn from(err: ParseFloatError) -> Self {
        Self::Float(err)
    }
}

impl From<ParseIntError> for DecodeNumericError {
    fn from(err: ParseIntError) -> Self {
        Self::Integer(err)
    }
}
