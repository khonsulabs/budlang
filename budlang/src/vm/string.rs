use std::{
    cmp::Ordering,
    fmt::{Display, Write},
    hash::Hash,
};

use crate::{
    symbol::Symbol,
    vm::{DynamicValue, FaultKind, PoppedValues, Value, ValueKind},
};

/// A [`Display`] implementor that converts a string value to its literal form
/// including wrapping double quotes.
#[must_use]
pub struct StringLiteralDisplay<'a>(&'a str);

impl<'a> StringLiteralDisplay<'a> {
    /// Returns a new instance for the provided string.
    pub fn new(value: &'a str) -> Self {
        Self(value)
    }
}

impl<'a> Display for StringLiteralDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('"')?;
        for ch in self.0.chars() {
            match ch {
                ch if ch.is_alphanumeric() || ch == ' ' || ch.is_ascii_punctuation() => {
                    f.write_char(ch)?;
                }
                '\t' => {
                    f.write_str("\\t")?;
                }
                '\r' => {
                    f.write_str("\\r")?;
                }
                '\n' => {
                    f.write_str("\\n")?;
                }
                other => {
                    let codepoint = u32::from(other);
                    write!(f, "\\u{{{codepoint:x}}}").expect("error writing codepoint");
                }
            }
        }
        f.write_char('"')
    }
}

impl DynamicValue for String {
    fn is_truthy(&self) -> bool {
        !self.is_empty()
    }

    fn kind(&self) -> &'static str {
        "String"
    }

    fn partial_eq(&self, other: &Value) -> Option<bool> {
        other.as_dynamic::<Self>().map(|other| self == other)
    }

    fn partial_cmp(&self, other: &Value) -> Option<Ordering> {
        other.as_dynamic::<Self>().map(|other| self.cmp(other))
    }

    fn call(&self, name: &Symbol, args: &mut PoppedValues<'_>) -> Result<Value, FaultKind> {
        match name.as_str() {
            "replace" => {
                let needle = args.next_argument("pattern")?;
                let needle = needle.as_dynamic::<Self>().ok_or_else(|| {
                    FaultKind::invalid_type(
                        "search pattern must be a string. Found `@received-value` (@received-kind)",
                        needle.clone(),
                    )
                })?;
                let replacement = args.next_argument("replacement")?;
                let replacement = replacement.as_dynamic::<Self>().ok_or_else(|| {
                    FaultKind::invalid_type(
                        "replacement must be a string. Found `@received-value` (@received-kind)",
                        replacement.clone(),
                    )
                })?;

                args.verify_empty()?;

                Ok(Value::dynamic(self.replace(needle, replacement)))
            }
            _ => Err(FaultKind::UnknownFunction {
                kind: ValueKind::Dynamic(self.kind()),
                name: name.clone(),
            }),
        }
    }

    fn to_source(&self) -> Option<String> {
        Some(StringLiteralDisplay::new(self).to_string())
    }

    fn checked_add(&self, other: &Value, _is_reverse: bool) -> Result<Option<Value>, FaultKind> {
        if let Some(other) = other.as_dynamic::<Self>() {
            // We can ignore is_reverse because when both lhs and rhs are the
            // same dynamic type, we never return Ok(None), so the reverse
            // operation will not be attempted.
            let combined = [self.as_str(), other.as_str()].join("");
            Ok(Some(Value::dynamic(combined)))
        } else {
            Ok(None)
        }
    }

    fn checked_mul(&self, other: &Value, _is_reverse: bool) -> Result<Option<Value>, FaultKind> {
        if let Some(repeat) = other
            .as_i64()
            .and_then(|repeat| usize::try_from(repeat).ok())
        {
            if let Some(total_length) = self.len().checked_mul(repeat) {
                let mut repeated = String::with_capacity(total_length);
                for _ in 0..repeat {
                    repeated.push_str(self);
                }
                return Ok(Some(Value::dynamic(repeated)));
            }
        }

        Ok(None)
    }

    fn hash<H>(&self, state: &mut H) -> bool
    where
        H: std::hash::Hasher,
    {
        Hash::hash(self, state);
        true
    }
}
