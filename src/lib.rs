#![doc = include_str!(".crate-docs.md")]
#![forbid(unsafe_code)]
#![warn(
    clippy::cargo,
    missing_docs,
    clippy::pedantic,
    future_incompatible,
    rust_2018_idioms
)]
#![allow(
    clippy::option_if_let_else,
    clippy::module_name_repetitions,
    clippy::missing_errors_doc
)]

use std::fmt::Display;

/// The abstract syntax tree Bud uses.
pub mod ast;
pub mod ir;
// mod optimizer;
/// The interface for parsing Bud code.
pub mod parser;
/// An "interned" string-like type used for identifiers in Bud.
pub mod symbol;
/// The Bud virtual machine.
pub mod vm;

/// All errors that can be encountered executing Bud code.
#[derive(Debug)]
pub enum Error<'a, Env, ReturnType> {
    /// An error occurred while parsing the source code.
    Parse(parser::ParseError),
    /// An error occurred while compiling [`CodeUnit`](ast::CodeUnit).
    Compilation(ast::CompilationError),
    /// A fault occurred while running the virtual machine.
    Fault(vm::Fault<'a, Env, ReturnType>),
}

impl<'a, Env, ReturnType> std::error::Error for Error<'a, Env, ReturnType>
where
    Env: std::fmt::Debug,
    ReturnType: std::fmt::Debug,
{
}

impl<'a, Env, ReturnType> Display for Error<'a, Env, ReturnType> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Parse(err) => write!(f, "parse error: {err}"),
            Error::Compilation(err) => write!(f, "compilation error: {err}"),
            Error::Fault(err) => write!(f, "vm fault: {err}"),
        }
    }
}

impl<'a, Env, ReturnType> From<parser::ParseError> for Error<'a, Env, ReturnType> {
    fn from(err: parser::ParseError) -> Self {
        Self::Parse(err)
    }
}

impl<'a, Env, ReturnType> From<ast::CompilationError> for Error<'a, Env, ReturnType> {
    fn from(err: ast::CompilationError) -> Self {
        Self::Compilation(err)
    }
}

impl<'a, Env, ReturnType> From<vm::Fault<'a, Env, ReturnType>> for Error<'a, Env, ReturnType> {
    fn from(fault: vm::Fault<'a, Env, ReturnType>) -> Self {
        Self::Fault(fault)
    }
}

impl<'a, Env, ReturnType> From<vm::FaultKind> for Error<'a, Env, ReturnType> {
    fn from(fault: vm::FaultKind) -> Self {
        Self::Fault(vm::Fault::from(fault))
    }
}

#[cfg(test)]
mod tests;
