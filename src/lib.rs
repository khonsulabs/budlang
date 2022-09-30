#![forbid(unsafe_code)]

use std::fmt::Display;

pub mod ast;
pub mod parser;
pub mod symbol;
pub mod vm;

#[derive(Debug)]
pub enum Error<'a, Env, ReturnType> {
    Parse(parser::ParseError),
    Compilation(ast::CompilationError),
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

#[cfg(test)]
mod tests;
