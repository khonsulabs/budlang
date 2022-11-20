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

use std::{
    borrow::Cow,
    env,
    fmt::Display,
    ops::{Deref, DerefMut, Range},
};

use budvm::{
    ir::{LinkError, Scope},
    Environment, Fault, FaultKind, FromStack, NativeFunction, Symbol, Value,
};

pub use budvm as vm;
use vm::{Function, VirtualMachine};

use crate::parser::parse;

/// The abstract syntax tree Bud uses.
pub mod ast;

// mod optimizer;
/// The interface for parsing Bud code.
pub mod parser;

/// All errors that can be encountered executing Bud code.
#[derive(Debug, PartialEq)]
pub enum Error<'a, Env, ReturnType> {
    /// An error occurred while parsing the source code.
    Parse(parser::ParseError),
    /// An error occurred while compiling [`CodeUnit`](ast::CodeUnit).
    Compilation(ast::CompilationError),
    /// A fault occurred while running the virtual machine.
    Vm(budvm::Error<'a, Env, ReturnType>),
}

impl<Env, ReturnType> Clone for Error<'static, Env, ReturnType> {
    fn clone(&self) -> Self {
        match self {
            Self::Parse(arg0) => Self::Parse(arg0.clone()),
            Self::Compilation(arg0) => Self::Compilation(arg0.clone()),
            Self::Vm(arg0) => Self::Vm(arg0.clone()),
        }
    }
}

impl<'a, Env, ReturnType> Error<'a, Env, ReturnType> {
    /// Asserts that this error does not contain a paused execution. Returns an
    /// [`Error`] instance with a `'static` lifetime.
    ///
    /// # Panics
    ///
    /// If this contains [`Error::Vm`] with a kind of
    /// [`FaultOrPause::Pause`](budvm::FaultOrPause), this function will panic.
    /// Paused execution mutably borrows the virtual machine's state.
    #[must_use]
    pub fn expect_no_pause(self) -> Error<'static, Env, ReturnType> {
        match self {
            Error::Parse(parse) => Error::Parse(parse),
            Error::Compilation(compilation) => Error::Compilation(compilation),
            Error::Vm(err) => Error::Vm(err.expect_no_pause()),
        }
    }

    /// Returns the source range for this error, if available.
    #[must_use]
    pub fn location(&self) -> Option<Range<usize>> {
        match self {
            Error::Parse(err) => err.location(),
            Error::Compilation(_) | Error::Vm(_) => None,
        }
    }
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
            Error::Vm(err) => write!(f, "vm error: {err}"),
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

impl<'a, Env, ReturnType> From<LinkError> for Error<'a, Env, ReturnType> {
    fn from(err: LinkError) -> Self {
        Self::Vm(budvm::Error::from(err))
    }
}

impl<'a, Env, ReturnType> From<budvm::Error<'a, Env, ReturnType>> for Error<'a, Env, ReturnType> {
    fn from(fault: budvm::Error<'a, Env, ReturnType>) -> Self {
        Self::Vm(fault)
    }
}

impl<'a, Env, ReturnType> From<Fault<'a, Env, ReturnType>> for Error<'a, Env, ReturnType> {
    fn from(fault: Fault<'a, Env, ReturnType>) -> Self {
        Self::Vm(budvm::Error::Fault(fault))
    }
}
impl<'a, Env, ReturnType> From<FaultKind> for Error<'a, Env, ReturnType> {
    fn from(fault: FaultKind) -> Self {
        Self::Vm(budvm::Error::from(fault))
    }
}

/// A Bud virtual machine instance.
///
/// Each instance of this type has its own sandboxed environment. Its stack
/// space, function declarations, and [`Environment`] are unique from all other
/// instances of Bud with the exception that [`Symbol`]s are tracked globally.
pub struct Bud<Env>(VirtualMachine<Env>);

impl Bud<()> {
    /// Returns a default instance of Bud with no custom [`Environment`]
    #[must_use]
    pub fn empty() -> Self {
        Self::default_for(())
    }
}

impl<Env> Bud<Env>
where
    Env: Environment,
{
    /// Returns a new instance with the provided virtual machine.
    pub const fn new(vm: VirtualMachine<Env>) -> Self {
        Self(vm)
    }

    /// Returns a new instance with the provided environment.
    pub fn default_for(environment: Env) -> Self {
        Self::new(VirtualMachine::default_for(environment))
    }

    /// Registers a function with the provided name and returns self. This is a
    /// builder-style function.
    #[must_use]
    pub fn with_function(mut self, function: Function) -> Self {
        self.define_function(function);
        self
    }

    /// Registers a function with the provided name and returns self. This is a
    /// builder-style function.
    #[must_use]
    pub fn with_native_function(
        mut self,
        name: impl Into<Symbol>,
        function: impl NativeFunction + 'static,
    ) -> Self {
        self.define_native_function(name, function);
        self
    }

    /// Evaluates `source` interactively and returns the provided result.
    ///
    /// Bud is a compiled language. When compiling a chunk of source code, it is
    /// organized into a series of declarations. If any non-declaration
    /// statements are encountered, they are gathered into an initialization
    /// function.
    ///
    /// The difference between this function and [`Bud::run_source()`] is that
    /// the initialization function will be compiled with existing knowledge of
    /// any local variables defined in previous code evaluated on this instance.
    /// [`Bud::run_source()`] always executes the initialization code in its own
    /// environment, preventing persisting variables across invoations.
    pub fn evaluate<'a, ReturnType: FromStack>(
        &'a mut self,
        source: &str,
    ) -> Result<ReturnType, Error<'a, Env, ReturnType>> {
        let previous_variable_count = self.persistent_variables().len();
        let unit = parse(source)?.compile(&mut self.0)?;
        for function in unit.vtable {
            if env::var("PRINT_IR").is_ok() {
                println!("function {}", function.name);
            }
            function.link_into(&mut self.0)?;
        }

        if let Some(init) = &unit.init {
            if env::var("PRINT_IR").is_ok() {
                println!("function __init");
            }

            let function = init.link(&mut self.0)?;
            let variable_count = self.persistent_variables().len();
            let new_variables = variable_count - previous_variable_count;
            if new_variables > 0 {
                self.stack.grow_by(new_variables)?;
            }

            self.run_interactive(Cow::Owned(function.code), variable_count, false)
                .map_err(Error::from)
        } else {
            ReturnType::from_value(Value::Void).map_err(Error::from)
        }
    }

    /// Compiles `source` and executes it in this context. Any declarations will
    /// persist in the virtual machine, but all local variables will be removed
    /// from the stack upon completion.
    ///
    /// To enable persisting of local variables, use [`Bud::evaluate()`].
    pub fn run_source<Output: FromStack>(
        &mut self,
        source: &str,
    ) -> Result<Output, Error<'_, Env, Output>> {
        let unit = parse(source)?;
        unit.compile(&mut self.0)?
            .load_into(self)
            .map_err(Error::from)
    }
}

impl<Env> Deref for Bud<Env> {
    type Target = VirtualMachine<Env>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<Env> DerefMut for Bud<Env> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[cfg(test)]
mod tests;
