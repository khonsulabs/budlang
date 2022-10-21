use std::{
    borrow::Cow,
    collections::{hash_map::Entry, HashMap},
    io::{stdin, Read},
    path::PathBuf,
};

use ariadne::{Label, Report, ReportKind};
use budlang::{
    parser::ParseError,
    vm::{Bud, Value},
    Error,
};
use clap::Parser;
use crossterm::tty::IsTty;
use reedline::{
    FileBackedHistory, Prompt, PromptEditMode, PromptHistorySearch, PromptHistorySearchStatus,
    PromptViMode, Reedline, Signal, ValidationResult, Validator,
};

#[derive(Parser, Debug)]
struct Args {
    #[clap(short('f'), long)]
    source_file: Option<PathBuf>,
    eval: Option<String>,
}

macro_rules! unwrap_or_print_error_and_exit {
    ($result:expr, $source:expr, $source_map:ident) => {
        match $result {
            Ok(result) => result,
            Err(err) => {
                print_error($source, &mut $source_map, err)?;
                std::process::exit(-1);
            }
        }
    };
}

macro_rules! unwrap_or_print_error {
    ($result:expr, $source:expr, $source_map:ident) => {
        match $result {
            Ok(result) => result,
            Err(err) => {
                print_error($source, &mut $source_map, err)?;
                continue;
            }
        }
    };
}

fn main() -> anyhow::Result<()> {
    let mut bud = Bud::empty();

    let args = Args::parse();
    let mut source_cache = SourceCache::default();
    if let Some(file) = args.source_file {
        let source = std::fs::read_to_string(&file)?;
        let source_id = SourceId::File(file);
        source_cache.register(&source_id, &source);
        let value = unwrap_or_print_error_and_exit!(
            bud.run_source::<Value>(&source),
            &source_id,
            source_cache
        );
        print_value(false, &value);
    }

    let is_interactive = stdin().is_tty();

    if let Some(eval) = args.eval {
        source_cache.register(&SourceId::CommandLine, &eval);
        let value = unwrap_or_print_error_and_exit!(
            bud.run_source::<Value>(&eval),
            &SourceId::CommandLine,
            source_cache
        );
        print_value(false, &value);

        // If we are on an interactive shell, running a command should exit
        // immediately. If we aren't on an interactive shell, we should process
        // the piped program.
        if is_interactive {
            return Ok(());
        }
    };

    // Check for st
    if is_interactive {
        let config_dir = dirs::config_dir().unwrap_or_else(|| PathBuf::from("test"));
        let bud_dir = config_dir.join("bud");
        if !bud_dir.exists() {
            std::fs::create_dir_all(&bud_dir)?;
        }
        let history = Box::new(
            FileBackedHistory::with_file(100, bud_dir.join("history.txt"))
                .expect("Error configuring history with file"),
        );
        let mut line_editor = Reedline::create()
            .with_history(history)
            .with_validator(Box::new(BudValidator));
        let mut counter = 1;

        loop {
            let sig = line_editor.read_line(&BudPrompt(counter));
            match sig {
                Ok(Signal::Success(buffer)) => {
                    let source_id = SourceId::Counter(counter);
                    counter += 1;
                    source_cache.register(&source_id, &buffer);
                    // let source = unwrap_or_print_error!(
                    //     Source::parse(source_id, &buffer, runtime.pool()),
                    //     source_cache
                    // );
                    let result =
                        unwrap_or_print_error!(bud.evaluate(&buffer), &source_id, source_cache);

                    print_value(true, &result);
                }
                Ok(Signal::CtrlD) | Ok(Signal::CtrlC) => {
                    break Ok(());
                }
                x => {
                    println!("Event: {:?}", x);
                }
            }
        }
    } else {
        let mut piped = String::new();
        stdin().read_to_string(&mut piped)?;
        if !piped.is_empty() {
            let result = bud.evaluate::<Value>(&piped).unwrap();
            print_value(false, &result);
        }

        Ok(())
    }
}

fn print_value(is_interactive: bool, value: &Value) {
    if !matches!(value, Value::Void) {
        if is_interactive {
            println!("> {value}");
        } else {
            println!("{value}");
        }
    }
}

struct BudValidator;

impl Validator for BudValidator {
    fn validate(&self, line: &str) -> ValidationResult {
        match budlang::parser::parse(line) {
            Err(
                ParseError::MissingEnd { .. }
                | ParseError::UnexpectedEof(_)
                | ParseError::ExpectedEndOfLine { .. },
            ) => ValidationResult::Incomplete,

            _ => ValidationResult::Complete,
        }
    }
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Clone, Hash)]
enum SourceId {
    Counter(u64),
    File(PathBuf),
    CommandLine,
}

#[derive(Default)]
struct SourceCache {
    entries: HashMap<SourceId, ariadne::Source>,
}

impl SourceCache {
    pub fn register(&mut self, source: &SourceId, contents: &str) {
        self.entries
            .insert(source.clone(), ariadne::Source::from(contents));
    }
}

impl ariadne::Cache<SourceId> for SourceCache {
    fn fetch(&mut self, id: &SourceId) -> Result<&ariadne::Source, Box<dyn std::fmt::Debug + '_>> {
        match self.entries.entry(id.clone()) {
            Entry::Occupied(cached) => Ok(cached.into_mut()),
            Entry::Vacant(entry) => {
                if let SourceId::File(path) = id {
                    let contents = std::fs::read_to_string(path).unwrap(); // TODO this should be able to be boxed somehow
                    let source = ariadne::Source::from(contents);
                    Ok(entry.insert(source))
                } else {
                    unreachable!("unknown source id {id:?}")
                }
            }
        }
    }

    fn display<'a>(&self, id: &'a SourceId) -> Option<Box<dyn std::fmt::Display + 'a>> {
        match id {
            SourceId::Counter(number) => Some(Box::new(format!("({number})"))),
            SourceId::File(path) => Some(Box::new(path.display())),
            SourceId::CommandLine => Some(Box::new("(cli)")),
        }
    }
}

fn print_error(
    source: &SourceId,
    cache: &mut SourceCache,
    error: Error<'_, (), Value>,
) -> anyhow::Result<()> {
    if let Some(range) = error.location() {
        let mut report = Report::build(ReportKind::Error, source.clone(), range.start);
        report.add_label(Label::new((source.clone(), range)).with_message(error.to_string()));
        report
            .with_config(
                ariadne::Config::default()
                    .with_label_attach(ariadne::LabelAttach::Start)
                    .with_underlines(false),
            )
            .finish()
            .eprint(cache)?;
    } else {
        eprintln!("Error: {error}");
    }
    Ok(())
}

pub static DEFAULT_PROMPT_INDICATOR: &str = ") ";
pub static DEFAULT_VI_INSERT_PROMPT_INDICATOR: &str = ": ";
pub static DEFAULT_VI_NORMAL_PROMPT_INDICATOR: &str = ") ";
pub static DEFAULT_MULTILINE_INDICATOR: &str = "::: ";

#[derive(Clone)]
struct BudPrompt(u64);

impl Prompt for BudPrompt {
    fn render_prompt_left(&self) -> Cow<str> {
        Cow::Owned(self.0.to_string())
    }

    fn render_prompt_right(&self) -> Cow<str> {
        Cow::Borrowed("")
    }

    fn render_prompt_indicator(&self, edit_mode: PromptEditMode) -> Cow<str> {
        match edit_mode {
            PromptEditMode::Default | PromptEditMode::Emacs => DEFAULT_PROMPT_INDICATOR.into(),
            PromptEditMode::Vi(vi_mode) => match vi_mode {
                PromptViMode::Normal => DEFAULT_VI_NORMAL_PROMPT_INDICATOR.into(),
                PromptViMode::Insert => DEFAULT_VI_INSERT_PROMPT_INDICATOR.into(),
            },
            PromptEditMode::Custom(str) => format!("({})", str).into(),
        }
    }

    fn render_prompt_multiline_indicator(&self) -> Cow<str> {
        Cow::Borrowed(DEFAULT_MULTILINE_INDICATOR)
    }

    fn render_prompt_history_search_indicator(
        &self,
        history_search: PromptHistorySearch,
    ) -> Cow<str> {
        let prefix = match history_search.status {
            PromptHistorySearchStatus::Passing => "",
            PromptHistorySearchStatus::Failing => "failing ",
        };
        // NOTE: magic strings, given there is logic on how these compose I am not sure if it
        // is worth extracting in to static constant
        Cow::Owned(format!(
            "({}reverse-search: {}) ",
            prefix, history_search.term
        ))
    }
}
