//! Hash compiler module for converting from tokens to an AST tree
//!
//! All rights reserved 2021 (c) The Hash Language authors
use crate::error::ParseError;
use crate::grammar::{HashGrammar, Rule};
use crate::{
    ast::{self, *},
    modules::ModuleIdx,
};
use std::{
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

extern crate pretty_env_logger;

use crossbeam_channel::Sender;
use pest::Parser;

/// Parser options including the number of workers any specific options
/// relating to parsing
pub struct ParserOptions {
    /// The number of workers that should be used when parsing a module
    pub worker_count: Option<usize>,

    /// Whether to run the parsing job in a concurrent mode or a single threaded mode.
    /// This is inferred if [worker_count] option is 1.
    pub concurrent: bool,

    /// whether or not the parser should run in debug mode
    pub debug: bool,
}

pub enum ParserMessage {
    ModuleImport {
        filename: PathBuf,
        parent: ModuleIdx,
    },
    ParsedModule {
        node: Module,
        filename: PathBuf,
        contents: String,
    },
}

/// Default implementation for the [ParserOptions] struct.
impl Default for ParserOptions {
    fn default() -> ParserOptions {
        ParserOptions {
            worker_count: Some(num_cpus::get()),
            concurrent: true,
            debug: false,
        }
    }
}
#[allow(dead_code)]
pub struct ParsedModule {
    node: ast::Module,
    contents: String,
}

#[allow(dead_code)]
pub struct HashParser<'a> {
    channel: Option<Sender<ParserMessage>>,
    opts: &'a ParserOptions,
}

impl HashParser<'_> {
    /// Create a new instance of a hash parser
    pub fn new(s: Option<Sender<ParserMessage>>, opts: &ParserOptions) -> HashParser {
        HashParser { channel: s, opts }
    }

    pub fn parse_file(&self, filename: impl AsRef<Path>) -> Result<ParsedModule, ParseError> {
        debug!("Parsing file: {}", filename.as_ref().to_str().unwrap());

        // load the file in...
        let source = fs::read_to_string(filename.as_ref());

        // check if reading the filed failed, if so return an error
        if let Err(err) = source {
            return Err(ParseError::IoError {
                filename: filename.as_ref().to_path_buf(),
                err: err.to_string(),
            });
        }

        let source = source.unwrap();

        // record the time of parsing and emit for debug purposes.
        let init = Instant::now();
        let result = HashGrammar::parse(Rule::module, &source);
        debug!("pest_grammar: {:.2?}", init.elapsed());

        // now continue onto the ast-emit part
        match result {
            Ok(pairs) => {
                let after_token = Instant::now();

                // take rules from the grammar until we reach EOF
                let contents = pairs
                    .take_while(|p| p.as_rule() != Rule::EOI)
                    .map(|p| p.into_ast())
                    .collect();

                debug!("ast: {:.2?}", after_token.elapsed());

                Ok(ParsedModule {
                    contents: source,
                    node: ast::Module { contents },
                })
            }
            Err(err) => Err(ParseError::from(err)),
        }
    }

    /// Function to parse an individual statement. This function is primarily used for the interactive
    /// mode where only statements are accepted.
    pub fn parse_statement(&self, source: &str) -> Result<AstNode<Statement>, ParseError> {
        let mut result = HashGrammar::parse(Rule::statement, source)?;

        // @@ErrorReporting: change _into_ast to return an Result in case the
        // ast emit had a reason for failure since it might not always be a bug...
        let body: AstNode<Statement> = result.next().unwrap().into_ast();
        Ok(body)
    }
}
