//! Hash Compiler Frontend library file
//!
//! All rights reserved 2021 (c) The Hash Language authors

use std::{
    path::Path,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};

use crossbeam_channel::unbounded;
use error::ParseError;
use modules::Modules;
use parse::ParserOptions;

use crate::parse::{HashParser, ParserMessage};

extern crate pest;

#[macro_use]
extern crate lazy_static;

#[macro_use]
extern crate log;

pub mod ast;
pub mod emit;
pub mod error;
pub mod parse;

mod grammar;
mod location;
mod modules;
mod precedence;

#[allow(dead_code)]
pub struct ParseInfo {
    modules: Modules,
    // names: Names,
}
type ParseResult = Result<ParseInfo, ParseError>;

/// Main function to parse a input file
pub fn parse(filename: impl AsRef<Path> + Send, opts: &ParserOptions) -> ParseResult {
    // create the logger for the parser...
    pretty_env_logger::init();

    // setup a global table to track what modules have been and haven't been
    // parsed.
    // let module_map: HashMap<PathBuf, ModuleIndex> = HashMap::new();

    // create a parser job counter to wait on all the parsing jobs
    let job_counter = Arc::new(AtomicUsize::new(0));

    // create the modules object
    let mut modules = Modules::new();

    // check if we're operating in concurrent mode or single threaded...
    match opts.worker_count {
        Some(worker_count) if opts.concurrent && worker_count > 1 => {
            // create the channel and the pool
            let (s, r) = unbounded();

            info!("Creating worker pool with {} workers", worker_count);
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(worker_count)
                .build()
                .unwrap();

            pool.scope(|scope| {
                // spawn the initial job
                scope.spawn(|_| {
                    let _data = HashParser::new(Some(s.clone()), opts).parse_file(filename);
                });

                // start the reciever and listen for any messages from the jobs, continue looping until all of the module
                // dependencies were resovled from the initially supplied file.
                loop {
                    match r.recv() {
                        Ok(ParserMessage::ModuleImport {
                            filename,
                            parent: _parent,
                        }) => {
                            if !modules.map.contains_key(&filename) {
                                scope.spawn(|_| {
                                    let _data =
                                        HashParser::new(Some(s.clone()), opts).parse_file(filename);
                                });
                            } else {
                                continue;
                            }
                        }
                        Ok(ParserMessage::ParsedModule {
                            node,
                            filename,
                            contents,
                        }) => {
                            // decrement the atomic job counter here...
                            job_counter.fetch_add(1, Ordering::SeqCst);
                            // add the module to the modules list.
                            modules.add_module(node, filename, contents);
                        }
                        Err(_) => unreachable!(),
                    }

                    // lock the job_counter and check if the number of pending jobs is zero
                    if job_counter.load(Ordering::SeqCst) == 0 {
                        break;
                    }
                }

                // now return the modules value
                Ok(ParseInfo { modules })
            })
        }
        _ => {
            // single threaded mode!
            unimplemented!()
        }
    }
}
