#![feature(test)]
extern crate test;

use hash_alloc::Castle;
use hash_parser::lexer::Lexer;
use hash_pipeline::InteractiveBlock;
use hash_pipeline::Sources;
use hash_source::SourceId;
use test::{black_box, Bencher};

static STRINGS: &str = r#""tree" "to" "a" "graph" "that can" "more adequately represent" "loops and arbitrary state jumps" "with\"\"\"out" "the\n\n\n\n\n" "expl\"\"\"osive" "nature\"""of trying to build up all possible permutations in a tree." "tree" "to" "a" "graph" "that can" "more adequately represent" "loops and arbitrary state jumps" "with\"\"\"out" "the\n\n\n\n\n" "expl\"\"\"osive" "nature\"""of trying to build up all possible permutations in a tree." "tree" "to" "a" "graph" "that can" "more adequately represent" "loops and arbitrary state jumps" "with\"\"\"out" "the\n\n\n\n\n" "expl\"\"\"osive" "nature\"""of trying to build up all possible permutations in a tree." "tree" "to" "a" "graph" "that can" "more adequately represent" "loops and arbitrary state jumps" "with\"\"\"out" "the\n\n\n\n\n" "expl\"\"\"osive" "nature\"""of trying to build up all possible permutations in a tree.""#;
static KEYWORDS: &str = include_str!("examples/keywords.hash");
static OPERATORS: &str = include_str!("examples/operators.hash");
static IDENTIFIERS: &str = include_str!("examples/identifiers.hash");
static NUMBERS: &str = include_str!("examples/numbers.hash");

macro_rules! bench_func {
    ($fn_name:ident,$source:tt) => {
        #[bench]
        fn $fn_name(b: &mut Bencher) {
            b.bytes = $source.len() as u64;

            let castle = Castle::new();
            let wall = castle.wall();

            // make a new sources
            let mut sources = Sources::new();
            let interactive_id = sources.add_interactive_block(InteractiveBlock::new($source.to_string()));

            b.iter(|| {
                // create a new lexer
                let mut lex = Lexer::new($source, SourceId::Interactive(interactive_id), &wall);

                while let Ok(Some(token)) = lex.advance_token() {
                    black_box(token);
                }
            });
        }
    };
}

bench_func!(lex_identifiers, IDENTIFIERS);
bench_func!(lex_keywords, KEYWORDS);
bench_func!(lex_operators, OPERATORS);
bench_func!(lex_numbers, NUMBERS);
bench_func!(lex_strings, STRINGS);
