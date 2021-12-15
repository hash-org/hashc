#![feature(test)]
extern crate test;

use hash_alloc::Castle;
use hash_ast::module::ModuleIdx;
use hash_parser::lexer::Lexer;
use test::{black_box, Bencher};

static IDENTIFIERS: &str = "It was the year when they finally immanentized the Eschaton \
                            It was the year when they finally immanentized the Eschaton \
                            It was the year when they finally immanentized the Eschaton \
                            It was the year when they finally immanentized the Eschaton \
                            It was the year when they finally immanentized the Eschaton \
                            It was the year when they finally immanentized the Eschaton \
                            It was the year when they finally immanentized the Eschaton \
                            It was the year when they finally immanentized the Eschaton \
                            It was the year when they finally immanentized the Eschaton \
                            It was the year when they finally immanentized the Eschaton \
                            It was the year when they finally immanentized the Eschaton \
                            It was the year when they finally immanentized the Eschaton \
                            It was the year when they finally immanentized the Eschaton";

static STRINGS: &str = r#""tree" "to" "a" "graph" "that can" "more adequately represent" "loops and arbitrary state jumps" "with\"\"\"out" "the\n\n\n\n\n" "expl\"\"\"osive" "nature\"""of trying to build up all possible permutations in a tree." "tree" "to" "a" "graph" "that can" "more adequately represent" "loops and arbitrary state jumps" "with\"\"\"out" "the\n\n\n\n\n" "expl\"\"\"osive" "nature\"""of trying to build up all possible permutations in a tree." "tree" "to" "a" "graph" "that can" "more adequately represent" "loops and arbitrary state jumps" "with\"\"\"out" "the\n\n\n\n\n" "expl\"\"\"osive" "nature\"""of trying to build up all possible permutations in a tree." "tree" "to" "a" "graph" "that can" "more adequately represent" "loops and arbitrary state jumps" "with\"\"\"out" "the\n\n\n\n\n" "expl\"\"\"osive" "nature\"""of trying to build up all possible permutations in a tree.""#;

static SOURCE: &str = "
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
if (match let while for in) { + ++ = == === => }
";

#[bench]
fn lex_identifiers(b: &mut Bencher) {
    b.bytes = IDENTIFIERS.len() as u64;

    let castle = Castle::new();
    let wall = castle.wall();

    b.iter(|| {
        // create a new lexer
        let lex = Lexer::new(IDENTIFIERS, ModuleIdx(0), &wall);

        while let Ok(Some(token)) = lex.advance_token() {
            black_box(token);
        }
    });
}

#[bench]
fn lex_keywords_and_punctuation(b: &mut Bencher) {
    b.bytes = SOURCE.len() as u64;

    let castle = Castle::new();
    let wall = castle.wall();

    b.iter(|| {
        // create a new lexer
        let lex = Lexer::new(SOURCE, ModuleIdx(0), &wall);

        while let Ok(Some(token)) = lex.advance_token() {
            black_box(token);
        }
    });
}

#[bench]
fn lex_strings(b: &mut Bencher) {
    b.bytes = STRINGS.len() as u64;

    let castle = Castle::new();
    let wall = castle.wall();

    b.iter(|| {
        let lex = Lexer::new(STRINGS, ModuleIdx(0), &wall);

        while let Ok(Some(token)) = lex.advance_token() {
            black_box(token);
        }
    });
}
