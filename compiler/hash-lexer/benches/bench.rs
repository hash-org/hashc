//! Some Hash lexer benchmarks.
use std::hint::black_box;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};
use hash_lexer::Lexer;
use hash_source::{SourceId, location::SpannedSource};

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

static KEYWORDS: &str = "for while loop if else match as in trait enum struct continue break return import raw false unsafe pub priv mut mod impl true type \
                         for while loop if else match as in trait enum struct continue break return import raw false unsafe pub priv mut mod impl true type \
                         for while loop if else match as in trait enum struct continue break return import raw false unsafe pub priv mut mod impl true type \
                         for while loop if else match as in trait enum struct continue break return import raw false unsafe pub priv mut mod impl true type \
                         for while loop if else match as in trait enum struct continue break return import raw false unsafe pub priv mut mod impl true type \
                         for while loop if else match as in trait enum struct continue break return import raw false unsafe pub priv mut mod impl true type \
                         for while loop if else match as in trait enum struct continue break return import raw false unsafe pub priv mut mod impl true type \
                         for while loop if else match as in trait enum struct continue break return import raw false unsafe pub priv mut mod impl true type \
                         for while loop if else match as in trait enum struct continue break return import raw false unsafe pub priv mut mod impl true type \
                         for while loop if else match as in trait enum struct continue break return import raw false unsafe pub priv mut mod impl true type \
                         for while loop if else match as in trait enum struct continue break return import raw false unsafe pub priv mut mod impl true type \
                         for while loop if else match as in trait enum struct continue break return import raw false unsafe pub priv mut mod impl true type \
                         for while loop if else match as in trait enum struct continue break return import raw false unsafe pub priv mut mod impl true type \
                        for while loop if else match as in trait enum struct continue break return import raw false unsafe pub priv mut mod impl true type";

static MIX: &str = "for it was in the year as they finally immanentized the enum Eschaton while struct \
                    for it was in the year as they finally immanentized the enum Eschaton while struct \
                    for it was in the year as they finally immanentized the enum Eschaton while struct \
                    for it was in the year as they finally immanentized the enum Eschaton while struct \
                    for it was in the year as they finally immanentized the enum Eschaton while struct \
                    for it was in the year as they finally immanentized the enum Eschaton while struct \
                    for it was in the year as they finally immanentized the enum Eschaton while struct \
                    for it was in the year as they finally immanentized the enum Eschaton while struct \
                    for it was in the year as they finally immanentized the enum Eschaton while struct \
                    for it was in the year as they finally immanentized the enum Eschaton while struct \
                    for it was in the year as they finally immanentized the enum Eschaton while struct \
                    for it was in the year as they finally immanentized the enum Eschaton while struct \
                    for it was in the year as they finally immanentized the enum Eschaton while struct";

/// Test candidates that are to be run.
static CANDIDATES: [(&str, &str); 3] =
    [("identifiers", IDENTIFIERS), ("mixed", MIX), ("keywords", KEYWORDS)];

fn lex(source: &str) {
    let mut lexer = Lexer::new(SpannedSource(source), SourceId::default());

    while let Some(token) = lexer.advance_token() {
        black_box(token);
    }
}

fn bench_idents(c: &mut Criterion) {
    let mut group = c.benchmark_group("idents");

    for (name, source) in CANDIDATES {
        group.throughput(Throughput::Bytes(source.len() as u64));
        group.bench_with_input(name, &source, |b, &s| b.iter(|| lex(s)));
    }
}

criterion_group!(benches, bench_idents);
criterion_main!(benches);
