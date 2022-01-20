//! All rights reserved 2022 (c) The Hash Language authors
use std::path::PathBuf;

#[derive(Debug, Clone)]
pub struct TestingInput {
    pub path: PathBuf,
    pub snake_name: String,
}

pub type TestingFn = fn(input: TestingInput);
