use pest_derive::Parser;

#[allow(missing_docs)]
#[derive(Parser)]
#[grammar = "rust_fmt.pest"] // relative to src
pub(crate) struct FmtParser;
