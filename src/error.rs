use core::fmt;
use std::io;

use crate::{evaluator::BaseEvaluationError, parser::ParseError, ranged::Ranged};

pub fn report<E: fmt::Display>(
    error: &Ranged<E>,
    source_name: &str,
    source: &str,
    stage_name: &str,
) {
    let lines = source.lines();

    let (col_start, row_start) = error.starts();
    let (col_end, row_end) = error.ends();

    eprintln!();
    eprintln!("  Error | [{source_name}:{row_start}:{col_start}] (at {stage_name})",);
    eprintln!("        |");

    let first_line = lines.clone().nth(row_start - 1).unwrap();
    eprintln!("   {row_start:>4} | {first_line}");
    eprint!("        | {}", " ".repeat(col_start - 1));

    if row_start == row_end {
        eprintln!("{}", "^".repeat(col_end - col_start));
    } else {
        eprintln!("{}", "^".repeat(first_line.len() + 1 - col_start));

        for row_middle in row_start + 1..row_end {
            let line = lines.clone().nth(row_middle - 1).unwrap();
            eprintln!("   {row_middle:>4} | {line}");
            eprintln!("        | {}", "^".repeat(line.len()));
        }

        let last_line = lines.clone().nth(row_end - 1).unwrap();
        eprintln!("   {row_end:>4} | {last_line}");
        eprintln!("        | {}", "^".repeat(col_end - 1));
    }
    eprintln!("        | {}\n", error.data);
}

pub fn report_file_read(error: &io::Error, source_name: &str) {
    eprintln!();
    eprintln!("  Error | [{source_name}]",);
    eprintln!("        |");
    eprintln!("        | {error}\n");
}

pub fn report_unexpected_eof(error: &ParseError, source_name: &str, source: &str) {
    let lines = source.lines().enumerate();

    let (line_index, last_line) = lines.last().unwrap();
    let row_start = line_index + 1;
    eprintln!();
    eprintln!("  Error | [{source_name}:{row_start}] (at parsing)");
    eprintln!("        |");
    eprintln!("   {row_start:>4} | {last_line}");
    eprintln!("        | {error}\n");
}

pub fn report_absent_main(error: &BaseEvaluationError, source_name: &str) {
    eprintln!();
    eprintln!("  Error | [{source_name}]",);
    eprintln!("        |");
    eprintln!("        | {error}\n");
}
