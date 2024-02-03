use core::fmt;
use std::{fs, io};

use crate::ranged::Ranged;

pub fn report<E: fmt::Display>(
    error: &Ranged<E>,
    source_name: &str,
    stage_name: &str,
) -> io::Result<()> {
    let file = fs::read_to_string(source_name)?;
    let lines = file.lines();

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

    Ok(())
}
