use std::path::PathBuf;

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> rustyflower::Result<()> {
    let mut args = std::env::args_os().skip(1);
    let Some(input) = args.next() else {
        return Err(rustyflower::DecompileError::Usage(
            "usage: rustyflower <input.class> [output.java]".to_string(),
        ));
    };
    let input = PathBuf::from(input);
    let output = rustyflower::decompile_path(&input)?;
    if let Some(path) = args.next() {
        std::fs::write(PathBuf::from(path), output)?;
    } else {
        print!("{output}");
    }
    Ok(())
}
