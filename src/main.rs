use std::fs::read_to_string;
use std::path::Path;

mod compiler;
use crate::compiler::{generator::Generator, parser::Parser, tokeniser::tokenise};

const IR_EXTENSION: &str = "ir";

fn main() {
    // read command line arguments
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 || 3 < args.len() {
        println!(
            "incorrect usage - correct usage: iridium-compiler <source.ir> <executable-name>");
        return;
    }

    // extract source file path of iridium file to be compiled
    let filepath_str = args.get(1).unwrap();

    // check file extension
    let filepath = Path::new(filepath_str);
    match filepath.extension() {
        Some(ext) => {
            if ext != IR_EXTENSION {
                println!("warning - expected iridium file to be .ir, got: .{:?}", ext);
            }
        }
        None => {
            println!("warning - expected iridium file to have extension");
        }
    }

    // extract source code
    let source_code = match read_to_string(&filepath) {
        Ok(contents) => contents,
        Err(e) => {
            println!("error opening file {}: {}", filepath_str, e);
            return;
        }
    };

    // tokenise source code
    println!("Tokenising source code...");
    let tokens = match tokenise(&source_code) {
        Ok(tokens) => tokens,
        Err(e) => {
            println!("Failed to tokenise {}: {}", filepath_str, e);
            return;
        }
    };

    // parse source code
    println!("Parsing source code...");
    let mut parser = Parser::new(&tokens);
    let node_prog = match parser.parse() {
        Ok(node_prog) => node_prog,
        Err(e) => {
            println!("Failed to parse {}: {}", filepath_str, e);
            return;
        }
    };

    // generate ARM64 assembly
    println!("Generating ARM64 assembly...");
    let mut generator = Generator::new();
    match generator.generate(&node_prog) {
        Ok(()) => (),
        Err(e) => {
            println!("Failed to generate code for {}: {}", filepath_str, e);
            return;
        }
    }

    // write assembly to out.s
    let asm_filepath = match args.get(2) {
        Some(path) => format!("{}.s", path),
        None => "out.s".to_owned(),
    };
    println!("Writing assembly to {}...", asm_filepath);
    if let Err(e) = std::fs::write(&asm_filepath, generator.output()) {
        println!("Failed to write assembly to {}: {}", asm_filepath, e);
    }
}
