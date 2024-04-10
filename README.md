# Iridium Compiler

## Purpose of this Project

This is a side project inspired by Pixeled's "Let's Create a Compiler" series. I wanted to learn a bit about assembly, learn about how compilers work, and practice my Rust.

## Usage

Iridium language is written in .ir files. It has a very basic syntax at the moment, loosely inspired by that of Rust, favouring `let`, avoiding unnecessary parentheses, and using implicit static typing.

This project will only compile Iridium files into ARM64 assembly (because I'm working on MacOS, sorry). Put your script name in `compile_and_run.sh` to use Mac's default assembler and linker to compile, run, and print the exit code.
