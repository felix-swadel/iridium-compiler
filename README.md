# Iridium Compiler

## Purpose of this Project

This is a side project inspired by Pixeled's "Let's Create a Compiler" series. I wanted to learn a bit about assembly, learn about how compilers work, and practice my Rust.

## Usage

Iridium language is written in .ir files. It has a very basic syntax at the moment, loosely inspired by that of Rust, favouring `let`, avoiding unnecessary parentheses, and using implicit static typing.

This project will only compile Iridium files into ARM64 assembly (because I'm working on MacOS, sorry). Put your script name in `compile_and_run.sh` to use Mac's default assembler and linker to compile, run, and print the exit code.

## Syntax

### Types

Currently positive `int-32` and `bool` are supported. Types are always inferred.

### Operators

All operators are binary. `+`, `-`, `*`, `/`, `<`, `>`, `==`, `!=`, `&&`, `||` are supported.

### Variables

Variables are declared with `let`. Currently all variables are mutable.

```
let x = 5;
x = x + 12;
```

### Built-Ins

Currently the only built-in is `exit(int)` which exits the program with a value.

### Control Flow

Simple control flow is supported:

```
// simple if
if x > 2 {
    x = x + 1;
}

// if-else
if y > 0 {
    y = 10;
} else {
    y = 0;
}

// infinite loop ~ while(true)
loop {
    y = y + 1;
    if y > 20 {
        break;
    }
}

// while loop
while y < 100 {
    y = y + 12;
}
```

### Functions

Functions take typed arguments and must return a single typed value. E.g.

```
fn operate(x: i32, y: i32, sub: bool) i32 {
    if sub {
        return x - y;
    } else {
        return x + y;
    }
}

let val = operate(3, 4, false);
```

Currently the logic surrounding returns is a bit messy. Also, functions which call functions aren't supported - currently the arguments of the outer function are overwritten.

## TODO:

- Add assignment operators (e.g. `+=`).
- Add `print` built-in.
- Add function definition post-processor which determines where we need to include the assembly `ret` statement. This gets complicated when there is branching involved and not all branches necessarily contain returns.
- Add support for functions which call other functions by pushing the calling function's arguments to the stack.
