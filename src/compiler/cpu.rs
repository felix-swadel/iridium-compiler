#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Type {
    Int32,
    Bool,
}

impl Type {
    pub fn bytes(&self) -> usize {
        match self {
            Type::Int32 => 4,
            Type::Bool => 1,
        }
    }

    pub fn is_signed(&self) -> bool {
        match self {
            Type::Int32 => true,
            Type::Bool => false,
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Type::Int32 => "i32",
                Type::Bool => "bool",
            }
        )
    }
}

#[derive(Debug, Clone)]
pub struct StackVar {
    name: String,
    // num bytes from the top of the stack
    location: usize,
    type_: Type,
}

impl StackVar {
    pub fn new(name: &str, location: usize, type_: Type) -> StackVar {
        // variables can take up one or two doublewords
        StackVar {
            name: name.to_owned(),
            location,
            type_,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn location(&self) -> usize {
        self.location
    }

    pub fn type_(&self) -> &Type {
        &self.type_
    }

    pub fn bytes(&self) -> usize {
        self.type_.bytes()
    }
}

#[derive(Debug, Clone)]
pub struct Arg {
    name: String,
    register: Register,
    type_: Type,
}

impl Arg {
    pub fn new(name: String, reg_ix: usize, type_: Type) -> Result<Arg, String> {
        if reg_ix > 8 {
            Err("function has too many args, max is 9".to_owned())
        } else {
            Ok(Arg {
                name,
                register: Register::infer(type_.bytes(), reg_ix),
                type_,
            })
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn register(&self) -> &Register {
        &self.register
    }

    pub fn type_(&self) -> &Type {
        &self.type_
    }

    pub fn bytes(&self) -> usize {
        self.type_.bytes()
    }
}

#[derive(Debug)]
pub enum Value {
    Arg(Arg),
    StackVar(StackVar),
}

impl Value {
    pub fn type_(&self) -> &Type {
        match self {
            Value::Arg(arg) => arg.type_(),
            Value::StackVar(var) => var.type_(),
        }
    }

    pub fn bytes(&self) -> usize {
        match self {
            Value::Arg(arg) => arg.bytes(),
            Value::StackVar(var) => var.bytes(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Register {
    X(usize),
    W(usize),
    XZR,
    WZR,
    SP,
}

impl Register {
    #[inline]
    pub fn default_reg() -> usize {
        15
    }

    pub fn infer(bytes: usize, ix: usize) -> Register {
        if bytes > 4 {
            Register::X(ix)
        } else {
            Register::W(ix)
        }
    }

    pub fn infer_default(bytes: usize) -> Register {
        Register::infer(bytes, Register::default_reg())
    }

    pub fn infer_zr(bytes: usize) -> Register {
        if bytes > 4 {
            Register::XZR
        } else {
            Register::WZR
        }
    }
}

impl std::fmt::Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Register::W(val) => write!(f, "w{}", val),
            Register::X(val) => write!(f, "x{}", val),
            Register::WZR => "wzr".fmt(f),
            Register::XZR => "xzr".fmt(f),
            Register::SP => "sp".fmt(f),
        }
    }
}

pub fn bytes_to_size_suffix(bytes: usize) -> String {
    match bytes {
        1 => "b".to_owned(),
        2 => "h".to_owned(),
        4 | 8 => "".to_owned(),
        _ => panic!("invalid number of bytes for variable: {bytes}"),
    }
}
