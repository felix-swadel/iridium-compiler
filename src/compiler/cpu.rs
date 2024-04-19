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
pub struct Var {
    name: String,
    // num bytes from the top of the stack
    location: usize,
    type_: Type,
}

impl Var {
    pub fn new(name: &str, location: usize, type_: Type) -> Var {
        // variables can take up one or two doublewords
        Var {
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

    pub fn type_(&self) -> Type {
        self.type_
    }

    pub fn bytes(&self) -> usize {
        self.type_.bytes()
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Register {
    X(usize),
    W(usize),
    XZR,
    WZR,
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
            Register::WZR => write!(f, "wzr"),
            Register::XZR => write!(f, "xzr"),
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
