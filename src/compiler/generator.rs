use super::cpu::*;
use super::node::*;

// in ARM64 the stack pointer needs to be 16-byte aligned
const STACK_DELTA: usize = 16;

pub type GenResult = Result<(), String>;
pub type TypeResult = Result<Type, String>;

pub struct Generator {
    output: String,
    top_level_exit_found: bool,
    // stack management
    vars: Vec<Var>,
    scopes: Vec<usize>,
    // bytes written to the stack
    stack_length: usize,
    // bytes allocated on the stack
    stack_capacity: usize,
    // label management
    condition_counter: usize,
}

// public interface
impl Generator {
    pub fn new() -> Generator {
        Generator {
            output: String::new(),
            top_level_exit_found: false,
            vars: Vec::new(),
            scopes: Vec::new(),
            stack_length: 0,
            stack_capacity: 0,
            condition_counter: 0,
        }
    }

    pub fn generate(&mut self, prog: &NodeProg) -> GenResult {
        self.gen_prelude();

        self.gen_prog(prog, true)?;

        if !self.top_level_exit_found {
            // exit with code 0 if no top level exit was found
            self.output
                .push_str(&format!("    add sp, sp, #{}\n", self.stack_capacity,));
            self.gen_exit(&NodeExit {
                expr: NodeExpr::new_int(0),
            })?;
        }

        Ok(())
    }

    pub fn output(&self) -> &str {
        &self.output
    }
}

// formatting utilities
impl Generator {
    fn fmt_bin_op(&mut self, dst: Register, lhs: Register, op: BinOp, rhs: Register) {
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::And | BinOp::Or => {
                self.output.push_str(&format!(
                    "    {} {}, {}, {}\n",
                    op.get_instruction().unwrap(),
                    dst,
                    lhs,
                    rhs,
                ));
            }
            BinOp::Gt | BinOp::Lt | BinOp::Eq | BinOp::Ne => {
                // signed subtraction stored in rhs
                self.output
                    .push_str(&format!("    subs {}, {}, {}\n", dst, lhs, rhs,));
                self.output
                    .push_str(&format!("    cset {}, {}\n", dst, op.get_flag().unwrap(),));
            }
        }
    }

    fn fmt_move_int32(&mut self, reg: Register, val: u32) {
        self.output
            .push_str(&format!("    mov {}, #{}\n", reg, val,));
    }

    fn fmt_move_bool(&mut self, reg: Register, val: bool) {
        self.output.push_str(&format!(
            "    mov {}, {}\n",
            reg,
            if val { "#1" } else { "wzr" },
        ));
    }

    fn fmt_store_reg(&mut self, reg: Register, bytes: usize, offset: usize) {
        if offset > 0 {
            self.output.push_str(&format!(
                "    str{} {}, [sp, #{}]\n",
                bytes_to_size_suffix(bytes),
                reg,
                offset,
            ))
        } else {
            self.output.push_str(&format!(
                "    str{} {}, [sp]\n",
                bytes_to_size_suffix(bytes),
                reg,
            ))
        }
    }

    fn fmt_load_reg(&mut self, reg: Register, bytes: usize, offset: usize) {
        if offset > 0 {
            self.output.push_str(&format!(
                "    ldr{} {}, [sp, #{}]\n",
                bytes_to_size_suffix(bytes),
                reg,
                offset,
            ))
        } else {
            self.output.push_str(&format!(
                "    ldr{} {}, [sp]\n",
                bytes_to_size_suffix(bytes),
                reg,
            ))
        }
    }

    fn fmt_load_pair(&mut self, reg_1: Register, reg_2: Register, offset: usize) {
        if offset > 0 {
            self.output.push_str(&format!(
                "    ldp {}, {}, [sp, #{}]\n",
                reg_1, reg_2, offset,
            ));
        } else {
            self.output
                .push_str(&format!("    ldp {}, {}, [sp]\n", reg_1, reg_2,));
        }
    }
}

// assembly utilities
impl Generator {
    fn grow_stack(&mut self, bytes: usize) {
        assert_eq!(bytes % STACK_DELTA, 0);
        self.output
            .push_str(&format!("    sub sp, sp, #{}\n", bytes));
        self.stack_capacity += bytes;
    }

    fn shrink_stack(&mut self, bytes: usize) {
        assert_eq!(bytes % STACK_DELTA, 0);
        self.output.push_str(&format!("    add sp, sp, #{}", bytes));
        self.stack_capacity -= bytes;
    }

    fn push(&mut self, reg: Register, bytes: usize) {
        // allocate stack space and compute offset
        let stack_space = self.stack_capacity - self.stack_length;
        let offset = if stack_space < bytes {
            // there isn't enough space on the stack for this variable
            self.grow_stack(STACK_DELTA);
            STACK_DELTA + stack_space - bytes
        } else {
            // there is already space for this new value
            stack_space - bytes
        };
        // push variable to stack
        self.fmt_store_reg(reg, bytes, offset);
        self.stack_length += bytes;
    }

    fn pop(&mut self, reg: Register, bytes: usize) {
        let offset = self.stack_capacity - self.stack_length;
        self.fmt_load_reg(reg, bytes, offset);
        self.stack_length -= bytes;
        if self.stack_capacity - self.stack_length >= STACK_DELTA {
            self.shrink_stack(STACK_DELTA);
        }
    }

    fn pop_pair(&mut self, reg_1: Register, reg_2: Register, bytes: usize) {
        if bytes < 4 {
            // can't use ldp, must push and pop separately
            self.pop(reg_1, bytes);
            self.pop(reg_2, bytes);
        } else {
            // with words and double words we can use ldp
            let offset = self.stack_capacity - self.stack_length;
            self.fmt_load_pair(reg_1, reg_2, offset);
            self.stack_length -= 2 * bytes;
            if self.stack_capacity - self.stack_length >= STACK_DELTA {
                self.shrink_stack(STACK_DELTA);
            }
        }
    }

    fn move_int32(&mut self, reg: Register, val: u32) {
        self.fmt_move_int32(reg, val);
    }

    fn move_bool(&mut self, reg: Register, val: bool) {
        self.fmt_move_bool(reg, val);
    }

    fn load_ident(&mut self, reg: Register, var: &Var) {
        let offset = self.stack_capacity - var.location();
        self.fmt_load_reg(reg, var.bytes(), offset);
    }

    fn write_ident(&mut self, reg: Register, var: &Var) {
        let offset = self.stack_capacity - var.location();
        self.fmt_store_reg(reg, var.bytes(), offset);
    }

    fn syscall(&mut self, code: &str) {
        self.output.push_str(&format!("    svc #{}\n", code));
    }
}

// variable management
impl Generator {
    fn find_var(&self, name: &str) -> Option<&Var> {
        // reverse iterate to allow shadowing
        self.vars.iter().rev().find(|&v| v.name() == name)
    }

    // useful for checking if a var already exists in this scope for assignment
    fn find_var_in_scope(&self, name: &str) -> Option<&Var> {
        match self.scopes.last() {
            Some(scope_start) => {
                for var in self.vars.iter().rev() {
                    if var.location() <= *scope_start {
                        break;
                    }
                    if var.name() == name {
                        return Some(var);
                    }
                }
                None
            }
            None => self.find_var(name),
        }
    }
}

// generation functions
// when a node results in a value in assembly, that value is
// pushed to the stack unless a register is explicitly specified
// for the result
impl Generator {
    fn gen_int32(&mut self, val: u32, reg_ix: Option<usize>) -> TypeResult {
        match reg_ix {
            Some(ix) => self.move_int32(Register::W(ix), val),
            None => {
                let reg = Register::W(Register::default_reg());
                self.move_int32(reg, val);
                self.push(reg, Type::Int32.bytes());
            }
        }
        Ok(Type::Int32)
    }

    fn gen_bool(&mut self, val: bool, reg_ix: Option<usize>) -> TypeResult {
        match reg_ix {
            Some(ix) => self.move_bool(Register::W(ix), val),
            None => {
                let reg = Register::W(Register::default_reg());
                self.move_bool(reg, val);
                self.push(reg, Type::Bool.bytes());
            }
        }
        Ok(Type::Bool)
    }

    fn gen_ident(&mut self, name: &str, reg_ix: Option<usize>) -> TypeResult {
        let var = match self.find_var(name) {
            Some(var) => var.clone(),
            None => return Err(format!("undeclared identifier: {}", name)),
        };
        match reg_ix {
            Some(ix) => self.load_ident(Register::infer(var.bytes(), ix), &var),
            None => {
                let reg = Register::infer_default(var.bytes());
                self.load_ident(reg, &var);
                self.push(reg, var.bytes());
            }
        }
        Ok(var.type_())
    }

    fn gen_term(&mut self, term: &NodeTerm, reg_ix: Option<usize>) -> TypeResult {
        match term {
            NodeTerm::IntLit(val) => self.gen_int32(*val, reg_ix),
            NodeTerm::Bool(val) => self.gen_bool(*val, reg_ix),
            NodeTerm::Ident(name) => self.gen_ident(name, reg_ix),
            NodeTerm::Paren(expr) => self.gen_expr(expr.as_ref(), reg_ix),
        }
    }

    fn gen_bin_op(&mut self, bin_op: &NodeBinOp, reg_ix: Option<usize>) -> TypeResult {
        // generate operands
        // push lhs onto stack so it isn't overwritten by rhs generation
        let lhs_type = self.gen_expr(bin_op.lhs.as_ref(), None)?;
        // write rhs to r15
        let rhs_type = self.gen_expr(bin_op.rhs.as_ref(), Some(15))?;
        // check that binop is valid
        if lhs_type != rhs_type {
            return Err(format!("invalid operands in binary operation: {}", bin_op));
        }

        // generate binary operator expression
        let in_bytes = lhs_type.bytes();
        let out_type = match bin_op.op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => lhs_type,
            BinOp::Eq | BinOp::Ne | BinOp::Gt | BinOp::Lt | BinOp::Or | BinOp::And => Type::Bool,
        };
        let out_bytes = out_type.bytes();
        // pop lhs off stack into r14
        self.pop(Register::infer(in_bytes, 14), in_bytes);
        let lhs = Register::infer(in_bytes, 14);
        let rhs = Register::infer(in_bytes, 15);
        match reg_ix {
            Some(ix) => {
                let dst = Register::infer(out_bytes, ix);
                self.fmt_bin_op(dst, lhs, bin_op.op, rhs);
            }
            None => {
                let dst = Register::infer_default(out_bytes);
                self.fmt_bin_op(dst, lhs, bin_op.op, rhs);
                self.push(dst, out_bytes);
            }
        }
        Ok(out_type)
    }

    fn gen_expr(&mut self, expr: &NodeExpr, reg_ix: Option<usize>) -> TypeResult {
        match expr {
            NodeExpr::Term(term) => self.gen_term(term, reg_ix),
            NodeExpr::BinOp(bin_op) => self.gen_bin_op(bin_op, reg_ix),
        }
    }

    fn gen_let(&mut self, node_let: &NodeLet) -> GenResult {
        let ident = &node_let.ident;
        // check that identifier doesn't already exist
        if let Some(_) = self.find_var_in_scope(ident) {
            return Err(format!("identifier already used: {}", ident));
        }
        let expr = &node_let.expr;
        let type_ = self.gen_expr(expr, None)?;
        self.vars.push(Var::new(ident, self.stack_length, type_));

        Ok(())
    }

    fn gen_assign(&mut self, node_assign: &NodeAssign) -> GenResult {
        let ident = &node_assign.ident;
        // check that identifier already exists
        let var = match self.find_var(ident) {
            Some(var) => var.clone(),
            None => return Err(format!("undeclared identifier: {}", ident)),
        };
        let expr = &node_assign.expr;

        let expr_type = self.gen_expr(expr, Some(15))?;
        if expr_type != var.type_() {
            return Err(format!(
                "tried to assign {} value to identifier {}, which is {}",
                expr_type,
                ident,
                var.type_(),
            ));
        }
        let reg = Register::infer(var.bytes(), 15);
        self.write_ident(reg, &var);

        Ok(())
    }

    fn gen_exit(&mut self, node_exit: &NodeExit) -> GenResult {
        // compute the value of the expression at compile time if possible
        let expr = &node_exit.expr;
        // push the expression value to w0
        self.gen_expr(expr, Some(0))?;
        // move the exit syscall number #1 to register X16
        self.move_int32(Register::W(16), 1);
        // make the syscall
        self.syscall("0x80");

        Ok(())
    }

    fn gen_scope(&mut self, node_scope: &NodeScope) -> GenResult {
        self.scopes.push(self.stack_length);
        for stmt in node_scope.stmts.iter() {
            self.gen_stmt(stmt)?;
        }
        self.stack_length = self.scopes.pop().unwrap();
        let stack_space = self.stack_capacity - self.stack_length;
        let num_deltas = stack_space / STACK_DELTA;
        if num_deltas > 0 {
            self.shrink_stack(num_deltas * STACK_DELTA);
        }

        Ok(())
    }

    fn gen_if_stmt(&mut self, node_condition: &NodeCondition) -> GenResult {
        let node_expr = &node_condition.expr;
        let expr_type = self.gen_expr(node_expr, Some(15))?;
        match expr_type {
            Type::Bool => (),
            _ => {
                return Err(format!(
                    "expected bool in conditional expression - got: {}",
                    node_expr,
                ))
            }
        }
        let if_label = format!(".condition{}_if", self.condition_counter);
        let remainder_label = format!(".condition{}_continue", self.condition_counter);
        self.condition_counter += 1;
        // if first bit of w15 is 0, branch to remainder
        self.output
            .push_str(&format!("    tbz w15, #0, {}\n", remainder_label,));
        // else branch to if
        self.output.push_str(&format!("    b {}\n", if_label,));
        // generate if scope
        self.output.push_str(&format!("{}:\n", if_label,));
        let node_scope = &node_condition.scope;
        self.gen_scope(node_scope)?;
        // branch to remainder
        self.output
            .push_str(&format!("    b {}\n", remainder_label,));
        // generate remainder
        self.output.push_str(&format!("{}:\n", remainder_label,));

        Ok(())
    }

    fn gen_if_else_stmt(&mut self, node_condition: &NodeCondition) -> GenResult {
        let node_expr = &node_condition.expr;
        let expr_type = self.gen_expr(node_expr, Some(15))?;
        match expr_type {
            Type::Bool => (),
            _ => {
                return Err(format!(
                    "expected bool in conditional expression - got: {}",
                    node_expr,
                ))
            }
        }
        let if_label = format!(".condition{}_if", self.condition_counter);
        let else_label = format!(".condition{}_else", self.condition_counter);
        let remainder_label = format!(".condition{}_continue", self.condition_counter);
        self.condition_counter += 1;
        // if first bit of w15 is 0, branch to else
        self.output
            .push_str(&format!("    tbz w15, #0, {}\n", else_label,));
        // else branch to if
        self.output.push_str(&format!("    b {}\n", if_label,));
        // generate if scope
        self.output.push_str(&format!("{}:\n", if_label,));
        let node_scope = &node_condition.scope;
        self.gen_scope(node_scope)?;
        // branch to remainder
        self.output
            .push_str(&format!("    b {}\n", remainder_label,));
        // generate else scope
        self.output.push_str(&format!("{}:\n", else_label,));
        let node_else_scope = &node_condition.else_scope.as_ref().unwrap();
        self.gen_scope(node_else_scope)?;
        // branch to remainder
        self.output
            .push_str(&format!("    b {}\n", remainder_label,));
        // generate remainder
        self.output.push_str(&format!("{}:\n", remainder_label,));

        Ok(())
    }

    fn gen_condition(&mut self, node_condition: &NodeCondition) -> GenResult {
        match node_condition.else_scope {
            Some(_) => self.gen_if_else_stmt(node_condition),
            None => self.gen_if_stmt(node_condition),
        }
    }

    fn gen_stmt(&mut self, stmt: &NodeStmt) -> GenResult {
        match stmt {
            NodeStmt::Exit(node_exit) => self.gen_exit(node_exit),
            NodeStmt::Let(node_let) => self.gen_let(node_let),
            NodeStmt::Assign(node_assign) => self.gen_assign(node_assign),
            NodeStmt::Scope(node_scope) => self.gen_scope(node_scope),
            NodeStmt::Condition(node_condition) => self.gen_condition(node_condition),
        }
    }

    fn gen_prog(&mut self, prog: &NodeProg, top_level: bool) -> GenResult {
        for stmt in prog.stmts.iter() {
            self.gen_stmt(stmt)?;
            // exit early if we have found a top level exit statement
            if top_level {
                #[allow(irrefutable_let_patterns)]
                if let NodeStmt::Exit(_) = stmt {
                    self.top_level_exit_found = true;
                    return Ok(());
                }
            }
        }

        Ok(())
    }

    fn gen_prelude(&mut self) {
        self.output
            .push_str("// ARM64 generated by iridium-compiler\n\n");
        self.output.push_str(".global _start\n");
        self.output.push_str(".p2align 2\n\n");
        self.output.push_str("_start:\n");
    }
}
