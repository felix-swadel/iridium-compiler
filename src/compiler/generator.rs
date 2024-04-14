use super::cpu::*;
use super::node::*;

// in ARM64 the stack pointer needs to be 16-byte aligned
const STACK_DELTA: usize = 16;

pub type GenResult = Result<(), String>;
pub type TypeResult = Result<Type, String>;

enum Cycle {
    Loop(usize),
    While(usize),
}

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
    loop_counter: usize,
    while_counter: usize,
    loop_stack: Vec<Cycle>,
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
            loop_counter: 0,
            while_counter: 0,
            loop_stack: Vec::new(),
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

    fn fmt_branch(&mut self, label: &str) {
        self.output.push_str(&format!("    b {}\n", label));
    }

    fn fmt_label(&mut self, label: &str) {
        self.output.push_str(&format!("{}:\n", label));
    }

    fn fmt_branch_if_false(&mut self, reg: Register, label: &str) {
        self.output
            .push_str(&format!("    tbz {}, #0, {}\n", reg, label));
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

    fn expr_is_atomic(&self, expr: &NodeExpr) -> bool {
        match expr {
            NodeExpr::Term(term) => match term {
                NodeTerm::Bool(_) | NodeTerm::Int32(_) | NodeTerm::Ident(_) => true,
                NodeTerm::Paren(expr) => self.expr_is_atomic(expr),
            },
            NodeExpr::BinOp(_) => false,
        }
    }
}

// loop management
impl Generator {
    fn gen_if_labels(&mut self) -> (String, String) {
        let if_label = format!(".condition{}_if", self.condition_counter);
        let end_label = format!(".condition{}_end", self.condition_counter);
        self.condition_counter += 1;
        (if_label, end_label)
    }

    fn gen_if_else_labels(&mut self) -> (String, String, String) {
        let if_label = format!(".condition{}_if", self.condition_counter);
        let else_label = format!(".condition{}_else", self.condition_counter);
        let end_label = format!(".condition{}_end", self.condition_counter);
        self.condition_counter += 1;
        (if_label, else_label, end_label)
    }

    fn gen_loop_labels(&mut self) -> (String, String) {
        let loop_label = format!(".loop{}_body", self.loop_counter);
        let end_label = format!(".loop{}_end", self.loop_counter);
        // push loop idx to stack for break and continue
        self.loop_stack.push(Cycle::Loop(self.loop_counter));
        self.loop_counter += 1;
        (loop_label, end_label)
    }

    fn gen_while_labels(&mut self) -> (String, String, String) {
        let while_label = format!(".while{}_condition", self.while_counter);
        let body_label = format!(".while{}_body", self.while_counter);
        let end_label = format!(".while{}_end", self.while_counter);
        // push loop idx to stack for break and continue
        self.loop_stack.push(Cycle::While(self.while_counter));
        self.while_counter += 1;
        (while_label, body_label, end_label)
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
            NodeTerm::Int32(val) => self.gen_int32(*val, reg_ix),
            NodeTerm::Bool(val) => self.gen_bool(*val, reg_ix),
            NodeTerm::Ident(name) => self.gen_ident(name, reg_ix),
            NodeTerm::Paren(expr) => self.gen_expr(expr.as_ref(), reg_ix),
        }
    }

    fn gen_bin_op_exprs(&mut self, bin_op: &NodeBinOp, lhs_ix: usize, rhs_ix: usize) -> TypeResult {
        let lhs = bin_op.lhs.as_ref();
        let rhs = bin_op.rhs.as_ref();
        let (lhs_type, rhs_type) = if self.expr_is_atomic(lhs) {
            if self.expr_is_atomic(rhs) {
                // both types are atomic
                (
                    self.gen_expr(lhs, Some(lhs_ix))?,
                    self.gen_expr(rhs, Some(rhs_ix))?,
                )
            } else {
                // rhs is not atomic - generate it first
                (
                    self.gen_expr(rhs, Some(rhs_ix))?,
                    self.gen_expr(lhs, Some(lhs_ix))?,
                )
            }
        } else {
            if self.expr_is_atomic(rhs) {
                // lhs is not atomic - generate it first
                (
                    self.gen_expr(lhs, Some(lhs_ix))?,
                    self.gen_expr(rhs, Some(rhs_ix))?,
                )
            } else {
                // neither side is atomic
                // push lhs to stack
                let lhs_type = self.gen_expr(lhs, None)?;
                // generate rhs into register
                let rhs_type = self.gen_expr(rhs, Some(rhs_ix))?;
                // pop lhs into register
                let lhs_bytes = lhs_type.bytes();
                self.pop(Register::infer(lhs_bytes, lhs_ix), lhs_bytes);
                (lhs_type, rhs_type)
            }
        };
        // check that binop is valid
        if lhs_type != rhs_type {
            Err(format!("invalid operands in binary operation: {}", bin_op))
        } else {
            Ok(lhs_type)
        }
    }

    fn gen_bin_op(&mut self, bin_op: &NodeBinOp, reg_ix: Option<usize>) -> TypeResult {
        // generate operands into r14, r15
        let lhs_ix = 14;
        let rhs_ix = 15;
        let in_type = self.gen_bin_op_exprs(bin_op, lhs_ix, rhs_ix)?;
        let out_type = match bin_op.op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => in_type,
            BinOp::Eq | BinOp::Ne | BinOp::Gt | BinOp::Lt | BinOp::Or | BinOp::And => Type::Bool,
        };
        // generate binary operator expression
        let in_bytes = in_type.bytes();
        let out_bytes = out_type.bytes();
        let lhs_reg = Register::infer(in_bytes, lhs_ix);
        let rhs_reg = Register::infer(in_bytes, rhs_ix);
        match reg_ix {
            Some(ix) => {
                let dst = Register::infer(out_bytes, ix);
                self.fmt_bin_op(dst, lhs_reg, bin_op.op, rhs_reg);
            }
            None => {
                let dst = Register::infer_default(out_bytes);
                self.fmt_bin_op(dst, lhs_reg, bin_op.op, rhs_reg);
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
        if let Some(exp_type) = &node_let.exp_type {
            if type_ != *exp_type {
                return Err(format!(
                    "cannot assign {} value to {} identifier",
                    type_, exp_type
                ));
            }
        }
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
        // store stack pointer at start of scope
        self.scopes.push(self.stack_length);
        for stmt in node_scope.stmts.iter() {
            self.gen_stmt(stmt)?;
        }
        // restore stack pointer from before scope
        self.stack_length = self.scopes.pop().unwrap();
        // remove any vars local to the scope
        for (ix, var) in self.vars.iter().rev().enumerate() {
            if var.location() > self.stack_length {
                continue;
            }
            // take complement of reverse iterator
            let cur_ix = self.vars.len() - ix;
            // remove all vars after cur_ix
            self.vars.truncate(cur_ix);
            break;
        }
        let stack_space = self.stack_capacity - self.stack_length;
        let num_deltas = stack_space / STACK_DELTA;
        if num_deltas > 0 {
            self.shrink_stack(num_deltas * STACK_DELTA);
        }

        Ok(())
    }

    fn gen_if_stmt(&mut self, node_condition: &NodeCondition) -> GenResult {
        let expr_type = self.gen_expr(&node_condition.expr, Some(15))?;
        match expr_type {
            Type::Bool => (),
            _ => {
                return Err(format!(
                    "expected bool in conditional expression - got: {}",
                    &node_condition.expr,
                ))
            }
        }
        let (if_label, end_label) = self.gen_if_labels();
        // if first bit of w15 is 0, branch to remainder
        self.fmt_branch_if_false(Register::W(15), &end_label);
        // else branch to if
        self.fmt_branch(&if_label);
        // generate if scope
        self.fmt_label(&if_label);
        self.gen_scope(&node_condition.scope)?;
        // branch to remainder
        self.fmt_branch(&end_label);
        // generate remainder
        self.fmt_label(&end_label);

        Ok(())
    }

    fn gen_if_else_stmt(&mut self, node_condition: &NodeCondition) -> GenResult {
        let expr_type = self.gen_expr(&node_condition.expr, Some(15))?;
        match expr_type {
            Type::Bool => (),
            _ => {
                return Err(format!(
                    "expected bool in conditional expression - got: {}",
                    &node_condition.expr,
                ))
            }
        }
        let (if_label, else_label, end_label) = self.gen_if_else_labels();
        // if first bit of w15 is 0, branch to else
        self.fmt_branch_if_false(Register::W(15), &else_label);
        // else branch to if
        self.fmt_branch(&if_label);
        // generate if scope
        self.fmt_label(&if_label);
        self.gen_scope(&node_condition.scope)?;
        // branch to remainder
        self.fmt_branch(&end_label);
        // generate else scope
        self.fmt_label(&else_label);
        self.gen_scope(node_condition.else_scope.as_ref().unwrap())?;
        // branch to remainder
        self.fmt_branch(&end_label);
        // generate remainder
        self.fmt_label(&end_label);

        Ok(())
    }

    fn gen_condition(&mut self, node_condition: &NodeCondition) -> GenResult {
        match node_condition.else_scope {
            Some(_) => self.gen_if_else_stmt(node_condition),
            None => self.gen_if_stmt(node_condition),
        }
    }

    fn gen_loop(&mut self, node_loop: &NodeLoop) -> GenResult {
        let (loop_label, end_label) = self.gen_loop_labels();
        // branch to loop
        self.fmt_branch(&loop_label);
        // generate loop
        self.fmt_label(&loop_label);
        self.gen_scope(&node_loop.scope)?;
        // pop loop idx from stack now that body has been generated
        if let None = self.loop_stack.pop() {
            panic!("ran out of loop indices while generating loop");
        }
        // branch back to start of loop body
        self.fmt_branch(&loop_label);
        // begin remainder block
        self.fmt_label(&end_label);

        Ok(())
    }

    fn gen_while(&mut self, node_while: &NodeWhile) -> GenResult {
        let (while_label, body_label, end_label) = self.gen_while_labels();
        // branch to while condition
        self.fmt_branch(&while_label);
        // generate while condition
        self.fmt_label(&while_label);
        // check condition
        let expr_type = self.gen_expr(&node_while.expr, Some(15))?;
        match expr_type {
            Type::Bool => (),
            _ => {
                return Err(format!(
                    "expected bool in conditional expression - got: {}",
                    &node_while.expr,
                ))
            }
        }
        // if first bit of w15 is 0, branch to remainder
        self.fmt_branch_if_false(Register::W(15), &end_label);
        // else branch to body
        self.fmt_branch(&body_label);
        // generate body
        self.fmt_label(&body_label);
        self.gen_scope(&node_while.scope)?;
        // pop loop idx from stack now that body has been generated
        if let None = self.loop_stack.pop() {
            panic!("ran out of loop indices while generating loop");
        }
        // branch back to condition
        self.fmt_branch(&while_label);
        // generate remainder
        self.fmt_label(&end_label);

        Ok(())
    }

    fn gen_continue(&mut self) -> GenResult {
        let Some(cycle_ix) = self.loop_stack.last() else {
            return Err("encountered `continue` outside of loop".to_owned());
        };
        match cycle_ix {
            Cycle::Loop(ix) => {
                self.fmt_branch(&format!(".loop{}_body", ix));
            }
            Cycle::While(ix) => {
                self.fmt_branch(&format!(".while{}_condition", ix));
            }
        }
        Ok(())
    }

    fn gen_break(&mut self) -> GenResult {
        let Some(cycle_ix) = self.loop_stack.last() else {
            return Err("encountered `break` outside of loop".to_owned());
        };
        match cycle_ix {
            Cycle::Loop(ix) => {
                self.fmt_branch(&format!(".loop{}_end", ix));
            }
            Cycle::While(ix) => {
                self.fmt_branch(&format!(".while{}_end", ix));
            }
        }
        Ok(())
    }

    fn gen_stmt(&mut self, stmt: &NodeStmt) -> GenResult {
        match stmt {
            NodeStmt::Exit(node_exit) => self.gen_exit(node_exit),
            NodeStmt::Let(node_let) => self.gen_let(node_let),
            NodeStmt::Assign(node_assign) => self.gen_assign(node_assign),
            NodeStmt::Scope(node_scope) => self.gen_scope(node_scope),
            NodeStmt::Condition(node_condition) => self.gen_condition(node_condition),
            NodeStmt::Loop(node_loop) => self.gen_loop(node_loop),
            NodeStmt::While(node_while) => self.gen_while(node_while),
            NodeStmt::Continue => self.gen_continue(),
            NodeStmt::Break => self.gen_break(),
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
