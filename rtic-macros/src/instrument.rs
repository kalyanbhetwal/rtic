#[allow(dead_code,unused_imports, non_camel_case_types,non_upper_case_globals, unused_variables)]

use std::collections::{HashSet, HashMap};  

use proc_macro::TokenStream;
use quote::{quote, ToTokens};

use syn::ExprReference;
#[allow(unused_imports)]
use syn::{
    parse_macro_input, parse_quote,
    Expr, ExprAssign, ExprBinary, ExprField, ExprIndex, ExprPath, ExprUnary, ItemFn, Result, Stmt, Ident,BinOp, ExprClosure,
    ExprIf, Block, ExprUnsafe, UnOp
};

use syn::visit_mut::VisitMut;

struct WARVisitor{
    reads: HashSet<String>,
    writes: HashSet<String>,
    conditional_writes: HashMap<String, usize>,
    branch_count: usize, // Count the number of branches
    in_region: bool,
    tainted_vars: HashSet<String>,
    branch_reads: HashSet<String>,
    stmts :Vec<Stmt>
}

impl WARVisitor {
    fn new() -> Self {
        WARVisitor{
            reads : HashSet::new(),
            writes: HashSet::new(),
            conditional_writes: HashMap::new(),
            branch_count: 0,
            in_region: false,
            tainted_vars: HashSet::new(),
            branch_reads: HashSet::new(),
            stmts: vec![]
        }
    }

    fn add_checkpointed_vars(&mut self, var: &str){

        self.writes.insert(var.to_string());
        //println!("the WAR dependencies are {}", var);

        if var.starts_with("*") {
            let ident = Ident::new(&var[1..], proc_macro2::Span::call_site());
            self.stmts.push(parse_quote! {
                save_variables(#ident as *const _, core::mem::size_of_val(#ident));
            });
        }else if var.contains("[") && var.ends_with("]") {
            // Handle array accesses like arr[i]
            let index_start = var.find("[").unwrap();
            let index_end = var.find("]").unwrap();
            let array_name = &var[..index_start];
            let index_expr = &var[index_start + 1..index_end];
    
            // Parse index expression to an expression
            let index_expr: syn::Expr = match syn::parse_str(index_expr) {
                Ok(expr) => expr,
                Err(err) => {return ()}
            };
    
            let ident = Ident::new(array_name, proc_macro2::Span::call_site());
            self.stmts.push(parse_quote! {
                save_variables(&#ident[#index_expr] as *const _, core::mem::size_of_val(&#ident[#index_expr]));
            });
        }
        else{
            //println!("the idents are {:?}", var);
            let ident = Ident::new(&var, proc_macro2::Span::call_site());
            self.stmts.push(parse_quote! {
                save_variables(&#ident as *const _, core::mem::size_of_val(&#ident));
            });
        }
    }

    //add conditionally written variables
    fn add_emw_dependency(&mut self, var: &str){
        let mut updated_var = var;
        if updated_var.contains("_#"){
            updated_var = var.splitn(2, "_#").next().unwrap_or("");
            self.reads.insert(updated_var.to_string());
            return
        }
        if !self.writes.contains(updated_var){
            self.add_checkpointed_vars(updated_var);
        }

    }
    // Add WAR dependency if not already written
    fn add_war_dependency(&mut self, var: &str) {
        let mut updated_var = var;
        if updated_var.contains("_#"){
            updated_var = var.splitn(2, "_#").next().unwrap_or("");
        }
        if self.reads.contains(updated_var) && !self.writes.contains(updated_var) {
            self.add_checkpointed_vars(updated_var);
           
        }
    }
    fn process_emw(&mut self, var_name: String) {
        let counter = self.conditional_writes.entry(var_name).or_insert(0);
        *counter += 1;
    }

    fn output_fn(&self, original_fn: &ItemFn) -> ItemFn {
        let mut output_fn = original_fn.clone();
        output_fn.block.stmts = self.stmts.clone();
        output_fn
    }

    fn taint_var(&mut self, var: String) {
        self.tainted_vars.insert(var);
    }

    fn propagate_taints(&mut self, reads: HashSet<String>, writes:String){
        for read in reads{
            if self.tainted_vars.contains(&read){
                self.tainted_vars.insert(writes);
                //println!("taints {:?}", self.tainted_vars);
                break;
            }
        }

    }

    fn is_branch_tainted(&mut self, reads: HashSet<String>)->bool{
        for read in reads{
            if self.tainted_vars.contains(&read){
                //println!("the branches are tainited {}",read);
                return true;
            }
        }
        return false;
    }

    fn process_branch_reads(&mut self, reads: HashSet<String>){
        
        for read in &reads{
            let mut updated_read: &str = read;
            if updated_read.contains("_#"){
                updated_read = updated_read.splitn(2, "_#").next().unwrap_or("");
            }
           self.branch_reads.insert(updated_read.to_string());
        }
        
    }

    fn extract_vars_from_expr(&self, expr: &Expr) -> (HashSet<String>, HashSet<String>) {
        let mut reads = HashSet::new();
        let mut writes = HashSet::new();

        match expr {
            Expr::Path(ExprPath { path, .. }) => {
                //println!("my path {:?}", path.to_token_stream());
                if let Some(ident) = path.get_ident() {
                   // println!("all the paths {}", ident);
                    reads.insert(ident.to_string());
                }
            }
            Expr::Binary(ExprBinary { left, right, op, .. }) => {
                let (reads_, _) = self.extract_vars_from_expr(left);
                let (writes_, _) = self.extract_vars_from_expr(right);
                reads.extend(reads_.clone());
                writes.extend(reads_);  
                reads.extend(writes_);

            }
            Expr::Unary(ExprUnary {op, expr, .. }) => {
                match op {
                    UnOp::Deref(_) => {
    
                        if let Expr::Path(ExprPath { path, .. }) = &**expr {
                            if let Some(ident) = path.get_ident() {
                                let pointer_expr = format!("*{}", ident);
                                reads.insert(pointer_expr);
                            }
                        }
                    }
                    _ => {
                        //println!(" rest of the test {:?}", reads);
                        let (sub_reads, _) = self.extract_vars_from_expr(expr);
                        reads.extend(sub_reads);
                    }
                }
            }
            Expr::Field(ExprField { base, .. }) => {
                //println!("hello ");
                let (base_reads, base_writes) = self.extract_vars_from_expr(base);
                reads.extend(base_reads);
                writes.extend(base_writes);
            }
            Expr::Index(ExprIndex { expr, index, .. }) => {
                if let Expr::Path(ExprPath { path, .. }) = &**expr {
                    if let Some(ident) = path.get_ident() {
                        let index_str = index.to_token_stream().to_string();
                        let location = format!("{}[{}]", ident, index_str);
                        reads.insert(location);
                    }
                }
                let (index_reads, index_writes) = self.extract_vars_from_expr(index);
                reads.extend(index_reads);
                writes.extend(index_writes);
            }
            Expr::Assign(assign) => {

                let (writes_, _) = self.extract_vars_from_expr(&assign.left);
                let (reads_, _) = self.extract_vars_from_expr(&assign.right);

                if let Expr::Reference(ExprReference {expr, mutability,..}) = &*assign.right{
                    //println!("5679 {} {}",expr.to_token_stream(), mutability.to_token_stream());
                    for w in writes_{
                        let fmt_str = format!("*{}_#{}",w, expr.to_token_stream());
                        //println!("{}",fmt_str); 
                        writes.insert(fmt_str);
                    }
                }else{writes.extend(writes_);}
               // writes.extend(writes_);
                reads.extend(reads_);
        
            }
            _ => {}
        }

        (reads, writes)
    }

    fn visit_else_branch(&mut self, else_branch: &Expr) {
        match else_branch {
            Expr::If(expr_if) => {
               self.visit_conditional_expr(expr_if);
            }
            _ => {
                self.branch_count += 1;
                if let Expr::Block(block) = else_branch {
                    for stmt in &block.block.stmts {
                        if let Stmt::Expr(expr,_)  = stmt {
                            let (_, writes) = self.extract_vars_from_expr(expr);
                            for w in writes{
                                self.process_emw(w);

                            }
                        }
                    }
                }

            }
        }
    }

    fn visit_conditional_expr(&mut self, expr_if: &ExprIf) {
        self.branch_count += 1;
        let (reads_, _) = self.extract_vars_from_expr(&expr_if.cond);
        //println!("my reads {:?}", reads_);

        self.process_branch_reads(reads_);
        //self.branch_reads.extend(reads_);

        for stmt in &expr_if.then_branch.stmts {
            if let Stmt::Expr(expr,_)  = stmt {
                let (_, writes) = self.extract_vars_from_expr(expr);
                for w in writes{
                    //println!("The writes are {}",w);
                    self.process_emw(w);
                }
            }
        }

        // Track writes in the 'else if/else' branches
        if let Some((_, else_branch)) = &expr_if.else_branch {
            self.visit_else_branch(else_branch);
        }
    }

}
impl VisitMut for WARVisitor {
    fn visit_stmt_mut(&mut self, stmt: &mut Stmt){
        match stmt {
            Stmt::Expr(Expr::Call(call), _) => {
                if let Expr::Path(ExprPath { path, .. }) = &*call.func {
                    if let Some(ident) = path.get_ident() {
                        if ident == "start_atomic" {
                            //println!("in start");
                            self.in_region = true;
                        } else if ident == "end_atomic" {
                            self.in_region = false;
                            //println!("in end");
                        }
                        else{
                            println!("I am here and there ");
                        }
                    }
                }
                self.stmts.push(stmt.clone());
            }
            Stmt::Expr(Expr::MethodCall(method_call),_) =>{
                if method_call.method == "lock" {
                    println!("I found lock");
                    if let Some(arg) = method_call.args.first_mut() {
                        if let Expr::Closure(ExprClosure { body, .. }) = arg {
                            
                            if let Expr::Block(closure_body) = &mut **body {
                                let new_stmt: syn::Stmt = parse_quote! {
                                    let x = 42;
                                };
                                    println!("test {:?}", closure_body.to_token_stream().to_string());
                                   closure_body.block.stmts.insert(0, new_stmt);
                            }
                           
                        }

                    }

                }
                self.stmts.push(stmt.clone()); 
            }
            Stmt::Local(_)=>{
                if self.in_region {
                    println!("I am here and there {}", stmt.to_token_stream());
                }
                self.stmts.push(stmt.clone()); 
            }
            Stmt::Expr(expr,_)=>{
                if self.in_region {
                    self.visit_expr_mut(expr);
                }
                self.stmts.push(stmt.clone());
            } 
            _ => {
                //println!("stmt {}", stmt.to_token_stream());
                self.stmts.push(stmt.clone());
            }
        }
    }
    
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        match expr {
            Expr::Assign(assign) => {
                //println!("here1 {}", assign.to_token_stream());
                //println!("The assigment stmt {}",assign.to_token_stream());
                //let (reads_, writes_) = self.extract_vars_from_expr(assign);
                //println!("{:?} and 4567 {:?}", reads_, writes_);
                match &mut *assign.left { 
                    Expr::Index(ExprIndex { expr, index, .. }) => {
                    }
                    Expr::Unary(unary_expr) if matches!(unary_expr.op, syn::UnOp::Deref(_))=>{
                      
                        if let Expr::Path(ExprPath { path, .. }) = &*unary_expr.expr {
                            if let Some(ident) = path.get_ident() {
                                let to_write = format!("*{}", ident.to_string());
                                self.add_war_dependency(&to_write);
                        }
                    }

                    }
                    Expr::Unary(ExprUnary { op, expr, .. }) => {
                        //println!("here {} {:?}", expr.to_token_stream(), op.to_token_stream());
                        if let Expr::Path(ExprPath { path, .. }) = &**expr {
                            if let Some(ident) = path.get_ident() {
                                self.add_war_dependency(&ident.to_string());
                            }
                        }
                    }
                    Expr::Field(ExprField { base, .. }) => {
                    }
                    Expr::Path(ExprPath { path,..})=>{
                        //println!("{} right.. {}",path.to_token_stream(), &assign.right.to_token_stream());
                        let (reads_, _) = self.extract_vars_from_expr(&assign.right);
                        self.reads.extend(reads_.clone());
                        let mut path_written = "rnd_str".to_string();
                        if let Some(ident) = path.get_ident() {
                            path_written = ident.to_string();
                            self.add_war_dependency(&ident.to_string());
                            self.propagate_taints(reads_,path_written.clone());
                        }
                        if let Expr::Call(call) = &*assign.right {
                            if let Expr::Path(ExprPath{path,..}) = &*call.func {
                            if let Some(ident) = path.get_ident() {
                                if ident.to_string().contains("input") {
                                   self.taint_var(path_written);
                                }
                            }
                        }
                        }
                    }
                     _ => { println!("No match {}", expr.to_token_stream().to_string());}  

                    }
                }
            Expr::Path(ExprPath { path, .. }) => {
                let var_name = path.segments.last().unwrap().ident.to_string();
                self.reads.insert(var_name);
            },

            Expr::Binary(ExprBinary { left, op,right,..})=>{
                match &**left {
                    Expr::Index(ExprIndex { expr, index, .. }) => {
                        if let Expr::Path(ExprPath { path, .. }) = &**expr {
                            if let Some(ident) = path.get_ident() {
                                let index_str = index.to_token_stream().to_string();
                                let location = format!("{}[{}]", ident, index_str);
                                let (loc_reads, _) = self.extract_vars_from_expr(right);
                                self.reads.extend(loc_reads.clone());
                                self.reads.insert(location.clone());
                                //println!("the reads are: {:?} and writes are: {:?}", self.reads, self.writes);
                                self.add_war_dependency(&location);
                                self.propagate_taints(loc_reads,location );
                            }
                        }
                    }
                    Expr::Unary(unary_expr) if matches!(unary_expr.op, syn::UnOp::Deref(_)) =>{
                        if let Expr::Path(ExprPath { path, .. }) = &*unary_expr.expr {
                            if let Some(ident) = path.get_ident() {
                                let to_write = format!("*{}", ident.to_string());
                                self.add_war_dependency(&to_write);
                            }
                        }
                     }
                     Expr::Path(ExprPath { path, .. }) => {
                        if let Some(ident) = path.get_ident() {
                            self.reads.insert(ident.to_string());
                            self.add_war_dependency(&ident.to_string());
                        }
                    }
                    _ => {println!("All left  {}", right.to_token_stream());}
                }
            }
            
            Expr::If(expr_if) => {
                self.visit_conditional_expr(expr_if);
                let flag = self.is_branch_tainted(self.branch_reads.clone());
                if flag {
                    self.tainted_vars.extend(self.conditional_writes.keys().cloned());
                    let unique_writes: HashSet<_> = self.conditional_writes.iter()
                                                    .filter(|(_, &count)| count != self.branch_count || (self.branch_count == 1 && count == 1))
                                                    .map(|(var, _)| var.clone())
                                                    .collect();

                    for var in &unique_writes {
                        //println!("the vars in if {}",var);
                        self.add_emw_dependency(var);
                    }
                }
                self.branch_count = 0;
                self.conditional_writes.drain();
            }

            Expr::Unsafe(expr_unsafe) => {
                //self.visit_unsafe_expr(expr_unsafe);
                //let back_up_stms = self.stmts.clone();
                //self.stmts.clear();
                for stmt in &expr_unsafe.block.stmts{
                    if let Stmt::Expr(expr,_) = stmt {
                        let (reads , writes) = self.extract_vars_from_expr(expr);
                        //println!("the unsafe reads and writes are {:?} {:?}", reads, writes);
                        self.reads.extend(reads);
                        // there will be single write but still this way is easier
                        for w in &writes{
                            let ident = Ident::new(&w, proc_macro2::Span::call_site());
                            self.stmts.push(  parse_quote! {
                                unsafe {save_variables(&#ident as *const _, core::mem::size_of_val(&#ident)); }
                            });
                            }
                        }
                    }
                    //self.stmts.extend(back_up_stms);
            }
            _ => {
               println!("shouldn't be here {}", expr.to_token_stream().to_string() );
               // visit_mut::visit_expr_mut(self, expr)
            }
        }

    }
}

pub fn my_proc_macro(stmts: &mut Vec<Stmt>) -> Vec<Stmt> {


    // for s in stmts{
    //     println!("this is test {:?}", s.to_token_stream().to_string());
    // }
    
    let stmts_ = stmts.clone();
    let mut visitor = WARVisitor::new();
    for mut s in &mut *stmts{
        visitor.visit_stmt_mut(&mut s);
    }
    // for s in visitor.stmts{
    //         println!("the is stmts {:?}", s.to_token_stream().to_string());
    // }
    visitor.stmts
    // Parse the input tokens into a syntax tree
//     let mut input = parse_macro_input!(item as ItemFn);

//     let mut visitor = WARVisitor::new();
//     visitor.visit_item_fn_mut(&mut input);
//     //println!("3456 {:?}", visitor.tainted_vars);

//     let transformed_fn = visitor.output_fn(&input);

//     TokenStream::from(quote! {
//         #transformed_fn
//     })
}
