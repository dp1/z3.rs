use ast;
use ast::Ast;
use std::convert::{TryFrom, TryInto};
use std::ffi::CStr;
use std::fmt;
use z3_sys::*;

use crate::ast::Dynamic;
use {Context, DeclParam, FuncDecl, Sort, Symbol};

impl<'ctx> FuncDecl<'ctx> {
    pub(crate) unsafe fn wrap(ctx: &'ctx Context, z3_func_decl: Z3_func_decl) -> Self {
        Z3_inc_ref(ctx.z3_ctx, Z3_func_decl_to_ast(ctx.z3_ctx, z3_func_decl));
        Self { ctx, z3_func_decl }
    }

    pub fn new<S: Into<Symbol>>(
        ctx: &'ctx Context,
        name: S,
        domain: &[&Sort<'ctx>],
        range: &Sort<'ctx>,
    ) -> Self {
        assert!(domain.iter().all(|s| s.ctx.z3_ctx == ctx.z3_ctx));
        assert_eq!(ctx.z3_ctx, range.ctx.z3_ctx);

        let domain: Vec<_> = domain.iter().map(|s| s.z3_sort).collect();

        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_func_decl(
                    ctx.z3_ctx,
                    name.into().as_z3_symbol(ctx),
                    domain.len().try_into().unwrap(),
                    domain.as_ptr(),
                    range.z3_sort,
                ),
            )
        }
    }

    pub fn decl(&self) -> Z3_func_decl {
        self.z3_func_decl
    }

    /// Return the number of arguments of a function declaration.
    ///
    /// If the function declaration is a constant, then the arity is `0`.
    ///
    /// ```
    /// # use z3::{Config, Context, FuncDecl, Solver, Sort, Symbol};
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// let f = FuncDecl::new(
    ///     &ctx,
    ///     "f",
    ///     &[&Sort::int(&ctx), &Sort::real(&ctx)],
    ///     &Sort::int(&ctx));
    /// assert_eq!(f.arity(), 2);
    /// ```
    pub fn arity(&self) -> usize {
        unsafe { Z3_get_arity(self.ctx.z3_ctx, self.z3_func_decl) as usize }
    }

    /// Create a constant (if `args` has length 0) or function application (otherwise).
    ///
    /// Note that `args` should have the types corresponding to the `domain` of the `FuncDecl`.
    pub fn apply(&self, args: &[&dyn ast::Ast<'ctx>]) -> ast::Dynamic<'ctx> {
        assert!(args.iter().all(|s| s.get_ctx().z3_ctx == self.ctx.z3_ctx));

        let args: Vec<_> = args.iter().map(|a| a.get_z3_ast()).collect();

        unsafe {
            ast::Dynamic::wrap(self.ctx, {
                Z3_mk_app(
                    self.ctx.z3_ctx,
                    self.z3_func_decl,
                    args.len().try_into().unwrap(),
                    args.as_ptr(),
                )
            })
        }
    }

    /// Create a constant (if `args` has length 0) or function application (otherwise).
    ///
    /// Note that `args` should have the types corresponding to the `domain` of the `FuncDecl`.
    ///
    /// This variant of `apply` takes in concrete Dynamic<'ctx> objects as args
    pub fn apply_to_dynamic(&self, args: &[&Dynamic<'ctx>]) -> ast::Dynamic<'ctx> {
        assert!(args.iter().all(|s| s.get_ctx().z3_ctx == self.ctx.z3_ctx));

        let args: Vec<_> = args.iter().map(|a| a.get_z3_ast()).collect();

        unsafe {
            ast::Dynamic::wrap(self.ctx, {
                Z3_mk_app(
                    self.ctx.z3_ctx,
                    self.z3_func_decl,
                    args.len().try_into().unwrap(),
                    args.as_ptr(),
                )
            })
        }
    }

    /// Return the `DeclKind` of this `FuncDecl`.
    pub fn kind(&self) -> DeclKind {
        unsafe { Z3_get_decl_kind(self.ctx.z3_ctx, self.z3_func_decl) }
    }

    /// Return the name of this `FuncDecl`.
    ///
    /// Strings will return the `Symbol`.  Ints will have a `"k!"` prepended to
    /// the `Symbol`.
    pub fn name(&self) -> String {
        unsafe {
            let z3_ctx = self.ctx.z3_ctx;
            let symbol = Z3_get_decl_name(z3_ctx, self.z3_func_decl);
            match Z3_get_symbol_kind(z3_ctx, symbol) {
                SymbolKind::String => CStr::from_ptr(Z3_get_symbol_string(z3_ctx, symbol))
                    .to_string_lossy()
                    .into_owned(),
                SymbolKind::Int => format!("k!{}", Z3_get_symbol_int(z3_ctx, symbol)),
            }
        }
    }

    pub fn symbol(&self) -> Symbol {
        unsafe {
            let z3_ctx = self.ctx.z3_ctx;
            let symbol = Z3_get_decl_name(z3_ctx, self.z3_func_decl);
            Symbol::wrap(self.ctx, symbol)
        }
    }

    pub fn num_params(&self) -> usize {
        unsafe { Z3_get_decl_num_parameters(self.ctx.z3_ctx, self.z3_func_decl) as usize }
    }

    pub fn nth_param(&self, idx: usize) -> Option<DeclParam<'ctx>> {
        if idx >= self.num_params() {
            return None;
        }

        let z3_ctx = self.ctx.z3_ctx;
        let idx = u32::try_from(idx).unwrap();
        unsafe {
            match Z3_get_decl_parameter_kind(z3_ctx, self.z3_func_decl, idx) {
                ParameterKind::Int => {
                    let x = Z3_get_decl_int_parameter(z3_ctx, self.z3_func_decl, idx);
                    Some(DeclParam::Int(x))
                }
                ParameterKind::Double => {
                    let x = Z3_get_decl_double_parameter(z3_ctx, self.z3_func_decl, idx);
                    Some(DeclParam::Double(x))
                }
                ParameterKind::Rational => {
                    let x = Z3_get_decl_rational_parameter(z3_ctx, self.z3_func_decl, idx);
                    let x = CStr::from_ptr(x).to_owned().into_string().unwrap();
                    Some(DeclParam::Rational(x))
                }
                ParameterKind::Symbol => {
                    let x = Z3_get_decl_symbol_parameter(z3_ctx, self.z3_func_decl, idx);
                    Some(DeclParam::Symbol(Symbol::wrap(self.ctx, x)))
                }
                ParameterKind::Sort => {
                    let x = Z3_get_decl_sort_parameter(z3_ctx, self.z3_func_decl, idx);
                    Some(DeclParam::Sort(Sort::wrap(self.ctx, x)))
                }
                ParameterKind::AST => {
                    let x = Z3_get_decl_ast_parameter(z3_ctx, self.z3_func_decl, idx);
                    Some(DeclParam::Ast(Dynamic::wrap(self.ctx, x)))
                }
                ParameterKind::FuncDecl => {
                    let x = Z3_get_decl_func_decl_parameter(z3_ctx, self.z3_func_decl, idx);
                    Some(DeclParam::FuncDecl(FuncDecl::wrap(self.ctx, x)))
                }
            }
        }
    }

    pub fn params(&self) -> Vec<DeclParam<'ctx>> {
        let n = self.num_params();
        (0..n).map(|i| self.nth_param(i).unwrap()).collect()
    }
}

impl<'ctx> fmt::Display for FuncDecl<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_func_decl_to_string(self.ctx.z3_ctx, self.z3_func_decl) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> fmt::Debug for FuncDecl<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<'ctx> Drop for FuncDecl<'ctx> {
    fn drop(&mut self) {
        unsafe {
            Z3_dec_ref(
                self.ctx.z3_ctx,
                Z3_func_decl_to_ast(self.ctx.z3_ctx, self.z3_func_decl),
            );
        }
    }
}
