use std::ffi::CString;
use z3_sys::*;
use Context;
use Symbol;

impl Symbol {
    /// Wrap a raw [`Z3_symbol`].
    ///
    /// # Safety
    ///
    /// `sym` must be a valid pointer to a [`Z3_symbol`].
    pub unsafe fn wrap(ctx: &Context, sym: Z3_symbol) -> Self {
        match Z3_get_symbol_kind(ctx.z3_ctx, sym) {
            SymbolKind::Int => Symbol::Int(Z3_get_symbol_int(ctx.z3_ctx, sym) as u32),
            SymbolKind::String => {
                let sym = Z3_get_symbol_string(ctx.z3_ctx, sym);
                let sym = ::std::ffi::CStr::from_ptr(sym)
                    .to_owned()
                    .into_string()
                    .unwrap();
                Symbol::String(sym)
            }
        }
    }

    pub fn as_z3_symbol(&self, ctx: &Context) -> Z3_symbol {
        match self {
            Symbol::Int(i) => unsafe { Z3_mk_int_symbol(ctx.z3_ctx, *i as ::std::os::raw::c_int) },
            Symbol::String(s) => {
                let ss = CString::new(s.clone()).unwrap();
                let p = ss.as_ptr();
                unsafe { Z3_mk_string_symbol(ctx.z3_ctx, p) }
            }
        }
    }
}

impl From<u32> for Symbol {
    fn from(val: u32) -> Self {
        Symbol::Int(val)
    }
}

impl From<String> for Symbol {
    fn from(val: String) -> Self {
        Symbol::String(val)
    }
}

impl From<&str> for Symbol {
    fn from(val: &str) -> Self {
        Symbol::String(val.to_owned())
    }
}
