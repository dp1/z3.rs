use z3_sys::*;
use Config;
use Context;
use ContextHandle;

impl Context {
    pub fn new(cfg: &Config) -> Context {
        Context {
            z3_ctx: unsafe {
                let p = Z3_mk_context_rc(cfg.z3_cfg);
                debug!("new context {:p}", p);
                Z3_set_error_handler(p, None);
                p
            },
            is_owned: true,
        }
    }

    /// Create a context around an existing Z3_context. This constructor DOES NOT take ownership of
    /// z3_ctx, it needs to be manually freed after this object is dropped.
    pub unsafe fn wrap(z3_ctx: Z3_context) -> Context {
        assert!(!z3_ctx.is_null());
        Context {
            z3_ctx,
            is_owned: false,
        }
    }

    /// Interrupt a solver performing a satisfiability test, a tactic processing a goal, or simplify functions.
    pub fn interrupt(&self) {
        self.handle().interrupt()
    }

    /// Obtain a handle that can be used to interrupt computation from another thread.
    ///
    /// # See also:
    ///
    /// - [`ContextHandle`]
    /// - [`ContextHandle::interrupt()`]
    pub fn handle(&self) -> ContextHandle {
        ContextHandle { ctx: self }
    }

    /// Returns a handle to the underlying Z3_context
    pub fn ctx(&self) -> Z3_context {
        self.z3_ctx
    }
}

impl<'ctx> ContextHandle<'ctx> {
    /// Interrupt a solver performing a satisfiability test, a tactic processing a goal, or simplify functions.
    pub fn interrupt(&self) {
        unsafe {
            Z3_interrupt(self.ctx.z3_ctx);
        }
    }
}

unsafe impl<'ctx> Sync for ContextHandle<'ctx> {}
unsafe impl<'ctx> Send for ContextHandle<'ctx> {}

impl Drop for Context {
    fn drop(&mut self) {
        if self.is_owned {
            unsafe { Z3_del_context(self.z3_ctx) }
        }
    }
}
