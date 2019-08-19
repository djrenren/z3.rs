use std::convert::TryInto;
use std::ffi::CStr;
use std::collections::HashMap;
use std::fmt;
use z3_sys::*;
use Context;
use FuncDecl;
use SortRef;
use Symbol;
use Z3_MUTEX;

/// Describes a sort that is not necessarily manifest in the Z3 context
/// This allows for passing around Sort independent of a context
/// so long as it consists of transparent sort types.
///
/// A SortDescription can contain a reference to an instantiated sort. This
/// is to support the use of Enum's and Datatype's that cannot be declared multiple
/// times.
#[derive(Debug)]
pub enum Sort<'ctx> {
    Int,
    Bool,
    Real,
    BV(u32),
    Array {
        domain: &'ctx Sort<'ctx>,
        range: &'ctx Sort<'ctx>
    },
    Set(&'ctx Sort<'ctx>),
    Enum(Enum<'ctx>),
    Ref(SortRef<'ctx>)
}

impl<'ctx> From<SortRef<'ctx>> for Sort<'ctx> {
    fn from(s: SortRef<'ctx>) -> Self {
        Self::Ref(s)
    }
}

impl<'ctx> Sort<'ctx> {
    pub(crate) fn as_z3_sort(&self, ctx: &Context) -> Z3_sort {
        match self {
            Self::Int => unsafe { Z3_mk_int_sort(ctx.z3_ctx)},
            Self::Bool => unsafe { Z3_mk_bool_sort(ctx.z3_ctx)},
            Self::Real => unsafe { Z3_mk_real_sort(ctx.z3_ctx)},
            Self::BV(bv) => unsafe { Z3_mk_bv_sort(ctx.z3_ctx, *bv as ::std::os::raw::c_uint)},
            Self::Enum(e) => e.sort.z3_sort,
            Self::Array { domain, range } => {
                let dom = domain.as_z3_sort(ctx);
                let rng = range.as_z3_sort(ctx);

                unsafe {
                    Z3_mk_array_sort(ctx.z3_ctx, dom, rng)
                }
            },
            Self::Set(s) => unsafe { Z3_mk_set_sort(ctx.z3_ctx, s.as_z3_sort(ctx))},
            Self::Ref(s) => s.z3_sort
        }
    }

    pub fn kind(&self) -> SortKind {
        match self {
            Self::Int => SortKind::Int,
            Self::Bool => SortKind::Bool,
            Self::Real => SortKind::Real,
            Self::BV(_) => SortKind::BV,
            Self::Array {..} => SortKind::Array,
            // Surprise! This is how Z3 works
            Self::Set(_) => SortKind::Array,
            Self::Enum(Enum {sort, ..}) => unsafe {
                Z3_get_sort_kind(sort.ctx.z3_ctx, sort.z3_sort)
            },
            Self::Ref(sr) => unsafe { 
                Z3_get_sort_kind(sr.ctx.z3_ctx, sr.z3_sort)
            }
        }
    }
}


impl<'ctx> fmt::Display for Sort<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Debug>::fmt(self, f)
    }
}

pub trait SortDescription {
    fn instantiate<'ctx>(&self, ctx: &'ctx Context) -> Sort<'ctx>;
}

impl<'ctx> SortDescription for Sort<'ctx> {
    fn instantiate<'out_ctx>(&self, ctx: &'out_ctx Context) -> Sort<'out_ctx> {
        Sort::Ref(SortRef::new(ctx, self.as_z3_sort(ctx)))
    }
}

#[derive(Clone, Debug)]
pub struct EnumDesc<'names>{
    name: Symbol,
    variant_names: &'names[Symbol],
}

impl<'names> EnumDesc<'names> {
    fn to_enum<'ctx>(&self, ctx: &'ctx Context) -> Enum<'ctx> {
        let variants_raw: Vec<_> = self.variant_names.iter().map(|s| s.as_z3_symbol(ctx)).collect();
        let mut enum_consts = vec![std::ptr::null_mut(); variants_raw.len()];
        let mut enum_testers = vec![std::ptr::null_mut(); variants_raw.len()];

        let sort = SortRef::new(ctx, unsafe {
            Z3_mk_enumeration_sort(
                ctx.z3_ctx,
                self.name.as_z3_symbol(ctx),
                variants_raw.len().try_into().unwrap(),
                variants_raw.as_ptr(),
                enum_consts.as_mut_ptr(),
                enum_testers.as_mut_ptr(),
            )
        });

        // increase ref counts
        for i in &enum_consts {
            unsafe {
                Z3_inc_ref(ctx.z3_ctx, *i as Z3_ast);
            }
        }
        for i in &enum_testers {
            unsafe {
                Z3_inc_ref(ctx.z3_ctx, *i as Z3_ast);
            }
        }

        // convert to Rust types
        let enum_consts = enum_consts
            .iter()
            .map(|z3_func_decl| unsafe { FuncDecl::from_raw(ctx, *z3_func_decl) });

        let enum_testers = enum_testers
            .iter()
            .map(|z3_func_decl| unsafe { FuncDecl::from_raw(ctx, *z3_func_decl)});

        let variants: HashMap<Symbol,_> = self.variant_names.iter().map(Clone::clone).zip(enum_consts.zip(enum_testers)
            .map(|(cons, tester)| Variant {cons, tester}))
            .collect();

        Enum { sort, variants}
    }
}

impl<'names> SortDescription for EnumDesc<'names> {
    fn instantiate<'ctx>(&self, ctx: &'ctx Context) -> Sort<'ctx> {
        Sort::Enum(self.to_enum(ctx))
    }
}

#[derive(Debug)]
pub struct Enum<'ctx> {
    sort: SortRef<'ctx>,
    variants: HashMap<Symbol, Variant<'ctx>>,
}

#[derive(Debug)]
pub struct Variant<'ctx> {
    cons: FuncDecl<'ctx>,
    tester: FuncDecl<'ctx>
}


impl<'ctx> SortRef<'ctx> {
    pub(crate) fn new(ctx: &'ctx Context, z3_sort: Z3_sort) -> Self {
        let guard = Z3_MUTEX.lock().unwrap();
        unsafe { Z3_inc_ref(ctx.z3_ctx, Z3_sort_to_ast(ctx.z3_ctx, z3_sort)) };
        SortRef { ctx, z3_sort }
    }

    pub fn kind(&self) -> SortKind {
        unsafe { Z3_get_sort_kind(self.ctx.z3_ctx, self.z3_sort) }
    }
}

impl<'ctx> fmt::Display for SortRef<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_sort_to_string(self.ctx.z3_ctx, self.z3_sort) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{}", s),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> fmt::Debug for SortRef<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<'ctx> Clone for SortRef<'ctx> {
    fn clone(&self) -> Self {
        Self::new(self.ctx, self.z3_sort)
    }
}

impl<'ctx> PartialEq<SortRef<'ctx>> for SortRef<'ctx> {
    fn eq(&self, other: &SortRef<'ctx>) -> bool {
        unsafe { Z3_is_eq_sort(self.ctx.z3_ctx, self.z3_sort, other.z3_sort) }
    }
}

impl<'ctx> Eq for SortRef<'ctx> {}

impl<'ctx> Drop for SortRef<'ctx> {
    fn drop(&mut self) {
        unsafe {
            Z3_dec_ref(
                self.ctx.z3_ctx,
                Z3_sort_to_ast(self.ctx.z3_ctx, self.z3_sort),
            );
        }
    }
}