//! Rigor Trusted Computing Base: a zero-dependency, safe Rust CIC proof kernel.

#![forbid(unsafe_code)]

pub mod arena;
pub mod check;
pub mod env;
pub mod error;
pub mod expr;
pub mod hash;
pub mod inductive;
pub mod level;
pub mod nat;
pub mod reduce;

pub use arena::{
    Arena, BinderInfo, ExprData, ExprId, FVarId, LevelData, LevelId, LevelListId, LitId, Literal,
    NameId,
};
pub use check::TypeChecker;
pub use env::{
    ConstructorInfo, Declaration, Environment, FrozenEnv, InductiveInfo, QuotKind, RecursorInfo,
    RecursorRule, ReducibilityHint,
};
pub use error::KernelError;
pub use expr::{abstract_fvars, instantiate1, instantiate_level_params, instantiate_rev};
pub use inductive::{InductiveSpec, InductiveTypeSpec};
pub use nat::Nat;
pub use level::{level_eq, level_instantiate, level_is_nonzero, level_is_zero, level_leq};
