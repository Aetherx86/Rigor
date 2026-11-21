//! Kernel error definitions. Every soundness or well-typedness failure surfaces as a typed error.

use core::fmt;

use crate::arena::{ExprId, FVarId, NameId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KernelError {
    DuplicateDeclaration(NameId),
    UnknownConstant(NameId),
    DuplicateLevelParam(NameId),
    UnboundLevelParam(NameId),
    LevelParamCountMismatch { constant: NameId, expected: usize, got: usize },
    UnboundBVar(u32),
    UnknownFVar(FVarId),
    ExpectedSort(ExprId),
    ExpectedPi(ExprId),
    TypeMismatch { expected: ExprId, got: ExprId },
    TheoremNotInProp { name: NameId, sort: ExprId },
    InvalidInductive(String),
    NonPositiveInductive { ind: NameId, ctor: NameId },
    UniverseTooSmall { ind: NameId, ctor: NameId },
    InvalidProjection { struct_name: NameId, idx: u32, reason: &'static str },
    Unsupported(&'static str),
}

impl fmt::Display for KernelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            KernelError::DuplicateDeclaration(n) => write!(f, "duplicate declaration: {n:?}"),
            KernelError::UnknownConstant(n) => write!(f, "unknown constant: {n:?}"),
            KernelError::DuplicateLevelParam(n) => write!(f, "duplicate universe parameter: {n:?}"),
            KernelError::UnboundLevelParam(n) => write!(f, "unbound universe parameter: {n:?}"),
            KernelError::LevelParamCountMismatch { constant, expected, got } => {
                write!(f, "universe parameter count mismatch for {constant:?}: expected {expected}, got {got}")
            }
            KernelError::UnboundBVar(idx) => write!(f, "unbound de Bruijn variable #{idx}"),
            KernelError::UnknownFVar(id) => write!(f, "unknown free variable {id:?}"),
            KernelError::ExpectedSort(ty) => write!(f, "expected a Sort (universe), got {ty:?}"),
            KernelError::ExpectedPi(ty) => write!(f, "expected a Pi (function) type, got {ty:?}"),
            KernelError::TypeMismatch { expected, got } => write!(f, "type mismatch: expected {expected:?}, got {got:?}"),
            KernelError::TheoremNotInProp { name, sort } => write!(f, "theorem {name:?} must live in Prop (Sort 0), got {sort:?}"),
            KernelError::InvalidInductive(msg) => write!(f, "invalid inductive declaration: {msg}"),
            KernelError::NonPositiveInductive { ind, ctor } => write!(f, "non-strictly-positive occurrence of {ind:?} in constructor {ctor:?}"),
            KernelError::UniverseTooSmall { ind, ctor } => write!(f, "constructor {ctor:?} has a field in a universe larger than {ind:?}"),
            KernelError::InvalidProjection { struct_name, idx, reason } => write!(f, "invalid projection {struct_name:?}.{idx}: {reason}"),
            KernelError::Unsupported(msg) => write!(f, "unsupported kernel feature: {msg}"),
        }
    }
}

impl std::error::Error for KernelError {}
