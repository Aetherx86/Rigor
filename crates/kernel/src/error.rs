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
}

impl fmt::Display for KernelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for KernelError {}
