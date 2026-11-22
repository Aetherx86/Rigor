//! Inductive type validator, strict positivity checker (including sound nested inductive
//! elimination), Subsingleton large-elimination check, and structural recursor generator.

use crate::arena::{Arena, BinderInfo, ExprData, ExprId, FVarId, LevelId, NameId};
use crate::check::TypeChecker;
use crate::env::{ConstructorInfo, Declaration, InductiveInfo, RecursorInfo, RecursorRule};
use crate::error::KernelError;
use crate::expr::{
    abstract_fvars, expr_check_level_params, expr_mentions_any_const, expr_mentions_fvar,
    instantiate1, instantiate_level_params, replace_expr,
};
use crate::hash::FxHashMap;
use crate::level::{level_eq, level_is_zero, level_leq};

#[derive(Debug, Clone)]
pub struct InductiveTypeSpec {
    pub name: NameId,
    pub ty: ExprId,
    pub ctors: Vec<(NameId, ExprId)>,
}

#[derive(Debug, Clone)]
pub struct InductiveSpec {
    pub level_params: Box<[NameId]>,
    pub num_params: u32,
    pub types: Vec<InductiveTypeSpec>,
}

struct Binder { name: NameId, bi: BinderInfo, ty: ExprId, fv: FVarId }
struct RecField { field_idx: usize, target_ind: usize, extra: Vec<Binder>, target_indices: Vec<ExprId> }
struct ParsedCtor {
    name: NameId,
    ind_idx: usize,
    fields: Vec<Binder>,
    rec_fields: Vec<RecField>,
    result_indices: Vec<ExprId>,
}
struct ParsedInd {
    name: NameId,
    ty: ExprId,
    indices: Vec<Binder>,
    res_lvl: LevelId,
    is_prop: bool,
    ctor_names: Vec<NameId>,
}
struct NestedAux {
    aux_name: NameId,
    orig_app: ExprId,
    ctors: Vec<(NameId, NameId, ExprId)>, // (aux_ctor_name, orig_ctor_name, orig_ctor_app)
}

fn wrap(arena: &mut Arena, binders: &[Binder], mut body: ExprId, pi: bool) -> ExprId {
    for b in binders.iter().rev() {
        let abs = abstract_fvars(arena, body, &[b.fv]);
        body = if pi { arena.pi(b.name, b.bi, b.ty, abs) } else { arena.lam(b.name, b.bi, b.ty, abs) };
    }
    body
}

fn lvls_eq(arena: &mut Arena, a: &[LevelId], b: &[LevelId]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(&x, &y)| level_eq(arena, x, y))
}

/// Instantiate the leading Pi binders of `e` (after whnf) with `args`.
fn inst_pis(tc: &mut TypeChecker<'_>, mut e: ExprId, args: &[ExprId]) -> ExprId {
    for &a in args {
        e = tc.whnf(e);
        if let ExprData::Pi { body, .. } = *tc.arena.get_expr(e) { e = instantiate1(tc.arena, body, a); }
    }
    e
}

/// Open up to `max` leading Pi binders of `e` as new locals; returns them and the (whnf) rest.
fn open_pis(tc: &mut TypeChecker<'_>, mut e: ExprId, max: usize) -> (Vec<Binder>, ExprId) {
    let mut bs = Vec::new();
    while bs.len() < max {
        e = tc.whnf(e);
        let ExprData::Pi { name, binder_info, ty, body } = *tc.arena.get_expr(e) else { break };
        let fv = tc.push_local(ty, None);
        let fve = tc.arena.fvar(fv);
        bs.push(Binder { name, bi: binder_info, ty, fv });
        e = instantiate1(tc.arena, body, fve);
    }
    (bs, e)
}

/// Index locals of `ind` and the major premise type `I params indices`.
fn major_type(tc: &mut TypeChecker<'_>, ind: &ParsedInd, param_lvls: &[LevelId], param_fve: &[ExprId]) -> (Vec<ExprId>, ExprId) {
    let idx_e: Vec<ExprId> = ind.indices.iter().map(|ix| tc.arena.fvar(ix.fv)).collect();
    let head = tc.arena.const_(ind.name, param_lvls);
    let p = tc.arena.app_n(head, param_fve);
    let ty = tc.arena.app_n(p, &idx_e);
    (idx_e, ty)
}

fn ind_info(spec: &InductiveSpec, p: &ParsedInd, all: Box<[NameId]>, is_rec: bool, can_elim_large: bool) -> Declaration {
    Declaration::Inductive(InductiveInfo {
        name: p.name, level_params: spec.level_params.clone(), ty: p.ty,
        num_params: spec.num_params, num_indices: p.indices.len() as u32,
        all, ctors: p.ctor_names.clone().into(), is_rec, is_prop: p.is_prop, can_elim_large,
    })
}

/// Validate a (possibly mutual or nested) inductive block and generate Inductive, Constructor,
/// and Recursor declarations.
pub fn check_inductive_block(
    decls: &FxHashMap<NameId, Declaration>,
    arena: &mut Arena,
    spec: &InductiveSpec,
) -> Result<Vec<Declaration>, KernelError> {
    if spec.types.is_empty() {
        return Err(KernelError::InvalidInductive("empty inductive block".into()));
    }
    crate::check::check_unique_params(&spec.level_params)?;

    let orig_n = spec.types.len();
    let orig_names: Vec<NameId> = spec.types.iter().map(|t| t.name).collect();
    let mut seen = Vec::new();
    for &n in orig_names.iter().chain(spec.types.iter().flat_map(|t| t.ctors.iter().map(|(c, _)| c))) {
        if decls.contains_key(&n) || seen.contains(&n) {
            return Err(KernelError::DuplicateDeclaration(n));
        }
        seen.push(n);
    }

    // 1. Validate inductive headers and register provisional inductive constants.
    let mut work_decls = decls.clone();
    let mut parsed_inds = Vec::with_capacity(orig_n);
    let param_lvls: Vec<LevelId> = spec.level_params.iter().map(|&p| arena.lvl_param(p)).collect();
    {
        let mut tc = TypeChecker::new(&work_decls, arena);
        let mut hdr_params: Vec<Binder> = Vec::new();
        for (ti, t) in spec.types.iter().enumerate() {
            expr_check_level_params(tc.arena, t.ty, &spec.level_params)?;
            let _ = tc.infer_sort(t.ty)?;
            let mut cur = t.ty;
            for pi in 0..spec.num_params as usize {
                cur = tc.whnf(cur);
                let ExprData::Pi { name, binder_info, ty: dom, body } = *tc.arena.get_expr(cur) else {
                    return Err(KernelError::InvalidInductive("fewer binders than num_params".into()));
                };
                if ti == 0 {
                    let fv = tc.push_local(dom, None);
                    hdr_params.push(Binder { name, bi: binder_info, ty: dom, fv });
                    let fve = tc.arena.fvar(fv);
                    cur = instantiate1(tc.arena, body, fve);
                } else {
                    if !tc.is_def_eq(dom, hdr_params[pi].ty)? {
                        return Err(KernelError::InvalidInductive("mutual inductive parameter mismatch".into()));
                    }
                    let fve = tc.arena.fvar(hdr_params[pi].fv);
                    cur = instantiate1(tc.arena, body, fve);
                }
            }
            let (indices, cur) = open_pis(&mut tc, cur, usize::MAX);
            let ExprData::Sort(res_lvl) = *tc.arena.get_expr(cur) else {
                return Err(KernelError::InvalidInductive("inductive type must end in Sort".into()));
            };
            for _ in &indices { tc.pop_local(); }
            parsed_inds.push(ParsedInd {
                name: t.name, ty: t.ty, indices, res_lvl, is_prop: level_is_zero(tc.arena, res_lvl),
                ctor_names: t.ctors.iter().map(|(c, _)| *c).collect(),
            });
        }
        for _ in &hdr_params { tc.pop_local(); }
    }

    for p in &parsed_inds {
        work_decls.insert(p.name, ind_info(spec, p, orig_names.clone().into(), false, !p.is_prop));
    }

    // 2. Discover & expand any nested inductives (e.g., `Array Syntax`, `List Syntax`) into
    //    auxiliary mutual types so strict positivity, universes, and recursors are checked uniformly.
    let mut all_types = spec.types.clone();
    let mut nested_aux: Vec<NestedAux> = Vec::new();
    {
        let mut ti = 0usize;
        while ti < all_types.len() {
            let ctors_snapshot = all_types[ti].ctors.clone();
            for (ci, &(_, orig_cty)) in ctors_snapshot.iter().enumerate() {
                let mut tc = TypeChecker::new(&work_decls, arena);
                let (p_fvs, _) = open_pis(&mut tc, all_types[0].ty, spec.num_params as usize);
                let p_fve: Vec<ExprId> = p_fvs.iter().map(|b| tc.arena.fvar(b.fv)).collect();
                let mut cur = inst_pis(&mut tc, orig_cty, &p_fve);
                let mut fields = Vec::new();
                let mut new_aux_to_add: Vec<(InductiveTypeSpec, ParsedInd, NestedAux)> = Vec::new();
                loop {
                    cur = tc.whnf(cur);
                    let ExprData::Pi { name, binder_info, mut ty, body } = *tc.arena.get_expr(cur) else { break };
                    if expr_mentions_any_const(tc.arena, ty, &orig_names) {
                        let mut fty = ty;
                        let mut extra_pushed = 0usize;
                        let mut bad_dom = false;
                        loop {
                            fty = tc.whnf(fty);
                            let ExprData::Pi { ty: dom, body: eb, .. } = *tc.arena.get_expr(fty) else { break };
                            if expr_mentions_any_const(tc.arena, dom, &orig_names) { bad_dom = true; break; }
                            let efv = tc.push_local(dom, None);
                            let efve = tc.arena.fvar(efv);
                            extra_pushed += 1;
                            fty = instantiate1(tc.arena, eb, efve);
                        }
                        if !bad_dom {
                            let (hd, args) = tc.app_spine(fty);
                            if let ExprData::Const(jn, jlvls_id) = *tc.arena.get_expr(hd) {
                                let jlvls: Box<[LevelId]> = tc.arena.get_level_list(jlvls_id).into();
                                if !orig_names.contains(&jn) && !nested_aux.iter().any(|x| x.aux_name == jn) {
                                    if let Some(Declaration::Inductive(ji)) = decls.get(&jn) {
                                        let jnp = ji.num_params as usize;
                                        if ji.all.len() == 1 && args.len() == jnp + ji.num_indices as usize
                                            && args[..jnp].iter().any(|&a| expr_mentions_any_const(tc.arena, a, &orig_names))
                                            && !args[jnp..].iter().any(|&a| expr_mentions_any_const(tc.arena, a, &orig_names))
                                            && !args[..jnp].iter().any(|&a| fields.iter().any(|fb: &Binder| expr_mentions_fvar(tc.arena, a, fb.fv)))
                                        {
                                            let j_head = tc.arena.intern_expr(ExprData::Const(jn, jlvls_id));
                                            let orig_app = tc.arena.app_n(j_head, &args[..jnp]);
                                            let aux_name = if let Some(ex) = nested_aux.iter().find(|x| x.orig_app == orig_app)
                                                .or_else(|| new_aux_to_add.iter().find(|(_, _, x)| x.orig_app == orig_app).map(|(_, _, x)| x))
                                            {
                                                ex.aux_name
                                            } else {
                                                let idx = nested_aux.len() + new_aux_to_add.len() + 1;
                                                let an = tc.arena.name_str(spec.types[0].name, &format!("_nested_{idx}"));
                                                let aux_head = tc.arena.const_(an, &param_lvls);
                                                let aux_app = tc.arena.app_n(aux_head, &p_fve);
                                                // Build auxiliary type: instantiate `ji.ty` with `jlvls` & `args[..jnp]`, wrap `p_fvs`.
                                                let jty = instantiate_level_params(tc.arena, ji.ty, &ji.level_params, &jlvls);
                                                let jty = inst_pis(&mut tc, jty, &args[..jnp]);
                                                let mut j_indices = Vec::new();
                                                let mut jc = jty;
                                                let j_res_lvl = loop {
                                                    jc = tc.whnf(jc);
                                                    match *tc.arena.get_expr(jc) {
                                                        ExprData::Pi { name: in_, binder_info: ibi, ty: ity, body: ib } => {
                                                            let ifv = tc.fresh_fvar();
                                                            let ifve = tc.arena.fvar(ifv);
                                                            j_indices.push(Binder { name: in_, bi: ibi, ty: ity, fv: ifv });
                                                            jc = instantiate1(tc.arena, ib, ifve);
                                                        }
                                                        ExprData::Sort(l) => break l,
                                                        _ => break Arena::LEVEL_ZERO,
                                                    }
                                                };
                                                let aux_ty = wrap(tc.arena, &p_fvs, jty, true);
                                                let mut aux_ctors = Vec::new();
                                                let mut aux_ctor_map = Vec::new();
                                                for (k, &orig_cn) in ji.ctors.iter().enumerate() {
                                                    let Some(Declaration::Constructor(oc)) = decls.get(&orig_cn) else { continue };
                                                    let octy = instantiate_level_params(tc.arena, oc.ty, &oc.level_params, &jlvls);
                                                    let octy = inst_pis(&mut tc, octy, &args[..jnp]);
                                                    let octy = replace_expr(tc.arena, octy, orig_app, aux_app);
                                                    let aux_cn = tc.arena.name_num(an, k as u64);
                                                    let aux_cty = wrap(tc.arena, &p_fvs, octy, true);
                                                    let orig_c_head = tc.arena.intern_expr(ExprData::Const(orig_cn, jlvls_id));
                                                    let orig_c_app = tc.arena.app_n(orig_c_head, &args[..jnp]);
                                                    aux_ctors.push((aux_cn, aux_cty));
                                                    aux_ctor_map.push((aux_cn, orig_cn, orig_c_app));
                                                }
                                                let pi = ParsedInd {
                                                    name: an, ty: aux_ty, indices: j_indices, res_lvl: j_res_lvl,
                                                    is_prop: level_is_zero(tc.arena, j_res_lvl),
                                                    ctor_names: aux_ctors.iter().map(|(c, _)| *c).collect(),
                                                };
                                                let its = InductiveTypeSpec { name: an, ty: aux_ty, ctors: aux_ctors };
                                                new_aux_to_add.push((its, pi, NestedAux { aux_name: an, orig_app, ctors: aux_ctor_map }));
                                                an
                                            };
                                            let aux_head = tc.arena.const_(aux_name, &param_lvls);
                                            let aux_app = tc.arena.app_n(aux_head, &p_fve);
                                            ty = replace_expr(tc.arena, ty, orig_app, aux_app);
                                        }
                                    }
                                }
                            }
                        }
                        for _ in 0..extra_pushed { tc.pop_local(); }
                    }
                    let fv = tc.push_local(ty, None);
                    let fve = tc.arena.fvar(fv);
                    fields.push(Binder { name, bi: binder_info, ty, fv });
                    cur = instantiate1(tc.arena, body, fve);
                }
                if !new_aux_to_add.is_empty() || !nested_aux.is_empty() {
                    let inner = wrap(tc.arena, &fields, cur, true);
                    all_types[ti].ctors[ci].1 = wrap(tc.arena, &p_fvs, inner, true);
                }
                for _ in &fields { tc.pop_local(); }
                for _ in &p_fvs { tc.pop_local(); }
                drop(tc);
                for (its, pi, aux) in new_aux_to_add {
                    work_decls.insert(pi.name, ind_info(spec, &pi, Box::new([pi.name]), true, !pi.is_prop));
                    parsed_inds.push(pi);
                    all_types.push(its);
                    nested_aux.push(aux);
                }
            }
            ti += 1;
        }
    }

    let all_names: Vec<NameId> = all_types.iter().map(|t| t.name).collect();
    let rec_names: Vec<NameId> = (0..all_types.len())
        .map(|i| {
            if i < orig_n { arena.name_str(all_types[i].name, "rec") }
            else { arena.name_str(all_types[0].name, &format!("rec_{}", i - orig_n + 1)) }
        })
        .collect();
    for &rn in &rec_names {
        if decls.contains_key(&rn) { return Err(KernelError::DuplicateDeclaration(rn)); }
    }

    // 3. Validate all constructors (original + expanded nested) for universe bounds and strict positivity.
    let mut tc = TypeChecker::new(&work_decls, arena);
    let (param_fvs, _) = open_pis(&mut tc, all_types[0].ty, spec.num_params as usize);
    let param_fve: Vec<ExprId> = param_fvs.iter().map(|p| tc.arena.fvar(p.fv)).collect();
    for p in &mut parsed_inds {
        let c = inst_pis(&mut tc, p.ty, &param_fve);
        p.indices = open_pis(&mut tc, c, usize::MAX).0;
        for _ in &p.indices { tc.pop_local(); }
    }

    let mut parsed_ctors = Vec::new();
    let mut is_rec = false;
    for (ti, t) in all_types.iter().enumerate() {
        let ind = &parsed_inds[ti];
        for &(cname, cty) in &t.ctors {
            expr_check_level_params(tc.arena, cty, &spec.level_params)?;
            let _ = tc.infer_sort(cty)?;
            let mut cur = cty;
            for pf in &param_fvs {
                cur = tc.whnf(cur);
                let ExprData::Pi { ty: dom, body, .. } = *tc.arena.get_expr(cur) else {
                    return Err(KernelError::InvalidInductive("ctor has fewer binders than num_params".into()));
                };
                if !tc.is_def_eq(dom, pf.ty)? {
                    return Err(KernelError::InvalidInductive("ctor parameter type mismatch".into()));
                }
                let fve = tc.arena.fvar(pf.fv);
                cur = instantiate1(tc.arena, body, fve);
            }
            let mut fields = Vec::new();
            let mut rec_fields = Vec::new();
            loop {
                cur = tc.whnf(cur);
                let ExprData::Pi { name, binder_info, ty, body } = *tc.arena.get_expr(cur) else { break };
                if !ind.is_prop {
                    let field_lvl = tc.infer_sort(ty)?;
                    if !level_leq(tc.arena, field_lvl, ind.res_lvl) {
                        return Err(KernelError::UniverseTooSmall { ind: ind.name, ctor: cname });
                    }
                }
                if expr_mentions_any_const(tc.arena, ty, &all_names) {
                    is_rec = true;
                    let rf = check_strict_positivity(
                        &mut tc, ind.name, cname, ty, &all_names, &param_lvls, &param_fve, fields.len(),
                    )?;
                    rec_fields.push(rf);
                }
                let fv = tc.push_local(ty, None);
                let fve = tc.arena.fvar(fv);
                fields.push(Binder { name, bi: binder_info, ty, fv });
                cur = instantiate1(tc.arena, body, fve);
            }
            let (head, args) = tc.app_spine(cur);
            let ok_head = match *tc.arena.get_expr(head) {
                ExprData::Const(hn, hl_id) => {
                    let hl: Box<[LevelId]> = tc.arena.get_level_list(hl_id).into();
                    hn == ind.name && lvls_eq(tc.arena, &hl, &param_lvls)
                }
                _ => false,
            };
            if !ok_head || args.len() != spec.num_params as usize + ind.indices.len()
                || args.iter().zip(&param_fve).any(|(&g, &e)| g != e)
            {
                return Err(KernelError::InvalidInductive("ctor return type does not match inductive".into()));
            }
            for _ in &fields { tc.pop_local(); }
            parsed_ctors.push(ParsedCtor {
                name: cname, ind_idx: ti, fields, rec_fields,
                result_indices: args[spec.num_params as usize..].to_vec(),
            });
        }
    }

    // Subsingleton large-elimination check.
    let mut can_elim = Vec::with_capacity(parsed_inds.len());
    for (ti, ind) in parsed_inds.iter().enumerate() {
        let allowed = if !ind.is_prop { true } else if parsed_inds.len() > 1 { false } else {
            let cs: Vec<&ParsedCtor> = parsed_ctors.iter().filter(|c| c.ind_idx == ti).collect();
            if cs.is_empty() { true } else if cs.len() == 1 {
                let c0 = cs[0];
                let (mut ok, mut pushed) = (true, 0);
                for f in &c0.fields {
                    let in_prop = tc.infer_sort(f.ty).map(|l| level_is_zero(tc.arena, l)).unwrap_or(false);
                    // The field must *be* one of the result indices (as in Lean's kernel). Merely
                    // occurring inside an index (`P (f n)`) does not determine it, since `f` need not be
                    // injective, and large elimination would then contradict proof irrelevance.
                    let fv_e = tc.arena.fvar(f.fv);
                    let in_idx = c0.result_indices.contains(&fv_e);
                    if !in_prop && !in_idx { ok = false; break; }
                    tc.push_existing_local(f.fv, f.ty);
                    pushed += 1;
                }
                for _ in 0..pushed { tc.pop_local(); }
                ok
            } else { false }
        };
        can_elim.push(allowed);
    }
    for _ in &param_fvs { tc.pop_local(); }

    // Helper to restore synthetic nested names (`aux_name`, `aux_ctor`) back to real `J params` / `J.ctor params`.
    let restore = |arena: &mut Arena, mut e: ExprId| -> ExprId {
        for aux in &nested_aux {
            let ah = arena.const_(aux.aux_name, &param_lvls);
            let a_app = arena.app_n(ah, &param_fve);
            e = replace_expr(arena, e, a_app, aux.orig_app);
            for &(aux_cn, _, orig_c_app) in &aux.ctors {
                let ch = arena.const_(aux_cn, &param_lvls);
                let c_app = arena.app_n(ch, &param_fve);
                e = replace_expr(arena, e, c_app, orig_c_app);
            }
        }
        e
    };

    // 4. Emit Inductive, Constructor (only original types), and Recursor (all orig + nested) declarations.
    let mut out = Vec::new();
    let orig_all_box: Box<[NameId]> = orig_names.into();
    let mut motive_u = tc.arena.name_from_path("u_rec");
    let mut suffix = 0u64;
    while spec.level_params.contains(&motive_u) {
        suffix += 1;
        motive_u = tc.arena.name_num(motive_u, suffix);
    }
    for ti in 0..orig_n {
        out.push(ind_info(spec, &parsed_inds[ti], orig_all_box.clone(), is_rec, can_elim[ti]));
    }

    let mut ctor_idx = vec![0usize; orig_n];
    for c in parsed_ctors.iter().filter(|c| c.ind_idx < orig_n) {
        let ci = ctor_idx[c.ind_idx];
        ctor_idx[c.ind_idx] += 1;
        let orig_ty = spec.types[c.ind_idx].ctors[ci].1;
        out.push(Declaration::Constructor(ConstructorInfo {
            name: c.name, ind_name: parsed_inds[c.ind_idx].name, level_params: spec.level_params.clone(),
            ty: orig_ty, num_params: spec.num_params, num_fields: c.fields.len() as u32,
        }));
    }

    let large_block = can_elim.iter().all(|&b| b);
    let rec_lvls: Box<[NameId]> = if large_block {
        std::iter::once(motive_u).chain(spec.level_params.iter().copied()).collect()
    } else { spec.level_params.clone() };
    let mlvl = if large_block { tc.arena.lvl_param(motive_u) } else { Arena::LEVEL_ZERO };
    let motive_sort = tc.arena.sort(mlvl);
    let rec_lvl_args: Vec<LevelId> = rec_lvls.iter().map(|&p| tc.arena.lvl_param(p)).collect();

    let mut motive_fvs = Vec::with_capacity(parsed_inds.len());
    for (ti, ind) in parsed_inds.iter().enumerate() {
        let (_, major_ty) = major_type(&mut tc, ind, &param_lvls, &param_fve);
        let t_n = tc.arena.name_from_path("t");
        let mty = tc.arena.pi(t_n, BinderInfo::Default, major_ty, motive_sort);
        let mty = wrap(tc.arena, &ind.indices, mty, true);
        let mty = restore(tc.arena, mty);
        let base = tc.arena.name_from_path("motive");
        let mname = if parsed_inds.len() == 1 { base } else { tc.arena.name_num(base, ti as u64 + 1) };
        motive_fvs.push(Binder { name: mname, bi: BinderInfo::Implicit, ty: mty, fv: tc.fresh_fvar() });
    }
    let motive_fve: Vec<ExprId> = motive_fvs.iter().map(|m| tc.arena.fvar(m.fv)).collect();

    let mut minor_fvs = Vec::with_capacity(parsed_ctors.len());
    for c in &parsed_ctors {
        let ctor_c = tc.arena.const_(c.name, &param_lvls);
        let field_e: Vec<ExprId> = c.fields.iter().map(|f| tc.arena.fvar(f.fv)).collect();
        let ctor_val = { let p = tc.arena.app_n(ctor_c, &param_fve); tc.arena.app_n(p, &field_e) };
        let mut mty = tc.arena.app_n(motive_fve[c.ind_idx], &c.result_indices);
        mty = tc.arena.app(mty, ctor_val);
        for rf in c.rec_fields.iter().rev() {
            let eb_e: Vec<ExprId> = rf.extra.iter().map(|e| tc.arena.fvar(e.fv)).collect();
            let f_app = tc.arena.app_n(field_e[rf.field_idx], &eb_e);
            let ih_ret = tc.arena.app_n(motive_fve[rf.target_ind], &rf.target_indices);
            let ih_ret = tc.arena.app(ih_ret, f_app);
            let ih_ty = wrap(tc.arena, &rf.extra, ih_ret, true);
            let ih_n = tc.arena.name_from_path("ih");
            mty = tc.arena.pi(ih_n, BinderInfo::Default, ih_ty, mty);
        }
        let mty = wrap(tc.arena, &c.fields, mty, true);
        let mty = restore(tc.arena, mty);
        minor_fvs.push(Binder { name: c.name, bi: BinderInfo::Default, ty: mty, fv: tc.fresh_fvar() });
    }
    let minor_fve: Vec<ExprId> = minor_fvs.iter().map(|m| tc.arena.fvar(m.fv)).collect();

    for (ti, ind) in parsed_inds.iter().enumerate() {
        let (idx_e, major_ty) = major_type(&mut tc, ind, &param_lvls, &param_fve);
        let major_fv = tc.fresh_fvar();
        let major_e = tc.arena.fvar(major_fv);
        let ret = tc.arena.app_n(motive_fve[ti], &idx_e);
        let ret = tc.arena.app(ret, major_e);
        let t_n = tc.arena.name_from_path("t");
        let abs_m = abstract_fvars(tc.arena, ret, &[major_fv]);
        let mut rec_ty = tc.arena.pi(t_n, BinderInfo::Default, major_ty, abs_m);
        rec_ty = wrap(tc.arena, &ind.indices, rec_ty, true);
        rec_ty = restore(tc.arena, rec_ty);
        rec_ty = wrap(tc.arena, &minor_fvs, rec_ty, true);
        rec_ty = wrap(tc.arena, &motive_fvs, rec_ty, true);
        rec_ty = wrap(tc.arena, &param_fvs, rec_ty, true);

        let mut rules = Vec::new();
        for (mi, c) in parsed_ctors.iter().enumerate().filter(|(_, c)| c.ind_idx == ti) {
            let field_e: Vec<ExprId> = c.fields.iter().map(|f| tc.arena.fvar(f.fv)).collect();
            let mut rhs = tc.arena.app_n(minor_fve[mi], &field_e);
            for rf in &c.rec_fields {
                let target_rec = tc.arena.const_(rec_names[rf.target_ind], &rec_lvl_args);
                let eb_e: Vec<ExprId> = rf.extra.iter().map(|e| tc.arena.fvar(e.fv)).collect();
                let f_app = tc.arena.app_n(field_e[rf.field_idx], &eb_e);
                let mut ih = tc.arena.app_n(target_rec, &param_fve);
                ih = tc.arena.app_n(ih, &motive_fve);
                ih = tc.arena.app_n(ih, &minor_fve);
                ih = tc.arena.app_n(ih, &rf.target_indices);
                ih = tc.arena.app(ih, f_app);
                ih = wrap(tc.arena, &rf.extra, ih, false);
                rhs = tc.arena.app(rhs, ih);
            }
            rhs = wrap(tc.arena, &c.fields, rhs, false);
            rhs = restore(tc.arena, rhs);
            rhs = wrap(tc.arena, &minor_fvs, rhs, false);
            rhs = wrap(tc.arena, &motive_fvs, rhs, false);
            rhs = wrap(tc.arena, &param_fvs, rhs, false);
            let real_ctor = nested_aux.iter()
                .flat_map(|a| a.ctors.iter())
                .find(|(ac, _, _)| *ac == c.name)
                .map(|(_, oc, _)| *oc)
                .unwrap_or(c.name);
            rules.push(RecursorRule { ctor_name: real_ctor, num_fields: c.fields.len() as u32, rhs });
        }

        let k_like = parsed_inds.len() == 1 && ind.is_prop && rules.len() == 1 && rules[0].num_fields == 0;
        out.push(Declaration::Recursor(RecursorInfo {
            name: rec_names[ti], level_params: rec_lvls.clone(), ty: rec_ty, all: orig_all_box.clone(),
            num_params: spec.num_params, num_indices: ind.indices.len() as u32,
            num_motives: parsed_inds.len() as u32, num_minors: parsed_ctors.len() as u32,
            rules: rules.into(), k: k_like,
        }));
    }
    Ok(out)
}

#[allow(clippy::too_many_arguments)]
fn check_strict_positivity(
    tc: &mut TypeChecker<'_>,
    ind: NameId,
    ctor: NameId,
    mut ty: ExprId,
    all_names: &[NameId],
    param_lvls: &[LevelId],
    param_fve: &[ExprId],
    field_idx: usize,
) -> Result<RecField, KernelError> {
    let mut extra = Vec::new();
    loop {
        ty = tc.whnf(ty);
        let ExprData::Pi { name, binder_info, ty: dom, body } = *tc.arena.get_expr(ty) else { break };
        if expr_mentions_any_const(tc.arena, dom, all_names) {
            for _ in &extra { tc.pop_local(); }
            return Err(KernelError::NonPositiveInductive { ind, ctor });
        }
        let fv = tc.push_local(dom, None);
        let fve = tc.arena.fvar(fv);
        extra.push(Binder { name, bi: binder_info, ty: dom, fv });
        ty = instantiate1(tc.arena, body, fve);
    }
    let (head, args) = tc.app_spine(ty);
    for _ in &extra { tc.pop_local(); }
    let target_ind = match *tc.arena.get_expr(head) {
        ExprData::Const(hn, hl_id) => {
            let hl: Box<[LevelId]> = tc.arena.get_level_list(hl_id).into();
            lvls_eq(tc.arena, &hl, param_lvls).then(|| all_names.iter().position(|&x| x == hn)).flatten()
        }
        _ => None,
    }
    .ok_or(KernelError::NonPositiveInductive { ind, ctor })?;

    if args.len() < param_fve.len() || args.iter().zip(param_fve).any(|(&g, &e)| g != e) {
        return Err(KernelError::NonPositiveInductive { ind, ctor });
    }
    let target_indices = args[param_fve.len()..].to_vec();
    if target_indices.iter().any(|&ix| expr_mentions_any_const(tc.arena, ix, all_names)) {
        return Err(KernelError::NonPositiveInductive { ind, ctor });
    }
    Ok(RecField { field_idx, target_ind, extra, target_indices })
}
