#!/usr/bin/env python3
"""Soundness mutation-testing harness for the Rigor proof kernel.

Generates syntactically valid NDJSON mutants of a Lean 4 lean4export file
across five mutation operators and verifies that Rigor rejects broken proofs.
Uses Python 3 standard library only.
"""

import argparse
import concurrent.futures
import json
import os
import random
import subprocess
import sys
import tempfile
import time
from pathlib import Path


def parse_ndjson_index(path: Path):
    """Parse the NDJSON export and build lookup tables for mutation generation."""
    raw_lines = path.read_text(encoding="utf-8").splitlines()
    names = {0: ""}
    levels = {0: {"zero": True}}
    exprs = {}
    expr_line = {}
    max_il = 0
    max_ie = 0

    # Declarations and constant metadata
    # const_info[name_id] = {
    #   "kind": "def"|"thm"|"axiom"|"opaque"|"ind"|"ctor"|"rec"|"quot",
    #   "line": int,
    #   "type": int,
    #   "levelParams": list[int],
    # }
    const_info = {}
    thms = []  # list of (line_idx, obj)
    defs = []  # list of (line_idx, obj)
    decl_name_by_line = {}

    for idx, line in enumerate(raw_lines):
        if not line.strip():
            continue
        d = json.loads(line)
        if "in" in d:
            nid = d["in"]
            if "str" in d:
                pre = names[d["str"]["pre"]]
                names[nid] = f"{pre}.{d['str']['str']}" if pre else d["str"]["str"]
            elif "num" in d:
                pre = names[d["num"]["pre"]]
                names[nid] = f"{pre}.{d['num']['i']}" if pre else str(d["num"]["i"])
        elif "il" in d:
            lid = d["il"]
            levels[lid] = d
            if lid > max_il:
                max_il = lid
        elif "ie" in d:
            eid = d["ie"]
            exprs[eid] = d
            expr_line[eid] = idx
            if eid > max_ie:
                max_ie = eid
        elif "thm" in d:
            obj = d["thm"]
            thms.append((idx, obj))
            const_info[obj["name"]] = {
                "kind": "thm",
                "line": idx,
                "type": obj["type"],
                "levelParams": obj["levelParams"],
            }
            decl_name_by_line[idx] = names[obj["name"]]
        elif "def" in d:
            obj = d["def"]
            defs.append((idx, obj))
            const_info[obj["name"]] = {
                "kind": "def",
                "line": idx,
                "type": obj["type"],
                "levelParams": obj["levelParams"],
            }
            decl_name_by_line[idx] = names[obj["name"]]
        elif "axiom" in d:
            obj = d["axiom"]
            const_info[obj["name"]] = {
                "kind": "axiom",
                "line": idx,
                "type": obj["type"],
                "levelParams": obj["levelParams"],
            }
            decl_name_by_line[idx] = names[obj["name"]]
        elif "opaque" in d:
            obj = d["opaque"]
            const_info[obj["name"]] = {
                "kind": "opaque",
                "line": idx,
                "type": obj["type"],
                "levelParams": obj["levelParams"],
            }
            decl_name_by_line[idx] = names[obj["name"]]
        elif "quot" in d:
            obj = d["quot"]
            const_info[obj["name"]] = {
                "kind": "quot",
                "line": idx,
                "type": obj["type"],
                "levelParams": obj["levelParams"],
            }
            decl_name_by_line[idx] = names[obj["name"]]
        elif "inductive" in d:
            ind = d["inductive"]
            for t in ind["types"]:
                const_info[t["name"]] = {
                    "kind": "ind",
                    "line": idx,
                    "type": t["type"],
                    "levelParams": t["levelParams"],
                }
            for c in ind["ctors"]:
                const_info[c["name"]] = {
                    "kind": "ctor",
                    "line": idx,
                    "type": c["type"],
                    "levelParams": c["levelParams"],
                }
            for r in ind["recs"]:
                const_info[r["name"]] = {
                    "kind": "rec",
                    "line": idx,
                    "type": r["type"],
                    "levelParams": r["levelParams"],
                }
            if ind["types"]:
                decl_name_by_line[idx] = names[ind["types"][0]["name"]]

    # Precompute level params used by each level id
    lvl_params_cache = {0: frozenset()}

    def level_params_of(lid: int) -> frozenset:
        if lid in lvl_params_cache:
            return lvl_params_cache[lid]
        o = levels[lid]
        if "param" in o:
            res = frozenset([o["param"]])
        elif "succ" in o:
            res = level_params_of(o["succ"])
        elif "max" in o:
            res = level_params_of(o["max"][0]) | level_params_of(o["max"][1])
        elif "imax" in o:
            res = level_params_of(o["imax"][0]) | level_params_of(o["imax"][1])
        else:
            res = frozenset()
        lvl_params_cache[lid] = res
        return res

    # Precompute loose bvar range and level params for each expr id (bottom-up since IDs are topological)
    expr_closed = {}
    expr_lparams = {}
    for eid in sorted(exprs.keys()):
        e = exprs[eid]
        if "bvar" in e:
            expr_closed[eid] = e["bvar"] + 1
            expr_lparams[eid] = frozenset()
        elif "sort" in e:
            expr_closed[eid] = 0
            expr_lparams[eid] = level_params_of(e["sort"])
        elif "const" in e:
            expr_closed[eid] = 0
            lp = frozenset()
            for u in e["const"]["us"]:
                lp |= level_params_of(u)
            expr_lparams[eid] = lp
        elif "app" in e:
            f, a = e["app"]["fn"], e["app"]["arg"]
            expr_closed[eid] = max(expr_closed[f], expr_closed[a])
            expr_lparams[eid] = expr_lparams[f] | expr_lparams[a]
        elif "lam" in e:
            t, b = e["lam"]["type"], e["lam"]["body"]
            expr_closed[eid] = max(expr_closed[t], max(0, expr_closed[b] - 1))
            expr_lparams[eid] = expr_lparams[t] | expr_lparams[b]
        elif "forallE" in e:
            t, b = e["forallE"]["type"], e["forallE"]["body"]
            expr_closed[eid] = max(expr_closed[t], max(0, expr_closed[b] - 1))
            expr_lparams[eid] = expr_lparams[t] | expr_lparams[b]
        elif "letE" in e:
            t, v, b = e["letE"]["type"], e["letE"]["value"], e["letE"]["body"]
            expr_closed[eid] = max(expr_closed[t], expr_closed[v], max(0, expr_closed[b] - 1))
            expr_lparams[eid] = expr_lparams[t] | expr_lparams[v] | expr_lparams[b]
        elif "proj" in e:
            s = e["proj"]["struct"]
            expr_closed[eid] = expr_closed[s]
            expr_lparams[eid] = expr_lparams[s]
        elif "mdata" in e:
            x = e["mdata"]["expr"]
            expr_closed[eid] = expr_closed[x]
            expr_lparams[eid] = expr_lparams[x]
        else:
            expr_closed[eid] = 0
            expr_lparams[eid] = frozenset()

    return {
        "raw_lines": raw_lines,
        "names": names,
        "levels": levels,
        "exprs": exprs,
        "expr_line": expr_line,
        "expr_closed": expr_closed,
        "expr_lparams": expr_lparams,
        "max_il": max_il,
        "max_ie": max_ie,
        "const_info": const_info,
        "thms": thms,
        "defs": defs,
        "decl_name_by_line": decl_name_by_line,
    }


def expr_dag_size(exprs, root_eid: int, cap: int = 400) -> int:
    seen = set()
    stack = [root_eid]
    while stack and len(seen) < cap:
        x = stack.pop()
        if x in seen:
            continue
        seen.add(x)
        e = exprs[x]
        if "app" in e:
            stack.append(e["app"]["fn"])
            stack.append(e["app"]["arg"])
        elif "lam" in e:
            stack.append(e["lam"]["type"])
            stack.append(e["lam"]["body"])
        elif "forallE" in e:
            stack.append(e["forallE"]["type"])
            stack.append(e["forallE"]["body"])
        elif "letE" in e:
            stack.append(e["letE"]["type"])
            stack.append(e["letE"]["value"])
            stack.append(e["letE"]["body"])
        elif "proj" in e:
            stack.append(e["proj"]["struct"])
        elif "mdata" in e:
            stack.append(e["mdata"]["expr"])
    return len(seen)


def collect_consts_in_expr(exprs, root_eid: int, cap: int = 500) -> set:
    out = set()
    seen = set()
    stack = [root_eid]
    while stack and len(seen) < cap:
        x = stack.pop()
        if x in seen:
            continue
        seen.add(x)
        e = exprs[x]
        if "const" in e:
            out.add(e["const"]["name"])
        elif "app" in e:
            stack.append(e["app"]["fn"])
            stack.append(e["app"]["arg"])
        elif "lam" in e:
            stack.append(e["lam"]["type"])
            stack.append(e["lam"]["body"])
        elif "forallE" in e:
            stack.append(e["forallE"]["type"])
            stack.append(e["forallE"]["body"])
        elif "letE" in e:
            stack.append(e["letE"]["type"])
            stack.append(e["letE"]["value"])
            stack.append(e["letE"]["body"])
        elif "proj" in e:
            stack.append(e["proj"]["struct"])
        elif "mdata" in e:
            stack.append(e["mdata"]["expr"])
    return out


def find_paths(exprs, root_eid: int, pred, max_paths: int = 25, max_depth: int = 40):
    """Find paths from root_eid to subexpressions matching pred(eid, expr_dict).

    Each path is a list of (parent_eid, field_key) ending at target_eid.
    """
    results = []
    visited = set()

    def dfs(eid, path):
        if len(results) >= max_paths or len(path) > max_depth:
            return
        if eid in visited:
            return
        visited.add(eid)
        e = exprs[eid]
        if pred(eid, e):
            results.append((list(path), eid))
        if "app" in e:
            path.append((eid, "app.fn"))
            dfs(e["app"]["fn"], path)
            path.pop()
            path.append((eid, "app.arg"))
            dfs(e["app"]["arg"], path)
            path.pop()
        elif "lam" in e:
            path.append((eid, "lam.body"))
            dfs(e["lam"]["body"], path)
            path.pop()
            path.append((eid, "lam.type"))
            dfs(e["lam"]["type"], path)
            path.pop()
        elif "forallE" in e:
            path.append((eid, "forallE.body"))
            dfs(e["forallE"]["body"], path)
            path.pop()
            path.append((eid, "forallE.type"))
            dfs(e["forallE"]["type"], path)
            path.pop()
        elif "letE" in e:
            path.append((eid, "letE.value"))
            dfs(e["letE"]["value"], path)
            path.pop()
            path.append((eid, "letE.body"))
            dfs(e["letE"]["body"], path)
            path.pop()
            path.append((eid, "letE.type"))
            dfs(e["letE"]["type"], path)
            path.pop()
        elif "proj" in e:
            path.append((eid, "proj.struct"))
            dfs(e["proj"]["struct"], path)
            path.pop()
        elif "mdata" in e:
            path.append((eid, "mdata.expr"))
            dfs(e["mdata"]["expr"], path)
            path.pop()

    dfs(root_eid, [])
    return results


def rebuild_path(exprs, path, new_leaf_eid: int, next_ie: int):
    """Clone ancestor exprs along `path` with fresh IDs starting at `next_ie`.

    Returns (new_lines: list[str], new_root_eid: int, next_ie_after: int).
    """
    new_lines = []
    cur_child = new_leaf_eid
    for parent_eid, slot in reversed(path):
        orig = exprs[parent_eid]
        kind, subkey = slot.split(".")
        cloned_sub = dict(orig[kind])
        cloned_sub[subkey] = cur_child
        new_id = next_ie
        next_ie += 1
        obj = {kind: cloned_sub, "ie": new_id}
        new_lines.append(json.dumps(obj, separators=(",", ":")))
        cur_child = new_id
    return new_lines, cur_child, next_ie


def build_mutated_text(raw_lines, target_line: int, insert_before: list, replaced_line: str) -> str:
    out = []
    out.extend(raw_lines[:target_line])
    out.extend(insert_before)
    out.append(replaced_line)
    out.extend(raw_lines[target_line + 1 :])
    return "\n".join(out) + "\n"


def generate_mutants(idx_data, seed: int, per_op: int):
    rng = random.Random(seed)
    names = idx_data["names"]
    exprs = idx_data["exprs"]
    expr_line = idx_data["expr_line"]
    expr_closed = idx_data["expr_closed"]
    expr_lparams = idx_data["expr_lparams"]
    const_info = idx_data["const_info"]
    thms = idx_data["thms"]
    defs = idx_data["defs"]
    max_ie = idx_data["max_ie"]
    max_il = idx_data["max_il"]

    # Sort theorems and definitions preferring smaller value DAGs
    thms_by_size = sorted(thms, key=lambda item: (expr_dag_size(exprs, item[1]["value"]), item[0]))
    defs_by_size = sorted(defs, key=lambda item: (expr_dag_size(exprs, item[1]["value"]), item[0]))

    # Index constants by universe parameter arity
    consts_by_arity = {}
    consts_by_type_arity = {}
    for nid, info in const_info.items():
        ar = len(info["levelParams"])
        consts_by_arity.setdefault(ar, []).append((info["line"], nid, info["type"], info["kind"]))
        consts_by_type_arity.setdefault((info["type"], ar), []).append((info["line"], nid, info["kind"]))
    for v in consts_by_arity.values():
        v.sort()
    for v in consts_by_type_arity.values():
        v.sort()

    # Closed candidate expressions for Op 3 (arg_swap): pre-collect closed const/sort/lit exprs
    # tagged with a coarse type key so we pick replacements of a genuinely different type.
    def coarse_type_key(eid: int):
        e = exprs[eid]
        if "const" in e:
            cn = e["const"]["name"]
            if cn in const_info:
                return ("const_ty", const_info[cn]["type"], len(e["const"]["us"]))
            return ("const_raw", cn)
        if "sort" in e:
            return ("sort", e["sort"])
        if "natVal" in e:
            return ("natVal",)
        if "strVal" in e:
            return ("strVal",)
        if "app" in e:
            return ("app", e["app"]["fn"])
        return ("other", eid)

    closed_arg_pool = []
    for eid, e in exprs.items():
        if expr_closed[eid] != 0:
            continue
        if "const" in e or "sort" in e or "natVal" in e or "strVal" in e:
            closed_arg_pool.append((expr_line[eid], eid, expr_lparams[eid], coarse_type_key(eid)))
    closed_arg_pool.sort()

    mutants = []

    # ------------------------------------------------------------------
    # Operator 1: Theorem value swap
    # ------------------------------------------------------------------
    op1_pool = []
    for l1, t1 in thms_by_size:
        lp1 = set(t1["levelParams"])
        cands = [
            (l2, t2)
            for l2, t2 in thms
            if l2 < l1
            and t2["type"] != t1["type"]
            and t2["value"] != t1["value"]
            and set(t2["levelParams"]).issubset(lp1)
        ]
        if cands:
            op1_pool.append((l1, t1, cands))
    rng.shuffle(op1_pool)
    op1_count = 0
    seen_op1 = set()
    for l1, t1, cands in op1_pool:
        if op1_count >= per_op:
            break
        l2, t2 = rng.choice(cands)
        key = (t1["name"], t2["name"])
        if key in seen_op1:
            continue
        seen_op1.add(key)
        new_obj = dict(t1)
        new_obj["value"] = t2["value"]
        mutants.append({
            "op": "thm_value_swap",
            "target": names[t1["name"]],
            "target_line": l1,
            "insert_before": [],
            "replaced_line": json.dumps({"thm": new_obj}, separators=(",", ":")),
            "detail": f"replaced value of {names[t1['name']]} with value of {names[t2['name']]}",
        })
        op1_count += 1

    # ------------------------------------------------------------------
    # Operator 2: Constant swap inside a theorem or definition value
    # ------------------------------------------------------------------
    op2_decls = [("thm", l, o) for l, o in thms_by_size] + [("def", l, o) for l, o in defs_by_size[:250]]
    rng.shuffle(op2_decls)
    op2_count = 0
    seen_op2 = set()
    for dkind, lno, obj in op2_decls:
        if op2_count >= per_op:
            break
        paths = find_paths(exprs, obj["value"], lambda _eid, e: "const" in e, max_paths=15)
        rng.shuffle(paths)
        picked = False
        for path, ceid in paths:
            cobj = exprs[ceid]["const"]
            n1 = cobj["name"]
            us = cobj["us"]
            if n1 not in const_info:
                continue
            ty1 = const_info[n1]["type"]
            alts = [
                n2
                for l2, n2, ty2, _k2 in consts_by_arity.get(len(us), [])
                if l2 < lno and n2 != n1 and ty2 != ty1
            ]
            if not alts:
                continue
            n2 = rng.choice(alts)
            key = (obj["name"], ceid, n2)
            if key in seen_op2:
                continue
            seen_op2.add(key)
            next_ie = max_ie + 1
            leaf_id = next_ie
            next_ie += 1
            leaf_line = json.dumps({"const": {"name": n2, "us": us}, "ie": leaf_id}, separators=(",", ":"))
            anc_lines, new_root, _ = rebuild_path(exprs, path, leaf_id, next_ie)
            new_obj = dict(obj)
            new_obj["value"] = new_root
            mutants.append({
                "op": "const_swap",
                "target": names[obj["name"]],
                "target_line": lno,
                "insert_before": [leaf_line] + anc_lines,
                "replaced_line": json.dumps({dkind: new_obj}, separators=(",", ":")),
                "detail": f"in {dkind} {names[obj['name']]}, swapped const {names[n1]} -> {names[n2]} (arity {len(us)})",
            })
            op2_count += 1
            picked = True
            break
        if picked:
            continue

    # ------------------------------------------------------------------
    # Operator 3: Argument swap in an app node used by a theorem value
    # ------------------------------------------------------------------
    op3_thms = list(thms_by_size)
    rng.shuffle(op3_thms)
    op3_count = 0
    seen_op3 = set()
    for lno, obj in op3_thms:
        if op3_count >= per_op:
            break
        lp_set = frozenset(obj["levelParams"])
        paths = find_paths(exprs, obj["value"], lambda _eid, e: "app" in e, max_paths=20)
        rng.shuffle(paths)
        for path, aeid in paths:
            app_obj = exprs[aeid]["app"]
            fn_id = app_obj["fn"]
            arg_id = app_obj["arg"]
            arg_tkey = coarse_type_key(arg_id)
            # Sample candidate replacement arguments defined before lno with compatible level params & different type
            cands = []
            for _ in range(40):
                el, ceid, clp, ctkey = rng.choice(closed_arg_pool)
                if el < lno and ceid != arg_id and clp.issubset(lp_set) and ctkey != arg_tkey:
                    cands.append(ceid)
                    if len(cands) >= 5:
                        break
            if not cands:
                continue
            alt_arg = rng.choice(cands)
            key = (obj["name"], aeid, alt_arg)
            if key in seen_op3:
                continue
            seen_op3.add(key)
            next_ie = max_ie + 1
            leaf_id = next_ie
            next_ie += 1
            leaf_line = json.dumps({"app": {"fn": fn_id, "arg": alt_arg}, "ie": leaf_id}, separators=(",", ":"))
            anc_lines, new_root, _ = rebuild_path(exprs, path, leaf_id, next_ie)
            new_obj = dict(obj)
            new_obj["value"] = new_root
            mutants.append({
                "op": "arg_swap",
                "target": names[obj["name"]],
                "target_line": lno,
                "insert_before": [leaf_line] + anc_lines,
                "replaced_line": json.dumps({"thm": new_obj}, separators=(",", ":")),
                "detail": f"in thm {names[obj['name']]}, swapped app({aeid}) arg {arg_id} -> {alt_arg}",
            })
            op3_count += 1
            break

    # ------------------------------------------------------------------
    # Operator 4: Universe level change on a const node in a theorem value
    # ------------------------------------------------------------------
    op4_thms = list(thms_by_size)
    rng.shuffle(op4_thms)
    op4_count = 0
    seen_op4 = set()
    for lno, obj in op4_thms:
        if op4_count >= per_op:
            break
        paths = find_paths(
            exprs,
            obj["value"],
            lambda _eid, e: "const" in e and len(e["const"]["us"]) >= 1,
            max_paths=20,
        )
        rng.shuffle(paths)
        for path, ceid in paths:
            cobj = exprs[ceid]["const"]
            n1 = cobj["name"]
            us = list(cobj["us"])
            pos = rng.randrange(len(us))
            old_u = us[pos]
            key = (obj["name"], ceid, pos)
            if key in seen_op4:
                continue
            seen_op4.add(key)
            new_il = max_il + 1
            lvl_line = json.dumps({"succ": old_u, "il": new_il}, separators=(",", ":"))
            new_us = list(us)
            new_us[pos] = new_il
            next_ie = max_ie + 1
            leaf_id = next_ie
            next_ie += 1
            leaf_line = json.dumps({"const": {"name": n1, "us": new_us}, "ie": leaf_id}, separators=(",", ":"))
            anc_lines, new_root, _ = rebuild_path(exprs, path, leaf_id, next_ie)
            new_obj = dict(obj)
            new_obj["value"] = new_root
            mutants.append({
                "op": "level_change",
                "target": names[obj["name"]],
                "target_line": lno,
                "insert_before": [lvl_line, leaf_line] + anc_lines,
                "replaced_line": json.dumps({"thm": new_obj}, separators=(",", ":")),
                "detail": f"in thm {names[obj['name']]}, bumped level arg[{pos}] of {names[n1]} from il={old_u} to succ({old_u})",
            })
            op4_count += 1
            break

    # ------------------------------------------------------------------
    # Operator 5: Definition body change for defs proven about by later rfl theorems
    # ------------------------------------------------------------------
    rfl_ids = {nid for nid, nm in names.items() if nm in ("Eq.refl", "rfl", "HEq.refl")}
    bool_true_id = next((nid for nid, nm in names.items() if nm == "Bool.true"), None)
    bool_false_id = next((nid for nid, nm in names.items() if nm == "Bool.false"), None)
    def_by_name = {obj["name"]: (lno, obj) for lno, obj in defs}

    # Map each definition to later theorems proved using rfl/Eq.refl/HEq.refl whose type mentions it
    rfl_dependents = {}
    for tidx, tobj in thms:
        vconsts = collect_consts_in_expr(exprs, tobj["value"])
        if not (vconsts & rfl_ids):
            continue
        tconsts = collect_consts_in_expr(exprs, tobj["type"])
        for cn in tconsts:
            if cn in def_by_name and def_by_name[cn][0] < tidx:
                rfl_dependents.setdefault(cn, []).append(names[tobj["name"]])

    # Also include 1-hop helper defs unfolded by those directly-referenced defs
    for cn, thm_list in list(rfl_dependents.items()):
        didx, dobj = def_by_name[cn]
        for sub in collect_consts_in_expr(exprs, dobj["value"]):
            if sub in def_by_name and def_by_name[sub][0] < didx and sub not in rfl_dependents:
                rfl_dependents[sub] = [f"{t} (via {names[cn]})" for t in thm_list[:2]]

    # Sort rfl-tested definitions by size ascending
    rfl_def_items = sorted(
        [(def_by_name[cn][0], def_by_name[cn][1], rfl_dependents[cn]) for cn in rfl_dependents],
        key=lambda x: (expr_dag_size(exprs, x[1]["value"]), x[0]),
    )
    rng.shuffle(rfl_def_items)

    op5_count = 0
    seen_op5 = set()

    def try_op5_on_def(lno, dobj, dep_thms):
        nonlocal op5_count
        dname = dobj["name"]

        # Strategy 5a: Increment a natVal literal inside D.value (preserves type Nat!)
        nat_paths = find_paths(exprs, dobj["value"], lambda _eid, e: "natVal" in e, max_paths=10)
        rng.shuffle(nat_paths)
        for path, neid in nat_paths:
            old_val = int(exprs[neid]["natVal"])
            new_val = old_val + 1
            key = (dname, "nat", neid, new_val)
            if key in seen_op5:
                continue
            seen_op5.add(key)
            next_ie = max_ie + 1
            leaf_id = next_ie
            next_ie += 1
            leaf_line = json.dumps({"natVal": str(new_val), "ie": leaf_id}, separators=(",", ":"))
            anc_lines, new_root, _ = rebuild_path(exprs, path, leaf_id, next_ie)
            new_obj = dict(dobj)
            new_obj["value"] = new_root
            mutants.append({
                "op": "def_body_rfl_break",
                "target": names[dname],
                "target_line": lno,
                "insert_before": [leaf_line] + anc_lines,
                "replaced_line": json.dumps({"def": new_obj}, separators=(",", ":")),
                "detail": f"in def {names[dname]} (rfl deps: {', '.join(dep_thms[:2])}), changed natVal {old_val} -> {new_val}",
            })
            op5_count += 1
            return True

        # Strategy 5b: Flip Bool.true <-> Bool.false inside D.value (preserves type Bool!)
        if bool_true_id is not None and bool_false_id is not None:
            bool_paths = find_paths(
                exprs,
                dobj["value"],
                lambda _eid, e: "const" in e and e["const"]["name"] in (bool_true_id, bool_false_id),
                max_paths=10,
            )
            rng.shuffle(bool_paths)
            for path, beid in bool_paths:
                old_c = exprs[beid]["const"]["name"]
                new_c = bool_false_id if old_c == bool_true_id else bool_true_id
                key = (dname, "bool", beid, new_c)
                if key in seen_op5:
                    continue
                seen_op5.add(key)
                next_ie = max_ie + 1
                leaf_id = next_ie
                next_ie += 1
                leaf_line = json.dumps({"const": {"name": new_c, "us": []}, "ie": leaf_id}, separators=(",", ":"))
                anc_lines, new_root, _ = rebuild_path(exprs, path, leaf_id, next_ie)
                new_obj = dict(dobj)
                new_obj["value"] = new_root
                mutants.append({
                    "op": "def_body_rfl_break",
                    "target": names[dname],
                    "target_line": lno,
                    "insert_before": [leaf_line] + anc_lines,
                    "replaced_line": json.dumps({"def": new_obj}, separators=(",", ":")),
                    "detail": f"in def {names[dname]} (rfl deps: {', '.join(dep_thms[:2])}), flipped {names[old_c]} -> {names[new_c]}",
                })
                op5_count += 1
                return True

        # Strategy 5c: Swap an inner const with another earlier non-theorem const of the EXACT SAME type
        # (keeps def well-typed so the later rfl theorem fails on definitional equality!)
        c_paths = find_paths(exprs, dobj["value"], lambda _eid, e: "const" in e, max_paths=15)
        rng.shuffle(c_paths)
        for path, ceid in c_paths:
            cobj = exprs[ceid]["const"]
            n1 = cobj["name"]
            us = cobj["us"]
            if n1 not in const_info or const_info[n1]["kind"] == "thm":
                continue
            ty1 = const_info[n1]["type"]
            same_ty_alts = [
                n2
                for l2, n2, k2 in consts_by_type_arity.get((ty1, len(us)), [])
                if l2 < lno and n2 != n1 and k2 != "thm"
            ]
            if not same_ty_alts:
                continue
            n2 = rng.choice(same_ty_alts)
            key = (dname, "same_const", ceid, n2)
            if key in seen_op5:
                continue
            seen_op5.add(key)
            next_ie = max_ie + 1
            leaf_id = next_ie
            next_ie += 1
            leaf_line = json.dumps({"const": {"name": n2, "us": us}, "ie": leaf_id}, separators=(",", ":"))
            anc_lines, new_root, _ = rebuild_path(exprs, path, leaf_id, next_ie)
            new_obj = dict(dobj)
            new_obj["value"] = new_root
            mutants.append({
                "op": "def_body_rfl_break",
                "target": names[dname],
                "target_line": lno,
                "insert_before": [leaf_line] + anc_lines,
                "replaced_line": json.dumps({"def": new_obj}, separators=(",", ":")),
                "detail": f"in def {names[dname]} (rfl deps: {', '.join(dep_thms[:2])}), same-type const swap {names[n1]} -> {names[n2]}",
            })
            op5_count += 1
            return True

        # Strategy 5d: Swap whole def body with an earlier def of the exact same type
        lp_d = set(dobj["levelParams"])
        same_defs = [
            d2
            for l2, d2 in defs
            if l2 < lno
            and d2["type"] == dobj["type"]
            and d2["value"] != dobj["value"]
            and set(d2["levelParams"]).issubset(lp_d)
        ]
        if same_defs:
            d2 = rng.choice(same_defs)
            key = (dname, "def_swap", d2["name"])
            if key not in seen_op5:
                seen_op5.add(key)
                new_obj = dict(dobj)
                new_obj["value"] = d2["value"]
                mutants.append({
                    "op": "def_body_rfl_break",
                    "target": names[dname],
                    "target_line": lno,
                    "insert_before": [],
                    "replaced_line": json.dumps({"def": new_obj}, separators=(",", ":")),
                    "detail": f"replaced body of def {names[dname]} (rfl deps: {', '.join(dep_thms[:2])}) with same-type def {names[d2['name']]}",
                })
                op5_count += 1
                return True
        return False

    # Pass 1: one mutant per distinct rfl-tested definition
    for lno, dobj, dep_thms in rfl_def_items:
        if op5_count >= per_op:
            break
        try_op5_on_def(lno, dobj, dep_thms)
    # Pass 2: if still under per_op, emit additional distinct mutations on rfl-tested defs
    for _ in range(3):
        if op5_count >= per_op:
            break
        rng.shuffle(rfl_def_items)
        for lno, dobj, dep_thms in rfl_def_items:
            if op5_count >= per_op:
                break
            try_op5_on_def(lno, dobj, dep_thms)

    return mutants


def run_checker(checker_bin: Path, ndjson_path: Path):
    env = os.environ.copy()
    env["RIGOR_THREADS"] = "4"
    proc = subprocess.run(
        [str(checker_bin), "--check", str(ndjson_path)],
        env=env,
        capture_output=True,
        text=True,
    )
    stdout = proc.stdout.strip()
    stderr = proc.stderr.strip()
    accepted = proc.returncode == 0 and any(ln.startswith("CHECK_OK") for ln in stdout.splitlines())
    err_line = ""
    if not accepted:
        stderr_lines = stderr.splitlines()
        for ln in stderr_lines:
            if "kernel rejected" in ln or "Kernel {" in ln:
                err_line = ln.strip()
                break
        if not err_line:
            for ln in stderr_lines:
                if "Error" in ln or "rejected" in ln:
                    err_line = ln.strip()
                    break
        if not err_line:
            for ln in stderr_lines:
                if "panicked" in ln:
                    err_line = ln.strip()
                    break
        if not err_line:
            err_line = (stderr_lines[0] if stderr_lines else stdout.splitlines()[0] if stdout else f"exit={proc.returncode}")
    else:
        err_line = next((ln for ln in stdout.splitlines() if ln.startswith("CHECK_OK")), stdout)
    return accepted, proc.returncode, err_line


def evaluate_mutant(args_tuple):
    idx, mutant, raw_lines, checker_bin, tmp_dir = args_tuple
    tmp_file = Path(tmp_dir) / f"mutant_{idx:04d}.ndjson"
    text = build_mutated_text(
        raw_lines,
        mutant["target_line"],
        mutant["insert_before"],
        mutant["replaced_line"],
    )
    tmp_file.write_text(text, encoding="utf-8")
    try:
        accepted, rc, err_line = run_checker(checker_bin, tmp_file)
    finally:
        try:
            tmp_file.unlink()
        except OSError:
            pass
    return {
        "id": idx,
        "op": mutant["op"],
        "target": mutant["target"],
        "target_line": mutant["target_line"] + 1,
        "mutated_line": mutant["target_line"] + 1 + len(mutant["insert_before"]),
        "detail": mutant["detail"],
        "expected": "REJECT",
        "observed": "ACCEPT" if accepted else "REJECT",
        "returncode": rc,
        "error_line": err_line,
    }


def write_report(report_path: Path, cmd_str: str, sanity_line: str, results: list, elapsed_s: float):
    ops = [
        "thm_value_swap",
        "const_swap",
        "arg_swap",
        "level_change",
        "def_body_rfl_break",
    ]
    by_op = {op: [r for r in results if r["op"] == op] for op in ops}
    total = len(results)
    rejected = sum(1 for r in results if r["observed"] == "REJECT")
    accepted_list = [r for r in results if r["observed"] == "ACCEPT"]

    lines = [
        "# Rigor Soundness Mutation-Testing Report",
        "",
        "## Command",
        "",
        "```sh",
        cmd_str,
        "```",
        "",
        "## Sanity Check (Unmutated Input)",
        "",
        f"- Result: PASS (`{sanity_line}`)",
        f"- Total elapsed time: {elapsed_s:.2f} s",
        "",
        "## Summary by Mutation Operator",
        "",
        "| Operator | Total | Rejected | Accepted | Rejection Rate |",
        "|---|---:|---:|---:|---:|",
    ]
    for op in ops:
        rs = by_op[op]
        n = len(rs)
        rej = sum(1 for r in rs if r["observed"] == "REJECT")
        acc = n - rej
        rate = (100.0 * rej / n) if n else 0.0
        lines.append(f"| `{op}` | {n} | {rej} | {acc} | {rate:.1f}% |")
    rate_all = (100.0 * rejected / total) if total else 0.0
    lines.append(f"| **Total** | **{total}** | **{rejected}** | **{len(accepted_list)}** | **{rate_all:.1f}%** |")
    lines.append("")

    # Breakdown for Op 5: rejected at later declaration vs at mutated def itself
    op5_rej = [r for r in by_op["def_body_rfl_break"] if r["observed"] == "REJECT"]
    later_fails = 0
    for r in op5_rej:
        err = r["error_line"]
        marker = "kernel rejected declaration "
        if marker in err:
            decl_failed = err.split(marker, 1)[1].split(":", 1)[0].strip()
            if decl_failed and decl_failed != r["target"]:
                later_fails += 1
        elif "line: " in err:
            after = err.split("line: ", 1)[1]
            digits = ""
            for ch in after:
                if ch.isdigit():
                    digits += ch
                else:
                    break
            if digits and int(digits) > r["mutated_line"]:
                later_fails += 1
    if op5_rej:
        lines.extend([
            "## Operator 5 (`def_body_rfl_break`) Rejection Breakdown",
            "",
            f"- Rejected mutants: {len(op5_rej)}",
            f"- Rejected at a later dependent declaration (mutated definition remained well-typed and broke a downstream proof/rfl check): {later_fails}",
            f"- Rejected at the mutated definition line itself: {len(op5_rej) - later_fails}",
            "",
        ])

    lines.append("## Accepted Mutants")
    lines.append("")
    if not accepted_list:
        lines.append("None. Every generated mutant was rejected by Rigor.")
    else:
        lines.append(
            "The following mutants were accepted by Rigor and require manual review to determine "
            "whether each mutation was semantically harmless (for example, proof irrelevance, "
            "unreachable branch, or definitionally equal replacement) or a genuine soundness bug:"
        )
        lines.append("")
        for r in accepted_list:
            lines.append(
                f"- Mutant #{r['id']} (`{r['op']}`): target `{r['target']}` (line {r['target_line']}) -- "
                f"{r['detail']} | output: `{r['error_line']}`"
            )
    lines.append("")
    report_path.write_text("\n".join(lines), encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description="Soundness mutation-testing harness for Rigor")
    parser.add_argument(
        "--input",
        type=Path,
        default=Path("/tmp/rigor_real/Init.Prelude.ndjson"),
        help="Path to input lean4export NDJSON file",
    )
    parser.add_argument(
        "--checker",
        type=Path,
        default=Path.home() / "rigor/target/release/rigor-bench",
        help="Path to rigor-bench binary",
    )
    parser.add_argument("--seed", type=int, default=1, help="Random seed (default: 1)")
    parser.add_argument("--per-op", type=int, default=50, help="Mutants per operator (default: 50)")
    parser.add_argument("--workers", type=int, default=2, help="Concurrent checker processes (default: 2)")
    parser.add_argument(
        "--report",
        type=Path,
        default=Path.home() / "rigor/tools/mutation/REPORT.md",
        help="Output Markdown report path",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=Path.home() / "rigor/tools/mutation/results.json",
        help="Output JSON log path",
    )
    args = parser.parse_args()

    t0 = time.monotonic()

    # 1. Sanity check on unmutated input
    ok, rc, sanity_line = run_checker(args.checker, args.input)
    if not ok:
        print(f"SANITY CHECK FAILED (rc={rc}): {sanity_line}", file=sys.stderr)
        sys.exit(2)
    print(f"SANITY_OK: {sanity_line}")

    # 2. Index input and generate mutants
    idx_data = parse_ndjson_index(args.input)
    mutants = generate_mutants(idx_data, seed=args.seed, per_op=args.per_op)
    print(f"Generated {len(mutants)} mutants (seed={args.seed}, per_op={args.per_op})")

    # 3. Evaluate all mutants
    results = []
    with tempfile.TemporaryDirectory(prefix="rigor_mut_") as tmp_dir:
        tasks = [
            (i + 1, m, idx_data["raw_lines"], args.checker, tmp_dir)
            for i, m in enumerate(mutants)
        ]
        if args.workers <= 1:
            for t in tasks:
                results.append(evaluate_mutant(t))
        else:
            with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
                for res in pool.map(evaluate_mutant, tasks):
                    results.append(res)

    elapsed = time.monotonic() - t0

    # Print any accepted mutants immediately for human inspection
    accepted = [r for r in results if r["observed"] == "ACCEPT"]
    for r in accepted:
        print(
            f"ACCEPTED Mutant #{r['id']} [{r['op']}] target={r['target']} (line {r['target_line']}): "
            f"{r['detail']}"
        )

    # Save JSON results and Markdown report
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")

    cmd_str = (
        f"RIGOR_THREADS=4 python3 {Path(__file__).resolve()} "
        f"--input {args.input} --checker {args.checker} --seed {args.seed} "
        f"--per-op {args.per_op} --workers {args.workers} --report {args.report}"
    )
    write_report(args.report, cmd_str, sanity_line, results, elapsed)

    # Print summary table to stdout
    ops = ["thm_value_swap", "const_swap", "arg_swap", "level_change", "def_body_rfl_break"]
    for op in ops:
        rs = [r for r in results if r["op"] == op]
        rej = sum(1 for r in rs if r["observed"] == "REJECT")
        print(f"  {op}: total={len(rs)} rejected={rej} accepted={len(rs) - rej}")
    print(f"TOTAL: {len(results)} | REJECTED: {len(results) - len(accepted)} | ACCEPTED: {len(accepted)} | {elapsed:.2f}s")
    print(f"Report written to {args.report}")


if __name__ == "__main__":
    main()
