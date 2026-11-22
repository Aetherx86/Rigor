#!/usr/bin/env python3
"""Soundness mutation-testing harness for the Rigor proof kernel.

Generates syntactically valid NDJSON mutants of a Lean 4 lean4export file
across seven mutation operators and verifies that Rigor rejects broken proofs.
Supports multi-million-line exports via mmap-backed lazy expression loading,
streaming binary mutant emission, and sound two-stage truncation (truncate right
after the mutated declaration + direct dependents; automatically re-verify any
accepted mutant against the full un-truncated file).

Uses Python 3 standard library only.
"""

import argparse
import bisect
import concurrent.futures
import json
import mmap
import os
import random
import subprocess
import sys
import tempfile
import time
from array import array
from pathlib import Path

sys.setrecursionlimit(10000)

ALL_OPS = [
    "thm_value_swap",
    "const_swap",
    "arg_swap",
    "level_change",
    "def_body_rfl_break",
    "inductive_mutation",
    "level_arity_mismatch",
]


class LazyExprStore:
    """Memory-efficient, mmap-backed expression store with lazy JSON decoding."""

    def __init__(self, mm: mmap.mmap, expr_offset: array, levels: dict):
        self._mm = mm
        self._offsets = expr_offset
        self._levels = levels
        self._cache = {}
        self._closed_cache = {}
        self._lparams_cache = {}
        self._lvl_params_cache = {0: frozenset()}

    def __getitem__(self, eid: int) -> dict:
        val = self._cache.get(eid)
        if val is not None:
            return val
        off = self._offsets[eid]
        nl = self._mm.find(b"\n", off)
        raw = self._mm[off:] if nl == -1 else self._mm[off:nl]
        val = json.loads(raw)
        self._cache[eid] = val
        return val

    def level_params_of(self, lid: int) -> frozenset:
        res = self._lvl_params_cache.get(lid)
        if res is not None:
            return res
        o = self._levels[lid]
        if "param" in o:
            res = frozenset([o["param"]])
        elif "succ" in o:
            res = self.level_params_of(o["succ"])
        elif "max" in o:
            res = self.level_params_of(o["max"][0]) | self.level_params_of(o["max"][1])
        elif "imax" in o:
            res = self.level_params_of(o["imax"][0]) | self.level_params_of(o["imax"][1])
        else:
            res = frozenset()
        self._lvl_params_cache[lid] = res
        return res

    def _compute_meta(self, root_eid: int):
        """Iteratively compute loose-bvar bound and level params for root_eid's DAG."""
        if root_eid in self._closed_cache:
            return
        stack = [(root_eid, False)]
        while stack:
            eid, expanded = stack.pop()
            if eid in self._closed_cache:
                continue
            e = self[eid]
            if not expanded:
                children = []
                if "app" in e:
                    children = [e["app"]["fn"], e["app"]["arg"]]
                elif "lam" in e:
                    children = [e["lam"]["type"], e["lam"]["body"]]
                elif "forallE" in e:
                    children = [e["forallE"]["type"], e["forallE"]["body"]]
                elif "letE" in e:
                    children = [e["letE"]["type"], e["letE"]["value"], e["letE"]["body"]]
                elif "proj" in e:
                    children = [e["proj"]["struct"]]
                elif "mdata" in e:
                    children = [e["mdata"]["expr"]]
                if children:
                    stack.append((eid, True))
                    for ch in children:
                        if ch not in self._closed_cache:
                            stack.append((ch, False))
                    continue

            if "bvar" in e:
                self._closed_cache[eid] = e["bvar"] + 1
                self._lparams_cache[eid] = frozenset()
            elif "sort" in e:
                self._closed_cache[eid] = 0
                self._lparams_cache[eid] = self.level_params_of(e["sort"])
            elif "const" in e:
                self._closed_cache[eid] = 0
                lp = frozenset()
                for u in e["const"]["us"]:
                    lp |= self.level_params_of(u)
                self._lparams_cache[eid] = lp
            elif "app" in e:
                f, a = e["app"]["fn"], e["app"]["arg"]
                self._closed_cache[eid] = max(self._closed_cache[f], self._closed_cache[a])
                self._lparams_cache[eid] = self._lparams_cache[f] | self._lparams_cache[a]
            elif "lam" in e:
                t, b = e["lam"]["type"], e["lam"]["body"]
                self._closed_cache[eid] = max(self._closed_cache[t], max(0, self._closed_cache[b] - 1))
                self._lparams_cache[eid] = self._lparams_cache[t] | self._lparams_cache[b]
            elif "forallE" in e:
                t, b = e["forallE"]["type"], e["forallE"]["body"]
                self._closed_cache[eid] = max(self._closed_cache[t], max(0, self._closed_cache[b] - 1))
                self._lparams_cache[eid] = self._lparams_cache[t] | self._lparams_cache[b]
            elif "letE" in e:
                t, v, b = e["letE"]["type"], e["letE"]["value"], e["letE"]["body"]
                self._closed_cache[eid] = max(
                    self._closed_cache[t], self._closed_cache[v], max(0, self._closed_cache[b] - 1)
                )
                self._lparams_cache[eid] = (
                    self._lparams_cache[t] | self._lparams_cache[v] | self._lparams_cache[b]
                )
            elif "proj" in e:
                s = e["proj"]["struct"]
                self._closed_cache[eid] = self._closed_cache[s]
                self._lparams_cache[eid] = self._lparams_cache[s]
            elif "mdata" in e:
                x = e["mdata"]["expr"]
                self._closed_cache[eid] = self._closed_cache[x]
                self._lparams_cache[eid] = self._lparams_cache[x]
            else:
                self._closed_cache[eid] = 0
                self._lparams_cache[eid] = frozenset()

    def get_closed(self, eid: int) -> int:
        val = self._closed_cache.get(eid)
        if val is None:
            self._compute_meta(eid)
            val = self._closed_cache[eid]
        return val

    def get_lparams(self, eid: int) -> frozenset:
        val = self._lparams_cache.get(eid)
        if val is None:
            self._compute_meta(eid)
            val = self._lparams_cache[eid]
        return val


def _extract_ie_fast(line: bytes):
    """Fast extraction of integer `ie` ID from a lean4export NDJSON expression line."""
    if line.startswith(b'{"ie":'):
        p = 6
        q = p
        n = len(line)
        while q < n and 48 <= line[q] <= 57:
            q += 1
        if q > p:
            return int(line[p:q])
    elif line.startswith((b'{"app":', b'{"bvar":', b'{"const":', b'{"forallE":')):
        p = line.rfind(b',"ie":')
        if p != -1:
            p += 6
            q = p
            n = len(line)
            while q < n and 48 <= line[q] <= 57:
                q += 1
            if q > p:
                return int(line[p:q])
    return None


def parse_ndjson_index(path: Path):
    """Stream-scan the NDJSON export and build compact lookup tables for mutation generation."""
    file_size = path.stat().st_size
    names = {0: ""}
    levels = {0: {"zero": True}}
    expr_offset = array("Q")
    expr_line = array("I")
    max_il = 0
    max_ie = 0

    const_info = {}
    thms = []  # list of (line_idx, obj)
    defs = []  # list of (line_idx, obj)
    inductives = []  # list of (line_idx, ind_obj)
    decl_name_by_line = {}
    decl_span = {}  # line_idx -> (start_byte, end_byte)
    all_decl_lines = []

    # Sample closed leaf exprs evenly across the file for Op 3 (arg_swap)
    leaf_stride = 25 if file_size > 20_000_000 else 1
    leaf_seen = 0
    sampled_leaf_eids = []

    byte_pos = 0
    total_lines = 0
    with path.open("rb") as f:
        for idx, line in enumerate(f):
            line_len = len(line)
            start_pos = byte_pos
            byte_pos += line_len
            total_lines = idx + 1

            if line_len <= 2:
                continue

            # Fast path for the 6.1M+ expression lines (avoid json.loads during Pass 1)
            if line.startswith((b'{"ie":', b'{"app":', b'{"bvar":', b'{"const":', b'{"forallE":')):
                eid = _extract_ie_fast(line)
                if eid is None:
                    d = json.loads(line)
                    eid = d["ie"]
                if eid >= len(expr_offset):
                    grow = eid - len(expr_offset) + 1
                    expr_offset.extend([0] * grow)
                    expr_line.extend([0] * grow)
                expr_offset[eid] = start_pos
                expr_line[eid] = idx
                if eid > max_ie:
                    max_ie = eid

                # Check if leaf closed expr (const, sort, natVal, strVal)
                if line.startswith(b'{"const":') or (
                    line.startswith(b'{"ie":')
                    and (b',"sort":' in line or b',"natVal":' in line or b',"strVal":' in line)
                ):
                    if leaf_seen % leaf_stride == 0:
                        sampled_leaf_eids.append((idx, eid))
                    leaf_seen += 1
                continue

            if line.startswith(b'{"meta":'):
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
                if eid >= len(expr_offset):
                    grow = eid - len(expr_offset) + 1
                    expr_offset.extend([0] * grow)
                    expr_line.extend([0] * grow)
                expr_offset[eid] = start_pos
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
                decl_span[idx] = (start_pos, byte_pos)
                all_decl_lines.append(idx)
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
                decl_span[idx] = (start_pos, byte_pos)
                all_decl_lines.append(idx)
            elif "axiom" in d:
                obj = d["axiom"]
                const_info[obj["name"]] = {
                    "kind": "axiom",
                    "line": idx,
                    "type": obj["type"],
                    "levelParams": obj["levelParams"],
                }
                decl_name_by_line[idx] = names[obj["name"]]
                decl_span[idx] = (start_pos, byte_pos)
                all_decl_lines.append(idx)
            elif "opaque" in d:
                obj = d["opaque"]
                const_info[obj["name"]] = {
                    "kind": "opaque",
                    "line": idx,
                    "type": obj["type"],
                    "levelParams": obj["levelParams"],
                }
                decl_name_by_line[idx] = names[obj["name"]]
                decl_span[idx] = (start_pos, byte_pos)
                all_decl_lines.append(idx)
            elif "quot" in d:
                obj = d["quot"]
                const_info[obj["name"]] = {
                    "kind": "quot",
                    "line": idx,
                    "type": obj["type"],
                    "levelParams": obj["levelParams"],
                }
                decl_name_by_line[idx] = names[obj["name"]]
                decl_span[idx] = (start_pos, byte_pos)
                all_decl_lines.append(idx)
            elif "inductive" in d:
                ind = d["inductive"]
                inductives.append((idx, ind))
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
                decl_span[idx] = (start_pos, byte_pos)
                all_decl_lines.append(idx)

    mm_file = path.open("rb")
    mm = mmap.mmap(mm_file.fileno(), 0, access=mmap.ACCESS_READ)
    exprs = LazyExprStore(mm, expr_offset, levels)

    return {
        "input_path": path,
        "file_size": file_size,
        "total_lines": total_lines,
        "mm_file": mm_file,
        "mm": mm,
        "names": names,
        "levels": levels,
        "exprs": exprs,
        "expr_line": expr_line,
        "sampled_leaf_eids": sampled_leaf_eids,
        "max_il": max_il,
        "max_ie": max_ie,
        "const_info": const_info,
        "thms": thms,
        "defs": defs,
        "inductives": inductives,
        "decl_name_by_line": decl_name_by_line,
        "decl_span": decl_span,
        "all_decl_lines": all_decl_lines,
    }


def close_ndjson_index(idx_data):
    try:
        idx_data["mm"].close()
    except Exception:
        pass
    try:
        idx_data["mm_file"].close()
    except Exception:
        pass


def collect_consts_in_expr(exprs: LazyExprStore, root_eid: int, cap: int = 500) -> set:
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


def find_paths(exprs: LazyExprStore, root_eid: int, pred, max_paths: int = 25, max_depth: int = 40):
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


def rebuild_path(exprs: LazyExprStore, path, new_leaf_eid: int, next_ie: int):
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


def shift_bvars(exprs: LazyExprStore, root_eid: int, cutoff: int, delta: int, next_ie: int):
    """Shift all loose de Bruijn indices >= cutoff by +delta, emitting fresh expr lines."""
    memo = {}
    out_lines = []

    def rec(eid: int, c: int) -> int:
        nonlocal next_ie
        if exprs.get_closed(eid) <= c:
            return eid
        key = (eid, c)
        if key in memo:
            return memo[key]
        e = exprs[eid]
        if "bvar" in e:
            idx = e["bvar"]
            if idx < c:
                res = eid
            else:
                res = next_ie
                next_ie += 1
                out_lines.append(json.dumps({"bvar": idx + delta, "ie": res}, separators=(",", ":")))
        elif "app" in e:
            f2 = rec(e["app"]["fn"], c)
            a2 = rec(e["app"]["arg"], c)
            if f2 == e["app"]["fn"] and a2 == e["app"]["arg"]:
                res = eid
            else:
                res = next_ie
                next_ie += 1
                out_lines.append(json.dumps({"app": {"fn": f2, "arg": a2}, "ie": res}, separators=(",", ":")))
        elif "lam" in e:
            t2 = rec(e["lam"]["type"], c)
            b2 = rec(e["lam"]["body"], c + 1)
            if t2 == e["lam"]["type"] and b2 == e["lam"]["body"]:
                res = eid
            else:
                sub = dict(e["lam"])
                sub["type"] = t2
                sub["body"] = b2
                res = next_ie
                next_ie += 1
                out_lines.append(json.dumps({"lam": sub, "ie": res}, separators=(",", ":")))
        elif "forallE" in e:
            t2 = rec(e["forallE"]["type"], c)
            b2 = rec(e["forallE"]["body"], c + 1)
            if t2 == e["forallE"]["type"] and b2 == e["forallE"]["body"]:
                res = eid
            else:
                sub = dict(e["forallE"])
                sub["type"] = t2
                sub["body"] = b2
                res = next_ie
                next_ie += 1
                out_lines.append(json.dumps({"forallE": sub, "ie": res}, separators=(",", ":")))
        elif "letE" in e:
            t2 = rec(e["letE"]["type"], c)
            v2 = rec(e["letE"]["value"], c)
            b2 = rec(e["letE"]["body"], c + 1)
            if t2 == e["letE"]["type"] and v2 == e["letE"]["value"] and b2 == e["letE"]["body"]:
                res = eid
            else:
                sub = dict(e["letE"])
                sub["type"] = t2
                sub["value"] = v2
                sub["body"] = b2
                res = next_ie
                next_ie += 1
                out_lines.append(json.dumps({"letE": sub, "ie": res}, separators=(",", ":")))
        elif "proj" in e:
            s2 = rec(e["proj"]["struct"], c)
            if s2 == e["proj"]["struct"]:
                res = eid
            else:
                sub = dict(e["proj"])
                sub["struct"] = s2
                res = next_ie
                next_ie += 1
                out_lines.append(json.dumps({"proj": sub, "ie": res}, separators=(",", ":")))
        elif "mdata" in e:
            x2 = rec(e["mdata"]["expr"], c)
            if x2 == e["mdata"]["expr"]:
                res = eid
            else:
                sub = dict(e["mdata"])
                sub["expr"] = x2
                res = next_ie
                next_ie += 1
                out_lines.append(json.dumps({"mdata": sub, "ie": res}, separators=(",", ":")))
        else:
            res = eid
        memo[key] = res
        return res

    new_root = rec(root_eid, cutoff)
    return out_lines, new_root, next_ie


def _copy_exact_bytes(src, dst, nbytes: int, chunk_size: int = 4 * 1024 * 1024):
    rem = nbytes
    while rem > 0:
        buf = src.read(chunk_size if rem > chunk_size else rem)
        if not buf:
            break
        dst.write(buf)
        rem -= len(buf)


def write_mutated_file(
    input_path: Path,
    out_path: Path,
    target_start: int,
    target_end: int,
    insert_before: list,
    replaced_line: str,
    cut_end: int,
):
    """Stream-write a mutated (optionally truncated) NDJSON file using binary chunks."""
    with input_path.open("rb") as src, out_path.open("wb") as dst:
        _copy_exact_bytes(src, dst, target_start)
        if insert_before:
            dst.write(("\n".join(insert_before) + "\n").encode("utf-8"))
        dst.write((replaced_line + "\n").encode("utf-8"))
        if cut_end > target_end:
            src.seek(target_end)
            _copy_exact_bytes(src, dst, cut_end - target_end)


def generate_mutants(idx_data, seed: int, per_op: int):
    rng = random.Random(seed)
    names = idx_data["names"]
    exprs = idx_data["exprs"]
    const_info = idx_data["const_info"]
    thms = idx_data["thms"]
    defs = idx_data["defs"]
    inductives = idx_data["inductives"]
    decl_name_by_line = idx_data["decl_name_by_line"]
    all_decl_lines = idx_data["all_decl_lines"]
    last_decl_line = all_decl_lines[-1] if all_decl_lines else 0
    max_ie = idx_data["max_ie"]
    max_il = idx_data["max_il"]

    consts_by_arity = {}
    consts_by_arity_lines = {}
    consts_by_type_arity = {}
    consts_by_type_arity_lines = {}
    for nid, info in const_info.items():
        ar = len(info["levelParams"])
        consts_by_arity.setdefault(ar, []).append((info["line"], nid, info["type"], info["kind"]))
        consts_by_type_arity.setdefault((info["type"], ar), []).append((info["line"], nid, info["kind"]))
    for ar, v in consts_by_arity.items():
        v.sort()
        consts_by_arity_lines[ar] = [x[0] for x in v]
    for k, v in consts_by_type_arity.items():
        v.sort()
        consts_by_type_arity_lines[k] = [x[0] for x in v]

    defs_by_type = {}
    defs_by_type_lines = {}
    for lno, dobj in defs:
        defs_by_type.setdefault(dobj["type"], []).append((lno, dobj))
    for k, v in defs_by_type.items():
        v.sort(key=lambda x: x[0])
        defs_by_type_lines[k] = [x[0] for x in v]

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

    # Build closed_arg_pool lazily from sampled leaf exprs
    closed_arg_pool = []
    for lno, eid in idx_data["sampled_leaf_eids"]:
        if exprs.get_closed(eid) != 0:
            continue
        closed_arg_pool.append((lno, eid, exprs.get_lparams(eid), coarse_type_key(eid)))
    closed_arg_pool.sort(key=lambda x: x[0])
    closed_arg_lines = [x[0] for x in closed_arg_pool]

    mutants = []

    # ------------------------------------------------------------------
    # Operator 1: Theorem value swap
    # ------------------------------------------------------------------
    op1_indices = list(range(1, len(thms)))
    op1_count = 0
    seen_op1 = set()
    for _pass in range(3):
        if op1_count >= per_op:
            break
        rng.shuffle(op1_indices)
        for i in op1_indices:
            if op1_count >= per_op:
                break
            l1, t1 = thms[i]
            lp1 = set(t1["levelParams"])
            picked = None
            for _ in range(50):
                j = rng.randrange(i)
                l2, t2 = thms[j]
                if (
                    t2["type"] != t1["type"]
                    and t2["value"] != t1["value"]
                    and set(t2["levelParams"]).issubset(lp1)
                ):
                    picked = (l2, t2)
                    break
            if picked is None:
                continue
            l2, t2 = picked
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
                "cut_line": l1,
                "insert_before": [],
                "replaced_line": json.dumps({"thm": new_obj}, separators=(",", ":")),
                "detail": f"replaced value of {names[t1['name']]} with value of {names[t2['name']]}",
            })
            op1_count += 1

    # ------------------------------------------------------------------
    # Operator 2: Constant swap inside a theorem or definition value
    # ------------------------------------------------------------------
    op2_decls = [("thm", l, o) for l, o in thms] + [("def", l, o) for l, o in defs]
    rng.shuffle(op2_decls)
    op2_count = 0
    seen_op2 = set()
    for dkind, lno, obj in op2_decls:
        if op2_count >= per_op:
            break
        paths = find_paths(exprs, obj["value"], lambda _eid, e: "const" in e, max_paths=15)
        rng.shuffle(paths)
        for path, ceid in paths:
            cobj = exprs[ceid]["const"]
            n1 = cobj["name"]
            us = cobj["us"]
            if n1 not in const_info:
                continue
            ty1 = const_info[n1]["type"]
            ar = len(us)
            arr = consts_by_arity.get(ar)
            if not arr:
                continue
            hi = bisect.bisect_left(consts_by_arity_lines[ar], lno)
            if hi == 0:
                continue
            n2 = None
            for _ in range(40):
                _l2, cand_n2, ty2, _k2 = arr[rng.randrange(hi)]
                if cand_n2 != n1 and ty2 != ty1:
                    n2 = cand_n2
                    break
            if n2 is None:
                continue
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
                "cut_line": lno,
                "insert_before": [leaf_line] + anc_lines,
                "replaced_line": json.dumps({dkind: new_obj}, separators=(",", ":")),
                "detail": f"in {dkind} {names[obj['name']]}, swapped const {names[n1]} -> {names[n2]} (arity {len(us)})",
            })
            op2_count += 1
            break

    # ------------------------------------------------------------------
    # Operator 3: Argument swap in an app node used by a theorem value
    # ------------------------------------------------------------------
    op3_thms = list(thms)
    op3_count = 0
    seen_op3 = set()
    for _pass in range(3):
        if op3_count >= per_op:
            break
        rng.shuffle(op3_thms)
        for lno, obj in op3_thms:
            if op3_count >= per_op:
                break
            hi = bisect.bisect_left(closed_arg_lines, lno)
            if hi == 0:
                continue
            lp_set = frozenset(obj["levelParams"])
            paths = find_paths(exprs, obj["value"], lambda _eid, e: "app" in e, max_paths=20)
            rng.shuffle(paths)
            for path, aeid in paths:
                app_obj = exprs[aeid]["app"]
                fn_id = app_obj["fn"]
                arg_id = app_obj["arg"]
                arg_tkey = coarse_type_key(arg_id)
                cands = []
                for _ in range(40):
                    _el, ceid, clp, ctkey = closed_arg_pool[rng.randrange(hi)]
                    if ceid != arg_id and clp.issubset(lp_set) and ctkey != arg_tkey:
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
                    "cut_line": lno,
                    "insert_before": [leaf_line] + anc_lines,
                    "replaced_line": json.dumps({"thm": new_obj}, separators=(",", ":")),
                    "detail": f"in thm {names[obj['name']]}, swapped app({aeid}) arg {arg_id} -> {alt_arg}",
                })
                op3_count += 1
                break

    # ------------------------------------------------------------------
    # Operator 4: Universe level change on a const node in a theorem value
    # ------------------------------------------------------------------
    op4_thms = list(thms)
    op4_count = 0
    seen_op4 = set()
    for _pass in range(3):
        if op4_count >= per_op:
            break
        rng.shuffle(op4_thms)
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
                    "cut_line": lno,
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

    # Scan theorems (all for small files; shuffled sample up to target pool for giant files)
    rfl_dependents = {}  # def_name_id -> list of (thm_line, thm_label)
    thm_scan = list(thms)
    if len(thm_scan) > 5000:
        rng.shuffle(thm_scan)
    target_rfl_defs = max(per_op * 15, 300)
    for tidx, tobj in thm_scan:
        if len(thm_scan) > 5000 and len(rfl_dependents) >= target_rfl_defs:
            break
        vconsts = collect_consts_in_expr(exprs, tobj["value"], cap=400)
        if not (vconsts & rfl_ids):
            continue
        tconsts = collect_consts_in_expr(exprs, tobj["type"], cap=400)
        for cn in tconsts:
            if cn in def_by_name and def_by_name[cn][0] < tidx:
                rfl_dependents.setdefault(cn, []).append((tidx, names[tobj["name"]]))

    for _hop in range(2):
        for cn, thm_list in list(rfl_dependents.items()):
            didx, dobj = def_by_name[cn]
            thm_list_sorted = sorted(thm_list, key=lambda x: x[0])
            for sub in collect_consts_in_expr(exprs, dobj["value"], cap=300):
                if sub in def_by_name and def_by_name[sub][0] < didx and sub not in rfl_dependents:
                    rfl_dependents[sub] = [
                        (tl, f"{tn} (via {names[cn]})") for tl, tn in thm_list_sorted[:2]
                    ]

    rfl_def_items = []
    for cn, dep_list in rfl_dependents.items():
        dep_list.sort(key=lambda x: x[0])
        rfl_def_items.append((def_by_name[cn][0], def_by_name[cn][1], dep_list))
    rng.shuffle(rfl_def_items)

    op5_count = 0
    seen_op5 = set()

    def _op5_cut_line(lno: int, dep_list: list) -> int:
        # Include the earliest direct rfl dependent (and up to 2 more if within +300k lines)
        chosen = lno
        for k, (dl, _dn) in enumerate(dep_list):
            if dl > chosen:
                if k == 0 or dl <= lno + 300_000:
                    chosen = dl
                if k >= 2:
                    break
        return chosen

    def try_op5_on_def(lno, dobj, dep_list):
        nonlocal op5_count
        dname = dobj["name"]
        dep_names = [dn for _dl, dn in dep_list[:2]]
        cut_line = _op5_cut_line(lno, dep_list)

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
                "cut_line": cut_line,
                "insert_before": [leaf_line] + anc_lines,
                "replaced_line": json.dumps({"def": new_obj}, separators=(",", ":")),
                "detail": f"in def {names[dname]} (rfl deps: {', '.join(dep_names)}), changed natVal {old_val} -> {new_val}",
            })
            op5_count += 1
            return True

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
                    "cut_line": cut_line,
                    "insert_before": [leaf_line] + anc_lines,
                    "replaced_line": json.dumps({"def": new_obj}, separators=(",", ":")),
                    "detail": f"in def {names[dname]} (rfl deps: {', '.join(dep_names)}), flipped {names[old_c]} -> {names[new_c]}",
                })
                op5_count += 1
                return True

        c_paths = find_paths(exprs, dobj["value"], lambda _eid, e: "const" in e, max_paths=15)
        rng.shuffle(c_paths)
        for path, ceid in c_paths:
            cobj = exprs[ceid]["const"]
            n1 = cobj["name"]
            us = cobj["us"]
            if n1 not in const_info or const_info[n1]["kind"] == "thm":
                continue
            ty1 = const_info[n1]["type"]
            tkey = (ty1, len(us))
            arr = consts_by_type_arity.get(tkey)
            if not arr:
                continue
            hi = bisect.bisect_left(consts_by_type_arity_lines[tkey], lno)
            if hi == 0:
                continue
            same_ty_alts = [n2 for _l2, n2, k2 in arr[:hi] if n2 != n1 and k2 != "thm"]
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
                "cut_line": cut_line,
                "insert_before": [leaf_line] + anc_lines,
                "replaced_line": json.dumps({"def": new_obj}, separators=(",", ":")),
                "detail": f"in def {names[dname]} (rfl deps: {', '.join(dep_names)}), same-type const swap {names[n1]} -> {names[n2]}",
            })
            op5_count += 1
            return True

        lp_d = set(dobj["levelParams"])
        same_arr = defs_by_type.get(dobj["type"])
        if same_arr:
            hi = bisect.bisect_left(defs_by_type_lines[dobj["type"]], lno)
            same_defs = [
                d2
                for _l2, d2 in same_arr[:hi]
                if d2["value"] != dobj["value"] and set(d2["levelParams"]).issubset(lp_d)
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
                        "cut_line": cut_line,
                        "insert_before": [],
                        "replaced_line": json.dumps({"def": new_obj}, separators=(",", ":")),
                        "detail": f"replaced body of def {names[dname]} (rfl deps: {', '.join(dep_names)}) with same-type def {names[d2['name']]}",
                    })
                    op5_count += 1
                    return True
        return False

    for lno, dobj, dep_list in rfl_def_items:
        if op5_count >= per_op:
            break
        try_op5_on_def(lno, dobj, dep_list)
    for _ in range(5):
        if op5_count >= per_op:
            break
        rng.shuffle(rfl_def_items)
        for lno, dobj, dep_list in rfl_def_items:
            if op5_count >= per_op:
                break
            try_op5_on_def(lno, dobj, dep_list)

    # ------------------------------------------------------------------
    # Operator 6: Inductive mutation (negative occurrence, sort change,
    #             Prop->Type field injection, or ctor field type corruption)
    # ------------------------------------------------------------------
    single_inds = [
        (lno, ind)
        for lno, ind in inductives
        if len(ind["types"]) == 1 and not ind["types"][0].get("isUnsafe", False)
    ]

    op6_count = 0
    seen_op6 = set()

    def _op6_cut_line(lno: int, ind_name_str: str) -> int:
        """Include direct helper/dependent declarations right after the inductive."""
        pos = bisect.bisect_left(all_decl_lines, lno)
        # Always include at least the next 30 declarations after the inductive (if present)
        end_pos = min(len(all_decl_lines) - 1, pos + 30)
        chosen = all_decl_lines[end_pos]
        prefix = ind_name_str + "."
        # Also extend through any `I.*` helper declarations within +400k lines
        limit_line = lno + 400_000
        scan_pos = pos + 1
        while scan_pos < len(all_decl_lines):
            dl = all_decl_lines[scan_pos]
            if dl > limit_line:
                break
            nm = decl_name_by_line.get(dl, "")
            if nm.startswith(prefix) and dl > chosen:
                chosen = dl
            scan_pos += 1
        return min(chosen, last_decl_line)

    def peel_forall_spine(root_eid: int, count: int):
        """Return (path_to_body, body_eid) after peeling `count` forallE binders, or None."""
        path = []
        cur = root_eid
        for _ in range(count):
            e = exprs[cur]
            if "forallE" not in e:
                return None
            path.append((cur, "forallE.body"))
            cur = e["forallE"]["body"]
        return path, cur

    def find_final_sort(root_eid: int):
        path = []
        cur = root_eid
        while "forallE" in exprs[cur]:
            path.append((cur, "forallE.body"))
            cur = exprs[cur]["forallE"]["body"]
        if "sort" in exprs[cur]:
            return path, cur, exprs[cur]["sort"]
        return None

    def try_op6(lno, ind, strategy):
        nonlocal op6_count
        t0 = ind["types"][0]
        iname = t0["name"]
        iname_str = names[iname]
        np = t0["numParams"]
        nidx = t0["numIndices"]
        lps = t0["levelParams"]
        ctors = ind["ctors"]

        if strategy == "neg_occ" and nidx == 0 and ctors:
            c_idx = rng.randrange(len(ctors))
            c = ctors[c_idx]
            key = (iname, "neg_occ", c["name"])
            if key in seen_op6:
                return False
            peeled = peel_forall_spine(c["type"], np)
            if peeled is None:
                return False
            path, rest_eid = peeled
            next_il = max_il + 1
            next_ie = max_ie + 1
            extra_lines = []
            lp_lids = []
            for lp_name in lps:
                lid = next_il
                next_il += 1
                extra_lines.append(json.dumps({"param": lp_name, "il": lid}, separators=(",", ":")))
                lp_lids.append(lid)
            cur_app = next_ie
            next_ie += 1
            extra_lines.append(json.dumps({"const": {"name": iname, "us": lp_lids}, "ie": cur_app}, separators=(",", ":")))
            for k in range(np - 1, -1, -1):
                bv_id = next_ie
                next_ie += 1
                extra_lines.append(json.dumps({"bvar": k, "ie": bv_id}, separators=(",", ":")))
                app_id = next_ie
                next_ie += 1
                extra_lines.append(json.dumps({"app": {"fn": cur_app, "arg": bv_id}, "ie": app_id}, separators=(",", ":")))
                cur_app = app_id
            prop_id = next_ie
            next_ie += 1
            extra_lines.append(json.dumps({"sort": 0, "ie": prop_id}, separators=(",", ":")))
            neg_dom = next_ie
            next_ie += 1
            extra_lines.append(json.dumps({
                "forallE": {"name": 0, "type": cur_app, "body": prop_id, "binderInfo": "default"},
                "ie": neg_dom,
            }, separators=(",", ":")))
            sh_lines, shifted_rest, next_ie = shift_bvars(exprs, rest_eid, 0, 1, next_ie)
            extra_lines.extend(sh_lines)
            new_rest = next_ie
            next_ie += 1
            extra_lines.append(json.dumps({
                "forallE": {"name": 0, "type": neg_dom, "body": shifted_rest, "binderInfo": "default"},
                "ie": new_rest,
            }, separators=(",", ":")))
            anc_lines, new_cty, _ = rebuild_path(exprs, path, new_rest, next_ie)
            extra_lines.extend(anc_lines)

            new_ind = json.loads(json.dumps(ind))
            new_ind["ctors"][c_idx]["type"] = new_cty
            seen_op6.add(key)
            mutants.append({
                "op": "inductive_mutation",
                "target": iname_str,
                "target_line": lno,
                "cut_line": _op6_cut_line(lno, iname_str),
                "insert_before": extra_lines,
                "replaced_line": json.dumps({"inductive": new_ind}, separators=(",", ":")),
                "detail": f"in inductive {iname_str} ctor {names[c['name']]}, injected negative occurrence ({iname_str} -> Prop)",
            })
            op6_count += 1
            return True

        if strategy == "sort_change":
            fs = find_final_sort(t0["type"])
            if fs is None:
                return False
            path, _seid, old_lvl = fs
            key = (iname, "sort_change", old_lvl)
            if key in seen_op6:
                return False
            next_il = max_il + 1
            next_ie = max_ie + 1
            extra_lines = []
            if old_lvl == 0:
                new_lvl = next_il
                next_il += 1
                extra_lines.append(json.dumps({"succ": 0, "il": new_lvl}, separators=(",", ":")))
                desc = "changed sort Prop -> Type 0"
            elif lps:
                new_lvl = next_il
                next_il += 1
                extra_lines.append(json.dumps({"succ": 0, "il": new_lvl}, separators=(",", ":")))
                desc = f"downgraded universe-polymorphic sort il={old_lvl} -> Type 0"
            else:
                new_lvl = next_il
                next_il += 1
                extra_lines.append(json.dumps({"succ": old_lvl, "il": new_lvl}, separators=(",", ":")))
                desc = f"bumped inductive sort il={old_lvl} -> succ({old_lvl})"
            new_sort_eid = next_ie
            next_ie += 1
            extra_lines.append(json.dumps({"sort": new_lvl, "ie": new_sort_eid}, separators=(",", ":")))
            anc_lines, new_ity, _ = rebuild_path(exprs, path, new_sort_eid, next_ie)
            extra_lines.extend(anc_lines)

            new_ind = json.loads(json.dumps(ind))
            new_ind["types"][0]["type"] = new_ity
            seen_op6.add(key)
            mutants.append({
                "op": "inductive_mutation",
                "target": iname_str,
                "target_line": lno,
                "cut_line": _op6_cut_line(lno, iname_str),
                "insert_before": extra_lines,
                "replaced_line": json.dumps({"inductive": new_ind}, separators=(",", ":")),
                "detail": f"in inductive {iname_str}, {desc}",
            })
            op6_count += 1
            return True

        if strategy == "prop_type_field" and ctors:
            fs = find_final_sort(t0["type"])
            if fs is None or fs[2] != 0:
                return False
            c_idx = rng.randrange(len(ctors))
            c = ctors[c_idx]
            key = (iname, "prop_type_field", c["name"])
            if key in seen_op6:
                return False
            peeled = peel_forall_spine(c["type"], np)
            if peeled is None:
                return False
            path, rest_eid = peeled
            next_il = max_il + 1
            next_ie = max_ie + 1
            extra_lines = []
            l1 = next_il
            next_il += 1
            extra_lines.append(json.dumps({"succ": 0, "il": l1}, separators=(",", ":")))
            type0_id = next_ie
            next_ie += 1
            extra_lines.append(json.dumps({"sort": l1, "ie": type0_id}, separators=(",", ":")))
            sh_lines, shifted_rest, next_ie = shift_bvars(exprs, rest_eid, 0, 1, next_ie)
            extra_lines.extend(sh_lines)
            new_rest = next_ie
            next_ie += 1
            extra_lines.append(json.dumps({
                "forallE": {"name": 0, "type": type0_id, "body": shifted_rest, "binderInfo": "default"},
                "ie": new_rest,
            }, separators=(",", ":")))
            anc_lines, new_cty, _ = rebuild_path(exprs, path, new_rest, next_ie)
            extra_lines.extend(anc_lines)

            new_ind = json.loads(json.dumps(ind))
            new_ind["ctors"][c_idx]["type"] = new_cty
            seen_op6.add(key)
            mutants.append({
                "op": "inductive_mutation",
                "target": iname_str,
                "target_line": lno,
                "cut_line": _op6_cut_line(lno, iname_str),
                "insert_before": extra_lines,
                "replaced_line": json.dumps({"inductive": new_ind}, separators=(",", ":")),
                "detail": f"in Prop inductive {iname_str} ctor {names[c['name']]}, injected non-Prop field (x : Type 0)",
            })
            op6_count += 1
            return True

        if strategy == "ctor_field_change" and ctors:
            c_idx = rng.randrange(len(ctors))
            c = ctors[c_idx]
            peeled = peel_forall_spine(c["type"], np)
            if peeled is None:
                return False
            path, rest_eid = peeled
            if "forallE" not in exprs[rest_eid]:
                return False
            key = (iname, "ctor_field_change", c["name"])
            if key in seen_op6:
                return False
            next_il = max_il + 1
            next_ie = max_ie + 1
            extra_lines = []
            l1 = next_il
            l2 = next_il + 1
            extra_lines.append(json.dumps({"succ": 0, "il": l1}, separators=(",", ":")))
            extra_lines.append(json.dumps({"succ": l1, "il": l2}, separators=(",", ":")))
            type1_id = next_ie
            next_ie += 1
            extra_lines.append(json.dumps({"sort": l2, "ie": type1_id}, separators=(",", ":")))
            orig_fe = dict(exprs[rest_eid]["forallE"])
            orig_fe["type"] = type1_id
            new_rest = next_ie
            next_ie += 1
            extra_lines.append(json.dumps({"forallE": orig_fe, "ie": new_rest}, separators=(",", ":")))
            anc_lines, new_cty, _ = rebuild_path(exprs, path, new_rest, next_ie)
            extra_lines.extend(anc_lines)

            new_ind = json.loads(json.dumps(ind))
            new_ind["ctors"][c_idx]["type"] = new_cty
            seen_op6.add(key)
            mutants.append({
                "op": "inductive_mutation",
                "target": iname_str,
                "target_line": lno,
                "cut_line": _op6_cut_line(lno, iname_str),
                "insert_before": extra_lines,
                "replaced_line": json.dumps({"inductive": new_ind}, separators=(",", ":")),
                "detail": f"in inductive {iname_str} ctor {names[c['name']]}, changed first field type to Type 1",
            })
            op6_count += 1
            return True

        return False

    strategies = ["neg_occ", "sort_change", "prop_type_field", "ctor_field_change"]
    ind_pool = list(single_inds)
    for _pass in range(4):
        if op6_count >= per_op:
            break
        rng.shuffle(ind_pool)
        for lno, ind in ind_pool:
            if op6_count >= per_op:
                break
            order = list(strategies)
            rng.shuffle(order)
            for st in order:
                if try_op6(lno, ind, st):
                    break

    # ------------------------------------------------------------------
    # Operator 7: Universe-parameter count mismatch on a const node in a theorem
    # ------------------------------------------------------------------
    op7_thms = list(thms)
    op7_count = 0
    seen_op7 = set()
    for _pass in range(3):
        if op7_count >= per_op:
            break
        rng.shuffle(op7_thms)
        for lno, obj in op7_thms:
            if op7_count >= per_op:
                break
            paths = find_paths(exprs, obj["value"], lambda _eid, e: "const" in e, max_paths=20)
            rng.shuffle(paths)
            for path, ceid in paths:
                cobj = exprs[ceid]["const"]
                n1 = cobj["name"]
                us = list(cobj["us"])
                if len(us) >= 1 and rng.random() < 0.5:
                    action = "drop"
                    new_us = us[:-1]
                else:
                    action = "add"
                    new_us = us + [0]
                key = (obj["name"], ceid, action)
                if key in seen_op7:
                    continue
                seen_op7.add(key)
                next_ie = max_ie + 1
                leaf_id = next_ie
                next_ie += 1
                leaf_line = json.dumps({"const": {"name": n1, "us": new_us}, "ie": leaf_id}, separators=(",", ":"))
                anc_lines, new_root, _ = rebuild_path(exprs, path, leaf_id, next_ie)
                new_obj = dict(obj)
                new_obj["value"] = new_root
                mutants.append({
                    "op": "level_arity_mismatch",
                    "target": names[obj["name"]],
                    "target_line": lno,
                    "cut_line": lno,
                    "insert_before": [leaf_line] + anc_lines,
                    "replaced_line": json.dumps({"thm": new_obj}, separators=(",", ":")),
                    "detail": f"in thm {names[obj['name']]}, {action} level arg on {names[n1]} ({len(us)} -> {len(new_us)})",
                })
                op7_count += 1
                break

    return mutants


def run_checker(checker_bin: Path, ndjson_path: Path, rigor_threads: int = 4):
    env = os.environ.copy()
    env["RIGOR_THREADS"] = str(rigor_threads)
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
            err_line = (
                stderr_lines[0]
                if stderr_lines
                else stdout.splitlines()[0]
                if stdout
                else f"exit={proc.returncode}"
            )
    else:
        err_line = next((ln for ln in stdout.splitlines() if ln.startswith("CHECK_OK")), stdout)
    return accepted, proc.returncode, err_line


def evaluate_mutant(args_tuple):
    (
        idx,
        mutant,
        input_path,
        file_size,
        total_lines,
        target_start,
        target_end,
        cut_end,
        truncate,
        checker_bin,
        rigor_threads,
        tmp_dir,
    ) = args_tuple

    tmp_file = Path(tmp_dir) / f"mutant_{idx:04d}.ndjson"
    effective_cut_end = cut_end if truncate else file_size
    effective_cut_line = (mutant["cut_line"] + 1) if truncate else total_lines
    full_recheck = False

    write_mutated_file(
        input_path,
        tmp_file,
        target_start,
        target_end,
        mutant["insert_before"],
        mutant["replaced_line"],
        effective_cut_end,
    )
    try:
        accepted, rc, err_line = run_checker(checker_bin, tmp_file, rigor_threads=rigor_threads)
    finally:
        try:
            tmp_file.unlink()
        except OSError:
            pass

    # Soundness safeguard: any truncated mutant that is ACCEPTED is automatically re-checked
    # against the complete un-truncated file so truncation can never produce a false ACCEPT.
    if accepted and truncate and effective_cut_end < file_size:
        full_recheck = True
        effective_cut_line = total_lines
        write_mutated_file(
            input_path,
            tmp_file,
            target_start,
            target_end,
            mutant["insert_before"],
            mutant["replaced_line"],
            file_size,
        )
        try:
            accepted, rc, err_line = run_checker(checker_bin, tmp_file, rigor_threads=rigor_threads)
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
        "checked_lines": effective_cut_line,
        "full_recheck": full_recheck,
        "detail": mutant["detail"],
        "expected": "REJECT",
        "observed": "ACCEPT" if accepted else "REJECT",
        "returncode": rc,
        "error_line": err_line,
    }


def format_report_section(
    title: str,
    cmd_str: str,
    sanity_line: str,
    results: list,
    elapsed_s: float,
    truncate: bool = False,
    total_lines: int = 0,
) -> str:
    by_op = {op: [r for r in results if r["op"] == op] for op in ALL_OPS}
    total = len(results)
    rejected = sum(1 for r in results if r["observed"] == "REJECT")
    accepted_list = [r for r in results if r["observed"] == "ACCEPT"]

    lines = [
        f"## {title}",
        "",
        "### Command",
        "",
        "```sh",
        cmd_str,
        "```",
        "",
        "### Sanity Check (Unmutated Input)",
        "",
        f"- Result: PASS (`{sanity_line}`)",
        f"- Total elapsed time: {elapsed_s:.2f} s",
    ]
    if truncate and results and total_lines > 0:
        avg_lines = sum(r.get("checked_lines", total_lines) for r in results) / len(results)
        rechecked = sum(1 for r in results if r.get("full_recheck"))
        lines.append(
            f"- Truncation mode: ON (avg {avg_lines:,.0f} / {total_lines:,} lines = "
            f"{100.0 * avg_lines / total_lines:.1f}% per mutant; {rechecked} Stage-1 accept(s) "
            f"re-verified against the full un-truncated file)"
        )
    lines.extend([
        "",
        "### Summary by Mutation Operator",
        "",
        "| Operator | Total | Rejected | Accepted | Rejection Rate |",
        "|---|---:|---:|---:|---:|",
    ])
    for op in ALL_OPS:
        rs = by_op[op]
        n = len(rs)
        rej = sum(1 for r in rs if r["observed"] == "REJECT")
        acc = n - rej
        rate = (100.0 * rej / n) if n else 0.0
        lines.append(f"| `{op}` | {n} | {rej} | {acc} | {rate:.1f}% |")
    rate_all = (100.0 * rejected / total) if total else 0.0
    lines.append(f"| **Total** | **{total}** | **{rejected}** | **{len(accepted_list)}** | **{rate_all:.1f}%** |")
    lines.append("")

    for op_name, label in [
        ("def_body_rfl_break", "Operator 5 (`def_body_rfl_break`)"),
        ("inductive_mutation", "Operator 6 (`inductive_mutation`)"),
    ]:
        rej_rs = [r for r in by_op[op_name] if r["observed"] == "REJECT"]
        if not rej_rs:
            continue
        later = 0
        for r in rej_rs:
            err = r["error_line"]
            marker = "kernel rejected declaration "
            if marker in err:
                decl_failed = err.split(marker, 1)[1].split(":", 1)[0].strip()
                if decl_failed and decl_failed != r["target"]:
                    later += 1
            elif "line: " in err:
                after = err.split("line: ", 1)[1]
                digits = ""
                for ch in after:
                    if ch.isdigit():
                        digits += ch
                    else:
                        break
                if digits and int(digits) > r["mutated_line"]:
                    later += 1
        lines.extend([
            f"### {label} Rejection Breakdown",
            "",
            f"- Rejected mutants: {len(rej_rs)}",
            f"- Rejected at a later dependent declaration: {later}",
            f"- Rejected at the mutated declaration itself: {len(rej_rs) - later}",
            "",
        ])

    lines.append("### Accepted Mutants")
    lines.append("")
    if not accepted_list:
        lines.append("None. Every generated mutant was rejected by Rigor.")
    else:
        for r in accepted_list:
            lines.append(
                f"- Mutant #{r['id']} (`{r['op']}`): target `{r['target']}` (line {r['target_line']}) -- "
                f"{r['detail']} | output: `{r['error_line']}`"
            )
    lines.append("")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description="Soundness mutation-testing harness for Rigor")
    parser.add_argument(
        "--input",
        type=Path,
        default=Path.home() / "rigor-data/exports/Init.Prelude.ndjson",
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
        "--rigor-threads",
        type=int,
        default=int(os.environ.get("RIGOR_THREADS", "4")),
        help="Threads per rigor-bench invocation (default: $RIGOR_THREADS or 4)",
    )
    parser.add_argument(
        "--truncate",
        action="store_true",
        help="Truncate each mutant right after target (+ direct dependents); re-verify any accept on full file",
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=Path.home() / "rigor/tools/mutation/REPORT.md",
        help="Output Markdown report path",
    )
    parser.add_argument(
        "--append-report",
        action="store_true",
        help="Append section to existing report instead of overwriting",
    )
    parser.add_argument(
        "--section-title",
        type=str,
        default="Mutation Run",
        help="Section title when appending to report",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=Path.home() / "rigor/tools/mutation/results.json",
        help="Output JSON log path",
    )
    args = parser.parse_args()

    t0 = time.monotonic()

    ok, rc, sanity_line = run_checker(args.checker, args.input, rigor_threads=args.rigor_threads)
    if not ok:
        print(f"SANITY CHECK FAILED (rc={rc}): {sanity_line}", file=sys.stderr)
        sys.exit(2)
    print(f"SANITY_OK: {sanity_line}", flush=True)

    t_idx = time.monotonic()
    idx_data = parse_ndjson_index(args.input)
    print(
        f"Indexed {idx_data['total_lines']:,} lines ({len(idx_data['thms']):,} thms, "
        f"{len(idx_data['defs']):,} defs, {len(idx_data['inductives']):,} inductives) "
        f"in {time.monotonic() - t_idx:.2f}s",
        flush=True,
    )

    t_gen = time.monotonic()
    mutants = generate_mutants(idx_data, seed=args.seed, per_op=args.per_op)
    print(
        f"Generated {len(mutants)} mutants (seed={args.seed}, per_op={args.per_op}, "
        f"truncate={args.truncate}) in {time.monotonic() - t_gen:.2f}s",
        flush=True,
    )

    decl_span = idx_data["decl_span"]
    file_size = idx_data["file_size"]
    total_lines = idx_data["total_lines"]

    tasks = []
    for i, m in enumerate(mutants):
        t_start, t_end = decl_span[m["target_line"]]
        _c_start, c_end = decl_span[m["cut_line"]]
        tasks.append((
            i + 1,
            m,
            args.input,
            file_size,
            total_lines,
            t_start,
            t_end,
            c_end,
            args.truncate,
            args.checker,
            args.rigor_threads,
        ))

    # Release mmap + index memory before spawning concurrent rigor-bench processes
    close_ndjson_index(idx_data)
    del idx_data

    results = []
    done = 0
    with tempfile.TemporaryDirectory(prefix="rigor_mut_") as tmp_dir:
        full_tasks = [t + (tmp_dir,) for t in tasks]
        if args.workers <= 1:
            for t in full_tasks:
                res = evaluate_mutant(t)
                results.append(res)
                done += 1
                if done % 10 == 0 or done == len(full_tasks):
                    acc_so_far = sum(1 for r in results if r["observed"] == "ACCEPT")
                    print(
                        f"Progress: {done}/{len(full_tasks)} checked "
                        f"(accepted={acc_so_far}, elapsed={time.monotonic() - t0:.1f}s)",
                        flush=True,
                    )
        else:
            with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
                for res in pool.map(evaluate_mutant, full_tasks):
                    results.append(res)
                    done += 1
                    if done % 10 == 0 or done == len(full_tasks):
                        acc_so_far = sum(1 for r in results if r["observed"] == "ACCEPT")
                        print(
                            f"Progress: {done}/{len(full_tasks)} checked "
                            f"(accepted={acc_so_far}, elapsed={time.monotonic() - t0:.1f}s)",
                            flush=True,
                        )

    elapsed = time.monotonic() - t0

    accepted = [r for r in results if r["observed"] == "ACCEPT"]
    for r in accepted:
        print(
            f"ACCEPTED Mutant #{r['id']} [{r['op']}] target={r['target']} (line {r['target_line']}): "
            f"{r['detail']}",
            flush=True,
        )

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")

    trunc_flag = " --truncate" if args.truncate else ""
    cmd_str = (
        f"RIGOR_THREADS={args.rigor_threads} python3 {Path(__file__).resolve()} "
        f"--input {args.input} --checker {args.checker} --seed {args.seed} "
        f"--per-op {args.per_op} --workers {args.workers}{trunc_flag} "
        f"--report {args.report} --append-report --section-title \"{args.section_title}\" "
        f"--json-out {args.json_out}"
    )
    section = format_report_section(
        args.section_title,
        cmd_str,
        sanity_line,
        results,
        elapsed,
        truncate=args.truncate,
        total_lines=total_lines,
    )
    if args.append_report and args.report.exists():
        prev = args.report.read_text(encoding="utf-8").rstrip()
        args.report.write_text(prev + "\n\n---\n\n" + section, encoding="utf-8")
    else:
        header = "# Rigor Soundness Mutation-Testing Report\n\n"
        args.report.write_text(header + section, encoding="utf-8")

    for op in ALL_OPS:
        rs = [r for r in results if r["op"] == op]
        rej = sum(1 for r in rs if r["observed"] == "REJECT")
        print(f"  {op}: total={len(rs)} rejected={rej} accepted={len(rs) - rej}")
    print(f"TOTAL: {len(results)} | REJECTED: {len(results) - len(accepted)} | ACCEPTED: {len(accepted)} | {elapsed:.2f}s")
    print(f"Report written to {args.report}")


if __name__ == "__main__":
    main()
