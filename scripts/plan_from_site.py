#!/usr/bin/env python3
"""Reconstruct a site policy with the Lean planner `plan` and kernel-check the reconstruction.

    plan_from_site.py SITE_POLICY.json [...] [--tables PRE.json] [--n 2048] [--fault none|unsorted|foreign-index|foreign-table]
                      [--replay] [--out RESULTS.json] [--cap-gb 8] [--timeout 1800] [--planner-crosscheck]
    plan_from_site.py --all-seeds DIR ...      # every DIR/S*/site_policy.json (read only)

Bridge (b) of the planner proof (`BandedPolicy/Plan.lean`, PTP suite `PTP/Plan.lean`):

1. tables   the planner's candidate set: the distinct tables of the seed's own pre-re-plan policy
            (`site_policy.pre_exact.json` next to the site policy, or --tables), in the Python planner's
            canonical order (k, digest). These are what `seed_policies.replan` hands `optimal_policy`.
2. oracle   read off the site policy with the SITE's Python: from n, `choose(w)` (first band with threshold <= w)
            and the Python exact width `Table.child_width(w, "exact")`; each recursive node contributes
            (w, index of its table in the candidate list). This is a finite `(width, index)` table.
3. Lean     one module per policy: the candidate tables, the oracle table, and the site policy rendered
            separately from the site JSON (its own table literals), then
              tables_ok    : tables.all (check) = true                  (kernel)
              reconstructs : plan tables mode n (oracleOfList tables oracle) = sitePolicy   (kernel, DecidableEq)
              site_check, site_correct, site_correct_tight, site_ladder  -- by `plan_check` etc., NOT re-decided.
            Lean recomputes the exact widths itself; `python_ladder` pins every Python width (leaf included)
            to Lean's. NOTE: the oracle is read off the site policy, so `reconstructs` certifies
            self-consistency + provenance (tables are the candidates), not the planner's objective.
4. faults   --fault unsorted       the site's band list reversed: reconstruction must FAIL, and the module instead
                                   proves `∀ o, plan … o ≠ sitePolicy` from `plan_ne_of_unsorted`.
            --fault foreign-index  every oracle index replaced by len(tables) (names no listed table): the
                                   reconstruction must FAIL (`oracleOfList` maps it to the leaf; a `Fin` index
                                   out of range is not expressible at all). This tests only the fallback.
            --fault foreign-table  site band 0's table replaced by a table NOT in the list (two extra `negate 0`,
                                   same function): the module proves `∀ o, plan … o ≠ sitePolicy` from
                                   `plan_ne_of_foreign`, and the reconstruction must FAIL.
            A fault passes only when its module BUILDS: the kernel proves `reconstruction_fails : plan … ≠ sitePolicy`\n            (and `no_oracle` where emitted). Build errors are mapped to declarations by line.
            Fault-free modules also prove `python_ladder`: the site's Python exact ladder (every width and k,
            leaf width included) equals the Lean exact ladder of the site policy (kernel).
5. replay   --replay: kernel replay of the module (scripts/trusted/ReplayPrefix.lean), one process, axioms checked.

Every lake/lean process waits while >= 2 `lean` processes run, runs under scripts/memcap.py (cap, timeout; memcap
starts it in its own session and kills the group). PP modules are built in this project, PTP modules in the PTP suite
(--ptp-root).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import secrets
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
from policy_json_to_lean import PolicyError, lean_comment, op_lean, point_lean  # noqa: E402

DEFAULT_PTP_ROOT = ROOT  # consolidated package: the PTP suite lives in this repository
DEFAULT_SITE_ENGINE = ROOT.parent / "sto_site" / "engine"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PP, PTP = "PhaseProduct", "PhaseTripleProduct"


def site_tcost(engine: Path):
    sys.path.insert(0, str(engine))
    from tcost import tables as tt  # noqa: E402  (pure Python; read only)
    return tt


# ------------------------------------------------------------------------------------------------ oracle
def candidates(tt, pre_doc: dict, mode: str):
    P = tt.Policy.from_json(pre_doc, widths="exact")
    tabs = list(dict.fromkeys(b.table for b in P.bands))
    return sorted({t for t in tabs if t.mode == mode}, key=lambda t: (t.k, t.digest))


def site_bands(tt, doc: dict):
    """The site policy's bands as (threshold, Table), WITHOUT Policy's sortedness validation (faults need it)."""
    out = []
    for b in doc["bands"]:
        tab = dict(b.get("table", b))
        tab.setdefault("mode", doc["mode"])
        out.append((b["threshold"], tt.Table.from_json(tab)))
    return out


def read_oracle(bands, cands, n: int):
    """Walk the site policy with the site's Python exact widths; return [(w, idx)] and the Python ladder."""
    idx = {t.digest: i for i, t in enumerate(cands)}
    oracle, ladder, w = [], [], n
    for _ in range(n + 1):
        T = next((t for th, t in bands if th <= w), None)
        if T is None:
            break
        w2 = T.child_width(w, "exact")
        if not w2 < w:
            break
        if T.digest not in idx:
            raise PolicyError(f"site band table {T.digest[:12]} at width {w} is not in the candidate set")
        oracle.append((w, idx[T.digest]))
        ladder.append((w, T.k))
        w = w2
    ladder.append((w, None))
    return oracle, ladder


def planner_crosscheck(engine: Path, pre_doc: dict, mode: str, n: int, oracle):
    """(a)-style check: the Python planner's RAW bands (before `canonical`) are exactly the oracle walk."""
    sys.path.insert(0, str(engine))
    from tcost import planner as tp, tables as tt  # noqa: E402
    P = tt.Policy.from_json(pre_doc, widths="exact")
    tabs = list(dict.fromkeys(b.table for b in P.bands))
    Q, _ = tp.optimal_policy(tabs, mode, n, 0.01, widths="exact")
    cands = sorted({t for t in tabs if t.mode == mode}, key=lambda t: (t.k, t.digest))
    idx = {t.digest: i for i, t in enumerate(cands)}
    raw = [(b.threshold, idx[b.table.digest]) for b in Q.bands]
    return raw == [tuple(x) for x in oracle], raw


# ------------------------------------------------------------------------------------------------ Lean
def table_lean(name: str, tydecl: str, t: dict) -> str:
    k = t["k"]
    pts = [point_lean(p) for p in t["point_order"]]
    ops = [op_lean(o, k) for o in t["operations"]]
    body = ("    [ " + "\n    , ".join(ops) + " ]") if ops else "    []"
    return f"def {name} : {tydecl} where\n  k := {k}\n  pts := [{', '.join(pts)}]\n  ops :=\n{body}\n"


def table_json(T) -> dict:
    return T.to_json()


def render(sid: str, mode: str, cands, site_doc: dict, oracle, n: int, fault: str, tag: str,
           ladder=None) -> tuple[str, str]:
    """Return (module name, Lean source)."""
    ptp = mode == PTP
    mod = f"{sid}{tag}"
    if ptp:
        ns_root, imp = "TableGeneration.PTP.PlanSeeds", "TableGeneration.RecursiveCost.PTP.Plan"
        tyT, tyP, opens = "PTPTable", "PTPPolicy", "open TableGeneration TableGeneration.Operations TableGeneration.PTP TableGeneration.PTP.Planner TableGeneration.PlanCore"
    else:
        ns_root, imp = "TableGeneration.PolicyMirror.PlanSeeds", "TableGeneration.RecursiveCost.BandedPolicy.Plan"
        tyT, tyP, opens = "PolicyTable", "BandedPolicy", "open TableGeneration TableGeneration.Operations TableGeneration.PolicyMirror TableGeneration.PolicyMirror.Planner TableGeneration.PlanCore"
    o = [f"import {imp}\n",
         f"/-! Generated by scripts/plan_from_site.py: site policy {lean_comment(site_doc.get('name', ''), 120)} "
         f"(fault: {fault}). -/\n",
         f"namespace {ns_root}.{mod}\n", opens + "\n"]
    for i, T in enumerate(cands):
        o.append(f"/-- candidate {i}: k = {T.k}, digest {T.digest[:12]} -/")
        o.append(table_lean(f"cand{i}", tyT, table_json(T)))
    o.append(f"/-- The planner's candidate set (Python order (k, digest)). -/")
    o.append(f"def tables : List {tyT} := [{', '.join(f'cand{i}' for i in range(len(cands)))}]\n")
    o.append("/-- The oracle read off the site policy with the site's Python exact widths: (width, index). -/")
    o.append("def oracleData : List (Nat × Nat) := [" + ", ".join(f"({w}, {i})" for w, i in oracle) + "]\n")
    o.append("def oracle : Oracle tables := oracleOfList tables oracleData\n")
    bands = site_doc["bands"]
    for bi, b in enumerate(bands):
        t = dict(b.get("table", b))
        o.append(f"/-- site band {bi}: threshold {b['threshold']}, k = {t['k']} -/")
        o.append(table_lean(f"site{bi}", tyT, t))
    blist = ", ".join(f"⟨{b['threshold']}, site{bi}⟩" for bi, b in enumerate(bands))
    o.append("/-- The site policy, rendered from the site JSON (its own table literals). -/")
    if ptp:
        o.append(f"def sitePolicy : {tyP} where\n  bands := [{blist}]\n")
    else:
        o.append(f"def sitePolicy : {tyP} where\n  mode := .PhaseProduct\n  bands := [{blist}]\n")
    check = "tables.all PTPTable.contract" if ptp else "tables.all (fun T => T.check .PhaseProduct)"
    planE = f"plan tables {n} oracle" if ptp else f"plan tables .PhaseProduct {n} oracle"
    o.append("/-- Every candidate passes STO's table contract (kernel). -/")
    o.append(f"theorem tables_ok : {check} = true := by decide +kernel\n")
    planA = f"plan tables {n} o" if ptp else f"plan tables .PhaseProduct {n} o"
    if fault == "foreign-table":
        o.append("/-- Site band 0's table is not in the candidate list, so NO oracle produces this policy\n"
                 "(`plan_ne_of_foreign`). -/")
        md = "" if ptp else ".PhaseProduct "
        o.append(f"theorem no_oracle : ∀ o : Oracle tables, {planA} ≠ sitePolicy :=\n"
                 f"  plan_ne_of_foreign tables {md}{n} sitePolicy ⟨{site_doc['bands'][0]['threshold']}, site0⟩\n"
                 f"    (by decide +kernel) (by decide +kernel)\n")
    if fault == "unsorted":
        o.append("/-- The reversed band list is the output of NO oracle (`plan_ne_of_unsorted`). -/")
        ne = (f"plan_ne_of_unsorted tables {n} sitePolicy (by decide +kernel)" if ptp else
              f"plan_ne_of_unsorted tables .PhaseProduct {n} sitePolicy (by decide +kernel)")
        o.append(f"theorem no_oracle : ∀ o : Oracle tables, {planA} ≠ sitePolicy :=\n  {ne}\n")
    if fault != "none":
        o.append("/-- **Fault**: the kernel evaluates the reconstruction equality to `false`, so the faulty\n"
                 "policy is NOT what the planner outputs on this oracle. -/")
        o.append(f"theorem reconstruction_fails : {planE} ≠ sitePolicy := by decide +kernel\n")
        o.append(f"end {ns_root}.{mod}\n")
        return mod, "\n".join(o)
    o.append("/-- **Reconstruction**: the Lean planner, given the oracle, outputs exactly the site policy (kernel). -/")
    o.append(f"theorem reconstructs : {planE} = sitePolicy := by decide +kernel\n")
    lad = ", ".join(f"({w}, {'none' if k is None else f'some {k}'})" for w, k in ladder)
    o.append("/-- The exact-width ladder the SITE's Python computes (widths and k, leaf width included),\n"
             "checked against Lean's exact widths by the kernel. -/")
    o.append(f"def pythonLadder : List (Nat × Option Nat) := [{lad}]\n")
    o.append(f"theorem python_ladder : sitePolicy.{'ladderX' if ptp else 'ladderTight'} {n} = pythonLadder := by decide +kernel\n")
    if ptp:
        o.append("/-- Validity of the site policy, from `plan_check` (not re-decided). -/")
        o.append("theorem site_check : sitePolicy.check = true :=\n"
                 f"  reconstructs ▸ plan_check_of_all tables tables_ok {n} oracle\n")
        o.append("theorem site_correct : ∀ (m : ℕ) (φ : ℚ) (x : Fin 3 → ℤ),\n"
                 "    sitePolicy.evalPhase m φ x = φ * x 0 * x 1 * x 2 :=\n"
                 "  evalPhase_correct sitePolicy site_check\n")
        o.append("theorem site_correct_tight : ∀ (m : ℕ) (φ : ℚ) (x : Fin 3 → ℤ),\n"
                 "    (∀ s, Shor.FitsSignedWidth m (x s)) → sitePolicy.evalPhaseTight m φ x = φ * x 0 * x 1 * x 2 :=\n"
                 "  evalPhaseTight_correct sitePolicy site_check\n")
        o.append("/-- On the exact board the site policy takes exactly the oracle's choices (`plan_ladder`). -/")
        o.append(f"theorem site_ladder : sitePolicy.ladderX {n} =\n"
                 f"    ladderOf (fun w => (oracle w).map tables.get) ptpTightWidth PTPTable.k ({n} + 1) {n} :=\n"
                 f"  reconstructs ▸ plan_ladder tables {n} oracle\n")
    else:
        o.append("/-- Validity of the site policy, from `plan_check` (not re-decided). -/")
        o.append("theorem site_check : sitePolicy.check = true :=\n"
                 f"  reconstructs ▸ plan_check_of_all tables .PhaseProduct tables_ok {n} oracle\n")
        o.append("theorem site_correct : ∀ (m : Nat) (φ : ℚ) (xs : Fin sitePolicy.mode.arity → ℤ),\n"
                 "    sitePolicy.evalPhase m φ xs = φ * ∏ s, (xs s : ℚ) :=\n"
                 "  evalPhase_correct_of_check sitePolicy site_check\n")
        o.append("theorem site_correct_tight : ∀ (m : Nat) (φ : ℚ) (xs : Fin sitePolicy.mode.arity → ℤ),\n"
                 "    (∀ s, Fits m (xs s)) → sitePolicy.evalPhaseRegTight m φ xs = φ * ∏ s, (xs s : ℚ) :=\n"
                 "  evalPhaseRegTight_correct sitePolicy site_check\n")
        o.append("/-- At the exact widths the site policy takes exactly the oracle's choices (`plan_ladder`). -/")
        o.append(f"theorem site_ladder : sitePolicy.ladderTight {n} =\n"
                 f"    ladderOf (fun w => (oracle w).map tables.get) PolicyTable.tightWidth PolicyTable.k ({n} + 1) {n} :=\n"
                 f"  reconstructs ▸ plan_ladder tables .PhaseProduct {n} oracle\n")
    o.append(f"end {ns_root}.{mod}\n")
    return mod, "\n".join(o)


# ------------------------------------------------------------------------------------------------ processes
def wait_for_lean_slot(limit: int = 2, poll: float = 15.0):
    while True:
        p = subprocess.run(["pgrep", "-x", "lean"], capture_output=True, text=True)
        if len([x for x in p.stdout.split() if x.strip()]) < limit:
            return
        time.sleep(poll)


def capped(cmd, cwd: Path, cap_gb: float, timeout: float):
    """Run `cmd` under memcap (own session; memcap kills the group on cap/timeout). Returns (rc, out, mem)."""
    wait_for_lean_slot()
    memlog = Path(tempfile.mkstemp(suffix=".mem.json")[1])
    full = [sys.executable, str(HERE / "memcap.py"), "--cap-gb", str(cap_gb), "--timeout", str(timeout),
            "--log", str(memlog), "--"] + cmd
    p = subprocess.Popen(full, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                         start_new_session=True)
    try:
        out, _ = p.communicate(timeout=timeout + 120)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        out, _ = p.communicate()
    try:
        mem = json.loads(memlog.read_text())
    except Exception:
        mem = {}
    memlog.unlink(missing_ok=True)
    return p.returncode, out, mem


def failed_theorems(src: str, out: str, fname: str) -> set:
    """Map each `FILE:LINE:COL: error` to the declaration containing LINE."""
    starts = [(i + 1, m.group(1)) for i, ln in enumerate(src.splitlines())
              for m in [re.match(r"(?:theorem|def) (\w+)", ln)] if m]
    bad = set()
    for m in re.finditer(rf"error: \S*{re.escape(fname)}:(\d+):\d+", out):
        line = int(m.group(1))
        name = [nm for st, nm in starts if st <= line]
        bad.add(name[-1] if name else "?")
    if not bad and "error" in out:
        bad.add("?")
    return bad


def lean_module_path(root: Path, mode: str, mod: str) -> tuple[Path, str]:
    sub = ("TableGeneration/RecursiveCost/PTP/PlanSeeds" if mode == PTP
           else "TableGeneration/RecursiveCost/BandedPolicy/PlanSeeds")
    dotted = sub.replace("/", ".") + "." + mod
    return root / sub / f"{mod}.lean", dotted


def replay(root: Path, dotted: str, cap_gb: float, timeout: float):
    nonce = secrets.token_hex(8)
    rc, out, mem = capped(["lake", "env", "lean", "--run", "scripts/trusted/ReplayPrefix.lean", "--", nonce,
                           dotted, dotted], root, cap_gb, timeout)
    lines = out.splitlines()
    if f"AF_TRUSTED_{nonce}" not in lines:
        return {"verdict": f"no trusted output (rc {rc}, {mem.get('outcome')})", "mem": mem, "tail": out[-1500:]}
    rj = json.loads(lines[lines.index(f"AF_TRUSTED_{nonce}") + 1])
    bad = [t["name"] for t in rj.get("theorems", []) if t.get("sorry") or not set(t.get("axioms", [])) <= ALLOWED_AXIOMS]
    axioms = sorted({a for t in rj.get("theorems", []) for a in t.get("axioms", [])})
    return {"verdict": rj.get("verdict"), "decls": rj.get("decls"), "axioms": axioms, "bad": bad,
            "peak_gb": mem.get("peak_gb"), "seconds": mem.get("seconds"),
            "types": {t["name"].rsplit(".", 1)[-1]: t["type"] for t in rj.get("theorems", [])
                      if t["name"].rsplit(".", 1)[-1] in ("reconstructs", "site_check", "site_correct", "site_correct_tight", "site_ladder", "python_ladder")}}


def run_one(site_path: Path, a, tt) -> dict:
    site_doc = json.loads(site_path.read_text())
    mode = site_doc["mode"]
    pre_path = Path(a.tables) if a.tables else site_path.with_name("site_policy.pre_exact.json")
    pre_doc = json.loads(pre_path.read_text())
    sid = site_path.parent.name if re.fullmatch(r"S[0-9a-f]{12}", site_path.parent.name) else "Site"
    rec = {"id": sid, "mode": mode, "fault": a.fault, "site_policy": str(site_path), "tables_from": str(pre_path)}
    cands = candidates(tt, pre_doc, mode)
    bands = site_bands(tt, site_doc)
    oracle, ladder = read_oracle(bands, cands, a.n)
    rec.update(candidates=[{"k": t.k, "digest": t.digest[:12]} for t in cands],
               site_bands=[[b["threshold"], b["k"]] for b in site_doc["bands"]],
               oracle=oracle, python_ladder=ladder)
    if a.planner_crosscheck and a.fault == "none":
        ok, raw = planner_crosscheck(Path(a.site_engine), pre_doc, mode, a.n, oracle)
        rec["planner_raw_equals_oracle"] = ok
        rec["planner_raw"] = raw
    doc = site_doc
    tag = ""
    if a.fault == "unsorted":
        doc = dict(site_doc, bands=list(reversed(site_doc["bands"])))
        tag = "_unsorted"
        if len(doc["bands"]) < 2:
            rec["verdict"] = "skipped (one band: reversal is the identity)"
            return rec
    elif a.fault == "foreign-index":
        oracle = [(w, len(cands)) for w, _ in oracle]
        tag = "_foreignidx"
    elif a.fault == "foreign-table":
        b0 = dict(site_doc["bands"][0])
        t0 = dict(b0.get("table", b0))
        ops = list(t0["operations"]) + [["negate", 0], ["negate", 0]]   # same function, not a listed table
        if "table" in b0:
            b0["table"] = dict(t0, operations=ops)
        else:
            b0["operations"] = ops
        doc = dict(site_doc, bands=[b0] + list(site_doc["bands"][1:]))
        tag = "_foreigntab"
    root = Path(a.ptp_root) if mode == PTP else ROOT
    mod, src = render(sid, mode, cands, doc, oracle, a.n, a.fault, tag, ladder)
    path, dotted = lean_module_path(root, mode, mod)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(src)
    rec["module"] = dotted
    t0 = time.monotonic()
    rc, out, mem = capped(["lake", "build", dotted], root, a.cap_gb, a.timeout)
    rec["build"] = {"rc": rc, "peak_gb": mem.get("peak_gb"), "seconds": round(time.monotonic() - t0, 1),
                    "outcome": mem.get("outcome")}
    failed = failed_theorems(src, out, path.name) if rc else set()
    rec["build"]["failed_theorems"] = sorted(failed)
    if rc:
        rec["build"]["tail"] = out[-2500:]
    if a.fault == "none":
        rec["verdict"] = "reconstructed" if rc == 0 else "FAILED"
    else:
        # Expected: the module builds, i.e. the kernel proves `reconstruction_fails` (plan ≠ faulty policy) and,
        # when emitted (unsorted, foreign-table), `no_oracle` (no oracle at all produces it).
        rec["verdict"] = "rejected as expected" if rc == 0 else "UNEXPECTED"
    if a.replay and rc == 0:
        rec["replay"] = replay(root, dotted, a.cap_gb, a.timeout)
    return rec


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("site_policy", nargs="*")
    ap.add_argument("--all-seeds")
    ap.add_argument("--ids", help="comma-separated seed ids (with --all-seeds)")
    ap.add_argument("--tables")
    ap.add_argument("--n", type=int, default=2048)
    ap.add_argument("--fault", default="none", choices=["none", "unsorted", "foreign-index", "foreign-table"])
    ap.add_argument("--replay", action="store_true")
    ap.add_argument("--planner-crosscheck", action="store_true")
    ap.add_argument("--site-engine", default=str(DEFAULT_SITE_ENGINE))
    ap.add_argument("--ptp-root", default=str(DEFAULT_PTP_ROOT))
    ap.add_argument("--cap-gb", type=float, default=8)
    ap.add_argument("--timeout", type=float, default=1800)
    ap.add_argument("--out")
    a = ap.parse_args(argv)
    tt = site_tcost(Path(a.site_engine))
    paths = [Path(p) for p in a.site_policy]
    if a.all_seeds:
        paths += sorted(Path(a.all_seeds).glob("S*/site_policy.json"))
    if a.ids:
        keep = set(a.ids.split(","))
        paths = [p for p in paths if p.parent.name in keep]
    results = []
    prev = json.loads(Path(a.out).read_text()) if a.out and Path(a.out).exists() else []
    done = {(r["id"], r["fault"]) for r in prev if r.get("verdict") in ("reconstructed", "rejected as expected")}
    results = [r for r in prev if (r["id"], r["fault"]) in done]
    for p in paths:
        if (p.parent.name, a.fault) in done:
            continue
        try:
            rec = run_one(p, a, tt)
        except (PolicyError, ValueError, KeyError) as e:
            rec = {"id": p.parent.name, "fault": a.fault, "verdict": f"ERROR: {e}"}
        results.append(rec)
        print(json.dumps({k: rec.get(k) for k in ("id", "mode", "verdict", "oracle", "build", "replay",
                                                  "planner_raw_equals_oracle")}, default=str)[:1200], flush=True)
        if a.out:
            Path(a.out).write_text(json.dumps(results, indent=1, default=str))
    bad = [r for r in results if r.get("verdict") not in ("reconstructed", "rejected as expected")
           and not str(r.get("verdict", "")).startswith("skipped")]
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
