#!/usr/bin/env python3
"""Verify one banded policy (PhaseProduct or PhaseTripleProduct) against the
Lean mirror `TableGeneration.RecursiveCost.BandedPolicy`, end to end.

    python3 scripts/check_banded_policy.py POLICY.json --target-width 2048 \
        [--index I] [--workdir DIR | --in-place] [--out RECORD.json] [--full-replay] \
        [--widths scan|exact]

Stages (each timed; the first failure stops the run and is recorded):

  parse    JSON -> two generated Lean modules (data only; no submitter Lean is
           ever compiled, so there is no lexical gate to run):
             .../Instances/Submitted.lean      bands + policy (defs of literals)
             .../Instances/SubmittedCert.lean  accepted / correct / chain_contracts
  stage    copy-on-write clone of this project (keeps .lake), unless
           --in-place
  data     lake build ...Instances.Submitted
  report   lake env lean --run scripts/BandedPolicyReport.lean -- N
           (evaluation tier: ladder, per-band check and child width; used for
           diagnostics, never for acceptance)
  threshold (--widths exact) the threshold rule `chainContractsTight N` from the report;
           rejected here, naming band, width and child width (see below)
  cert     lake build ...Instances.SubmittedCert  (the kernel reduces
           `policy.check = true` and `policy.chainContracts N = true` (scan) or
           `policy.chainContractsTight N = true` (exact) by `decide +kernel`; a false check fails here)
  replay   trusted kernel replay (scripts/trusted/ReplayPrefix.lean), one process
           per module under scripts/memcap.py (default 10 GB, resident+compressed):
           the two instance modules, plus the mirror library with --full-replay;
           every verdict must be `replayed`
  widths   (from the report) a declared ladder -- the policy's `declared_ladder`,
           or the site entry's `ladder` -- must never declare a working width
           below STO's scan (`BandedPolicy.declOK`); otherwise rejected here
  audit    `accepted`, `correct`, `correct_reg` (register-width soundness),
           `capacity`, `chain_contracts` (scan mode; exact mode: the threshold-rule theorems), plus `bands_contract` (F6, emitted when
           the report finds it true; advisory otherwise) and `declared_widths` /
           `declared_correct` (when a ladder is declared): axioms within
           {propext, Classical.choice, Quot.sound}, no sorryAx, and the types of
           `correct` and `correct_reg` equal to the pinned statements

Width rule (`--widths`, default `scan`, which keeps the 2026-10-28 records as they were):

  scan     the declared ladder is checked against STO's scan (`declOK`), as above
  exact    the declared ladder -- or, if none is declared, the exact ladder the report
           evaluates (`ladderTight`) -- is checked against the exact reachable-value width
           `PolicyTable.tightWidth` (Tight.lean; `declOKTight`); a ladder below it is rejected
           at `widths`. The certificate additionally proves `correct_tight` (pinned:
           `evalPhaseRegTight n φ xs = φ * ∏ xs` on operands fitting n), `exact_ladder`
           (`ladderTight N = exactLadder`, by the kernel), `declared_tight_widths` and
           `declared_tight_correct`; the record carries `exact_ladder` for the site.

           THRESHOLD RULE (stage `threshold`, exact mode only; Threshold.lean): every band chosen
           on the exact-width recursion from the target N strictly shrinks the width
           (tightWidth w < w) and is applied only at w >= k (lower limbs w/k nonzero):
           `policy.chainContractsTight N = true`, kernel-checked in the certificate as
           `chain_contracts_tight`. A policy failing it is rejected at `threshold`, naming the band,
           the width and the band's exact child width there. The scan chain (`chainContracts`, STO's
           nextSignedWidth) is NOT required in exact mode: it is recorded as the advisory
           `chain_contracts_scan`. Concrete theorems at N, statement-pinned: `chain_contracts_tight`,
           `thresholds_at_target` (the rule restated over every width the exact recursion reaches),
           `correct_at_target` (`evalPhaseRegTight N φ xs = φ * ∏ xs` on operands fitting N) and
           `exact_ladder_at_target` (`ladderTight N = exactLadder ∧ chainContractsTight N = true`).
           A declared ladder must obey the same rule (`declThresholdOK`, theorem `declared_thresholds`):
           otherwise rejected at `threshold` (HG7 T1).

Exit 0 = accepted, 1 = rejected (record says which stage and why), 2 = usage.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import secrets
import shutil
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
from policy_json_to_lean import PolicyError, ladder_of, render  # noqa: E402

# Stage the project by cloning it. macOS `cp -c` needs APFS; GNU coreutils has
# no `-c` at all and exits 1, which read as a rejected policy rather than a
# broken harness. `--reflink=auto` clones where the filesystem supports it and
# falls back to a full copy where it does not (ext4: 8.8 GB in ~18 s, against a
# report run measured in tens of minutes).
CLONE = ["cp", "-cR"] if sys.platform == "darwin" else ["cp", "-a", "--reflink=auto"]

INST = Path("TableGeneration/RecursiveCost/BandedPolicy/Instances")
DATA_MOD = "TableGeneration.RecursiveCost.BandedPolicy.Instances.Submitted"
CERT_MOD = "TableGeneration.RecursiveCost.BandedPolicy.Instances.SubmittedCert"
NS = "TableGeneration.PolicyMirror.Instances.SubmittedCert"
B = "TableGeneration.RecursiveCost.BandedPolicy"
FULL_LIBRARY = [f"{B}.Interp", f"{B}.Defs", f"{B}.Semantics", f"{B}.Submission", f"{B}.Bridge", f"{B}.Capacity", f"{B}.Tight", f"{B}.Threshold"]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
HEADLINE = ("accepted", "correct", "correct_reg", "capacity")
SCAN_CHAIN = ("chain_contracts",)
# Emitted only when they hold / apply: F6 band contraction, and the declared-ladder width check.
OPTIONAL = ("bands_contract", "declared_widths", "declared_correct")
EXACT = ("correct_tight", "exact_ladder", "declared_tight_widths", "declared_tight_correct",
         "chain_contracts_tight", "thresholds_at_target", "correct_at_target", "exact_ladder_at_target")
PINNED_CORRECT_TIGHT = ("∀ (n : Nat) (φ : Rat) (xs : Fin TableGeneration.PolicyMirror.Instances.Submitted.policy.mode.arity → Int), "
                        "(∀ (s : Fin TableGeneration.PolicyMirror.Instances.Submitted.policy.mode.arity), "
                        "TableGeneration.PolicyMirror.Fits n (xs s)) → "
                        "Eq (TableGeneration.PolicyMirror.Instances.Submitted.policy.evalPhaseRegTight n φ xs) "
                        "(instHMul.hMul φ (Finset.univ.prod fun s => (xs s).cast))")
# The pinned statement of `correct`, as the kernel-replayed environment prints it (pp.all off).
PINNED_CORRECT_REG = ("∀ (n : Nat) (φ : Rat) (xs : Fin TableGeneration.PolicyMirror.Instances.Submitted.policy.mode.arity → Int), "
                      "(∀ (s : Fin TableGeneration.PolicyMirror.Instances.Submitted.policy.mode.arity), "
                      "TableGeneration.PolicyMirror.Fits n (xs s)) → "
                      "Eq (TableGeneration.PolicyMirror.Instances.Submitted.policy.evalPhaseReg n φ xs) "
                      "(instHMul.hMul φ (Finset.univ.prod fun s => (xs s).cast))")
PINNED_CORRECT = ("∀ (n : Nat) (φ : Rat) (xs : Fin TableGeneration.PolicyMirror.Instances.Submitted.policy.mode.arity → Int), "
                  "Eq (TableGeneration.PolicyMirror.Instances.Submitted.policy.evalPhase n φ xs) "
                  "(instHMul.hMul φ (Finset.univ.prod fun s => (xs s).cast))")

SUB = "TableGeneration.PolicyMirror.Instances.Submitted.policy"
CERT_NS = "TableGeneration.PolicyMirror.Instances.SubmittedCert"


def target_pins(N: int) -> dict:
    """Pinned statements of the theorems at the target width N (exact mode)."""
    return {
        "chain_contracts_tight": f"Eq ({SUB}.chainContractsTight {N}) Bool.true",
        "thresholds_at_target": (f"∀ (m : Nat) (T : TableGeneration.PolicyMirror.PolicyTable), {SUB}.ExactReach {N} m → "
                                 f"Eq ({SUB}.choose m) (Option.some T) → "
                                 "And (instLENat.le T.k m) (instLTNat.lt (T.tightWidth m) m)"),
        "correct_at_target": (f"∀ (φ : Rat) (xs : Fin {SUB}.mode.arity → Int), "
                              f"(∀ (s : Fin {SUB}.mode.arity), TableGeneration.PolicyMirror.Fits {N} (xs s)) → "
                              f"Eq ({SUB}.evalPhaseRegTight {N} φ xs) "
                              "(instHMul.hMul φ (Finset.univ.prod fun s => (xs s).cast))"),
        "exact_ladder_at_target": (f"And (Eq ({SUB}.ladderTight {N}) {CERT_NS}.exactLadder) "
                                   f"(Eq ({SUB}.chainContractsTight {N}) Bool.true)"),
    }


def threshold_reason(f: dict, N: int) -> str:
    why = (f"the width is below k, so its lower limbs (width {f['width']} // {f['k']} = 0) are degenerate"
           if f["kind"] == "degenerate_limbs" else
           f"it does not shrink the width (exact child width {f['child_width']} >= {f['width']})")
    return (f"threshold too low: band {f['band']} (threshold {f['threshold']}, k = {f['k']}) is applied at width "
            f"{f['width']} on the exact-width recursion from {N}, where its exact child width is {f['child_width']}: "
            f"{why} (BandedPolicy.chainContractsTight {N} = false)")


def declared_rung_reason(doc: dict, declared) -> str:
    """Diagnostic only (acceptance is the kernel-checked `declThresholdOK`): the first declared rung that
    breaks the rule, with the band chosen there and its exact child width (Python exact_width mirror)."""
    from exact_width import exact_width
    bands = doc.get("bands", [])
    for j, (w, k) in enumerate(declared):
        i = next((i for i, b in enumerate(bands) if b["threshold"] <= w), None)
        if k is None and i is not None:
            b = bands[i]
            return (f"rung {j} declares a leaf at width {w}, but band {i} (threshold {b['threshold']}, k = {b['k']}) is "
                    f"chosen there, with exact child width {exact_width(b['k'], b['operations'], w)}")
        if k is not None and w < k:
            return f"rung {j} applies k = {k} at width {w} < k (degenerate limbs)"
        if k is None and j + 1 < len(declared):
            return f"rung {j} is a leaf at width {w} but rungs follow it"
    return "a declared rung breaks the rule"


class Reject(Exception):
    def __init__(self, stage: str, reason: str, detail: str = ""):
        super().__init__(f"{stage}: {reason}")
        self.stage, self.reason, self.detail = stage, reason, detail


def wait_for_lean_slot(limit: int = 2, poll: float = 15.0, give_up: float = 3600.0):
    """Machine rule: do not start a Lean process while `limit` or more are already running."""
    t0 = time.monotonic()
    while time.monotonic() - t0 < give_up:
        p = subprocess.run(["pgrep", "-x", "lean"], capture_output=True, text=True)
        if len(p.stdout.split()) < limit:
            return
        time.sleep(poll)


def run(cmd, cwd, timeout):
    if "lake" in cmd or "lean" in cmd:
        wait_for_lean_slot()
    t0 = time.monotonic()
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    return p, round(time.monotonic() - t0, 2)


def norm(s: str) -> str:
    return " ".join(s.split())


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("policy_json")
    ap.add_argument("--target-width", type=int, required=True)
    ap.add_argument("--index", type=int)
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--workdir")
    g.add_argument("--in-place", action="store_true")
    ap.add_argument("--out")
    ap.add_argument("--full-replay", action="store_true")
    ap.add_argument("--timeout", type=int, default=3600)
    ap.add_argument("--cap-gb", type=float, default=10.0)
    ap.add_argument("--widths", choices=["scan", "exact"], default="scan",
                    help="width rule the declared ladder is certified against (default scan)")
    a = ap.parse_args(argv)

    raw = Path(a.policy_json).read_bytes()
    rec = {"tool": "check_banded_policy", "started": datetime.now(timezone.utc).isoformat(),
           "policy_sha256": hashlib.sha256(raw).hexdigest(), "target_width": a.target_width,
           "seconds": {}, "verdict": None}
    if a.widths != "scan":
        rec["widths_rule"] = a.widths
    work = None
    try:
        doc = json.loads(raw)
        entry_ladder = None
        if a.index is not None:
            entry = doc["policies"][a.index]
            entry_ladder = entry.get("ladder")
            doc = entry["policy"]
        elif "policy" in doc and "bands" not in doc:
            entry_ladder = doc.get("ladder")
            doc = doc["policy"]
        raw_ladder = doc.get("declared_ladder", entry_ladder)
        rec["mode"] = doc.get("mode")
        rec["bands"] = [{"threshold": b.get("threshold"), "k": b.get("k")} for b in doc.get("bands", [])]
        try:
            declared = ladder_of(raw_ladder)
            data_src = render(doc, "Submitted", None, "data", declared=declared)
        except PolicyError as e:
            raise Reject("parse", str(e))
        rec["declared_ladder"] = declared

        if a.in_place:
            work = ROOT
        else:
            work = Path(a.workdir) if a.workdir else Path(tempfile.mkdtemp(prefix="banded_policy_"))
            if work.exists():
                shutil.rmtree(work)
            t0 = time.monotonic()
            subprocess.run(CLONE + [str(ROOT), str(work)], check=True)
            rec["seconds"]["stage"] = round(time.monotonic() - t0, 2)
        rec["workdir"] = str(work)
        (work / INST).mkdir(parents=True, exist_ok=True)
        (work / INST / "Submitted.lean").write_text(data_src)
        stale = work / INST / "SubmittedCert.lean"
        if stale.exists():
            stale.unlink()

        p, s = run(["lake", "build", DATA_MOD], work, a.timeout)
        rec["seconds"]["data"] = s
        if p.returncode:
            raise Reject("data", "data module does not elaborate", (p.stdout + p.stderr)[-4000:])

        p, s = run(["lake", "env", "lean", "--run", "scripts/BandedPolicyReport.lean", "--", str(a.target_width)],
                   work, a.timeout)
        rec["seconds"]["report"] = s
        if p.returncode:
            raise Reject("report", "report failed", (p.stdout + p.stderr)[-4000:])
        rec["report"] = json.loads(p.stdout.strip().splitlines()[-1])
        if not rec["report"]["check"]:
            bad = [i for i, b in enumerate(rec["report"]["bands"]) if not b["check"]]
            reason = "thresholds not strictly decreasing" if not bad else f"band(s) {bad} fail STO's table contract"
            raise Reject("check", reason)
        exact_ladder = None
        if a.widths == "exact":
            exact_ladder = [(r["width"], r["k"]) for r in rec["report"]["tight_ladder"]]
            rec["exact_ladder"] = rec["report"]["tight_ladder"]
            rec["scan_ladder"] = rec["report"]["ladder"]
            if "chain_contracts_tight" not in rec["report"]:
                raise Reject("report", "report lacks chain_contracts_tight")
            if rec["report"]["chain_contracts_tight"] is not True:
                f = rec["report"].get("threshold_failure")
                if not f:
                    raise Reject("threshold", f"BandedPolicy.chainContractsTight {a.target_width} = false",
                                 json.dumps({"exact": rec["report"]["tight_ladder"]}))
                raise Reject("threshold", threshold_reason(f, a.target_width),
                             json.dumps({"failure": f, "exact": rec["report"]["tight_ladder"]}))
            if declared is not None and rec["report"].get("declared_threshold_ok") is not True:
                raise Reject("threshold", "threshold too low on the declared ladder: " + declared_rung_reason(doc, declared) +
                             " (BandedPolicy.declThresholdOK = false)",
                             json.dumps({"declared": declared, "exact": rec["report"]["tight_ladder"]}))
            if rec["report"].get("declared_tight_ok") is False:
                raise Reject("widths", "declared ladder fails BandedPolicy.declOKTight: a declared working width is below "
                             "the exact reachable-value width tightWidth (some reachable register value of some operand "
                             "fitting the width would overflow), a step does not shrink, or a k tag disagrees with the "
                             "exact-width recursion",
                             json.dumps({"declared": declared, "exact": rec["report"]["tight_ladder"]}))
        elif rec["report"].get("declared_ok") is False:
            raise Reject("widths", "declared ladder fails BandedPolicy.declOK: a declared working width is below STO's Lean scan "
                         "nextSignedWidth (a conservative bound), a step does not shrink, or a k tag disagrees "
                         "with the policy; the register-width theorem does not apply",
                         json.dumps({"declared": declared, "scanned": rec["report"]["ladder"]}))
        if a.widths == "scan" and rec["report"].get("chain_contracts") is False:
            raise Reject("cert", f"chain does not contract from the target width (scan: BandedPolicy.chainContracts "
                         f"{a.target_width} = false)", json.dumps({"scanned": rec["report"]["ladder"]}))
        rec["advisory"] = {"bands_contract": rec["report"].get("bands_contract")}
        if a.widths == "exact":
            # Not required in exact mode (the threshold rule above replaces it); recorded only.
            rec["advisory"]["chain_contracts_scan"] = rec["report"].get("chain_contracts")
        try:
            cert_src = render(doc, "SubmittedCert", a.target_width, "cert", "Submitted", declared=declared,
                              bands_contract=bool(rec["report"].get("bands_contract")),
                              widths=a.widths, exact_ladder=exact_ladder)
        except PolicyError as e:
            raise Reject("parse", str(e))
        (work / INST / "SubmittedCert.lean").write_text(cert_src)
        rec["lean_sha256"] = {"Submitted.lean": hashlib.sha256(data_src.encode()).hexdigest(),
                              "SubmittedCert.lean": hashlib.sha256(cert_src.encode()).hexdigest()}

        p, s = run(["lake", "build", CERT_MOD], work, a.timeout)
        rec["seconds"]["cert"] = s
        if p.returncode:
            out = p.stdout + p.stderr
            if "chain_contracts_tight" in out:
                raise Reject("threshold", f"BandedPolicy.chainContractsTight {a.target_width} = false (kernel)", out[-4000:])
            reason = "chain does not contract from the target width" if "chain_contracts" in out else "certificate does not build"
            raise Reject("cert", reason, out[-4000:])

        # One process per module, each under a hard memory cap: a replay process loads the
        # module's import closure (Mathlib) twice, ~6 GB, and environments are not freed
        # between modules, so replaying several modules in one process grows without bound.
        thm_list, rec["replay"] = [], {"modules": [], "prefix": "per-module"}
        mods = [DATA_MOD, CERT_MOD] + (FULL_LIBRARY if a.full_replay else [])
        for mod in mods:
            nonce = secrets.token_hex(8)
            memlog = Path(tempfile.mkstemp(suffix=".mem.json")[1])
            p, s = run([sys.executable, str(ROOT / "scripts" / "memcap.py"), "--cap-gb", str(a.cap_gb),
                        "--timeout", str(a.timeout), "--log", str(memlog), "--",
                        "lake", "env", "lean", "--run", "scripts/trusted/ReplayPrefix.lean", "--", nonce, mod, mod],
                       work, a.timeout + 60)
            mem = json.loads(memlog.read_text()) if memlog.stat().st_size else {}
            rec["seconds"]["replay:" + mod.rsplit(".", 1)[-1]] = s
            lines = p.stdout.splitlines()
            if f"AF_TRUSTED_{nonce}" not in lines:
                raise Reject("replay", f"{mod}: no trusted output ({mem.get('outcome')})", (p.stdout + p.stderr)[-4000:])
            rj = json.loads(lines[lines.index(f"AF_TRUSTED_{nonce}") + 1])
            rec["replay"]["modules"].append({"module": mod, "verdict": rj["verdict"], "decls": rj.get("decls"),
                                             "peak_gb": mem.get("peak_gb"), "seconds": mem.get("seconds")})
            if rj["verdict"] != "replayed":
                raise Reject("replay", f"{mod}: {rj['verdict']}")
            thm_list += rj["theorems"]
        rj = {"theorems": thm_list}

        thms = {t["name"]: t for t in rj["theorems"]}
        audit = {}
        expected = list(HEADLINE) + (list(SCAN_CHAIN) if a.widths == "scan" else []) + (["bands_contract"] if rec["advisory"]["bands_contract"] else []) + \
            (["declared_widths", "declared_correct"] if declared is not None and a.widths == "scan" else []) + \
            (list(EXACT) if a.widths == "exact" else []) + \
            (["declared_thresholds"] if declared is not None and a.widths == "exact" else [])
        for h in expected:
            t = thms.get(f"{NS}.{h}")
            if t is None:
                raise Reject("audit", f"{h} missing from the replayed environment")
            if t["sorry"] or not set(t["axioms"]) <= ALLOWED_AXIOMS:
                raise Reject("audit", f"{h}: axioms {t['axioms']}")
            audit[h] = {"axioms": sorted(t["axioms"]), "type": t["type"]}
        if norm(audit["correct"]["type"]) != norm(PINNED_CORRECT):
            raise Reject("audit", "statement pin mismatch for `correct`", audit["correct"]["type"])
        if norm(audit["correct_reg"]["type"]) != norm(PINNED_CORRECT_REG):
            raise Reject("audit", "statement pin mismatch for `correct_reg`", audit["correct_reg"]["type"])
        if a.widths == "exact" and norm(audit["correct_tight"]["type"]) != norm(PINNED_CORRECT_TIGHT):
            raise Reject("audit", "statement pin mismatch for `correct_tight`", audit["correct_tight"]["type"])
        if a.widths == "exact":
            pins = target_pins(a.target_width)
            if declared is not None:
                pins["declared_thresholds"] = (f"Eq ({SUB}.declThresholdOK "
                                               "TableGeneration.PolicyMirror.Instances.Submitted.declared) Bool.true")
            for h, pin in pins.items():
                if norm(audit[h]["type"]) != norm(pin):
                    raise Reject("audit", f"statement pin mismatch for `{h}`", audit[h]["type"])
        rec["audit"] = audit
        rec["verdict"] = "accepted"
    except Reject as e:
        rec["verdict"] = "rejected"
        rec["rejection"] = {"stage": e.stage, "reason": e.reason, "detail": e.detail}
    except subprocess.TimeoutExpired as e:
        rec["verdict"] = "rejected"
        rec["rejection"] = {"stage": "timeout", "reason": str(e)}
    rec["finished"] = datetime.now(timezone.utc).isoformat()
    out = json.dumps(rec, indent=1, ensure_ascii=False)
    if a.out:
        Path(a.out).write_text(out)
    print(out)
    return 0 if rec["verdict"] == "accepted" else 1


if __name__ == "__main__":
    sys.exit(main())
