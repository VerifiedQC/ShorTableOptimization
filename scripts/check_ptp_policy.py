#!/usr/bin/env python3
"""Verify one PhaseTripleProduct banded policy against the PTP suite
`TableGeneration.RecursiveCost.PTP`, end to end.

    python3 scripts/check_ptp_policy.py POLICY.json --target-width 2048 [--out RECORD.json]
        [--full-replay] [--cap-gb 8] [--timeout 3600] [--save-lean DIR]

Stages (each timed; the first failure stops the run and is recorded):

  parse   JSON -> two generated Lean modules (literals + one-line proofs only):
            TableGeneration/RecursiveCost/PTP/Instances/PTPSubmitted.lean
            TableGeneration/RecursiveCost/PTP/Instances/PTPSubmittedCert.lean
  data    lake build ...PTPSubmitted
  report  lake env lean --run scripts/PTPPolicyReport.lean -- N
          (evaluation tier: PTP ladder, PP-scan ladder for comparison, per-band
          contract and child widths, census and qubits; diagnostics only)
  check   from the report: PTP check (rejection names the failing band)
  width   declared `child_width` fields (if any) must equal the PTP-derived ones
  threshold (--widths exact) THRESHOLD RULE (PTP/Threshold.lean): every band chosen on the
          exact-width recursion from the target N strictly shrinks the width
          (ptpTightWidth T w < w) and is applied only at w >= k: `chainContractsTight N`; a policy
          failing it is rejected here, naming the band, the width and its exact child width. The
          PTP scan chain (`chainContracts`) is not required in exact mode (advisory
          `chain_contracts_scan`); in scan mode it is required, as before (stage `cert`).
  cert    lake build ...PTPSubmittedCert (kernel: `decide +kernel` on check,
          chainContracts N (scan) / chainContractsTight N (exact), declared child widths;
          generic theorems applied; exact mode also the concrete theorems at N:
          `chain_contracts_tight`, `thresholds_at_target`, `correct_at_target`,
          `exact_ladder_at_target`, `gate_recursion_exact_at_target`, all statement-pinned)
  replay  trusted kernel replay (scripts/trusted/ReplayPrefix.lean), one module per
          process under scripts/memcap.py (default 8 GB); with --full-replay also
          every PTP library module
  audit   headline theorems: axioms within {propext, Classical.choice, Quot.sound},
          no sorryAx, statements of `correct` and `correct_wrapped` equal the pins

Runs in place (this project). Before every lean/lake process it waits while two
or more `lean` processes are running. Exit 0 accepted, 1 rejected, 2 usage.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import secrets
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
from policy_json_to_lean import PolicyError  # noqa: E402
from ptp_policy_json_to_lean import render  # noqa: E402
import ptp_exact_width  # noqa: E402

INST = Path("TableGeneration/RecursiveCost/PTP/Instances")
DATA_MOD = "TableGeneration.RecursiveCost.PTP.Instances.PTPSubmitted"
CERT_MOD = "TableGeneration.RecursiveCost.PTP.Instances.PTPSubmittedCert"
NS = "TableGeneration.PTP.Instances.PTPSubmittedCert"
P = "TableGeneration.RecursiveCost.PTP"
LIBRARY = [f"{P}.Contract", f"{P}.Width", f"{P}.Semantics", f"{P}.Leaf", f"{P}.LeafSandwich", f"{P}.Node", f"{P}.Census", f"{P}.Exact", f"{P}.Recursion", f"{P}.Build", f"{P}.CensusFull", f"{P}.RecursionWitness",
           f"{P}.Instances.FaultChallenge", f"{P}.ExactNode", f"{P}.ExactRecursion", f"{P}.ExactBuild",
           f"{P}.Instances.ExactFault", f"{P}.Threshold"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
HEADLINE = ("accepted", "correct", "correct_wrapped", "width_sound", "gate_node", "gate_recursion")
HEADLINE_SCAN = ("chain_contracts",)
HEADLINE_EXACT = ("chain_contracts_exact", "ladder_exact", "correct_exact", "exact_minimal", "exact_le_scan",
                  "exact_floor", "gate_node_exact", "gate_recursion_exact",
                  "chain_contracts_tight", "thresholds_at_target", "correct_at_target", "exact_ladder_at_target",
                  "gate_recursion_exact_at_target")
D = "TableGeneration.PTP.Instances.PTPSubmitted.policy"
PINS = {
    # pinned from runs_ptp/sandwich/round2/S1c115b37fd2c.record.json (2026-10-28); D-independent
    "gate_recursion": "∀ (qs : Shor.QSemantics) [inst : Shor.RegEncoding qs.Basis] [inst_1 : Shor.LowerGateClass qs] (n : Nat) (X : Fin 3 → Shor.ExtReg) (base : Nat),\n  TableGeneration.PTP.Good X n base →\n    Exists fun W =>\n      Exists fun G =>\n        And (TableGeneration.PTP.PolicyImpl TableGeneration.PTP.Instances.PTPSubmitted.policy X n W G)\n          (And (∀ (q : Nat), List.instMembership.mem W q → And (instLENat.le base q) (instLTNat.lt q (instHAdd.hAdd base (TableGeneration.PTP.ptpWorkspace TableGeneration.PTP.Instances.PTPSubmitted.policy n))))\n            (And (∀ (φ : Shor.Angle) (b : qs.Basis), (∀ (s : Fin 3), Shor.FitsSignedWidth n (Shor.extToInt (X s) b)) → (∀ (q : Nat), List.instMembership.mem W q → Eq (inst.bit q b) Bool.false) → Eq (inst_1.evalL (G φ) (qs.ket b)) (instHSMul.hSMul (Complex.exp (instHMul.hMul (instHMul.hMul (Complex.ofReal φ.toReal) Complex.I) (instHMul.hMul (instHMul.hMul (Shor.extToInt (X 0) b).cast (Shor.extToInt (X 1) b).cast) (Shor.extToInt (X 2) b).cast))) (qs.ket b)))\n              (∀ (φ : Shor.Angle),\n                have R := Shor.LowGate.resources Shor.shorGateResourceModel (G φ);\n                And (Eq R.rz (TableGeneration.PTP.ptpResources TableGeneration.PTP.Instances.PTPSubmitted.policy n).rz) (And (Eq R.toffoli (TableGeneration.PTP.ptpResources TableGeneration.PTP.Instances.PTPSubmitted.policy n).toffoli) (And (Eq R.x (TableGeneration.PTP.ptpResources TableGeneration.PTP.Instances.PTPSubmitted.policy n).x) (And (Eq R.h (TableGeneration.PTP.ptpResources TableGeneration.PTP.Instances.PTPSubmitted.policy n).h) (And (Eq R.cnot (TableGeneration.PTP.ptpCnotFull TableGeneration.PTP.Instances.PTPSubmitted.policy n)) (And (Eq (TableGeneration.PTP.adjToffCount (G φ)) (TableGeneration.PTP.ptpAndDag TableGeneration.PTP.Instances.PTPSubmitted.policy n)) (instLENat.le (G φ).usedQubits.card (instHAdd.hAdd (instHMul.hMul 3 n) (TableGeneration.PTP.ptpWorkspace TableGeneration.PTP.Instances.PTPSubmitted.policy n)))))))))))",
    "gate_node": "∀ (b : TableGeneration.PTP.PTPBand), List.instMembership.mem TableGeneration.PTP.Instances.PTPSubmitted.policy.bands b → ∀ (qs : Shor.QSemantics) [inst : Shor.RegEncoding qs.Basis] [inst_1 : Shor.LowerGateClass qs] (n : Nat) (x : Fin 3 → Int), (∀ (s : Fin 3), Shor.FitsSignedWidth n (x s)) → ∀ (Lay : TableGeneration.PTP.NodeLayout b.table.k), instLENat.le (TableGeneration.PTP.childWidth n b.table.ops) Lay.width → ∀ (φ : Shor.Angle) (ta ua : Nat), TableGeneration.PTP.NodeAnc Lay ta ua → ∀ (bas : qs.Basis), TableGeneration.PTP.AncClean ta ua bas → (∀ (s : Fin 3) (i : Fin b.table.k), Eq (Shor.extToInt (Lay.slot s i) bas) (TableGeneration.PTP.limbsAt b.table.k (TableGeneration.PTP.limbWidth n b.table.k) (x s) i)) → Eq (inst_1.evalL (TableGeneration.PTP.ptpNode b.table Lay n φ ta ua) (qs.ket bas)) (instHSMul.hSMul (Complex.exp (instHMul.hMul (instHMul.hMul (Complex.ofReal φ.toReal) Complex.I) (instHMul.hMul (instHMul.hMul (x 0).cast (x 1).cast) (x 2).cast))) (qs.ket bas))",
    # O5 (2026-10-29): derived from the two pins above by the exact-board renaming; confirmed by runs_ptp/exactgate/S1c115b37fd2c.record.json (audit types matched)
    "gate_recursion_exact": None,
    "gate_node_exact": None,
    "correct": f"∀ (n : Nat) (φ : Rat) (x : Fin 3 → Int), Eq ({D}.evalPhase n φ x) "
               "(instHMul.hMul (instHMul.hMul (instHMul.hMul φ (x 0).cast) (x 1).cast) (x 2).cast)",
    "correct_wrapped": f"∀ (n : Nat) (φ : Rat) (x : Fin 3 → Int), (∀ (s : Fin 3), Shor.FitsSignedWidth n (x s)) → "
                       f"Eq ({D}.evalPhaseW n φ x) "
                       "(instHMul.hMul (instHMul.hMul (instHMul.hMul φ (x 0).cast) (x 1).cast) (x 2).cast)",
    "correct_exact": f"∀ (n : Nat) (φ : Rat) (x : Fin 3 → Int), (∀ (s : Fin 3), Shor.FitsSignedWidth n (x s)) → "
                     f"Eq ({D}.evalPhaseTight n φ x) "
                     "(instHMul.hMul (instHMul.hMul (instHMul.hMul φ (x 0).cast) (x 1).cast) (x 2).cast)",
}

PINS["gate_recursion_exact"] = (PINS["gate_recursion"]
    .replace("TableGeneration.PTP.PolicyImpl ", "TableGeneration.PTP.PolicyImplX ")
    .replace("TableGeneration.PTP.ptpWorkspace ", "TableGeneration.PTP.ptpWorkspaceX ")
    .replace("TableGeneration.PTP.ptpResources ", "TableGeneration.PTP.ptpResourcesX ")
    .replace("TableGeneration.PTP.ptpCnotFull ", "TableGeneration.PTP.ptpCnotFullX ")
    .replace("TableGeneration.PTP.ptpAndDag ", "TableGeneration.PTP.ptpAndDagX "))
PINS["gate_node_exact"] = (PINS["gate_node"]
    .replace("instLENat.le (TableGeneration.PTP.childWidth n b.table.ops) Lay.width",
             "instLENat.le (TableGeneration.PTP.ptpTightWidth b.table n) Lay.width"))
assert PINS["gate_recursion_exact"] != PINS["gate_recursion"] and PINS["gate_node_exact"] != PINS["gate_node"]
CERT = "TableGeneration.PTP.Instances.PTPSubmittedCert"


def target_pins(N: int) -> dict:
    """Pinned statements at the target width N (exact mode). `gate_recursion_exact_at_target` is
    `gate_recursion_exact` with the binder `(n : Nat)` removed and `n` := N."""
    import re
    g = PINS["gate_recursion_exact"].replace("(n : Nat) ", "", 1)
    g = re.sub(r"(?<![\w.'])n(?![\w.'])", str(N), g)
    return {
        "chain_contracts_tight": f"Eq ({D}.chainContractsTight {N}) Bool.true",
        "thresholds_at_target": (f"∀ (m : Nat) (T : TableGeneration.PTP.PTPTable), {D}.ExactReach {N} m → "
                                 f"Eq ({D}.choose m) (Option.some T) → "
                                 "And (instLENat.le T.k m) (instLTNat.lt (TableGeneration.PTP.ptpTightWidth T m) m)"),
        "correct_at_target": (f"∀ (φ : Rat) (x : Fin 3 → Int), (∀ (s : Fin 3), Shor.FitsSignedWidth {N} (x s)) → "
                              f"Eq ({D}.evalPhaseTight {N} φ x) "
                              "(instHMul.hMul (instHMul.hMul (instHMul.hMul φ (x 0).cast) (x 1).cast) (x 2).cast)"),
        "exact_ladder_at_target": (f"And (Eq ({D}.ladderX {N}) {CERT}.exactLadder) "
                                   f"(Eq ({D}.chainContractsTight {N}) Bool.true)"),
        "gate_recursion_exact_at_target": g,
    }


def threshold_reason(f: dict, N: int) -> str:
    why = (f"the width is below k, so its lower limbs (width {f['width']} // {f['k']} = 0) are degenerate"
           if f["kind"] == "degenerate_limbs" else
           f"it does not shrink the width (exact child width {f['child_width']} >= {f['width']})")
    return (f"threshold too low: band {f['band']} (threshold {f['threshold']}, k = {f['k']}) is applied at width "
            f"{f['width']} on the exact-width recursion from {N}, where its exact child width is {f['child_width']}: "
            f"{why} (PTPPolicy.chainContractsTight {N} = false)")


class Reject(Exception):
    def __init__(self, stage, reason, detail=""):
        super().__init__(f"{stage}: {reason}")
        self.stage, self.reason, self.detail = stage, reason, detail


def wait_lean_slot():
    while True:
        out = subprocess.run(["pgrep", "-x", "lean"], capture_output=True, text=True).stdout
        if len(out.split()) < 2:
            return
        time.sleep(5)


def run(cmd, timeout):
    wait_lean_slot()
    t0 = time.monotonic()
    p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
    return p, round(time.monotonic() - t0, 2)


def capped(cmd, cap, timeout, log):
    return run([sys.executable, str(ROOT / "scripts" / "memcap.py"), "--cap-gb", str(cap), "--timeout",
                str(timeout), "--log", str(log), "--", *cmd], timeout + 60)


def norm(s):
    return " ".join(s.split())


def replay(mod, a, rec):
    nonce = secrets.token_hex(8)
    log = Path(tempfile.mkstemp(suffix=".mem.json")[1])
    p, s = capped(["lake", "env", "lean", "--run", "scripts/trusted/ReplayPrefix.lean", "--", nonce, mod, mod],
                  a.cap_gb, a.timeout, log)
    mem = json.loads(log.read_text()) if log.stat().st_size else {}
    lines = p.stdout.splitlines()
    if f"AF_TRUSTED_{nonce}" not in lines:
        raise Reject("replay", f"{mod}: no trusted output ({mem.get('outcome')})", (p.stdout + p.stderr)[-3000:])
    rj = json.loads(lines[lines.index(f"AF_TRUSTED_{nonce}") + 1])
    axioms = sorted({ax for t in rj["theorems"] for ax in t["axioms"]})
    rec["replay"].append({"module": mod, "verdict": rj["verdict"], "decls": rj.get("decls"),
                          "theorems": len(rj["theorems"]), "axiom_union": axioms,
                          "sorry": any(t["sorry"] for t in rj["theorems"]),
                          "peak_gb": mem.get("peak_gb"), "seconds": mem.get("seconds")})
    if rj["verdict"] != "replayed":
        raise Reject("replay", f"{mod}: {rj['verdict']}")
    return rj["theorems"]


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("policy_json")
    ap.add_argument("--target-width", type=int, required=True)
    ap.add_argument("--out")
    ap.add_argument("--full-replay", action="store_true")
    ap.add_argument("--timeout", type=int, default=3600)
    ap.add_argument("--cap-gb", type=float, default=8.0)
    ap.add_argument("--save-lean")
    ap.add_argument("--widths", default="scan", choices=["scan", "exact"],
                    help="exact: the PTP board's exact widths (ptpTightWidth); scan: the PTP scan (childWidth)")
    a = ap.parse_args(argv)
    raw = Path(a.policy_json).read_bytes()
    rec = {"tool": "check_ptp_policy", "policy": str(a.policy_json), "started": datetime.now(timezone.utc).isoformat(),
           "policy_sha256": hashlib.sha256(raw).hexdigest(), "target_width": a.target_width, "widths": a.widths,
           "seconds": {}, "replay": [], "verdict": None}
    try:
        doc = json.loads(raw)
        if "policy" in doc and "bands" not in doc:
            doc = doc["policy"]
        rec["name"], rec["mode"] = doc.get("name"), doc.get("mode")
        rec["bands"] = [{"threshold": b.get("threshold"), "k": b.get("k")} for b in doc.get("bands", [])]
        try:
            data_src = render(doc, "PTPSubmitted", None, "data")
            render(doc, "PTPSubmittedCert", a.target_width, "cert", "PTPSubmitted", a.widths, [])
        except PolicyError as e:
            raise Reject("parse", str(e))
        (ROOT / INST / "PTPSubmitted.lean").write_text(data_src)

        p, s = capped(["lake", "build", DATA_MOD], a.cap_gb, a.timeout, Path(tempfile.mkstemp()[1]))
        rec["seconds"]["data"] = s
        if p.returncode:
            raise Reject("data", "data module does not elaborate", (p.stdout + p.stderr)[-3000:])

        p, s = capped(["lake", "env", "lean", "--run", "scripts/PTPPolicyReport.lean", "--", str(a.target_width)],
                      a.cap_gb, a.timeout, Path(tempfile.mkstemp()[1]))
        rec["seconds"]["report"] = s
        if p.returncode:
            raise Reject("report", "report failed", (p.stdout + p.stderr)[-3000:])
        rep = json.loads(p.stdout.strip().splitlines()[-1])
        rec["report"] = rep
        rec["report_tiers"] = {
            "ladder, child widths, check": "evaluation tier; check and chain re-proved by the kernel in `cert`",
            "census":
                "PROVED at every depth (cert `gate_recursion`, Lean ptp_gate_full): rz/toffoli/x/h of the gate-level "
                "recursion = ptpResources (sandwich leaf, 1 Rz per cell); census.cnot EXCLUDES the split's "
                "sign-extension fan-out — the circuit's CNOT is `cnot_with_extension` (ptpCnotFull); "
                "`toffoli_uncompute` = And† (ptpAndDag), compute Toffoli (And) = toffoli - toffoli_uncompute",
            "reserve_need_per_operand, clean_ancilla_peak, qubits":
                "FORMULA (ForShor reserveNeed shape, private workspace per child); no theorem. The constructed "
                "circuit of `gate_recursion` has a different, proved bound: qubits <= 3n + ptpWorkspace (per level "
                "3k·C' reserve, children share one pool, 2 leaf ancillas)",
            "census_ccphase_leaf, qubits_ccphase_leaf":
                "FORMULA, documented alternative: the same with the CCPhase leaf (5 Rz per cell; "
                "ptpNodeCCPhase_resources, ptpResourcesCCPhase_depth_one)",
            "ladder_pp_scan": "comparison only (PP's nextSignedWidth), not used",
            "census_exact, cnot_with_extension_exact, toffoli_uncompute_exact, workspace_exact, qubits_bound_exact":
                "FORMULA PROVED at every depth on the EXACT ladder (cert `gate_recursion_exact`, Lean ptp_gate_full_exact, "
                "--widths exact only): the gate-level recursion with every node's children at ptpTightWidth exists, is "
                "correct, and has rz/toffoli/x/h = ptpResourcesX, CNOT = ptpCnotFullX (extension fan-out included; "
                "census_exact.cnot excludes it), And† = ptpAndDagX, qubits <= 3n + ptpWorkspaceX; the NUMBERS at the target "
                "width are compiled evaluation (lean --run) of those formulas, not kernel-reduced; ptpResourcesD recurses "
                "exactly as ladderX (choose, ptpTightWidth < n), agreement by construction, not a theorem (HG7 F1/F2)",
            "qubits_bound_scan": "PROVED bound for the scan-ladder circuit of `gate_recursion` (3n + ptpWorkspace)"}
        if not rep["check"]:
            bad = [i for i, b in enumerate(rep["bands"]) if not b["contract"]]
            raise Reject("check", "thresholds not strictly decreasing" if not bad
                         else f"band(s) {bad} fail the PTP table contract")
        wkey = "exact_width_at_threshold" if a.widths == "exact" else "ptp_child_width_at_threshold"
        for i, b in enumerate(doc["bands"]):
            if "child_width" in b and b["child_width"] != rep["bands"][i][wkey]:
                raise Reject("width", f"band {i}: declared child_width {b['child_width']} != {a.widths} PTP width "
                             f"{rep['bands'][i][wkey]} at threshold {b['threshold']}")
        if a.widths == "exact":
            py = [[w, kk] for w, kk in ptp_exact_width.exact_ladder(doc, a.target_width)]
            lean = [[r["width"], r["k"]] for r in rep["ladder_exact"]]
            rec["python_exact_ladder"] = py
            if py != lean:
                raise Reject("crosscheck", "Python exact ladder differs from the Lean report", f"{py} vs {lean}")
            if "chain_contracts_tight" not in rep:
                raise Reject("report", "report lacks chain_contracts_tight")
            if rep["chain_contracts_tight"] is not True:
                f = rep.get("threshold_failure")
                raise Reject("threshold", threshold_reason(f, a.target_width) if f else
                             f"PTPPolicy.chainContractsTight {a.target_width} = false",
                             json.dumps({"failure": f, "exact": rep["ladder_exact"]}))
            # Not required in exact mode (the threshold rule replaces it); recorded only.
            rec["advisory"] = {"chain_contracts_scan": rep.get("chain_contracts")}
            if rep.get("chain_contracts") is False:
                rec["advisory"]["scan_tier_note"] = (
                    "the scan chain does not contract from the target: the scan-tier theorems (gate_recursion, "
                    "correct_wrapped) and the scan numbers (census, cnot_with_extension, qubits_bound_scan) remain true "
                    "but describe a recursion that falls back to the leaf where a chosen band does not shrink; the "
                    "exact-width theorems and *_exact numbers are the ones the threshold rule covers")
        elif not rep["chain_contracts"]:
            raise Reject("cert", "chain does not contract from the target width")
        cert_src = render(doc, "PTPSubmittedCert", a.target_width, "cert", "PTPSubmitted", a.widths,
                          [(r["width"], r["k"]) for r in rep["ladder_exact"]])
        (ROOT / INST / "PTPSubmittedCert.lean").write_text(cert_src)
        rec["lean_sha256"] = {"PTPSubmitted.lean": hashlib.sha256(data_src.encode()).hexdigest(),
                              "PTPSubmittedCert.lean": hashlib.sha256(cert_src.encode()).hexdigest()}
        if a.save_lean:
            d = Path(a.save_lean); d.mkdir(parents=True, exist_ok=True)
            (d / "PTPSubmitted.lean").write_text(data_src); (d / "PTPSubmittedCert.lean").write_text(cert_src)

        p, s = capped(["lake", "build", CERT_MOD], a.cap_gb, a.timeout, Path(tempfile.mkstemp()[1]))
        rec["seconds"]["cert"] = s
        if p.returncode:
            raise Reject("cert", "certificate does not build", (p.stdout + p.stderr)[-3000:])

        thms = []
        for mod in [DATA_MOD, CERT_MOD] + (LIBRARY if a.full_replay else []):
            t0 = time.monotonic()
            thms += replay(mod, a, rec)
            rec["seconds"]["replay:" + mod.rsplit(".", 1)[-1]] = round(time.monotonic() - t0, 2)
        by = {t["name"]: t for t in thms}
        audit = {}
        for h in HEADLINE + (HEADLINE_EXACT if a.widths == "exact" else HEADLINE_SCAN):
            t = by.get(f"{NS}.{h}")
            if t is None:
                raise Reject("audit", f"{h} missing from the replayed environment")
            if t["sorry"] or not set(t["axioms"]) <= ALLOWED:
                raise Reject("audit", f"{h}: axioms {t['axioms']}")
            audit[h] = {"axioms": sorted(t["axioms"]), "type": t["type"]}
        pins = dict(PINS, **(target_pins(a.target_width) if a.widths == "exact" else {}))
        for h, pin in pins.items():
            if h not in audit:
                continue
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
