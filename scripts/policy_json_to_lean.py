#!/usr/bin/env python3
"""Render a banded-policy JSON document as a Lean instance file for
`TableGeneration.RecursiveCost.BandedPolicy`.

Input (the sto_site `reference_policies.json` band shape, one policy):

    {"name": ..., "mode": "PhaseProduct" | "PhaseTripleProduct",
     "bands": [{"threshold": 2048, "k": 6,
                "point_order": ["0", "inf", "1", "-1/2", ...],
                "operations": [["addScaled", dst, src, sign, shift],
                               ["shiftL", reg, n], ["shiftR", reg, n],
                               ["negate", reg], ["phaseProduct", reg]]}, ...]}

`point_order` is the order the program's phaseProduct checkpoints consume the
points (STO `generatePointsInOrder`), which is what the table check needs.

Usage:
    policy_json_to_lean.py POLICY.json --module NAME [--target-width N] [--index I] > NAME.lean
    # or split, so a harness can evaluate the data before proving anything:
    policy_json_to_lean.py POLICY.json --module D --part data > D.lean
    policy_json_to_lean.py POLICY.json --module C --part cert --data-module D --target-width N > C.lean

`--index` selects one policy from a file of the form {"policies": [{"policy": ...}, ...]}.
The emitted file contains only data (`def`s of literals) and one theorem whose
proof is `by decide +kernel`; it adds no axioms of its own.
"""
from __future__ import annotations

import argparse
import json
import re
import sys

MODES = {"PhaseProduct": ".PhaseProduct", "PhaseTripleProduct": ".PhaseTripleProduct"}
IDENT = re.compile(r"^[A-Z][A-Za-z0-9_]*$")


class PolicyError(ValueError):
    pass


def lean_comment(s: str, limit: int) -> str:
    """Quote an untrusted string for use inside a `/-! ... -/` Lean comment.

    json.dumps escapes quotes, backslashes and newlines but not the Lean
    comment delimiters, so a name containing `-/` would close the comment and
    make everything after it live code.
    """
    return json.dumps(s)[:limit].replace("-/", "- /").replace("/-", "/ -")


def point_lean(s: str) -> str:
    s = s.strip()
    if s == "inf":
        return "Point.frac 0"
    m = re.fullmatch(r"(-?)1/(\d+)", s)
    if m:
        v = int(m.group(2))
        if v == 0:
            raise PolicyError(f"bad point {s!r}")
        return f"Point.frac ({'-' if m.group(1) else ''}{v})"
    if re.fullmatch(r"-?\d+", s):
        return f"Point.int ({int(s)})"
    raise PolicyError(f"bad point {s!r}")


def fin(i, k: int) -> str:
    if not isinstance(i, int) or isinstance(i, bool) or not 0 <= i < k:
        raise PolicyError(f"register {i!r} out of range for k={k}")
    return f"⟨{i}, by decide⟩"


def nat(n) -> int:
    if not isinstance(n, int) or isinstance(n, bool) or n < 0:
        raise PolicyError(f"bad amount {n!r}")
    return n


def op_lean(op, k: int) -> str:
    if not isinstance(op, list) or not op:
        raise PolicyError(f"bad operation {op!r}")
    name, args = op[0], op[1:]
    if name == "addScaled" and len(args) == 4:
        dst, src, sign, shift = args
        if sign not in (1, -1):
            raise PolicyError(f"bad sign in {op!r}")
        neg = "true" if sign == -1 else "false"
        return f".addScaled {fin(dst, k)} {fin(src, k)} {neg} {nat(shift)}"
    if name in ("shiftL", "shiftR") and len(args) == 2:
        return f".{name} {fin(args[0], k)} {nat(args[1])}"
    if name in ("negate", "phaseProduct") and len(args) == 1:
        return f".{name} {fin(args[0], k)}"
    raise PolicyError(f"bad operation {op!r}")


def ladder_of(raw) -> list[tuple[int, int | None]] | None:
    """A declared ladder: the site's [{"width": w, "k": k | null}, ...] or [[w, k | null], ...]."""
    if raw is None:
        return None
    if not isinstance(raw, list) or not raw:
        raise PolicyError("declared ladder must be a non-empty list")
    out = []
    for r in raw:
        if isinstance(r, dict):
            w, k = r.get("width"), r.get("k")
        elif isinstance(r, list) and len(r) == 2:
            w, k = r
        else:
            raise PolicyError(f"bad ladder rung {r!r}")
        if k is not None:
            nat(k)
        out.append((nat(w), k))
    return out


def ladder_lean(ladder) -> str:
    return "[" + ", ".join(f"({w}, {'none' if k is None else f'some {k}'})" for w, k in ladder) + "]"


def render(policy: dict, module: str, target: int | None, part: str = "all", data_module: str | None = None,
           declared=None, bands_contract: bool = False, widths: str = "scan", exact_ladder=None) -> str:
    """widths = "scan": the 2026-10-28 certificate (declared ladder checked by `declOK`).
    widths = "exact": additionally `correct_tight` and, from `exact_ladder` (the report's
    `ladderTight`), `exact_ladder` (kernel-pinned); the declared ladder (or, if none, the exact
    ladder) is certified by `declOKTight` instead of `declOK`; the threshold rule
    `chain_contracts_tight` (`chainContractsTight N`) replaces the scan chain `chain_contracts`, plus
    `thresholds_at_target`, `correct_at_target` and `exact_ladder_at_target` at N."""
    if not IDENT.match(module):
        raise PolicyError("module name must be a Lean identifier starting upper-case")
    mode = policy.get("mode")
    if mode not in MODES:
        raise PolicyError(f"bad mode {mode!r}")
    bands = policy.get("bands")
    if not isinstance(bands, list):
        raise PolicyError("bands must be a list")
    if part not in ("all", "data", "cert"):
        raise PolicyError(f"bad part {part!r}")
    if widths not in ("scan", "exact"):
        raise PolicyError(f"bad width rule {widths!r}")
    if widths == "exact" and part != "data" and (exact_ladder is None or target is None):
        raise PolicyError("--widths exact needs the exact ladder and a target width")
    out = []
    if part == "cert":
        if not data_module or not IDENT.match(data_module):
            raise PolicyError("--part cert needs --data-module NAME")
        out.append(f"import TableGeneration.RecursiveCost.BandedPolicy.Instances.{data_module}\n")
    else:
        out.append("import TableGeneration.RecursiveCost.BandedPolicy\n")
    out.append(f"/-! Generated by scripts/policy_json_to_lean.py from: {lean_comment(policy.get('name', ''), 200)} -/\n")
    out.append(f"namespace TableGeneration.PolicyMirror.Instances.{module}\n")
    out.append("open TableGeneration TableGeneration.Operations TableGeneration.PolicyMirror\n")
    if part == "cert":
        out.append(f"open TableGeneration.PolicyMirror.Instances.{data_module}\n")
    band_names = []
    for bi, b in enumerate(bands):
        if b.get("mode", mode) != mode:
            raise PolicyError(f"band {bi} mode {b.get('mode')!r} differs from policy mode {mode!r}")
        k = b.get("k")
        if not isinstance(k, int) or isinstance(k, bool) or k < 1:
            raise PolicyError(f"band {bi}: bad k {k!r}")
        thr = nat(b.get("threshold"))
        pts = [point_lean(p) for p in b.get("point_order", [])]
        ops = [op_lean(o, k) for o in b.get("operations", [])]
        band_names.append((thr, f"band{bi}"))
        if part == "cert":
            continue
        out.append(f"/-- band {bi}: threshold {thr}, k = {k}, {len(pts)} points, {len(ops)} operations -/")
        out.append(f"def band{bi} : PolicyTable where")
        out.append(f"  k := {k}")
        out.append("  pts := [" + ", ".join(pts) + "]")
        out.append("  ops :=")
        if ops:
            out.append("    [ " + "\n    , ".join(ops) + " ]\n")
        else:
            out.append("    []\n")
    if declared is not None and part != "cert":
        out.append("/-- The declared ladder of operand widths (the cost model's working widths). -/")
        out.append(f"def declared : List (ℕ × Option ℕ) := {ladder_lean(declared)}\n")
    if part != "cert":
        out.append("/-- For the report: the declared ladder, if any. -/")
        out.append("def declared? : Option (List (ℕ × Option ℕ)) := " + ("some declared" if declared is not None else "none") + "\n")
    if part != "cert":
        out.append("/-- The policy: bands widest first. -/")
        out.append("def policy : BandedPolicy where")
        out.append(f"  mode := {MODES[mode]}")
        out.append("  bands := [" + ", ".join(f"⟨{t}, {n}⟩" for t, n in band_names) + "]\n")
    if part == "data":
        out.append(f"end TableGeneration.PolicyMirror.Instances.{module}\n")
        return "\n".join(out)
    out.append("/-- Acceptance: the whole decidable check, reduced by the kernel alone. -/")
    out.append("theorem accepted : policy.check = true := by decide +kernel\n")
    out.append("/-- The certificate: the policy computes the phase (triple) product at every width. -/")
    out.append("theorem correct : ∀ (n : Nat) (φ : ℚ) (xs : Fin policy.mode.arity → ℤ),")
    out.append("    policy.evalPhase n φ xs = φ * ∏ s, (xs s : ℚ) :=")
    out.append("  evalPhase_correct_of_check policy accepted\n")
    out.append("/-- Register-width soundness: on operands fitting `n` signed bits, the evaluation on")
    out.append("wrapping fixed-width registers at the scanned widths is exactly the phase (triple) product. -/")
    out.append("theorem correct_reg : ∀ (n : Nat) (φ : ℚ) (xs : Fin policy.mode.arity → ℤ),")
    out.append("    (∀ s, Fits n (xs s)) → policy.evalPhaseReg n φ xs = φ * ∏ s, (xs s : ℚ) :=")
    out.append("  evalPhaseReg_correct policy accepted\n")
    out.append("/-- Capacity at every level down to the leaf (limbs, every intermediate register, every child operand). -/")
    out.append("theorem capacity : ∀ (n : Nat) (xs : Fin policy.mode.arity → ℤ),")
    out.append("    (∀ s, Fits n (xs s)) → policy.CapacityOK n xs :=")
    out.append("  capacityOK_of_check policy accepted\n")
    if bands_contract:
        out.append("/-- Every band contracts at every width of its range (top band: all widths ≥ its threshold). -/")
        out.append("theorem bands_contract : policy.bandsContract = true := by decide +kernel\n")
    if declared is not None and widths == "scan":
        out.append("/-- The declared ladder never under-declares a working width. -/")
        out.append("theorem declared_widths : policy.declOK declared = true := by decide +kernel\n")
        out.append("/-- Register-width soundness at the declared widths. -/")
        out.append("theorem declared_correct : ∀ (n : Nat) (φ : ℚ) (xs : Fin policy.mode.arity → ℤ),")
        out.append("    (∀ s, Fits n (xs s)) → policy.evalPhaseRegW (ladderWidth declared) n φ xs = φ * ∏ s, (xs s : ℚ) :=")
        out.append("  TableGeneration.PolicyMirror.declared_correct policy accepted declared declared_widths\n")
    if widths == "exact":
        out.append("/-- Register-width soundness at the exact widths: on operands fitting `n` signed bits, the")
        out.append("evaluation on wrapping registers whose working width is `tightWidth` is exactly the phase (triple) product. -/")
        out.append("theorem correct_tight : ∀ (n : Nat) (φ : ℚ) (xs : Fin policy.mode.arity → ℤ),")
        out.append("    (∀ s, Fits n (xs s)) → policy.evalPhaseRegTight n φ xs = φ * ∏ s, (xs s : ℚ) :=")
        out.append("  evalPhaseRegTight_correct policy accepted\n")
        out.append(f"/-- The exact-width recursion ladder from {nat(target)} (kernel-evaluated `ladderTight`). -/")
        out.append(f"def exactLadder : List (ℕ × Option ℕ) := {ladder_lean(exact_ladder)}\n")
        out.append(f"theorem exact_ladder : policy.ladderTight {nat(target)} = exactLadder := by decide +kernel\n")
        lad = "declared" if declared is not None else "exactLadder"
        out.append("/-- The certified ladder never declares a working width below the exact width. -/")
        out.append(f"theorem declared_tight_widths : policy.declOKTight {lad} = true := by decide +kernel\n")
        out.append("/-- Register-width soundness at the certified ladder. -/")
        out.append("theorem declared_tight_correct : ∀ (n : Nat) (φ : ℚ) (xs : Fin policy.mode.arity → ℤ),")
        out.append(f"    (∀ s, Fits n (xs s)) → policy.evalPhaseRegW (ladderWidthTight {lad}) n φ xs = φ * ∏ s, (xs s : ℚ) :=")
        out.append(f"  TableGeneration.PolicyMirror.declaredTight_correct policy accepted {lad} declared_tight_widths\n")
    out.append("/-- The submission record. -/")
    out.append("def submission : PolicySubmission := ⟨policy, accepted⟩\n")
    if mode == "PhaseProduct":
        out.append("/-- The same policy as ForShor's object (`Shor.ShorPolicySubmission`, every band C1–C4). -/")
        out.append("def forshorSubmission : Shor.ShorPolicySubmission := toShorPolicySubmission policy accepted rfl\n")
    if target is not None and widths == "scan":
        out.append(f"/-- Every band the recursion from width {target} selects strictly contracts (no leaf fallback on the chain). -/")
        out.append(f"theorem chain_contracts : policy.chainContracts {nat(target)} = true := by decide +kernel\n")
    if widths == "exact":
        N = nat(target)
        out.append(f"/-- **Threshold acceptance rule** (exact widths): on the exact-width recursion from {N}, every chosen")
        out.append("band strictly shrinks the width and is applied at a width ≥ its k (non-degenerate limbs). The kernel")
        out.append("checks it on the pinned exact ladder. -/")
        out.append(f"theorem chain_contracts_tight : policy.chainContractsTight {N} = true := by")
        out.append("  unfold BandedPolicy.chainContractsTight")
        out.append("  rw [exact_ladder]")
        out.append("  decide +kernel\n")
        out.append(f"/-- The rule, stated without the ladder: every table chosen at every width the exact recursion from {N} reaches has k ≤ width and strictly shrinks it. -/")
        out.append(f"theorem thresholds_at_target : ∀ (m : ℕ) (T : PolicyTable), policy.ExactReach {N} m →")
        out.append("    policy.choose m = some T → T.k ≤ m ∧ T.tightWidth m < m :=")
        out.append(f"  (BandedPolicy.chainContractsTight_iff_reach policy {N}).mp chain_contracts_tight\n")
        out.append(f"/-- Concrete correctness at the target width {N}: on operands fitting {N} signed bits, the exact-width register semantics is the phase (triple) product. -/")
        out.append("theorem correct_at_target : ∀ (φ : ℚ) (xs : Fin policy.mode.arity → ℤ),")
        out.append(f"    (∀ s, Fits {N} (xs s)) → policy.evalPhaseRegTight {N} φ xs = φ * ∏ s, (xs s : ℚ) :=")
        out.append(f"  evalPhaseRegTight_correct policy accepted {N}\n")
        if declared is not None:
            out.append("/-- The declared ladder obeys the threshold rule too: every `none` rung is a genuine leaf, every")
            out.append("`some k` rung has k ≤ width, and nothing is declared after the leaf. -/")
            out.append("theorem declared_thresholds : policy.declThresholdOK declared = true := by decide +kernel\n")
        out.append(f"/-- The exact ladder at the target width {N}, and it passes the threshold rule. -/")
        out.append(f"theorem exact_ladder_at_target : policy.ladderTight {N} = exactLadder ∧ policy.chainContractsTight {N} = true :=")
        out.append("  ⟨exact_ladder, chain_contracts_tight⟩\n")
    out.append(f"end TableGeneration.PolicyMirror.Instances.{module}\n")
    return "\n".join(out)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("policy_json")
    ap.add_argument("--module", required=True)
    ap.add_argument("--target-width", type=int)
    ap.add_argument("--index", type=int)
    ap.add_argument("--part", default="all", choices=["all", "data", "cert"])
    ap.add_argument("--data-module")
    ap.add_argument("--bands-contract", action="store_true", help="also emit the F6 theorem `bands_contract`")
    a = ap.parse_args(argv)
    with open(a.policy_json) as f:
        doc = json.load(f)
    if a.index is not None:
        doc = doc["policies"][a.index]["policy"]
    elif "policy" in doc and "bands" not in doc:
        doc = doc["policy"]
    try:
        declared = ladder_of(doc.get("declared_ladder"))
        sys.stdout.write(render(doc, a.module, a.target_width, a.part, a.data_module, declared, a.bands_contract))
    except PolicyError as e:
        print(f"policy_json_to_lean: {e}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
