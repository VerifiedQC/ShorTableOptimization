#!/usr/bin/env python3
"""Lean-only checks on the recursive cost model.

These compare Lean against Lean, and no theorem covers them. They used to live
in the JavaScript mirror's test alongside a Lean/JS differential; the mirror was
deleted in Phase 2 and the differential went with it, but these did not, because
nothing else performs them.

What is kept, and why each one is not implied by a proof:

- `--width-scan`   the array scan against the companion's `Function.update`
                   scan. Nothing proves the two agree.
- `--dense-sparse` the dense and sparse planners agree, over a width list that
                   straddles the 32/64/128 boundaries.
- `--reference`    the binary and transition reference candidates agree with
                   themselves (columns 4 and 5 of each line).
- `--catalog`      the archived catalogue is ordered by arity and covers 2..16.
- default mode     two golden plan lines, so a silent change in the plan format
                   or in the costs is caught.

`--allocation` is deliberately NOT here: `canonicalAllocationCost_eq` already
proves it.

Stdlib only, no pytest. Run: python3 scripts/test_cost_model_lean.py
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
ORACLE = "scripts/tests/RecursiveCostOracle.lean"
COST_MODEL_MODULE = "TableGeneration.RecursiveCost.Correctness"

# Checked against the oracle on 2026-10-21. Tab-separated, not spaces.
GOLDEN_PLANS = {
    "8": "8\t254\t1\t2\t0\t2:5:test-binary",
    "16": "16\t668\t3\t14\t0\t2:9:test-binary",
}

DENSE_SPARSE_WIDTHS = [str(w) for w in range(0, 33)] + ["63", "64", "65", "127", "128"]
REFERENCE_WIDTHS = [str(w) for w in range(0, 65)]
# Boundary cases, then every width the five published plans in
# RECURSIVE_COST_MODEL.md actually recurse through. The planner evaluates
# `nextBalancedSignedWidth`; the width theorems are about `nextSignedWidth`.
# Nothing in the type system ties the two together, so this list is the only
# thing holding them in step -- and before the plan widths were added it
# covered just 1024 and 2048 of the 24 widths those plans visit, missing every
# interior one. Regenerate after a table is accepted that moves a plan:
#   lake env lean --run scripts/tests/RecursiveCostOracle.lean \
#     --best-known 1024 2048 4096 8192 16384
WIDTH_SCAN_BOUNDARIES = ["0", "1", "2", "8", "16", "63", "64", "65", "128"]
WIDTH_SCAN_PLAN_WIDTHS = [
    "37", "38", "44", "51", "55", "68", "70", "82", "96", "104", "130",
    "189", "225", "267", "291", "369", "712", "1024", "1225", "1621",
    "2048", "4096", "8192", "16384",
]
WIDTH_SCAN_WIDTHS = WIDTH_SCAN_BOUNDARIES + WIDTH_SCAN_PLAN_WIDTHS


def oracle(*args: str, timeout: int = 1800) -> str:
    done = subprocess.run(
        ["lake", "env", "lean", "--run", ORACLE, *args],
        cwd=REPO,
        text=True,
        capture_output=True,
        timeout=timeout,
    )
    if done.returncode != 0:
        raise AssertionError(
            f"oracle {' '.join(args) or '(default)'} exited {done.returncode}\n"
            f"{done.stdout}\n{done.stderr}"
        )
    return done.stdout


def test_cost_model_builds() -> None:
    done = subprocess.run(
        ["lake", "build", COST_MODEL_MODULE], cwd=REPO, text=True, capture_output=True
    )
    assert done.returncode == 0, done.stdout + done.stderr


def test_width_scan_agrees() -> None:
    out = oracle("--width-scan", *WIDTH_SCAN_WIDTHS)
    assert "width scan agreement passed" in out, out


def test_dense_and_sparse_planners_agree() -> None:
    out = oracle("--dense-sparse", *DENSE_SPARSE_WIDTHS)
    assert "dense/sparse agreement passed" in out, out


def test_reference_columns_agree() -> None:
    out = oracle("--reference", *REFERENCE_WIDTHS)
    lines = [line for line in out.splitlines() if line.startswith("reference\t")]
    assert len(lines) == 2 * len(REFERENCE_WIDTHS), f"{len(lines)} reference lines"
    for line in lines:
        fields = line.split("\t")
        assert len(fields) == 5, line
        assert fields[3] == fields[4], f"columns 4 and 5 differ: {line}"


def test_catalog_is_ordered_and_covers_every_arity() -> None:
    out = oracle("--catalog")
    arities = [
        int(line.split("\t")[2])
        for line in out.splitlines()
        if line.startswith("candidate\t")
    ]
    assert arities, out
    assert arities == sorted(arities), f"catalogue is not ordered by arity: {arities}"
    assert set(range(2, 17)) <= set(arities), f"missing arities: {sorted(set(range(2, 17)) - set(arities))}"


def test_golden_plan_lines() -> None:
    out = oracle(*GOLDEN_PLANS)
    printed = [line for line in out.splitlines() if line.strip()]
    assert len(printed) == len(GOLDEN_PLANS), out
    for line, width in zip(printed, GOLDEN_PLANS, strict=True):
        assert line == GOLDEN_PLANS[width], f"\n  got      {line!r}\n  expected {GOLDEN_PLANS[width]!r}"


if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    failures = 0
    for t in tests:
        try:
            t()
            print(f"ok    {t.__name__}")
        except Exception as exc:  # noqa: BLE001
            failures += 1
            print(f"FAIL  {t.__name__}\n{exc}")
    print(f"\n{len(tests) - failures} passed, {failures} failed")
    sys.exit(1 if failures else 0)
