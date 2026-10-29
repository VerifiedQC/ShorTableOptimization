#!/usr/bin/env python3
"""Exact PTP widths in Python, mirroring `TableGeneration.RecursiveCost.PTP.Exact`
(`ptpTightWidth`, `ladderX`) definition for definition, for the site's PTP pricer.

    from ptp_exact_width import ptp_tight_width, exact_ladder, ptp_scan_width
    ptp_tight_width(k, operations, n)  -> int   # exact width of one table at operand width n
    exact_ladder(policy, n)            -> [(width, k or None), ...]
    ptp_scan_width(k, operations, n)   -> int   # the PTP magnitude scan (childWidth)

CLI:  ptp_exact_width.py POLICY.json N   -> JSON {exact_ladder, scan_ladder, bands:[...]}

Definition (PTP limb split at operand width n, all three operands of width n):
W = n // k; lower limbs in [0, 2^W - 1]; top limb in [-2^(t-1), 2^(t-1) - 1] with
t = n - (k-1) W. Run the program on coefficient rows from the identity (STO
semantics; stop at an inexact right shift); collect every row of every state
(before each operation, and the final one). For each row r: rowLo/rowHi =
sum of coordinatewise min/max of r_j * lo_j, r_j * hi_j; demand(r) =
max(-rowLo, rowHi + 1, 0). D = max demand. Exact width = 1 + least e with D <= 2^e.
The Lean kernel recomputes the same numbers (`ladder_exact`, `child_width_i`);
check_ptp_policy.py --widths exact cross-checks this module against the Lean report.
"""
from __future__ import annotations

import json
import sys


def _rows_reached(k: int, ops: list) -> list[list[int]]:
    state = [[1 if j == i else 0 for j in range(k)] for i in range(k)]
    out = [r[:] for r in state]
    for op in ops:
        name, args = op[0], op[1:]
        if name == "shiftL":
            i, s = args
            state[i] = [c << s for c in state[i]]
        elif name == "shiftR":
            i, s = args
            m = 1 << s
            if any(c % m for c in state[i]):
                return out  # inexact: the run stops (Lean `reachRows` stops too)
            state[i] = [c // m for c in state[i]]
        elif name == "negate":
            (i,) = args
            state[i] = [-c for c in state[i]]
        elif name == "addScaled":
            d, s, sign, sh = args
            sgn = -1 if sign == -1 else 1
            state[d] = [a + sgn * b * (1 << sh) for a, b in zip(state[d], state[s])]
        elif name == "phaseProduct":
            pass
        else:
            raise ValueError(f"bad op {op!r}")
        out += [r[:] for r in state]
    return out


def _box(k: int, n: int):
    W = n // k
    t = n - (k - 1) * W
    lo = [0] * (k - 1) + [-(1 << (t - 1)) if t >= 1 else -1]
    hi = [(1 << W) - 1] * (k - 1) + [((1 << (t - 1)) - 1) if t >= 1 else 0]
    # (t >= 1 whenever n >= 1; Lean's Nat subtraction t - 1 = 0 at t = 0 gives the same values)
    if t == 0:
        lo[-1], hi[-1] = -1, 0
    return lo, hi


def ptp_tight_width(k: int, ops: list, n: int) -> int:
    lo, hi = _box(k, n)
    D = 0
    for r in _rows_reached(k, ops):
        rlo = sum(min(c * a, c * b) for c, a, b in zip(r, lo, hi))
        rhi = sum(max(c * a, c * b) for c, a, b in zip(r, lo, hi))
        D = max(D, max(-rlo, 0), max(rhi + 1, 0))
    e = 0
    while (1 << e) < D:
        e += 1
    return 1 + e


def ptp_scan_width(k: int, ops: list, n: int) -> int:
    W = n // k
    w = [W] * (k - 1) + [n - (k - 1) * W]
    mx = max(w)
    for op in ops:
        name, args = op[0], op[1:]
        if name == "shiftL":
            w[args[0]] += args[1]
        elif name == "shiftR":
            w[args[0]] = max(0, w[args[0]] - args[1])
        elif name == "addScaled":
            d, s, _sign, sh = args
            w[d] = 1 + max(w[d], w[s] + sh)
        mx = max(mx, max(w))
    return 1 + mx


def _choose(policy: dict, n: int):
    for b in policy["bands"]:
        if b["threshold"] <= n:
            return b
    return None


def _ladder(policy: dict, n: int, width_fn) -> list:
    out, fuel = [], n + 1
    while True:
        b = _choose(policy, n)
        if fuel == 0 or b is None:
            out.append((n, None)); return out
        c = width_fn(b["k"], b["operations"], n)
        if c < n:
            out.append((n, b["k"])); n = c; fuel -= 1
        else:
            out.append((n, None)); return out


def exact_ladder(policy: dict, n: int) -> list:
    return _ladder(policy, n, ptp_tight_width)


def scan_ladder(policy: dict, n: int) -> list:
    return _ladder(policy, n, ptp_scan_width)


def main(argv=None) -> int:
    argv = argv if argv is not None else sys.argv[1:]
    doc = json.loads(open(argv[0]).read())
    if "policy" in doc and "bands" not in doc:
        doc = doc["policy"]
    n = int(argv[1])
    print(json.dumps({
        "exact_ladder": exact_ladder(doc, n), "scan_ladder": scan_ladder(doc, n),
        "bands": [{"threshold": b["threshold"], "k": b["k"],
                   "exact_at_threshold": ptp_tight_width(b["k"], b["operations"], b["threshold"]),
                   "scan_at_threshold": ptp_scan_width(b["k"], b["operations"], b["threshold"])}
                  for b in doc["bands"]]}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
