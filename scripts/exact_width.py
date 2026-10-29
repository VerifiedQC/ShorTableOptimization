#!/usr/bin/env python3
"""The exact ("tight") working width of a banded-policy table, as Lean defines it.

    from exact_width import exact_width, exact_ladder
    exact_width(k, ops, n)          # PolicyTable.tightWidth T n  (Tight.lean)
    exact_ladder(policy, n)         # BandedPolicy.ladderTight P n, as [{"width", "k"}]

`ops` is the site/STO band list: ["addScaled",dst,src,±1,shift], ["shiftL"|"shiftR",reg,m],
["negate",reg], ["phaseProduct",reg]. `policy` is {"bands":[{"threshold","k","operations",...}]}.
Pure integer arithmetic; valid at any n >= 1 (cost is O(#ops * k^2) big-int ops, independent of n
apart from the integer sizes).

ALGORITHM (a transcription of Tight.lean, definition by definition)
  reachStates: the coefficient state (k rows of k integers) starts at the identity; record it,
    apply each op, record the new state; stop (recording nothing more) at a shiftR whose row is
    not divisible by 2^m (Lean's `none`; a checked table never has one).
  limb box at width n: Wl = n // k (floor), Wt = n - (k-1)*Wl;
    lower limbs j < k-1 in [0, 2^Wl - 1], top limb in [-2^(Wt-1), 2^(Wt-1) - 1].
  for each recorded row r: rowLo = sum_j min(r_j*lo_j, r_j*hi_j), rowHi = sum_j max(...);
    demand(r) = max(-rowLo, rowHi + 1, 0).
  D = max demand; width = 1 + (least e >= 0 with D <= 2^e).

WHAT LEAN PROVES ABOUT THIS NUMBER (Tight.lean, kernel-replayed; axioms propext, Classical.choice,
Quot.sound; see inquiry/PROOF_AUDIT.md). For a table T with k >= 1 and n >= 1:
  * tightWidth_le_iff: tightWidth T n <= W  iff  for every operand x with -2^(n-1) <= x < 2^(n-1),
    every register of every state reached by a prefix of T.ops (so every intermediate and every
    child operand), read on x's floor limbs, fits signed W bits. So the number is exactly the least
    no-overflow width (tightWidth_minimal: one bit below, some value for some x overflows).
  * tightWidth_le_childWidth: it never exceeds STO's scan nextSignedWidth n n ops.
  * evalPhaseRegW_tight_correct / evalPhaseRegTight_correct: for a policy passing `check`, the
    wrapping fixed-width register semantics with working width >= this number at every chosen node
    applies exactly phi * prod(xs) for operands fitting n (PP; PTP in the analogous register model).
What it does NOT prove: that Python equals Lean (that is the cross-check: equal on every band of
the 34 policies at their ladders, and HG7 brute force/pointwise checks), gate-level equivalence with
any circuit, or anything about the padded rule (k*ceil(n/k), sto_site TightRule.at_n), which is a
different limb layout. Minimality is for no overflow, not for correctness of the wrapped result.
"""
from __future__ import annotations

from typing import Dict, List, Optional, Sequence


def reach_rows(k: int, ops: Sequence[list]) -> set:
    sigma = [tuple(1 if j == i else 0 for j in range(k)) for i in range(k)]
    rows = set(sigma)
    for o in ops:
        n = o[0]
        if n == "phaseProduct":
            pass
        elif n == "negate":
            sigma[o[1]] = tuple(-c for c in sigma[o[1]])
        elif n == "shiftL":
            sigma[o[1]] = tuple(c << o[2] for c in sigma[o[1]])
        elif n == "shiftR":
            m = 1 << o[2]
            if any(c % m for c in sigma[o[1]]):
                return rows
            sigma[o[1]] = tuple(c // m for c in sigma[o[1]])
        elif n == "addScaled":
            d, s, sg, sh = o[1], o[2], o[3], o[4]
            if sg not in (1, -1):
                raise ValueError(f"bad sign in {o!r}")
            sigma[d] = tuple(a + sg * b * (1 << sh) for a, b in zip(sigma[d], sigma[s]))
        else:
            raise ValueError(f"unknown op {o!r}")
        rows.update(sigma)
    return rows


def exact_width(k: int, ops: Sequence[list], n: int) -> int:
    """PolicyTable.tightWidth at operand width n (floor limbs)."""
    if k < 1 or n < 1:
        raise ValueError("exact_width needs k >= 1 and n >= 1 (Lean's theorems assume both)")
    wl = n // k
    wt = n - (k - 1) * wl
    lo = [0] * (k - 1) + [-(1 << (wt - 1))]
    hi = [(1 << wl) - 1] * (k - 1) + [(1 << (wt - 1)) - 1]
    d = 0
    for r in reach_rows(k, ops):
        rlo = sum(min(c * a, c * b) for c, a, b in zip(r, lo, hi))
        rhi = sum(max(c * a, c * b) for c, a, b in zip(r, lo, hi))
        d = max(d, -rlo, rhi + 1)
    return 1 + (0 if d <= 1 else (d - 1).bit_length())   # least e with d <= 2^e


def choose(bands: Sequence[dict], w: int) -> Optional[dict]:
    """ForShor `choose`: the first band (widest first) whose threshold is <= w."""
    for b in bands:
        if b["threshold"] <= w:
            return b
    return None


def exact_ladder(policy: dict, n: int) -> List[Dict[str, Optional[int]]]:
    """BandedPolicy.ladderTight: recurse at the exact width while it shrinks."""
    out, w = [], n
    while True:
        b = choose(policy["bands"], w)
        if b is None:
            return out + [{"width": w, "k": None}]
        w2 = exact_width(b["k"], b["operations"], w)
        if not w2 < w:
            return out + [{"width": w, "k": None}]
        out.append({"width": w, "k": b["k"]})
        w = w2
