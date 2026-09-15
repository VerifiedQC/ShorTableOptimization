# Recursive PhaseProduct Cost Model

This document describes the standalone cost planner for the verified
table-generation policies in this repository. It is a design document, not the
current leaderboard scoring contract. `BENCHMARK.md` remains authoritative for
the existing structural benchmark.

## Scope

The first version:

- supports `PhaseProduct` only;
- optimizes the ForShor-compatible logical gate count only;
- accepts any positive integer bit length `n`, including values that were not
  precomputed;
- uses every successfully archived PhaseProduct policy for `k = 2` through `16`;
- selects both `k` and the policy independently at each recursion level;
- follows ForShor's width and logical-gate cost definitions unless the model
  explicitly identifies an intentional recursion improvement; and
- runs as part of the static website without requiring a server.

The website input should be labeled **Integer bit length (n)**. An input such as
`2048` means a 2048-bit integer, not the numerical value of an RSA modulus.

## Separation of Responsibilities

The existing Lean verifier proves that a policy's symbolic operation program is
valid. That proof is independent of the operand width.

The recursive planner consumes only verified programs and decides how to use
them for a particular width. The Lean model has one promoted built-in program
per `k`; the website augments that catalog with every successful PhaseProduct
result retained on `submission-results`:

```text
verified policies (k and operation program)
                    |
                    v
       recursive planner (n and objective)
                    |
                    v
     selected policy and k at every level
                    |
                    v
        resource estimate and compact plan
```

The submission-facing Lean interface therefore does not need an `n` parameter.
The planner owns the width-dependent selection.

## ForShor Foundation

The table-operation languages are compatible. Both repositories use:

- `shiftL` and `shiftR`;
- `negate`;
- `addScaled`; and
- `phaseProduct`.

The gate costs are not reproduced here. The minimal set of ForShor
definitions the cost model needs -- `Reg`, `ExtReg`, `LowGate`,
`LowGateCostModel`, `GateResources`, the Cuccaro resource records, and
`shorGateCostModel` itself -- is integrated verbatim under
`TableGeneration/RecursiveCost/ForShor/`, pinned to ForShor commit `d5a165b`
and carrying per-file provenance headers. The planner's `v3` constants are
computed from those records, so the familiar `9w - 16` and `10w - 14` are
theorems (`cuccaroModAddGateCount_eq`, `cuccaroNegateGateCount_eq`) rather
than numbers copied from the companion, and
`cuccaroNegateGateCount_eq_model` ties the planner's constant to what
`shorGateCostModel.negate` charges, by `rfl` and with no axioms.

### Re-checking the slice against upstream

The slice is pinned to companion commit `d5a165b`. It is a copy, so it can drift
if the companion changes. Re-check it deliberately when syncing to a newer
commit:

```sh
FORSHOR_ROOT=/path/to/ForShor python3 scripts/check_forshor_slice.py

# before re-pinning, compare against the companion's HEAD instead
python3 scripts/check_forshor_slice.py --forshor /path/to/ForShor --working-tree
```

It reports how many declarations match, lists the deliberate deviations with
their reasons, and exits non-zero on drift. It currently reports 61 matching
with 5 declared deviations, all of them generic order lemmas replaced by defeq
`Nat` counterparts.

This is a maintainer tool, not a CI gate: a hosted runner has no companion
checkout, so running it there would only ever skip. What guards the cost model
continuously is in-repo and needs no checkout -- the oracle's `--width-scan` and
`--allocation` modes, run by `scripts/test_recursive_cost.js`, which check the
planner's array width scan and its closed-form allocation charge against the
integrated copies.

ForShor is deliberately *not* a Lake dependency. Its cost-model files reach
`Mathlib.Tactic`, and this repository stays dependency-free so that the
submission axiom audit remains `propext`-only and a submitter's first build
stays seconds rather than gigabytes. Two things could not be integrated
mathlib-free and remain this repository's own formulations, marked as such in
`Model.lean`: the width scan's `commonNeededWidth` (ForShor uses
`Finset.univ.sup`) and `updateWidth` (ForShor uses `Function.update`).

What is integrated is the *circuit-level* model. ForShor's own
recurrence-level costing, `phaseArithmeticOpCost` in
`Implementation/GateCount/Definitions.lean`, still charges the conservative
`rippleAdderGateBound = 9w + 2`, which is this repository's `v2`. The `v3`
model here is ForShor's recurrence shape with ForShor's circuit constants --
a combination ForShor does not itself define, and it should not be described
as a number ForShor computes.

### Initial widths

The reference model supports a pair of operand widths `(xWidth,
zWidth)`. The initial website profile maps `n` to `(n, n)`.

For a policy with parameter `k`, ForShor uses a top-heavy split. The lower
`k - 1` limbs have a common width, and the final limb absorbs each operand's
remainder:

```text
limbWidth = min(floor(xWidth / k), floor(zWidth / k))
```

### Width transitions

For each operand, ForShor conservatively updates symbolic widths as follows:

```text
shiftL(i, amount):
  width[i] = width[i] + amount

shiftR(i, amount):
  width[i] = width[i] - amount, truncated at zero

negate(i):
  width[i] = width[i] + 1

addScaled(dst, src, shift):
  width[dst] = 1 + max(width[dst], width[src] + shift)
```

These are safe capacity bounds. They are not exact mathematical ranges, because
an inverse addition does not make the recorded width shrink. The initial model
retains these bounds so that its claims remain compatible with ForShor.

ForShor currently pads every recursive child to one common maximum width. The
planner implements this behavior as its conformance mode. A later
branch-sensitive mode may retain the widths seen at each `phaseProduct` call and
allow different branches to choose different recursive policies. That is an
intentional optimization and will require corresponding compiler support before
it can be described as an executable ForShor plan.

### Logical gate costs

The initial PhaseProduct model uses ForShor's conservative formulas:

```text
rippleAdder(width) = 9 * width + 2
directPhaseProduct(xWidth, zWidth) = 5 * xWidth * zWidth
```

Shifts have zero logical-gate cost in this model. `addScaled` and `negate` have
linear costs and are applied to both PhaseProduct operands. A controlled
PhaseProduct profile may use ForShor's controlled base-case multiplier, but it
must be identified separately from the ordinary PhaseProduct profile.

These values are exact with respect to the declared abstract cost model. They
are not hardware gate counts and do not include routing or error correction.

## Recursive Optimization

For a verified policy `P`, let `children(P, widths)` be the recursive
PhaseProduct calls found by interpreting its operation program at the supplied
widths.

The minimum logical-gate cost is:

```text
G(widths) = min(
  baseGateCost(widths),
  min over eligible (k, P) of
    arithmeticGateCost(P, widths)
      + sum(G(childWidths) for childWidths in children(P, widths))
)
```

The base case is always an available candidate. A recursive candidate is
eligible only when every child is strictly smaller than its parent. This ensures
termination and lets the cost model choose the base case based on cost rather
than an arbitrary fixed threshold.

In ForShor-conformance mode, all recursive calls at a node use the common padded
child width. In branch-sensitive mode, each call may have its own width and may
select a different `k` and policy.

## Initial Metrics

The first implementation optimizes logical gate count and reports a few
supporting structural measurements for the selected plan.

### Logical gate count

Logical gate count is the total work. Arithmetic gates at a node and the gates
from every recursive child are added.

### Recursion height

Recursion height is the number of decomposition levels on the longest branch:

```text
H(base) = 0
H(recursive node) = 1 + max(H(child))
```

This is exact for the selected plan but does not include the cost of arithmetic
within a level.

### Supporting measurements

The result also reports:

- total recursive PhaseProduct calls;
- total symbolic arithmetic operation count;
- every selected policy, `k`, child width, and local arithmetic gate count; and
- the expanded gate and arithmetic contribution from each recursion level.

The website presents these choices as an aggregated recursion tree. Because
ForShor-conformance mode pads every child at a level to one common width, equal
subproblems are shown once with their multiplicity instead of repeated as
identical branches. The exact verified operation sequence for each selected
policy remains available from that level.

Workspace and ancilla optimization are outside the first implementation.

## Objective

The first implementation has one objective: **minimum ForShor-compatible
logical gate count**. Recursion height is reported for the selected minimum-gate
plan. Full circuit depth, workspace, ancilla, and balanced objectives can be
added later without changing the verified table-policy interface.

## On-Demand Computation

Bit lengths are not precomputed. Archived policy operations are loaded from the
same verified result files used by the leaderboard. The browser evaluates a
requested width using memoized dynamic programming. The Lean reference visits
only reachable widths; only the policy programs and cost-model version are
published in advance.

The memoization key is the requested width within one fixed model and candidate
set. Any persistent cache should include at least:

```text
(model version, candidate set, width)
```

The dynamic program stores compact backpointers. Its machine-readable result has
one aggregated entry per recursion level rather than expanding identical child
nodes. Runtime depends mainly on the number of distinct widths encountered, not
directly on the numerical size of `n`.

Both implementations retain a dense all-width planner as a readable reference.
The actual Lean and JavaScript entry points use sparse or memoized traversal of
reachable widths, with bounded tests confirming that both forms select the same
plans.

## Validation

CI checks:

- an executable Lean reference model with theorems for its core invariants;
- golden width-transition cases generated from ForShor;
- differential tests for every operation kind;
- fixed-policy recurrence comparisons at small widths;
- strict-contraction and termination tests;
- bounded agreement between the dense reference and sparse or memoized planner;
- deterministic reproduction of selected plans and metrics;
- exact agreement between the Lean reference and the shared browser/Node
  implementation over exhaustive, boundary, and seeded-random bit lengths;
- plan-construction checks for representative inputs including
  `16`, `2048`, and `4096`.

The model version and objective must be included in published results so that a
future ForShor cost-model change does not silently reinterpret old estimates.

## Model versions (investigation branch)

`v2` (`forshor-phase-product-gates-v2`) remains the default and is unchanged:
`rippleAdder(w) = 9w + 2`, `negate(w) = 10w + 2`, free sign extension, no
allocation bookkeeping. Every existing plan regenerates byte-identically under
it; `analyzeWith_v2` in `TableGeneration/RecursiveCost/Catalog.lean` proves the
parameterized analyzer agrees with the original one at `v2Costs`.

`v3` (`forshor-phase-product-gates-v3`) transcribes the operative model at
companion commit `d5a165b`, `shorGateCostModel = shorGateResourceModel.toCostModel`
in `Framework/Gatecount/ResourceModel.lean`:

- `addScaled`: exact Cuccaro modulo adder,
  `(2w - 6) + (5w - 7) + (2w - 3)` = `9w - 16` for `w >= 3`;
- `negate`: complement plus a constant-one register plus that adder,
  `(w + (2w - 6) + 2) + (5w - 7) + (2w - 3)` = `10w - 14` for `w >= 3`;
- `shiftL` / `shiftR` / `zeroExtend` / `zeroDealloc`: free;
- `signExtend` / `signDealloc`: `n` CNOTs each.

Truncated `Nat` subtraction is deliberate: the companion's definitions are over
`Nat`, so the same truncation applies below the published `w >= 3` regime.

Because `allocChunkGate` sign-extends only the top limb and zero-extends the
other `k - 1` limbs, the exact per-node allocation charge is
`2 * ((W' - topLimb(x)) + (W' - topLimb(z)))`, not `4kW'`. The `4kW'` term is a
bound proved in `GateCount/PhaseProduct/Lemmas.lean` (`lgc_allocs_le`,
`lgc_deallocs_le`) for the asymptotic recurrence; it is the same category of
object as `rippleAdderGateBound` and is not a cost the operative model charges.
`v3-loose4kw` substitutes that bound and exists only as a sensitivity
comparison; it must not be described as the companion's model.

Selecting a version:

- Lean: `bestPlanWith v3Costs candidates width`, or the oracle's
  `--model=v2|v3|v3-loose4kw`.
- JavaScript: `RecursiveCost.selectModel("v3")`.
