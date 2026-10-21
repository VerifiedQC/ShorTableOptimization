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
them for a particular width. Both the Lean model and the website search the
same set: every accepted PhaseProduct result retained on `submission-results`,
not just the per-target champions. Champions are chosen by the leaderboard's
structural weighted cost and the planner minimises gate count, so a table that
lost its champion slot can still be the cheapest choice at some width:

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

The gate costs are not reproduced here, and they are no longer copied either.
`Reg`, `ExtReg`, `LowGate`, `LowGateCostModel`, `GateResources`, the Cuccaro
resource records and `shorGateCostModel` itself are the companion's own
definitions, imported from the `Fast_multiplication` dependency. There used to
be a transcribed slice under `TableGeneration/RecursiveCost/ForShor/` kept in
step by a hand-run drift check; sourcing the definitions removed the copy, the
drift and the checker alike. Nothing of that arrangement remains to look up.

The planner's constants are computed from those records, so the familiar
`9w - 16` and `10w - 14` are theorems (`cuccaroModAddGateCount_eq`,
`cuccaroNegateGateCount_eq`) rather than numbers copied from the companion, and
`cuccaroNegateGateCount_eq_model` ties the planner's constant to what
`shorGateCostModel.negate` charges, by `rfl` and with no axioms.

### What this repository adds on top

Three things the companion does not supply, all under
`TableGeneration/RecursiveCost/`:

- `CompanionTransport.lean` -- the single bridge between this repository's
  `Operations.valid_ops` / `Point` and the companion's. They are distinct
  inductives of identical shape, because the submission path has to stay
  Mathlib-free.
- `CompanionCost.lean` -- a `Nat`-indexed face on cost functions the companion
  states over an `ExtReg` but reads only a width from, so the planner pays no
  `O(w)` register construction per query.
- `CompanionAllocation.lean` and `AllocationAgreement.lean` -- the companion
  bounds its allocation bookkeeping (`<= 2nW`); the planner charges a closed
  form and needs the exact figure, so these evaluate
  `bookkeepingGateCost (compileSignedAllocations ...)` and prove the closed form
  **equal** to it.

What guards the cost model continuously is in-repo and needs no companion
checkout -- the oracle's `--width-scan` mode, run by
`scripts/test_cost_model_lean.py`, which checks the planner's array width scan
against the companion's own definitions. The closed-form allocation charge needs
no test: `canonicalAllocationCost_eq` proves it.

ForShor is a Lake dependency, declared in `lakefile.lean` as the package
`Fast_multiplication` and tracking its `main` branch. Mathlib is required first
so that this repository's pin governs: ForShor's own Mathlib requirement carries
no revision, and Lake resolves a package name once.

Tracking a branch does not make builds float. `lake-manifest.json` records a
resolved commit and is committed, and no workflow runs `lake update`, so CI and
a fresh clone both build that exact revision. Updating is deliberate:

    lake update Fast_multiplication

After any update, check that the planner still reports the same totals, because
these are the figures the write-up quotes:

    lake env lean --run scripts/tests/RecursiveCostOracle.lean \
      --best-known 1024 2048 4096 8192 16384

    1024   1649629   3    147    213
    2048   4343539   4    726    689
    4096   11330660  4    1628   2427
    8192   28618144  4    3016   4888
    16384  71324077  4    4872   7984

(width, gates, recursion height, recursive calls, arithmetic operations; the
command also prints a trailing `k:childWidth:policy` column, omitted here.)
These are the totals at `545cf76`, after the October 2026 promotion. They move
whenever a table is accepted that the planner prefers, so a mismatch is not by
itself a model change -- check `git log leaderboard/best-known.md` and the
archive before concluding the cost model moved. `--best-known-unbounded`
currently reports the same five gate totals and the same `k` chain; it reports a
lower arithmetic-operation count, because several plans reach the same gate cost
and the two searches break that tie differently. The agreement on gates is not
guaranteed -- see the two-catalogue note below.

`scripts/test_cost_model_lean.py` will not catch a change here: it compares the
planner against itself, so both sides move together. Only the totals above show
that the model itself moved.

The dependency is confined to `TableGeneration/RecursiveCost/**`, enforced by
`scripts/check_mathlib_confinement.py`, which is what keeps the submission axiom
audit reporting `propext` alone.

### Checking the closed form against the companion's compiler

The oracle checks the planner's *parts*. To check the whole number, the
companion can compile a table to a `LowGate` tree and count it, which is the
quantity `lake exe forshor_emit pp <k> <n> <phi> --flat` prints:

    lake env lean --run scripts/tests/ChampionGateCountDifferential.lean

It prices this repository's promoted champions -- not the companion's standard
table -- both ways, and insists on exact integer agreement. It is not in CI: it
takes about five minutes, and is feasible only at `k = 2` and `k = 3`, because
the lowered term has `recursiveCallCount ^ depth` leaves and does not finish at
`k >= 4`.

One subtlety it has to account for, set out in full in
`TableGeneration/RecursiveCost/ChampionLowering.lean`: the companion's
`PhaseLoweringPlan` recurses on exactly one condition, whether the table
strictly contracts the width, with no cost comparison anywhere. The planner also
gets to decline, reporting the schoolbook base case when recursing is dearer. So
the planner answers "what is the cheapest policy at this width" and the compiler
answers "what does this table compile to", and the two coincide only where the
planner's optimum is to recurse. The differential drives the planner's own
per-node charge with the companion's stopping rule, and prints the planner's
own figure beside it so the gap stays visible.

The default sweep agrees exactly at every width it can reach:

| k | width | child | closed form | planner min | `LowGate.gateCount` |
|---|---|---|---|---|---|
| 2 | 8 | 7 | 935 | 320 | 935 |
| 2 | 10 | 8 | 3041 | 500 | 3041 |
| 2 | 12 | 9 | 9395 | 720 | 9395 |
| 2 | 14 | 10 | 9431 | 980 | 9431 |
| 2 | 16 | 11 | 28529 | 1280 | 28529 |
| 3 | 20 | 19 | 60234 | 2000 | 60234 |
| 3 | 24 | 20 | 304826 | 2880 | 304826 |

The third and fifth columns are the two independent computations and they match
digit for digit. The fourth is the planner's own rule, and its distance from the
other two is the whole content of the subtlety above: at these widths the
champion's optimum is the schoolbook base case, so the planner declines to
recurse where the compiler cannot. That column is printed, not asserted on.

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

### Which tables are eligible: two catalogues

"Eligible" is decided by `scripts/promote.py`, which writes two lists into
`TableGeneration/RecursiveCost/ArchivedCatalog.lean`:

- `archivedCandidates` applies a **layer bound**: a table deeper than the
  current per-target champion at the same arity is dropped. The gate model
  charges nothing for layers, so without this a table could buy gates with depth
  for free.
- `archivedCandidatesUnbounded` is every accepted `PhaseProduct` table, bound or
  not.

The Lean planner reads the bounded list by default and the unbounded one under
`--catalog-unbounded` / `--best-known-unbounded`. **The website reads the
unbounded set.** It fetches `results.json` and filters on product mode alone; it
never sees the bound, because the bound lives in the generated Lean catalogue
and the site does not read Lean.

So the two can disagree, and in October 2026 they did, by 455,436 gates at 2048
bits, after a `k=3` table with four layers was accepted. They agree again now,
for a reason that is not a guarantee: a two-layer table reaching the same child
width was accepted afterwards, so the bound currently costs nothing. Treat
agreement as something to check, not something to assume, and read
`--best-known-unbounded` as the published number.

This was checked by `testPublishedNumberDifferential` in the JavaScript mirror,
which planned over the unbounded catalogue in both languages at 1024, 2048,
4096, 8192 and 16384. That mirror is gone; the totals table above is what now
shows the published number has not moved.

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
  `16`, `2048`, and `4096`;
- whole-plan agreement between Lean and the browser calculator over the
  unbounded catalogue, which is the set the published number is planned over.

The model version and objective must be included in published results so that a
future ForShor cost-model change does not silently reinterpret old estimates.

## Model versions (investigation branch)

`v3` (`forshor-phase-product-gates-v3`) is the only model. It is the companion's
operative `shorGateCostModel = shorGateResourceModel.toCostModel` in
`Framework/Gatecount/ResourceModel.lean`, read from the dependency at the
revision `lake-manifest.json` pins:

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
A `v3-loose4kw` variant substituting that bound used to exist as a sensitivity
comparison. It was never the companion's model and is gone, as is `v2`, whose
upstream counterpart the companion deleted. The version string survives in
`modelVersion`. The oracle's `--model=` selector is gone -- with one model it
selected nothing -- but it is refused by name rather than ignored, so an
invocation naming a retired model fails loudly instead of being read as a width.
