import TableGeneration.RecursiveCost.ChampionLowering

/-!
# Champion differential: the closed-form planner cost against the real lowering

The planner's gate count is a closed form. This checks it, by exact integer
comparison with no tolerance, against the number the companion's compiler
actually produces:

```
Shor.LowGate.gateCount Shor.shorGateCostModel
  (Shor.lowerGate k hk ops pts hpts (Shor.Gate.SignedPhaseProd phi x z) hws)
```

which is the same quantity the companion's own
`lake exe forshor_emit pp <k> <n> <phi> --flat` prints as `gate_count`.

## What is being compared, and against what

The tables are **this repository's promoted champions** --
`bestKnownGenerate`/`bestKnownGeneratedPoints`, the pair
`bestKnownCandidates` (`TableGeneration/RecursiveCost/Catalog.lean`) is built
from -- and not the companion's `standardLoweringSetup`. That distinction is the
point of the test. The two are different tables with different width scans and
different recursion thresholds; agreement on the standard table would say
nothing about the programs this benchmark actually ships.

The closed-form column is `forcedPlanGateCount`: the planner's own per-node
charge, `analyzeBalancedProgram`, driven by the companion's stopping rule. The
planner's own rule takes a `min` against the schoolbook base case and the
companion's compiler cannot, so the two answer different questions and disagree
by construction wherever the planner's optimum is not to recurse.
`ChampionLowering.lean` sets this out in full. The `min` column is printed
alongside for that reason, and is not asserted on.

## Running it

Not part of CI: the recursive count is minutes, not milliseconds.

```
lake build
lake env lean --run scripts/tests/ChampionGateCountDifferential.lean
```

about five minutes for the default sweep. To choose the widths:

```
lake env lean --run scripts/tests/ChampionGateCountDifferential.lean --k 2 8 10 12
```

Feasible at `k = 2` and `k = 3` only. The lowered term has
`recursiveCallCount ^ depth` naive leaves -- 3 per level at `k = 2`, 5 at
`k = 3` -- and at `k >= 4` the champion's first recursing width is large enough
that the evaluation does not finish.

A mismatch is a real finding about the cost model and is reported, not
accommodated: the run prints both numbers and exits non-zero.
-/

namespace TableGeneration.RecursiveCost.ChampionDifferential

open TableGeneration.RecursiveCost.Companion

/-- Widths the differential sweeps by default, per arity. Chosen to sit above
each champion's first recursing width (8 at `k = 2`, 20 at `k = 3`) while
keeping the lowered term evaluable. -/
def defaultWidths : Nat → List Nat
  | 2 => [8, 10, 12, 14, 16]
  | 3 => [20, 24]
  | _ => []

structure Row where
  k : Nat
  width : Nat
  childWidth : Nat
  forced : Nat
  planner : Nat
  lowered : Nat

def Row.render (row : Row) : String :=
  let pad (n : Nat) (w : Nat) : String :=
    let s := toString n
    "".pushn ' ' (w - min w s.length) ++ s
  String.intercalate "  "
    [ pad row.k 2, pad row.width 5, pad row.childWidth 6
    , pad row.forced 12, pad row.planner 10, pad row.lowered 12 ]

def header : String :=
  " k  width  child      closed-form   planner-min   lowered-real"

/-- Price one champion at one width both ways and insist the two agree. -/
def checkAt (k : Nat) (hk : k >= 2) (width : Nat) : IO Row := do
  let forced := championForcedPlanGateCount k hk width
  let planner := championMinPlanGateCount k hk width
  let childWidth := championChildWidth k hk width
  match championLoweredGateCount k hk width with
  | .error message =>
      throw (IO.userError
        s!"could not lower the k={k} champion at width {width}: {message}")
  | .ok lowered =>
      if forced != lowered then
        throw (IO.userError <| String.intercalate "\n"
          [ s!"DISAGREEMENT at k={k}, width={width}."
          , s!"  closed form (companion stopping rule) : {forced}"
          , s!"  Shor.LowGate.gateCount of lowerGate    : {lowered}"
          , s!"  planner's own min-rule figure          : {planner}"
          , s!"  child width                            : {childWidth}"
          , s!"reproduce with:"
          , s!"  lake env lean --run scripts/tests/ChampionGateCountDifferential.lean --k {k} {width}"
          , "This is a finding about the cost model. Do not adjust either side "
              ++ "to make it match." ])
      pure { k, width, childWidth, forced, planner, lowered }

def parseNat (raw : String) : IO Nat :=
  match raw.toNat? with
  | some value => pure value
  | none => throw (IO.userError s!"not a width: {raw}")

/-- `--k <k> <width>...`, or nothing for the default sweep. -/
def run (k : Nat) (hk : k >= 2) (widths : List Nat) : IO Nat := do
  let mut checked := 0
  for width in widths do
    let row ← checkAt k hk width
    IO.println row.render
    checked := checked + 1
  pure checked

end TableGeneration.RecursiveCost.ChampionDifferential

open TableGeneration.RecursiveCost.ChampionDifferential

def main (args : List String) : IO Unit := do
  IO.println header
  let checked ←
    match args with
    | "--k" :: rawK :: rawWidths => do
        let k ← parseNat rawK
        let widths ← rawWidths.mapM parseNat
        let widths := if widths.isEmpty then defaultWidths k else widths
        match k with
        | 2 => run 2 (by decide) widths
        | 3 => run 3 (by decide) widths
        | _ =>
            throw (IO.userError
              s!"k={k} is out of reach: the lowered term does not finish above k=3")
    | [] => do
        let atTwo ← run 2 (by decide) (defaultWidths 2)
        let atThree ← run 3 (by decide) (defaultWidths 3)
        pure (atTwo + atThree)
    | _ =>
        throw (IO.userError
          "usage: ChampionGateCountDifferential.lean [--k <k> <width>...]")
  IO.println s!"champion gate-count differential passed: \
{checked} exact matches against Shor.LowGate.gateCount"
