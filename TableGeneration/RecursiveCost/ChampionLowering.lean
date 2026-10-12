import TableGeneration.RecursiveCost.Catalog
import TableGeneration.RecursiveCost.CompanionTransport
import FastMultiplication.ShorVerification.Implementation.Shor.Lowering.LowerGate
import FastMultiplication.Emit.Lower.Registers
import FastMultiplication.Emit.Lower.Decide

/-!
# Pricing a promoted champion through the companion's recursive lowering

The planner reports a closed form. The companion can instead *compile* a table
to a `LowGate` tree and count it:
`Shor.LowGate.gateCount Shor.shorGateCostModel (Shor.lowerGate ...)`. That is the
expensive oracle, and this file is the route to it for a program this repository
actually promoted, rather than for the companion's own standard table.

Running the two side by side is the differential in
`scripts/tests/ChampionGateCountDifferential.lean`. Nothing here is imported by
`TableGeneration.lean`'s transitive graph for its own sake -- `Correctness.lean`
imports it only so `lake build` typechecks it.

## The two stopping rules, which is the whole subtlety

The planner and the companion's compiler answer different questions, and a naive
comparison of their outputs disagrees for a reason that is not an error.

`Shor.PhaseLoweringPlan` recurses on exactly one condition. Its `signedBase`
constructor carries `hstop : ¬ nextSignedWidth x z ops < initSize` and its
`signedStep` carries `hrec : nextSignedWidth x z ops < initSize`. There is no
cost comparison anywhere: the compiler recurses whenever the table strictly
contracts the operand width, whatever that costs.

`RecursiveCost.chooseAtWidth` folds candidates starting from
`PlanResult.base width`, keeping the lower gate count. It is entitled to decline
to recurse and report the schoolbook base case, and at small widths it usually
should -- at `k = 2, n = 16` the champion's base case is 1280 against 28529 for
the recursion.

So the planner's number is the cheapest *policy* at that width, and the
companion's is what *this table* compiles to. They coincide exactly when the
planner's optimum is to recurse. To compare the arithmetic rather than the
choice, `forcedPlanGateCount` below is the planner's own per-node charge
(`analyzeBalancedProgram`, unmodified) driven by the companion's stopping rule.
`minPlanGateCount` is the planner's rule, kept alongside so the size of the gap
is visible rather than hidden.
-/

namespace TableGeneration.RecursiveCost.Companion

/-! ## The closed form, under each stopping rule

Both recurrences charge `analyzeBalancedProgram`, which is the planner's own
per-node analysis: `phaseProgramOverhead` at the child width plus
`signExtensionAllocationGateCount`, with `recursiveCallCount` children. Neither
reimplements it. They differ only in when they stop. -/

/-- The planner's per-node charge under the **companion's** stopping rule:
recurse whenever the width strictly contracts, with no comparison against the
base case. This is the quantity comparable to `championLoweredGateCount`.

`fuel` bounds the descent; any `fuel` at least the width is enough, because each
step strictly contracts. -/
def forcedPlanGateCount {k : Nat} (ops : Prog k) : Nat → Nat → Nat
  | 0, width => directSignedPhaseProductGateCount width width
  | fuel + 1, width =>
      let analysis := analyzeBalancedProgram width ops
      if analysis.childWidth < width then
        analysis.arithmeticGateCount +
          analysis.recursiveCallCount * forcedPlanGateCount ops fuel analysis.childWidth
      else
        directSignedPhaseProductGateCount width width

/-- The same per-node charge under the **planner's** stopping rule: take the
base case whenever recursing is dearer. This is `chooseAtWidth` restricted to a
single candidate, and it is what `bestKnownPlan` would report if this champion
were the only one in the catalog. -/
def minPlanGateCount {k : Nat} (ops : Prog k) : Nat → Nat → Nat
  | 0, width => directSignedPhaseProductGateCount width width
  | fuel + 1, width =>
      let base := directSignedPhaseProductGateCount width width
      let analysis := analyzeBalancedProgram width ops
      if analysis.childWidth < width then
        let recursed :=
          analysis.arithmeticGateCount +
            analysis.recursiveCallCount * minPlanGateCount ops fuel analysis.childWidth
        if recursed < base then recursed else base
      else
        base

/-! ## The companion's recursive count -/

/-- What `Shor.lowerGate` emits for one balanced signed phase product at width
`n`, counted under the operative `Shor.shorGateCostModel`.

`Shor.ppRegisters` builds the two concrete `ExtReg`s with reserve sized by
`Shor.RecursivePhaseWorkspace.reserveNeed`, exactly as the companion's own
`forshor_emit pp` CLI does, so this figure is the one that command prints. Both
side conditions are discharged by decision rather than by proof, and both are
reported as errors rather than silently defaulted:

* `hpts : pts.length = Shor.q k` -- the point count the lowering record demands;
* `Shor.SignedRecursiveWorkspaceOK` -- the static register-layout claim that
  `Shor.GateWorkspaceOK` reduces to for `Gate.SignedPhaseProd`.

The `phi` argument is the rotation angle. It is carried through into the emitted
`Phase` gates and does not change how many gates there are, so the differential
fixes it at `1` (that is, `π`), which is what `forshor_emit pp k n 1` uses. -/
def loweredPhaseProductGateCount (k : Nat) (hk : k >= 2)
    (ops : Prog k) (pts : List Operations.Point) (n : Nat) (phi : Shor.Angle) :
    Except String Nat :=
  let companionOps := toCompanionProg ops
  let companionPts := toCompanionPoints pts
  if hpts : companionPts.length = Shor.q k then
    match Shor.ppRegisters companionOps n with
    | .error message => .error message
    | .ok (x, z, _ctrl) =>
        if hworkspace : Shor.SignedRecursiveWorkspaceOK companionOps x z then
          .ok (Shor.LowGate.gateCount Shor.shorGateCostModel
            (Shor.lowerGate k hk companionOps companionPts hpts
              (Shor.Gate.SignedPhaseProd phi x z) hworkspace))
        else
          .error s!"SignedRecursiveWorkspaceOK fails for k={k} at width {n}"
  else
    .error s!"point count {companionPts.length} is not q {k} = {Shor.q k}"

/-- The promoted PhaseProduct champion at arity `k`, priced through the
companion's recursive lowering at balanced width `n`.

This is the archived program and its archived points -- `bestKnownGenerate` and
`bestKnownGeneratedPoints`, the same pair `bestKnownCandidates` is built from --
and deliberately **not** the companion's `standardLoweringSetup`. The two are
different tables with different width scans, so a measurement on the standard
table says nothing about a champion. -/
def championLoweredGateCount (k : Nat) (hk : k >= 2) (n : Nat)
    (phi : Shor.Angle := 1) : Except String Nat :=
  loweredPhaseProductGateCount k hk
    (bestKnownGenerate .PhaseProduct k hk)
    (bestKnownGeneratedPoints .PhaseProduct k) n phi

/-- The champion's closed-form cost under the companion's stopping rule, at
balanced width `n`. Comparable, digit for digit, to
`championLoweredGateCount`. -/
def championForcedPlanGateCount (k : Nat) (hk : k >= 2) (n : Nat) : Nat :=
  forcedPlanGateCount (bestKnownGenerate .PhaseProduct k hk) (n + 1) n

/-- The champion's closed-form cost under the planner's own stopping rule. -/
def championMinPlanGateCount (k : Nat) (hk : k >= 2) (n : Nat) : Nat :=
  minPlanGateCount (bestKnownGenerate .PhaseProduct k hk) (n + 1) n

/-- The width the champion's table contracts a balanced `n`-bit node to. Below
the width at which this is `< n`, the companion emits the naive leaf and both
closed forms report `5 * n * n`. -/
def championChildWidth (k : Nat) (hk : k >= 2) (n : Nat) : Nat :=
  nextBalancedSignedWidth n (bestKnownGenerate .PhaseProduct k hk)

end TableGeneration.RecursiveCost.Companion
