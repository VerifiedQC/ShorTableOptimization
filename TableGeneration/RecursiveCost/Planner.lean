import TableGeneration.RecursiveCost.ArchivedCatalog

namespace TableGeneration.RecursiveCost

/-- Version attached to every result produced by the cost model.

There is one model: the companion's operative `Shor.shorGateCostModel`, taken
from the `Fast_multiplication` dependency at the revision `lake-manifest.json`
pins. The string is retained because archived plan output carries it, so a
future companion cost-model change cannot silently reinterpret old estimates. -/
def modelVersion : String := "forshor-phase-product-gates-v3"

/-- Stable machine-readable optimization objective. -/
def objective : String := "logical_gate_count"

/-- The local recursive choice retained as a compact plan backpointer. -/
structure StepChoice where
  policyId : String
  k : Nat
  childWidth : Nat
  localArithmeticGateCount : Nat
  localArithmeticOperationCount : Nat
  recursiveCallCount : Nat
deriving Repr, DecidableEq

/-- Minimum-gate summary for one balanced PhaseProduct input width. -/
structure PlanResult where
  width : Nat
  gateCount : Nat
  recursionHeight : Nat
  totalRecursiveCallCount : Nat
  totalArithmeticOperationCount : Nat
  choice : Option StepChoice
deriving Repr, DecidableEq

namespace PlanResult

/-- Direct schoolbook PhaseProduct at one width. -/
def base (width : Nat) : PlanResult where
  width
  gateCount := directSignedPhaseProductGateCount width width
  recursionHeight := 0
  totalRecursiveCallCount := 0
  totalArithmeticOperationCount := 0
  choice := none

/-- Compose one recursive table program with its already optimized child. -/
def step
    (width : Nat) (candidate : Candidate) (analysis : ProgramAnalysis)
    (child : PlanResult) : PlanResult :=
  let calls := analysis.recursiveCallCount
  { width
    gateCount := analysis.arithmeticGateCount + calls * child.gateCount
    recursionHeight := child.recursionHeight + 1
    totalRecursiveCallCount := calls * (child.totalRecursiveCallCount + 1)
    totalArithmeticOperationCount :=
      analysis.arithmeticOperationCount +
        calls * child.totalArithmeticOperationCount
    choice := some
      { policyId := candidate.policyId
        k := candidate.k
        childWidth := analysis.childWidth
        localArithmeticGateCount := analysis.arithmeticGateCount
        localArithmeticOperationCount := analysis.arithmeticOperationCount
        recursiveCallCount := calls } }

end PlanResult

/-- Keep the existing plan on a gate-count tie for deterministic selection. -/
def lowerGateCount (candidate current : PlanResult) : PlanResult :=
  if candidate.gateCount < current.gateCount then candidate else current

/--
Dense reference recurrence under a chosen model version: choose the
minimum-gate plan for `width` from children already computed at every smaller
width. Noncontracting recursive candidates are rejected.
-/
def chooseAtWidth
    (candidates : List Candidate) (plans : Array PlanResult)
    (width : Nat) : PlanResult :=
  candidates.foldl (fun current candidate =>
    let analysis := candidate.analyze width
    if analysis.childWidth < width then
      match plans[analysis.childWidth]? with
      | some child =>
          lowerGateCount (PlanResult.step width candidate analysis child) current
      | none => current
    else
      current) (PlanResult.base width)

/--
Readable dense reference planner for every width through `maxWidth`. The
production entry point `bestPlan` uses the equivalent sparse planner below.
-/
def buildPlanTable
    (candidates : List Candidate) (maxWidth : Nat) :
    Array PlanResult :=
  (List.range (maxWidth + 1)).foldl
    (fun plans width => plans.push (chooseAtWidth candidates plans width)) #[]

/-- Minimum-gate plan at `width`, with a direct base-case fallback. -/
def findPlan? (plans : List PlanResult) (width : Nat) : Option PlanResult :=
  plans.find? (fun plan => plan.width == width)

/--
Add every strictly contracting child of `width` that is not already queued.

`queued` marks a width the moment it enters the worklist, so membership is an
array read rather than a scan of two lists. Every reachable width is no greater
than the largest root, so the width itself indexes the array.
-/
def enqueueContractingChildren
    (candidates : List Candidate) (width : Nat)
    (queued : Array Bool) (pending : List Nat) : Array Bool × List Nat :=
  candidates.foldl (fun (state : Array Bool × List Nat) candidate =>
    let (queued, pending) := state
    let childWidth := (candidate.analyze width).childWidth
    if childWidth < width && !queued.getD childWidth true then
      (queued.set! childWidth true, childWidth :: pending)
    else
      (queued, pending)) (queued, pending)

/-- Worklist traversal bounded by the number of widths no greater than the root. -/
def reachableWidthsAux
    (candidates : List Candidate) :
    Nat → List Nat → Array Bool → List Nat → List Nat
  | 0, _, _, seen => seen
  | _ + 1, [], _, seen => seen
  | fuel + 1, width :: pending, queued, seen =>
      let (queued', pending') :=
        enqueueContractingChildren candidates width queued pending
      reachableWidthsAux candidates fuel pending' queued' (width :: seen)

/--
Widths needed to answer all supplied root queries.

Only the set matters: `buildSparsePlans` sorts the result before using it.
-/
def reachableWidths
    (candidates : List Candidate) (roots : List Nat) : List Nat :=
  let maxWidth := roots.foldl max 0
  let roots := roots.eraseDups
  let queued :=
    roots.foldl (fun (queued : Array Bool) root => queued.set! root true)
      (Array.replicate (maxWidth + 1) false)
  reachableWidthsAux candidates (maxWidth + 1) roots queued []

/-- Production recurrence using plans for reachable children only. -/
def chooseAtWidthSparse
    (candidates : List Candidate) (plans : List PlanResult)
    (width : Nat) : PlanResult :=
  candidates.foldl (fun current candidate =>
    let analysis := candidate.analyze width
    if analysis.childWidth < width then
      match findPlan? plans analysis.childWidth with
      | some child =>
          lowerGateCount (PlanResult.step width candidate analysis child) current
      | none => current
    else
      current) (PlanResult.base width)

/-- `chooseAtWidthSparse` against a table indexed by width rather than a list. -/
def chooseAtWidthTable
    (candidates : List Candidate) (plans : Array (Option PlanResult))
    (width : Nat) : PlanResult :=
  candidates.foldl (fun current candidate =>
    let analysis := candidate.analyze width
    if analysis.childWidth < width then
      match plans.getD analysis.childWidth none with
      | some child =>
          lowerGateCount (PlanResult.step width candidate analysis child) current
      | none => current
    else
      current) (PlanResult.base width)

/--
Production planner for widths reachable from `roots`. Sorting them first
preserves the dense reference recurrence without rescanning every intermediate
integer width.

Solved widths are held in an array indexed by width, not in a list. A child
lookup is the inner loop of the recurrence, run once per candidate per width,
so a linear scan made the planner quadratic in the number of reachable widths.
`checkDenseSparseAgreement` in the oracle compares this against the dense
reference planner, which is what holds the two in step.
-/
def buildSparsePlans
    (candidates : List Candidate) (roots : List Nat) :
    List PlanResult :=
  let widths := (reachableWidths candidates roots).mergeSort
  let size := widths.foldl max 0 + 1
  let table :=
    widths.foldl (fun (plans : Array (Option PlanResult)) width =>
      plans.set! width (some (chooseAtWidthTable candidates plans width)))
      (Array.replicate size none)
  widths.foldl (fun solved width =>
    match table.getD width none with
    | some plan => plan :: solved
    | none => solved) []

/-- Minimum-gate plan at `width` under a model version. -/
def bestPlan
    (candidates : List Candidate) (width : Nat) : PlanResult :=
  (findPlan? (buildSparsePlans candidates [width]) width).getD
    (PlanResult.base width)

/--
Minimum-gate plan over every accepted `PhaseProduct` table.

The search set is `archivedCandidates`, not `bestKnownCandidates`. Champions are
selected by the leaderboard's structural weighted cost; this planner minimises
gate count. Those are different objectives, so restricting the search to
champions can discard the cheapest table at a width.
-/
def bestKnownPlan (width : Nat) : PlanResult :=
  bestPlan archivedCandidates width

end TableGeneration.RecursiveCost
