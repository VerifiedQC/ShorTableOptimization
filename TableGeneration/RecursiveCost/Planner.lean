import TableGeneration.RecursiveCost.Catalog

namespace TableGeneration.RecursiveCost

/-- Version attached to every result produced by the default cost model. -/
def modelVersion : String := v3Costs.version

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
def chooseAtWidthWith
    (costs : CostConstants) (candidates : List Candidate) (plans : Array PlanResult)
    (width : Nat) : PlanResult :=
  candidates.foldl (fun current candidate =>
    let analysis := candidate.analyzeWith costs width
    if analysis.childWidth < width then
      match plans[analysis.childWidth]? with
      | some child =>
          lowerGateCount (PlanResult.step width candidate analysis child) current
      | none => current
    else
      current) (PlanResult.base width)

/-- Dense reference recurrence under the `v2` model. -/
def chooseAtWidth
    (candidates : List Candidate) (plans : Array PlanResult)
    (width : Nat) : PlanResult :=
  chooseAtWidthWith v3Costs candidates plans width

/--
Readable dense reference planner for every width through `maxWidth`. The
production entry point `bestPlan` uses the equivalent sparse planner below.
-/
def buildPlanTableWith
    (costs : CostConstants) (candidates : List Candidate) (maxWidth : Nat) :
    Array PlanResult :=
  (List.range (maxWidth + 1)).foldl
    (fun plans width => plans.push (chooseAtWidthWith costs candidates plans width)) #[]

/-- Dense reference planner under the `v2` model. -/
def buildPlanTable
    (candidates : List Candidate) (maxWidth : Nat) : Array PlanResult :=
  buildPlanTableWith v3Costs candidates maxWidth

/-- Minimum-gate plan at `width`, with a direct base-case fallback. -/
def findPlan? (plans : List PlanResult) (width : Nat) : Option PlanResult :=
  plans.find? (fun plan => plan.width == width)

/-- Add every unseen, strictly contracting child of `width` to the worklist. -/
def enqueueContractingChildrenWith
    (costs : CostConstants) (candidates : List Candidate) (width : Nat)
    (seen pending : List Nat) : List Nat :=
  candidates.foldl (fun pending candidate =>
    let childWidth := (candidate.analyzeWith costs width).childWidth
    if childWidth < width &&
        !seen.contains childWidth && !pending.contains childWidth then
      childWidth :: pending
    else
      pending) pending

/-- Worklist traversal bounded by the number of widths no greater than the root. -/
def reachableWidthsAuxWith
    (costs : CostConstants) (candidates : List Candidate) :
    Nat → List Nat → List Nat → List Nat
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, width :: pending, seen =>
      let pending' := enqueueContractingChildrenWith costs candidates width seen pending
      reachableWidthsAuxWith costs candidates fuel pending' (width :: seen)

/-- Widths needed to answer all supplied root queries. -/
def reachableWidthsWith
    (costs : CostConstants) (candidates : List Candidate) (roots : List Nat) : List Nat :=
  let maxWidth := roots.foldl max 0
  reachableWidthsAuxWith costs candidates (maxWidth + 1) roots.eraseDups []

/-- Production recurrence using plans for reachable children only. -/
def chooseAtWidthSparseWith
    (costs : CostConstants) (candidates : List Candidate) (plans : List PlanResult)
    (width : Nat) : PlanResult :=
  candidates.foldl (fun current candidate =>
    let analysis := candidate.analyzeWith costs width
    if analysis.childWidth < width then
      match findPlan? plans analysis.childWidth with
      | some child =>
          lowerGateCount (PlanResult.step width candidate analysis child) current
      | none => current
    else
      current) (PlanResult.base width)

/--
Production planner for widths reachable from `roots`. Sorting them first
preserves the dense reference recurrence without rescanning every intermediate
integer width.
-/
def buildSparsePlansWith
    (costs : CostConstants) (candidates : List Candidate) (roots : List Nat) :
    List PlanResult :=
  (reachableWidthsWith costs candidates roots).mergeSort.foldl
    (fun plans width => chooseAtWidthSparseWith costs candidates plans width :: plans) []

/-- Production planner under the `v2` model. -/
def buildSparsePlans
    (candidates : List Candidate) (roots : List Nat) : List PlanResult :=
  buildSparsePlansWith v3Costs candidates roots

/-- Minimum-gate plan at `width` under a model version. -/
def bestPlanWith
    (costs : CostConstants) (candidates : List Candidate) (width : Nat) : PlanResult :=
  (findPlan? (buildSparsePlansWith costs candidates [width]) width).getD
    (PlanResult.base width)

/-- Minimum-gate plan at `width`, with a direct base-case fallback. -/
def bestPlan (candidates : List Candidate) (width : Nat) : PlanResult :=
  bestPlanWith v3Costs candidates width

/-- Minimum-gate plan using the current promoted PhaseProduct catalog. -/
def bestKnownPlanWith (costs : CostConstants) (width : Nat) : PlanResult :=
  bestPlanWith costs bestKnownCandidates width

/-- Minimum-gate plan using the current promoted PhaseProduct catalog. -/
def bestKnownPlan (width : Nat) : PlanResult :=
  bestKnownPlanWith v3Costs width

end TableGeneration.RecursiveCost
