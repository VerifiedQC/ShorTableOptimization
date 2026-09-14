import TableGeneration.RecursiveCost.Correctness

namespace TableGeneration.RecursiveCost.TestOracle

open Operations

/-- Small independent policy used to compare the Lean and JavaScript planners. -/
def binaryCandidate : Candidate where
  policyId := "test-binary"
  k := 2
  hk := by decide
  program :=
    [ .phaseProduct ⟨0, by decide⟩
    , .phaseProduct ⟨1, by decide⟩ ]

/-- Short program covering every width transition used by the fast scan. -/
def transitionCandidate : Candidate where
  policyId := "test-transitions"
  k := 3
  hk := by decide
  program :=
    [ .shiftL ⟨0, by decide⟩ 3
    , .shiftR ⟨1, by decide⟩ 2
    , .negate ⟨2, by decide⟩
    , .addScaled ⟨0, by decide⟩ ⟨2, by decide⟩ false 4
    , .addScaled ⟨2, by decide⟩ ⟨1, by decide⟩ true 1
    , .phaseProduct ⟨0, by decide⟩ ]

def planLine (plan : PlanResult) : String :=
  let choice := match plan.choice with
    | none => "base"
    | some selected =>
        s!"{selected.k}:{selected.childWidth}:{selected.policyId}"
  String.intercalate "\t"
    [ toString plan.width
    , toString plan.gateCount
    , toString plan.recursionHeight
    , toString plan.totalRecursiveCallCount
    , toString plan.totalArithmeticOperationCount
    , choice ]

def operationText {k : Nat} : valid_ops k → String
  | .shiftL index amount => s!"shiftL,{index.val},{amount}"
  | .shiftR index amount => s!"shiftR,{index.val},{amount}"
  | .negate index => s!"negate,{index.val}"
  | .addScaled destination source negative shift =>
      let sign := if negative then "-1" else "1"
      s!"addScaled,{destination.val},{source.val},{sign},{shift}"
  | .phaseProduct index => s!"phaseProduct,{index.val}"

def candidateLine (candidate : Candidate) : String :=
  String.intercalate "\t"
    [ "candidate"
    , candidate.policyId
    , toString candidate.k
    , String.intercalate ";" (candidate.program.map operationText) ]

def referenceLine (candidate : Candidate) (width : Nat) : String :=
  String.intercalate "\t"
    [ "reference"
    , candidate.policyId
    , toString width
    , toString (nextBalancedSignedWidth width candidate.program)
    , toString (nextSignedWidth width width candidate.program) ]

def parseWidth (raw : String) : IO Nat :=
  match raw.toNat? with
  | some width => pure width
  | none => throw (IO.userError s!"invalid test width: {raw}")

/-- Resolve a `--model=<name>` selector to its cost constants. -/
def parseCosts (raw : String) : IO CostConstants :=
  if raw = "v2" then pure v2Costs
  else if raw = "v3" then pure v3Costs
  else if raw = "v3-loose4kw" then pure v3LooseCosts
  else throw (IO.userError s!"unknown cost model: {raw}")

/-- Split a leading `--model=<name>` argument from the remaining arguments. -/
def takeModel (args : List String) : IO (CostConstants × List String) :=
  match args with
  | arg :: rest =>
      if arg.startsWith "--model=" then do
        let costs ← parseCosts (arg.drop "--model=".length).toString
        pure (costs, rest)
      else pure (v2Costs, args)
  | [] => pure (v2Costs, args)

def printPlans (costs : CostConstants)
    (candidates : List Candidate) (rawWidths : List String) : IO Unit := do
  let widths ← rawWidths.mapM parseWidth
  let plans := buildSparsePlansWith costs candidates widths
  for width in widths do
    IO.println (planLine ((findPlan? plans width).getD (PlanResult.base width)))

def checkDenseSparseAgreement (costs : CostConstants)
    (label : String) (candidates : List Candidate) (widths : List Nat) : IO Unit := do
  let maxWidth := widths.foldl max 0
  let dense := buildPlanTableWith costs candidates maxWidth
  let sparse := buildSparsePlansWith costs candidates widths
  for width in widths do
    if dense[width]? = findPlan? sparse width then
      pure ()
    else
      throw (IO.userError s!"dense/sparse mismatch for {label} at width {width}")

end TableGeneration.RecursiveCost.TestOracle

open TableGeneration.RecursiveCost
open TableGeneration.RecursiveCost.TestOracle

def main (rawArgs : List String) : IO Unit := do
  let (costs, args) ← takeModel rawArgs
  match args with
  | "--catalog" :: _ =>
      for candidate in bestKnownCandidates do
        IO.println (candidateLine candidate)
  | "--best-known" :: rawWidths =>
      printPlans costs bestKnownCandidates rawWidths
  | "--reference" :: rawWidths =>
      for raw in rawWidths do
        let width ← parseWidth raw
        IO.println (referenceLine binaryCandidate width)
        IO.println (referenceLine transitionCandidate width)
  | "--dense-sparse" :: rawWidths =>
      let widths ← rawWidths.mapM parseWidth
      checkDenseSparseAgreement costs "binary" [binaryCandidate] widths
      checkDenseSparseAgreement costs "transitions" [transitionCandidate] widths
      checkDenseSparseAgreement costs "combined" [binaryCandidate, transitionCandidate] widths
      checkDenseSparseAgreement costs "best-known" bestKnownCandidates widths
      IO.println "dense/sparse agreement passed"
  | rawWidths =>
      printPlans costs [binaryCandidate] rawWidths
