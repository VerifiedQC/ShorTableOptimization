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

/-- Accept and discard a `--model=<name>` selector.

There is one cost model now -- the companion's operative `shorGateCostModel`.
The flag is still accepted, and still rejects anything but the current version
string, so an old invocation naming a retired model fails loudly instead of
silently being reinterpreted. -/
def parseModel (raw : String) : IO Unit :=
  if raw = "v3" || raw = modelVersion then pure ()
  else throw (IO.userError
    s!"unknown cost model: {raw} (the only model is {modelVersion}; \
       v2 mirrored the companion's deleted phaseProductCostModel)")

/-- Split a leading `--model=<name>` argument from the remaining arguments. -/
def takeModel (args : List String) : IO (List String) :=
  match args with
  | arg :: rest =>
      if arg.startsWith "--model=" then do
        parseModel (arg.drop "--model=".length).toString
        pure rest
      else pure args
  | [] => pure args

def printPlans
    (candidates : List Candidate) (rawWidths : List String) : IO Unit := do
  let widths ← rawWidths.mapM parseWidth
  let plans := buildSparsePlans candidates widths
  for width in widths do
    IO.println (planLine ((findPlan? plans width).getD (PlanResult.base width)))

def checkDenseSparseAgreement
    (label : String) (candidates : List Candidate) (widths : List Nat) : IO Unit := do
  let maxWidth := widths.foldl max 0
  let dense := buildPlanTable candidates maxWidth
  let sparse := buildSparsePlans candidates widths
  for width in widths do
    if dense[width]? = findPlan? sparse width then
      pure ()
    else
      throw (IO.userError s!"dense/sparse mismatch for {label} at width {width}")

/--
Check the evaluation-oriented array width scan against the companion's own
scan.

`nextBalancedSignedWidth` is this project's optimization: the companion threads
`Function.update` chains, which are far too slow to drive a planner over
thousands of widths, so balanced operands are scanned in a flat array instead.
Nothing in the type system ties the two together, and the planner uses the fast
one, so the agreement is checked here against the companion's definition applied
to canonical registers of the same width.
-/
def checkWidthScanAgreement (widths : List Nat) : IO Unit := do
  for width in widths do
    for candidate in bestKnownCandidates do
      let fast := nextBalancedSignedWidth width candidate.program
      let spec :=
        ForShor.nextSignedWidth (ForShor.canonicalExtReg width)
          (ForShor.canonicalExtReg width) candidate.program
      if fast != spec then
        throw (IO.userError
          s!"width scan mismatch at width {width}, k={candidate.k}: \
             array={fast} companion={spec}")

end TableGeneration.RecursiveCost.TestOracle

open TableGeneration.RecursiveCost
open TableGeneration.RecursiveCost.TestOracle

def main (rawArgs : List String) : IO Unit := do
  let args ← takeModel rawArgs
  match args with
  | "--catalog" :: _ =>
      for candidate in bestKnownCandidates do
        IO.println (candidateLine candidate)
  | "--best-known" :: rawWidths =>
      printPlans bestKnownCandidates rawWidths
  | "--reference" :: rawWidths =>
      for raw in rawWidths do
        let width ← parseWidth raw
        IO.println (referenceLine binaryCandidate width)
        IO.println (referenceLine transitionCandidate width)
  | "--width-scan" :: rawWidths =>
      let widths ← rawWidths.mapM parseWidth
      checkWidthScanAgreement widths
      IO.println "width scan agreement passed"
  | "--dense-sparse" :: rawWidths =>
      let widths ← rawWidths.mapM parseWidth
      checkDenseSparseAgreement "binary" [binaryCandidate] widths
      checkDenseSparseAgreement "transitions" [transitionCandidate] widths
      checkDenseSparseAgreement "combined" [binaryCandidate, transitionCandidate] widths
      checkDenseSparseAgreement "best-known" bestKnownCandidates widths
      IO.println "dense/sparse agreement passed"
  | rawWidths =>
      printPlans [binaryCandidate] rawWidths
