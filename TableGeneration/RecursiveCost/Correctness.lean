import TableGeneration.RecursiveCost.Planner

namespace TableGeneration.RecursiveCost

open Operations

/-!
# Recursive-cost model invariants

These lemmas cover the executable model's local accounting and deterministic
minimum selection. They do not claim that ForShor's abstract gate model is a
hardware resource estimate.
-/

/-! The width scan is the companion's, so its slot-update lemmas are Mathlib's
`Function.update_self` / `Function.update_of_ne`. Only the transition that is
specific to this language needs restating. -/

@[simp] theorem updateWidthState_phaseProduct {k : Nat}
    (state : ForShor.WidthState k) (index : Fin k) :
    ForShor.updateWidthState state (.phaseProduct index) = state := by
  rfl

@[simp] theorem phaseProgramOverhead_nil {k : Nat} (workingWidth : Nat) :
    phaseProgramOverhead (k := k) workingWidth [] = 0 := by
  rfl

@[simp] theorem phaseProgramOverhead_cons {k : Nat}
    (workingWidth : Nat) (op : valid_ops k) (ops : Prog k) :
    phaseProgramOverhead workingWidth (op :: ops) =
      phaseArithmeticOpCost workingWidth op +
        phaseProgramOverhead workingWidth ops := by
  rfl

@[simp] theorem analyzeProgram_childWidth {k : Nat}
    (xWidth zWidth : Nat) (ops : Prog k) :
    (analyzeProgram xWidth zWidth ops).childWidth =
      nextSignedWidth xWidth zWidth ops := by
  rfl

theorem analyzeProgram_childWidth_pos {k : Nat}
    (xWidth zWidth : Nat) (ops : Prog k) :
    0 < (analyzeProgram xWidth zWidth ops).childWidth := by
  exact nextSignedWidth_pos xWidth zWidth ops

@[simp] theorem PlanResult.base_gateCount (width : Nat) :
    (PlanResult.base width).gateCount = 5 * width * width := by
  rfl

@[simp] theorem PlanResult.base_choice (width : Nat) :
    (PlanResult.base width).choice = none := by
  rfl

@[simp] theorem PlanResult.step_gateCount
    (width : Nat) (candidate : Candidate) (analysis : ProgramAnalysis)
    (child : PlanResult) :
    (PlanResult.step width candidate analysis child).gateCount =
      analysis.arithmeticGateCount +
        analysis.recursiveCallCount * child.gateCount := by
  rfl

@[simp] theorem PlanResult.step_recursionHeight
    (width : Nat) (candidate : Candidate) (analysis : ProgramAnalysis)
    (child : PlanResult) :
    (PlanResult.step width candidate analysis child).recursionHeight =
      child.recursionHeight + 1 := by
  rfl

theorem lowerGateCount_gateCount_le_current
    (candidate current : PlanResult) :
    (lowerGateCount candidate current).gateCount ≤ current.gateCount := by
  by_cases h : candidate.gateCount < current.gateCount
  · simp [lowerGateCount, h, Nat.le_of_lt h]
  · simp [lowerGateCount, h]

theorem lowerGateCount_gateCount_le_candidate
    (candidate current : PlanResult) :
    (lowerGateCount candidate current).gateCount ≤ candidate.gateCount := by
  by_cases h : candidate.gateCount < current.gateCount
  · simp [lowerGateCount, h]
  · simp [lowerGateCount, h, Nat.le_of_not_gt h]

theorem lowerGateCount_tie_keeps_current
    (candidate current : PlanResult)
    (h : candidate.gateCount = current.gateCount) :
    lowerGateCount candidate current = current := by
  simp [lowerGateCount, h]

end TableGeneration.RecursiveCost
