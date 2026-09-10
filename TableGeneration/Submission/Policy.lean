import TableGeneration.Policy
import TableGeneration.Metrics

namespace TableGeneration.Submission.Policy

open Operations

def generatedPoints (mode : ProductMode) (k : Nat) : List Point :=
  if decide (mode = .PhaseTripleProduct ∧ k = 3) then
    [.int 1, .int 2, .frac 0, .int (-1), .int 0, .int (-2), .int (-4)]
  else
    canonicalPoints mode k

def handles (mode : ProductMode) (k : Nat) : Bool :=
  decide (mode = .PhaseTripleProduct ∧ k = 3)

def generatePointsInOrder
    (mode : ProductMode) (k : Nat) (_hk : k >= 2) : List Point :=
  generatedPoints mode k

def program : Prog 3 :=
  [.addScaled 0 1 false 0, .addScaled 1 0 false 0,
   .addScaled 0 2 false 0, .addScaled 1 2 false 2,
   .phaseProduct 0, .phaseProduct 1, .phaseProduct 2,
   .addScaled 0 1 true 0, .addScaled 0 2 false 1,
   .addScaled 1 0 false 1, .addScaled 0 1 false 0,
   .addScaled 1 2 true 1,
   .phaseProduct 0, .phaseProduct 1,
   .shiftL 0 1, .addScaled 0 1 true 0, .addScaled 0 2 false 1,
   .negate 1, .addScaled 1 0 false 1, .addScaled 1 2 false 3,
   .phaseProduct 0, .phaseProduct 1,
   .addScaled 1 2 true 3, .addScaled 1 0 true 1, .negate 1,
   .addScaled 0 2 true 2, .addScaled 0 1 false 0, .shiftR 0 1,
   .addScaled 1 0 true 0, .addScaled 0 1 false 0]

def generate (mode : ProductMode) (k : Nat) (hk : k >= 2) : Prog k :=
  if htarget : mode = .PhaseTripleProduct ∧ k = 3 then
    htarget.2.symm ▸ program
  else baselineGenerate mode k hk

theorem generatedPoints_valid
    (mode : ProductMode) (k : Nat) (_hk : k >= 2)
    (hhandles : handles mode k = true) :
    ValidPointList mode k (generatedPoints mode k) := by
  have htarget : mode = .PhaseTripleProduct ∧ k = 3 :=
    of_decide_eq_true hhandles
  rcases htarget with ⟨rfl, rfl⟩
  unfold ValidPointList
  decide

theorem generate_safe
    (mode : ProductMode) (k : Nat) (hk : k >= 2)
    (hhandles : handles mode k = true) :
    ValidPointOrder (generatedPoints mode k) (generatePointsInOrder mode k hk) /\
      ProgConsumesPtsSafe (positive_of_ge_two hk) State.start_state
        (generate mode k hk) (generatePointsInOrder mode k hk) := by
  have htarget : mode = .PhaseTripleProduct ∧ k = 3 :=
    of_decide_eq_true hhandles
  rcases htarget with ⟨rfl, rfl⟩
  have hhk : hk = (by decide : 3 >= 2) := Subsingleton.elim _ _
  subst hk
  constructor
  · exact List.Perm.refl _
  · apply progConsumesPtsSafe_of_checks <;> decide

def implementation : GeneratorPolicy where
  generatedPoints := generatedPoints
  handles := handles
  generatePointsInOrder := generatePointsInOrder
  generate := generate
  generatedPoints_valid := generatedPoints_valid
  generate_safe := generate_safe

/-- Direct arithmetic improvement, with the same number of parallel layers. -/
theorem metrics : arithmeticOperationCount program = 23 ∧
    parallelPhaseProductLayerCount program = 3 ∧ phaseProductCount program = 7 := by decide

/-- Register 2 is never even an arithmetic destination. -/
def doesNotWriteRegister2 : Operations.valid_ops 3 → Bool
  | .phaseProduct _ => true
  | .shiftL i _ | .shiftR i _ | .negate i => decide (i ≠ 2)
  | .addScaled dst _ _ _ => decide (dst ≠ 2)
theorem neverWritesRegister2 : program.all doesNotWriteRegister2 = true := by decide

/-- Every prefix executes safely and keeps register 2 equal to its initial row. -/
theorem everyPrefixKeepsRegister2 :
    ∀ n : Fin (program.length + 1),
      ((run? (program.take n.val) State.start_state).map
        (fun s => (List.finRange 3).map (fun j => s 2 j))) = some [0,0,1] := by decide


end TableGeneration.Submission.Policy
