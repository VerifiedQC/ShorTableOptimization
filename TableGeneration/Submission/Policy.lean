import TableGeneration.Policy

namespace TableGeneration.Submission.Policy
open Operations

/-- Mixed integer and reciprocal evaluation points, with exact restoration. -/
def programK6 : Prog 6 :=
  [.addScaled 2 0 false 0,
   .addScaled 2 4 false 0,
   .addScaled 1 3 false 0,
   .addScaled 1 5 false 0,
   .addScaled 1 2 false 0,
   .shiftL 2 1,
   .addScaled 2 1 true 0,
   .phaseProduct 0,
   .phaseProduct 5,
   .phaseProduct 1,
   .phaseProduct 2,
   .addScaled 2 1 false 0,
   .shiftR 2 1,
   .addScaled 1 5 true 0,
   .addScaled 1 2 true 0,
   .addScaled 1 3 true 0,
   .addScaled 2 4 true 0,
   .addScaled 2 0 true 0,
   .shiftL 4 4,
   .addScaled 4 0 false 0,
   .addScaled 4 2 false 2,
   .shiftL 5 4,
   .addScaled 5 3 false 2,
   .addScaled 5 1 false 0,
   .shiftL 5 1,
   .addScaled 5 4 false 0,
   .shiftL 4 1,
   .addScaled 4 5 true 0,
   .phaseProduct 5,
   .phaseProduct 4,
   .addScaled 4 5 false 0,
   .shiftR 4 1,
   .addScaled 5 4 true 0,
   .shiftR 5 1,
   .addScaled 5 1 true 0,
   .addScaled 5 3 true 2,
   .shiftR 5 4,
   .addScaled 4 2 true 2,
   .addScaled 4 0 true 0,
   .shiftR 4 4,
   .shiftL 2 2,
   .addScaled 2 0 false 4,
   .addScaled 2 4 false 0,
   .shiftL 3 2,
   .addScaled 3 5 false 0,
   .addScaled 3 1 false 4,
   .shiftL 2 1,
   .addScaled 2 3 false 0,
   .shiftL 3 1,
   .addScaled 3 2 true 0,
   .phaseProduct 2,
   .phaseProduct 3,
   .addScaled 3 2 false 0,
   .shiftR 3 1,
   .addScaled 2 3 true 0,
   .shiftR 2 1,
   .addScaled 3 1 true 4,
   .addScaled 3 5 true 0,
   .shiftR 3 2,
   .addScaled 2 4 true 0,
   .addScaled 2 0 true 4,
   .shiftR 2 2,
   .shiftL 4 8,
   .addScaled 4 0 false 0,
   .addScaled 4 2 false 4,
   .shiftL 5 8,
   .addScaled 5 1 false 0,
   .addScaled 5 3 false 4,
   .shiftL 5 2,
   .addScaled 5 4 false 0,
   .shiftL 4 1,
   .addScaled 4 5 true 0,
   .phaseProduct 5,
   .phaseProduct 4,
   .addScaled 4 5 false 0,
   .shiftR 4 1,
   .addScaled 5 4 true 0,
   .shiftR 5 2,
   .addScaled 5 3 true 4,
   .addScaled 5 1 true 0,
   .shiftR 5 8,
   .addScaled 4 2 true 4,
   .addScaled 4 0 true 0,
   .shiftR 4 8,
   .addScaled 5 1 false 8,
   .addScaled 5 3 false 4,
   .addScaled 5 0 false 10,
   .addScaled 5 2 false 6,
   .addScaled 5 4 false 2,
   .phaseProduct 5,
   .addScaled 5 2 true 6,
   .addScaled 5 4 true 2,
   .addScaled 5 3 true 4,
   .addScaled 5 1 true 8,
   .addScaled 5 0 true 10]

def generatedPoints (_mode : ProductMode) (_k : Nat) : List Point :=
  [.int 0, .frac 0, .int 1, .int (-1), .int 2, .int (-2), .frac 2, .frac (-2), .int 4, .int (-4), .frac 4]

def handles (mode : ProductMode) (k : Nat) : Bool :=
  match mode with
  | .PhaseProduct => decide (k = 6)
  | .PhaseTripleProduct => false

def generatePointsInOrder (mode : ProductMode) (k : Nat) (_hk : k >= 2) :=
  generatedPoints mode k

def generate (mode : ProductMode) (k : Nat) (hk : k >= 2) : Prog k :=
  if h6 : k = 6 then h6.symm ▸ programK6
  else baselineGenerate mode k hk

theorem generatedPoints_valid (mode : ProductMode) (k : Nat) (_hk : k >= 2)
    (hhandles : handles mode k = true) :
    ValidPointList mode k (generatedPoints mode k) := by
  cases mode with
  | PhaseTripleProduct => simp [handles] at hhandles
  | PhaseProduct =>
    have h : k = 6 := by simpa [handles] using hhandles
    subst k
    unfold ValidPointList generatedPoints
    decide

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem generate_safe (mode : ProductMode) (k : Nat) (hk : k >= 2)
    (hhandles : handles mode k = true) :
    ValidPointOrder (generatedPoints mode k) (generatePointsInOrder mode k hk) ∧
      ProgConsumesPtsSafe (positive_of_ge_two hk) State.start_state
        (generate mode k hk) (generatePointsInOrder mode k hk) := by
  cases mode with
  | PhaseTripleProduct => simp [handles] at hhandles
  | PhaseProduct =>
    have h : k = 6 := by simpa [handles] using hhandles
    subst k
    have hhk : hk = (by decide : 6 >= 2) := Subsingleton.elim _ _
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

end TableGeneration.Submission.Policy
