import TableGeneration.Policy

namespace TableGeneration.Policies.Accepted.P546fea33a7a4
open Operations

/-- Mixed integer and reciprocal evaluation points, with exact restoration. -/
def programK4 : Prog 4 :=
  [.shiftL 2 2,
   .addScaled 2 0 false 0,
   .shiftL 3 3,
   .addScaled 3 1 false 1,
   .addScaled 3 2 false 0,
   .shiftL 2 1,
   .addScaled 2 3 true 0,
   .phaseProduct 0,
   .phaseProduct 3,
   .phaseProduct 2,
   .addScaled 2 3 false 0,
   .shiftR 2 1,
   .addScaled 3 1 true 1,
   .addScaled 3 2 true 0,
   .shiftR 3 3,
   .addScaled 2 0 true 0,
   .shiftR 2 2,
   .shiftL 0 6,
   .shiftL 1 4,
   .addScaled 1 3 false 0,
   .addScaled 0 1 false 0,
   .addScaled 0 2 false 2,
   .shiftL 1 1,
   .addScaled 1 0 true 0,
   .phaseProduct 0,
   .phaseProduct 1,
   .addScaled 1 0 false 0,
   .shiftR 1 1,
   .addScaled 0 2 true 2,
   .addScaled 0 1 true 0,
   .addScaled 1 3 true 0,
   .shiftR 1 4,
   .shiftR 0 6,
   .addScaled 0 2 false 0,
   .addScaled 1 3 false 0,
   .addScaled 1 0 false 0,
   .shiftL 0 1,
   .addScaled 0 1 true 0,
   .phaseProduct 1,
   .phaseProduct 0,
   .addScaled 0 1 false 0,
   .shiftR 0 1,
   .addScaled 1 3 true 0,
   .addScaled 1 0 true 0,
   .addScaled 0 2 true 0]

def generatedPoints (_mode : ProductMode) (_k : Nat) : List Point :=
  [.int 0, .int 2, .int (-2), .frac 4, .frac (-4), .int 1, .int (-1)]

def handles (mode : ProductMode) (k : Nat) : Bool :=
  match mode with
  | .PhaseProduct => decide (k = 4)
  | .PhaseTripleProduct => false

def generatePointsInOrder (mode : ProductMode) (k : Nat) (_hk : k >= 2) :=
  generatedPoints mode k

def generate (mode : ProductMode) (k : Nat) (hk : k >= 2) : Prog k :=
  if h6 : k = 4 then h6.symm ▸ programK4
  else baselineGenerate mode k hk

theorem generatedPoints_valid (mode : ProductMode) (k : Nat) (_hk : k >= 2)
    (hhandles : handles mode k = true) :
    ValidPointList mode k (generatedPoints mode k) := by
  cases mode with
  | PhaseTripleProduct => simp [handles] at hhandles
  | PhaseProduct =>
    have h : k = 4 := by simpa [handles] using hhandles
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
    have h : k = 4 := by simpa [handles] using hhandles
    subst k
    have hhk : hk = (by decide : 4 >= 2) := Subsingleton.elim _ _
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

end TableGeneration.Policies.Accepted.P546fea33a7a4
