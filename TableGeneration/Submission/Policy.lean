import TableGeneration.Policy

namespace TableGeneration.Submission.Policy

open Operations

/-- Reorder commuting additions to reduce the running width maximum without
changing evaluation points, arithmetic count, or phase-product layers. -/
def programK3 : Prog 3 :=
  [.addScaled 1 0 false 0, .addScaled 1 2 false 0,
   .phaseProduct 0, .phaseProduct 1, .phaseProduct 2,
   .addScaled 0 1 true 0, .addScaled 1 2 false 1,
   .addScaled 1 0 false 1, .addScaled 0 2 false 2,
   .addScaled 0 1 false 0,
   .phaseProduct 0, .phaseProduct 1,
   .addScaled 1 2 true 0, .addScaled 0 2 true 2,
   .addScaled 1 0 true 0, .addScaled 0 1 false 1]

/-- Four phase layers, with the final basis restoration interleaved with the
independent additions building the last evaluation row. -/
def programK5 : Prog 5 :=
  [.addScaled 1 3 false 0,
   .addScaled 2 0 false 0,
   .addScaled 2 4 false 0,
   .addScaled 1 2 false 0,
   .shiftL 2 1,
   .addScaled 2 1 true 0,
   .phaseProduct 0,
   .phaseProduct 4,
   .phaseProduct 1,
   .phaseProduct 2,
   .addScaled 1 0 true 0,
   .addScaled 1 2 false 0,
   .shiftL 2 1,
   .addScaled 1 4 false 2,
   .addScaled 2 3 true 2,
   .addScaled 2 1 false 0,
   .addScaled 2 3 true 1,
   .shiftL 1 2,
   .addScaled 1 2 true 0,
   .addScaled 2 0 true 1,
   .addScaled 2 4 false 3,
   .phaseProduct 1,
   .phaseProduct 2,
   .addScaled 1 0 true 0,
   .addScaled 1 2 false 0,
   .shiftL 2 1,
   .addScaled 1 4 false 6,
   .addScaled 2 3 true 4,
   .addScaled 2 1 false 0,
   .shiftL 1 2,
   .addScaled 2 3 true 5,
   .addScaled 1 2 true 0,
   .addScaled 2 0 true 1,
   .addScaled 2 4 false 7,
   .phaseProduct 1,
   .phaseProduct 2,
   .addScaled 1 2 true 0,
   .shiftR 1 3,
   .addScaled 2 1 false 2,
   .addScaled 2 4 true 8,
   .addScaled 1 3 true 4,
   .addScaled 2 0 true 0,
   .addScaled 0 4 false 12,
   .shiftR 2 4,
   .addScaled 0 1 false 3,
   .addScaled 0 3 false 9,
   .addScaled 0 2 false 6,
   .phaseProduct 0,
   .addScaled 0 1 true 3,
   .addScaled 0 3 true 9,
   .addScaled 0 4 true 12,
   .addScaled 0 2 true 6]

def generatedPoints (_mode : ProductMode) (k : Nat) : List Point :=
  if k = 3 then [.int 0, .int 1, .frac 0, .int (-2), .int (-1)]
  else [.int 0, .frac 0, .int 1, .int (-1),
        .int 2, .int (-2), .int 4, .int (-4), .int 8]

def handles (mode : ProductMode) (k : Nat) : Bool :=
  match mode with
  | .PhaseProduct => decide (k = 3 ∨ k = 5)
  | .PhaseTripleProduct => false

def generatePointsInOrder (mode : ProductMode) (k : Nat) (_hk : k >= 2) :=
  generatedPoints mode k

def generate (mode : ProductMode) (k : Nat) (hk : k >= 2) : Prog k :=
  if h3 : k = 3 then h3.symm ▸ programK3
  else if h5 : k = 5 then h5.symm ▸ programK5
  else baselineGenerate mode k hk

theorem generatedPoints_valid (mode : ProductMode) (k : Nat) (_hk : k >= 2)
    (hhandles : handles mode k = true) :
    ValidPointList mode k (generatedPoints mode k) := by
  cases mode with
  | PhaseTripleProduct => simp [handles] at hhandles
  | PhaseProduct =>
    have h : k = 3 ∨ k = 5 := by simpa [handles] using hhandles
    rcases h with rfl | rfl <;> unfold ValidPointList generatedPoints <;> decide

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
    have h : k = 3 ∨ k = 5 := by simpa [handles] using hhandles
    rcases h with rfl | rfl
    · have hhk : hk = (by decide : 3 >= 2) := Subsingleton.elim _ _
      subst hk
      constructor
      · exact List.Perm.refl _
      · apply progConsumesPtsSafe_of_checks <;> decide
    · have hhk : hk = (by decide : 5 >= 2) := Subsingleton.elim _ _
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
