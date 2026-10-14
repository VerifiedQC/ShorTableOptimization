import TableGeneration.Policy

namespace TableGeneration.Policies.Accepted.P9d8a1554c43b
open Operations

/-- Two layers of quadratic evaluations, with exact restoration.

The first layer holds x₀, x₀+x₁+x₂, x₀-x₁+x₂. The second holds
4x₀+2x₁+x₂ and x₂. The intervening basis change reuses the first
layer instead of restoring all coefficients before building the second.
-/
def programK3 : Prog 3 :=
  [.addScaled 2 0 false 0,
   .addScaled 1 2 false 0,
   .shiftL 2 1,
   .addScaled 2 1 true 0,
   .phaseProduct 0,
   .phaseProduct 1,
   .phaseProduct 2,
   .addScaled 2 1 false 0,
   .shiftL 1 1,
   .addScaled 2 0 true 1,
   .addScaled 1 0 false 1,
   .shiftL 1 1,
   .addScaled 1 2 true 0,
   .shiftR 1 1,
   .shiftR 2 1,
   .phaseProduct 1,
   .phaseProduct 2,
   .addScaled 1 2 true 0,
   .shiftR 1 1,
   .addScaled 1 0 true 1]

def generatedPoints (_mode : ProductMode) (_k : Nat) : List Point :=
  [.int 0, .int 1, .int (-1), .frac 2, .frac 0]

def handles (mode : ProductMode) (k : Nat) : Bool :=
  match mode with
  | .PhaseProduct => decide (k = 3)
  | .PhaseTripleProduct => false

def generatePointsInOrder (mode : ProductMode) (k : Nat) (_hk : k >= 2) :=
  generatedPoints mode k

def generate (mode : ProductMode) (k : Nat) (hk : k >= 2) : Prog k :=
  if h6 : k = 3 then h6.symm ▸ programK3
  else baselineGenerate mode k hk

theorem generatedPoints_valid (mode : ProductMode) (k : Nat) (_hk : k >= 2)
    (hhandles : handles mode k = true) :
    ValidPointList mode k (generatedPoints mode k) := by
  cases mode with
  | PhaseTripleProduct => simp [handles] at hhandles
  | PhaseProduct =>
    have h : k = 3 := by simpa [handles] using hhandles
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
    have h : k = 3 := by simpa [handles] using hhandles
    subst k
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

end TableGeneration.Policies.Accepted.P9d8a1554c43b
