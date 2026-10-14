import TableGeneration.Policy

namespace TableGeneration.Policies.Accepted.P651fc8ae389d

open Operations

/-!
`PhaseProduct` at `k = 3` with evaluation points `0, inf, -1, 1, 1/2`.

Every evaluation row is built on a register that is then torn down with the
same number of additions, so the width scan (`nextSignedWidth`) stays within a
few bits of the top limb. The `1/2` row `[4, 2, 1]` is assembled on register 2
from `[1, 1, 1]` and the `2 * e1` left in register 1.
-/

def programK3 : Prog 3 :=
  [.phaseProduct 0,
   .phaseProduct 2,
   .addScaled 0 1 true 0,
   .addScaled 2 0 false 0,
   .phaseProduct 2,
   .addScaled 0 1 false 0,
   .addScaled 2 1 false 1,
   .phaseProduct 2,
   .addScaled 1 0 false 1,
   .addScaled 2 0 false 0,
   .addScaled 2 1 false 0,
   .phaseProduct 2,
   .addScaled 2 1 true 1,
   .addScaled 1 0 true 1]

def generatedPoints (_mode : ProductMode) (_k : Nat) : List Point :=
  [.int 0, .frac 0, .int (-1), .int 1, .frac 2]

def handles (mode : ProductMode) (k : Nat) : Bool :=
  match mode with
  | .PhaseProduct => decide (k = 3)
  | .PhaseTripleProduct => false

def generatePointsInOrder (mode : ProductMode) (k : Nat) (_hk : k >= 2) : List Point :=
  generatedPoints mode k

def generate (mode : ProductMode) (k : Nat) (hk : k >= 2) : Prog k :=
  if h3 : k = 3 then h3.symm ▸ programK3
  else baselineGenerate mode k hk

theorem generatedPoints_valid (mode : ProductMode) (k : Nat) (_hk : k >= 2)
    (hhandles : handles mode k = true) :
    ValidPointList mode k (generatedPoints mode k) := by
  cases mode with
  | PhaseTripleProduct => simp [handles] at hhandles
  | PhaseProduct =>
    have h : k = 3 := by simpa [handles] using hhandles
    subst h
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
    subst h
    have hhk : hk = (by decide : 3 >= 2) := Subsingleton.elim _ _
    subst hhk
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

end TableGeneration.Policies.Accepted.P651fc8ae389d
