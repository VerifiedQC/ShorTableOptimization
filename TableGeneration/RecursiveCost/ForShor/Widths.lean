import TableGeneration.RecursiveCost.ForShor.Layout
import TableGeneration.Language

/-!
# The companion's width scan, driven over a program

Integrated from the companion Lean formalization at commit `d5a165b`, file
`FastMultiplication/ShorVerification/Implementation/PhaseProduct/Compiler/Widths.lean`.
Apache-2.0; declaration names are the companion's.

`nextSignedWidth` is the width every recursive child of a PhaseProduct node
receives, and it is the function the recursive planner's `childWidth` must
agree with. Only the definitions are taken; the companion's scan-monotonicity
and target-layout lemmas belong to its compiler correctness proof.
-/

namespace TableGeneration.RecursiveCost.ForShor

open TableGeneration.Operations

/-- Initial width bookkeeping now uses the uniform lower-limb phase layout. -/
def initWidthState (x z : ExtReg) (k : Nat) : WidthState k :=
  let W := phaseLimbWidth x z k
  { xw := fun i => phaseSplitLogicalWidth (ExtReg.width x) W k i
    zw := fun i => phaseSplitLogicalWidth (ExtReg.width z) W k i }

/-- Pull the recursion in `scanNeededWidths` out to a top-level helper. -/
def scanNeededWidthsAux {k : Nat} (cur : WidthState k) (mx : NeededWidths k) :
    List (valid_ops k) → NeededWidths k
  | [] => mx
  | op :: rest =>
      let cur' := updateWidthState cur op
      let mx' := mergeNeededWidths mx (widthsOfState cur')
      scanNeededWidthsAux cur' mx' rest

/-- Scan needed widths using the new initial width state. -/
def scanNeededWidths {k : Nat} (x z : ExtReg) (ops : List (valid_ops k)) : NeededWidths k :=
  scanNeededWidthsAux (initWidthState x z k) (widthsOfState (initWidthState x z k)) ops

/-- The size parameter used when deciding whether a signed phase product
    should recurse again. -/
def phaseInputSize (x z : ExtReg) : Nat := max x.width z.width

/-- The actual width of the recursively compiled chunk phase products. -/
def nextSignedWidth {k : Nat} (x z : ExtReg) (ops : Prog k) : Nat :=
  commonNeededWidth (scanNeededWidths x z ops)

end TableGeneration.RecursiveCost.ForShor
