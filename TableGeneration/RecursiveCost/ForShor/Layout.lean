import TableGeneration.RecursiveCost.ForShor.Registers
import TableGeneration.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# The companion's width scan

Integrated from the companion Lean formalization at commit `d5a165b`, file
`FastMultiplication/ShorVerification/Implementation/PhaseProduct/Compiler/Layout.lean`.
Apache-2.0; declaration names are the companion's.

This is the layer that decides how wide the recursive children of a PhaseProduct
node must be, and it is where the two Mathlib constructs live that have no
Lean-core equivalent: `Function.update` in `updateWidthState` and
`Finset.univ.sup` in `commonNeededWidth`. An earlier revision of this project
reformulated both to stay dependency-free; they are now the companion's own
definitions, and the reformulated versions survive only as proven-equal fast
paths for evaluation.

Not taken: the concrete split layouts (`PhaseSplitLayout`, `phaseChunkActive`,
`Gate.PhaseProductLayout`) and their disjointness proofs, which belong to the
compiler rather than to width or cost.
-/

namespace TableGeneration.RecursiveCost.ForShor

open TableGeneration.Operations

/-- Width bookkeeping only: current logical widths of each chunk. -/
structure WidthState (k : Nat) where
  xw : Fin k → Nat
  zw : Fin k → Nat

/-- Symbolic width transition for one source operation. -/
def updateWidthState {k : Nat} (st : WidthState k) : valid_ops k → WidthState k
  | .shiftL i n =>
      { xw := Function.update st.xw i (st.xw i + n)
        zw := Function.update st.zw i (st.zw i + n) }
  | .shiftR i n =>
      { xw := Function.update st.xw i (st.xw i - n)
        zw := Function.update st.zw i (st.zw i - n) }
  | .negate i =>
      { xw := Function.update st.xw i (st.xw i + 1)
        zw := Function.update st.zw i (st.zw i + 1) }
  | .addScaled dst src _negsrc sh =>
      let newX := 1 + max (st.xw dst) (st.xw src + sh)
      let newZ := 1 + max (st.zw dst) (st.zw src + sh)
      { xw := Function.update st.xw dst newX
        zw := Function.update st.zw dst newZ }
  | .phaseProduct _ =>
      st

/-- Per-slot maximum widths discovered by scanning the source program. -/
structure NeededWidths (k : Nat) where
  xneed : Fin k → Nat
  zneed : Fin k → Nat

/-- Pointwise maximum of two width-demand records. -/
def mergeNeededWidths {k : Nat} (a b : NeededWidths k) : NeededWidths k where
  xneed := fun i => max (a.xneed i) (b.xneed i)
  zneed := fun i => max (a.zneed i) (b.zneed i)

/-- Regard current widths as the current lower bound on needed widths. -/
def widthsOfState {k : Nat} (st : WidthState k) : NeededWidths k where
  xneed := st.xw
  zneed := st.zw

/--
Lower-limb width for the top-heavy phase layout.
This deliberately uses floor division. The lower `k - 1` limbs have width `w / k`,
and the most significant limb absorbs all remaining bits.
For example, `w = 5`, `k = 4` gives widths `1, 1, 1, 2`.
-/
def phaseLimbWidthOfWidth (w k : Nat) : Nat := w / k

/--
Common radix width for decomposing both operands.
Use `min`, not `max`: the lower limbs must fit inside both operands.
The larger operand simply gets a larger top chunk.
-/
def phaseLimbWidth (x z : ExtReg) (k : Nat) : Nat :=
  min (phaseLimbWidthOfWidth x.width k) (phaseLimbWidthOfWidth z.width k)

/-- The most significant chunk is the last chunk. -/
def isTopChunk {k : Nat} (i : Fin k) : Prop := i.1 + 1 = k

instance {k : Nat} (i : Fin k) : Decidable (isTopChunk i) := by
  unfold isTopChunk
  infer_instance

/-- Logical width of chunk `i`; the last chunk absorbs the remainder. -/
def phaseSplitLogicalWidth (w W k : Nat) (i : Fin k) : Nat :=
  if isTopChunk i then w - i.1 * W else W

/-- Uniform target width chosen to dominate every scanned `x` and `z` need,
plus a sign bit. -/
def commonNeededWidth {k : Nat} (need : NeededWidths k) : Nat :=
  1 + Finset.univ.sup (fun i : Fin k => max (need.xneed i) (need.zneed i))

/-- Number of high bits added when growing `src` into `dst`. -/
def extraDelta (src dst : ExtReg) : Nat := dst.width - src.width

end TableGeneration.RecursiveCost.ForShor
