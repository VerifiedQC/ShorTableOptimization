import TableGeneration.Metrics
import TableGeneration.RecursiveCost.ForShor.Definitions

namespace TableGeneration.RecursiveCost

open Operations

/-!
# Recursive PhaseProduct cost model

The width scan and the gate costs are the companion's own definitions,
integrated under `TableGeneration.RecursiveCost.ForShor` and pinned to
companion commit `d5a165b`. This file adds only what the companion does not
have: a `Nat`-indexed interface for the planner, an evaluation-oriented array
scan, and the per-node analysis the recursive planner consumes.

There is one cost model, the companion's operative `shorGateCostModel`. An
earlier revision of this file also carried a `v2` model and a `4kW` variant;
`v2` mirrored the companion's `phaseProductCostModel`, which was **deleted**
upstream at `89c45ee`, and `4kW` was never a companion definition at all --
only an inline bound inside its asymptotic proofs. Both are gone.
-/

/-! ## Widths

The companion indexes its scan by `ExtReg`; the planner is indexed by a bare
`Nat` bit width. These are the `Nat`-facing forms, defined from the companion's.
-/

/-- Lower-limb width for the top-heavy split, at bare widths. -/
def phaseLimbWidth (xWidth zWidth k : Nat) : Nat :=
  min (ForShor.phaseLimbWidthOfWidth xWidth k) (ForShor.phaseLimbWidthOfWidth zWidth k)

@[simp] theorem phaseLimbWidth_eq_forshor (xWidth zWidth k : Nat) :
    phaseLimbWidth xWidth zWidth k
      = ForShor.phaseLimbWidth (ForShor.canonicalExtReg xWidth)
          (ForShor.canonicalExtReg zWidth) k := by
  rw [phaseLimbWidth, ForShor.phaseLimbWidth,
      ForShor.canonicalExtReg_width, ForShor.canonicalExtReg_width]

/-- Width of the recursively compiled PhaseProduct children, at bare widths.

This is the companion's `nextSignedWidth` applied to canonical registers of the
requested widths, which is sound because the scan reads only `ExtReg.width`.
It is the specification; `nextBalancedSignedWidth` below is the form the planner
evaluates. -/
def nextSignedWidth {k : Nat} (xWidth zWidth : Nat) (ops : Prog k) : Nat :=
  ForShor.nextSignedWidth (ForShor.canonicalExtReg xWidth)
    (ForShor.canonicalExtReg zWidth) ops

/-!
The website profile uses balanced operands. The following array scan is an
evaluation-oriented form of the same transitions above. It avoids retaining a
long chain of function updates when large promoted programs are interpreted.
-/

/-- Top-heavy split represented as a compact array for balanced inputs. -/
def initBalancedWidths (width k : Nat) : Array Nat :=
  let commonWidth := phaseLimbWidth width width k
  Array.ofFn (fun i : Fin k =>
    ForShor.phaseSplitLogicalWidth width commonWidth k i)

/-- Safe lookup for an index originating from the same `k` as the array. -/
def balancedWidthAt {k : Nat} (widths : Array Nat) (index : Fin k) : Nat :=
  widths[index.val]?.getD 0

/-- Array form of one balanced ForShor width transition. -/
def updateBalancedWidths {k : Nat}
    (widths : Array Nat) : valid_ops k → Array Nat
  | .shiftL index amount =>
      widths.setIfInBounds index.val (balancedWidthAt widths index + amount)
  | .shiftR index amount =>
      widths.setIfInBounds index.val (balancedWidthAt widths index - amount)
  | .negate index =>
      widths.setIfInBounds index.val (balancedWidthAt widths index + 1)
  | .addScaled destination source _negative shift =>
      let newWidth := 1 + max (balancedWidthAt widths destination)
        (balancedWidthAt widths source + shift)
      widths.setIfInBounds destination.val newWidth
  | .phaseProduct _ => widths

/-- Largest entry in a compact balanced width state. -/
def maximumBalancedWidth (widths : Array Nat) : Nat :=
  widths.foldl max 0

/-- Scan a balanced program and retain the maximum capacity ever requested. -/
def scanBalancedMaximumAux {k : Nat}
    (current : Array Nat) (maximum : Nat) : Prog k → Nat
  | [] => maximum
  | op :: rest =>
      let current' := updateBalancedWidths current op
      let maximum' := max maximum (maximumBalancedWidth current')
      scanBalancedMaximumAux current' maximum' rest

/-- Fast balanced-input form of `nextSignedWidth width width ops`.

Balanced operands keep the two width vectors equal at every step, so one array
suffices. This is an evaluation optimization, not a companion definition: the
companion's scan threads `Function.update` chains, which are far too slow to
drive a planner over thousands of widths. `nextBalancedSignedWidth_agrees` in
the oracle checks the two against each other. -/
def nextBalancedSignedWidth {k : Nat} (width : Nat) (ops : Prog k) : Nat :=
  let initial := initBalancedWidths width k
  1 + scanBalancedMaximumAux initial (maximumBalancedWidth initial) ops
/-! ## Gate costs

Every constant below is read from the companion's resource records rather than
written out, so the familiar closed forms are theorems.
-/

/-- Cuccaro modulo-`2^w` ripple-carry adder total, from the companion's
`cuccaroModAddResources`. Equals `9w - 16` for `w >= 3`. -/
def cuccaroModAddGateCount (width : Nat) : Nat :=
  (ForShor.cuccaroModAddResources width).totalGates

/-- Cuccaro-based negation total, from the companion's `negateResources`.
Equals `10w - 14` for `w >= 3`. -/
def cuccaroNegateGateCount (width : Nat) : Nat :=
  (ForShor.negateResourcesAtWidth width).totalGates

theorem cuccaroModAddGateCount_eq (width : Nat) (hw : 3 <= width) :
    cuccaroModAddGateCount width = 9 * width - 16 :=
  ForShor.cuccaroModAddResources_totalGates width hw

theorem cuccaroNegateGateCount_eq (width : Nat) (hw : 3 <= width) :
    cuccaroNegateGateCount width = 10 * width - 14 :=
  ForShor.negateResourcesAtWidth_totalGates width hw

/-- The planner's negation cost is what the operative model charges any register
of that width. -/
theorem cuccaroNegateGateCount_eq_model (r : ForShor.ExtReg) :
    (ForShor.negateResources r).totalGates
      = cuccaroNegateGateCount (ForShor.ExtReg.width r) := rfl

/-- The planner's adder cost is what the operative model charges `addScaled` at
that destination width. -/
theorem cuccaroModAddGateCount_eq_addScaled (width : Nat) (src : ForShor.ExtReg)
    (negSrc : Bool) (shift : Nat) :
    cuccaroModAddGateCount width =
      (ForShor.addScaledResources (ForShor.canonicalExtReg width) src negSrc shift).totalGates := by
  rw [cuccaroModAddGateCount, ForShor.addScaledResources, ForShor.canonicalExtReg_width]

/-- Direct signed PhaseProduct base case, at bare widths. The companion proves
this exact under any cost model. -/
def directSignedPhaseProductGateCount (xWidth zWidth : Nat) : Nat :=
  5 * xWidth * zWidth

/--
Nonrecursive arithmetic cost of one table operation at the common working width.

The shape is the companion's `phaseArithmeticOpCost`: shifts are free, and each
arithmetic operation is charged **twice**, because one symbolic operation acts
on the corresponding limb of both PhaseProduct operands. The constants differ
deliberately. The companion's recurrence charges its loose `rippleAdderGateBound`,
because a clean affine cost is what makes its asymptotic recurrence solvable;
this planner charges what `shorGateCostModel` actually charges.
`phaseArithmeticOpCost_le` records that the companion's own inequality between
the two carries over.
-/
def phaseArithmeticOpCost {k : Nat}
    (workingWidth : Nat) : valid_ops k -> Nat
  | .shiftL _ _ => 0
  | .shiftR _ _ => 0
  | .negate _ => 2 * cuccaroNegateGateCount workingWidth
  | .addScaled _ _ _ _ => 2 * cuccaroModAddGateCount workingWidth
  | .phaseProduct _ => 0

/-- What this planner charges never exceeds what the companion's recurrence
layer assumes. This is the companion's exact-below-bound relationship, lifted
from the primitives to one operation. -/
theorem phaseArithmeticOpCost_le {k : Nat} (workingWidth : Nat) (op : valid_ops k) :
    phaseArithmeticOpCost workingWidth op
      <= ForShor.phaseArithmeticOpCost workingWidth op := by
  cases op with
  | shiftL _ _ => exact Nat.le_refl 0
  | shiftR _ _ => exact Nat.le_refl 0
  | negate _ =>
      exact Nat.mul_le_mul_left 2
        (ForShor.negateResourcesAtWidth_totalGates_le_negateGateBound workingWidth)
  | addScaled _ _ _ _ =>
      exact Nat.mul_le_mul_left 2
        (ForShor.cuccaroModAddResources_totalGates_le_rippleAdderGateBound workingWidth)
  | phaseProduct _ => exact Nat.le_refl 0

/-- Total nonrecursive arithmetic cost of a table-generation program. -/
def phaseProgramOverhead {k : Nat}
    (workingWidth : Nat) (ops : Prog k) : Nat :=
  ops.foldr (fun op total => phaseArithmeticOpCost workingWidth op + total) 0

/-- Logical width of the most-significant limb of a top-heavy split. -/
def topLimbWidth (width limbWidth k : Nat) : Nat :=
  width - (k - 1) * limbWidth

/--
Sign-extension bookkeeping for one recursive node.

The companion's `allocChunkGate` sign-extends only the top limb and
zero-extends the other `k - 1` limbs, and `zeroExtend` / `zeroDealloc` are free
under `shorGateResourceModel`. Each of the two top limbs is therefore extended
and deallocated once, at `childWidth - topLimbWidth` CNOTs apiece.
-/
def signExtensionAllocationGateCount
    (xWidth zWidth k childWidth : Nat) : Nat :=
  let limbWidth := phaseLimbWidth xWidth zWidth k
  2 * ((childWidth - topLimbWidth xWidth limbWidth k) +
       (childWidth - topLimbWidth zWidth limbWidth k))

/-! ## Per-node analysis -/

/-- Width and local-cost information for one recursive policy candidate. -/
structure ProgramAnalysis where
  childWidth : Nat
  arithmeticGateCount : Nat
  arithmeticOperationCount : Nat
  recursiveCallCount : Nat
deriving Repr, DecidableEq

/-- Analyze a verified program at the supplied PhaseProduct operand widths. -/
def analyzeProgram {k : Nat}
    (xWidth zWidth : Nat) (ops : Prog k) : ProgramAnalysis :=
  let childWidth := nextSignedWidth xWidth zWidth ops
  { childWidth
    arithmeticGateCount :=
      phaseProgramOverhead childWidth ops +
        signExtensionAllocationGateCount xWidth zWidth k childWidth
    arithmeticOperationCount := TableGeneration.arithmeticOperationCount ops
    recursiveCallCount := TableGeneration.phaseProductCount ops }

/-- Planner-oriented balanced analysis using the compact array width scan. -/
def analyzeBalancedProgram {k : Nat}
    (width : Nat) (ops : Prog k) : ProgramAnalysis :=
  let childWidth := nextBalancedSignedWidth width ops
  { childWidth
    arithmeticGateCount :=
      phaseProgramOverhead childWidth ops +
        signExtensionAllocationGateCount width width k childWidth
    arithmeticOperationCount := TableGeneration.arithmeticOperationCount ops
    recursiveCallCount := TableGeneration.phaseProductCount ops }

@[simp] theorem analyzeProgram_recursiveCallCount {k : Nat}
    (xWidth zWidth : Nat) (ops : Prog k) :
    (analyzeProgram xWidth zWidth ops).recursiveCallCount =
      TableGeneration.phaseProductCount ops := rfl

@[simp] theorem analyzeProgram_arithmeticOperationCount {k : Nat}
    (xWidth zWidth : Nat) (ops : Prog k) :
    (analyzeProgram xWidth zWidth ops).arithmeticOperationCount =
      TableGeneration.arithmeticOperationCount ops := rfl

theorem commonNeededWidth_pos {k : Nat} (needed : ForShor.NeededWidths k) :
    0 < ForShor.commonNeededWidth needed := by
  simpa [ForShor.commonNeededWidth, Nat.add_comm] using
    (Nat.zero_lt_succ (Finset.univ.sup
      (fun i : Fin k => max (needed.xneed i) (needed.zneed i))))

theorem nextSignedWidth_pos {k : Nat}
    (xWidth zWidth : Nat) (ops : Prog k) :
    0 < nextSignedWidth xWidth zWidth ops :=
  commonNeededWidth_pos _

end TableGeneration.RecursiveCost
