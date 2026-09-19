import TableGeneration.RecursiveCost.ForShor.Allocation
import TableGeneration.RecursiveCost.Model

/-!
# Canonical layouts, for checking the allocation closed form

The planner charges a closed form for a node's sign-extension bookkeeping
(`signExtensionAllocationGateCount` in `Model.lean`) rather than running the
companion's allocation compiler, which would mean building `k` concrete
`ExtReg`s per node on a hot path. That closed form is this project's, derived by
reading `allocChunkGate`: only the top limb of each operand carries a sign, so
the other `k - 1` limbs zero-extend for free, and each top limb is extended once
and unwound once.

This file builds the layout the companion's compiler would receive at a balanced
node, so the derivation can be checked against
`bookkeepingGateCost (compileSignedAllocations ...)` rather than trusted. The
check itself is executable and lives in the test oracle; see `--allocation` in
`scripts/tests/RecursiveCostOracle.lean`.
-/

namespace TableGeneration.RecursiveCost.ForShor

/-- A register holding `width` active qubits at `offset`, with `reserve` further
qubits held for growth. Offsets keep distinct slots on distinct qubits. -/
def slotExtReg (offset width reserve : Nat) : ExtReg where
  active := ⟨(List.range width).map (fun i => offset + i), by
    refine List.Pairwise.map _ ?_ (List.nodup_range)
    intro a b hab
    omega⟩
  reserve := ⟨(List.range reserve).map (fun i => offset + width + i), by
    refine List.Pairwise.map _ ?_ (List.nodup_range)
    intro a b hab
    omega⟩
  active_reserve_disjoint := by
    intro q hq hq'
    simp only [List.mem_map, List.mem_range] at hq hq'
    obtain ⟨a, ha, rfl⟩ := hq
    obtain ⟨b, hb, hab⟩ := hq'
    omega

@[simp] theorem slotExtReg_width (offset width reserve : Nat) :
    (slotExtReg offset width reserve).width = width := by
  simp [slotExtReg, ExtReg.width, regSize, Reg.width]

@[simp] theorem slotExtReg_capacity (offset width reserve : Nat) :
    (slotExtReg offset width reserve).capacity = reserve := by
  simp [slotExtReg, ExtReg.capacity, regSize, Reg.width]

/-- The layout the companion's compiler receives at a balanced `w`-bit node
splitting into `k` limbs, each holding enough reserve to reach `childWidth`.

Slots are laid out at strictly increasing offsets, so distinct limbs and the two
operands never share a qubit. -/
def canonicalLayoutState (w k childWidth : Nat) : LayoutState k :=
  let limb := phaseLimbWidth (canonicalExtReg w) (canonicalExtReg w) k
  let stride := childWidth + w + 1
  { xslot := fun i =>
      slotExtReg (i.val * stride)
        (phaseSplitLogicalWidth w limb k i) childWidth
    zslot := fun i =>
      slotExtReg ((k + i.val) * stride)
        (phaseSplitLogicalWidth w limb k i) childWidth }

/-- Total bookkeeping the companion's compiler emits for one balanced node:
the allocation prologue plus the deallocation epilogue. -/
def canonicalAllocationCost (w k childWidth : Nat) : Nat :=
  let src := canonicalLayoutState w k childWidth
  let dst : LayoutState k :=
    { xslot := fun i => growExtRegTo (src.xslot i) childWidth
      zslot := fun i => growExtRegTo (src.zslot i) childWidth }
  bookkeepingGateCost (compileSignedAllocations k src dst) +
    bookkeepingGateCost (compileSignedDeallocations k src dst)


open TableGeneration.RecursiveCost in
/-- Growing a canonical slot to `target` extends it by exactly the shortfall. -/
theorem extraDelta_growExtRegTo (off wdt reserve target : Nat)
    (h : target - wdt ≤ reserve) :
    extraDelta (slotExtReg off wdt reserve)
        (growExtRegTo (slotExtReg off wdt reserve) target)
      = target - wdt := by
  have hcap : (slotExtReg off wdt reserve).CanGrow (target - wdt) := by
    simp only [ExtReg.CanGrow, slotExtReg_capacity]
    exact h
  have hw := ExtReg.width_grow (slotExtReg off wdt reserve) (target - wdt) hcap
  rw [slotExtReg_width] at hw
  simp only [extraDelta, growExtRegTo, slotExtReg_width, hw]
  omega

open TableGeneration.RecursiveCost in
/--
The planner's closed-form allocation charge is exactly what the companion's
allocation compiler emits for the same node.

This is the fact `signExtensionAllocationGateCount` was derived by hand from.
With it, the planner's per-node bookkeeping charge is no longer a reading of
`allocChunkGate` but a consequence of it.
-/
theorem canonicalAllocationCost_eq (w m childWidth : Nat) :
    canonicalAllocationCost w (m + 1) childWidth
      = signExtensionAllocationGateCount w w (m + 1) childWidth := by
  have hfit : childWidth - (w - m * phaseLimbWidthOfWidth w (m + 1)) ≤ childWidth :=
    Nat.sub_le _ _
  simp only [canonicalAllocationCost, canonicalLayoutState,
    bookkeepingGateCost_compileSignedAllocations,
    bookkeepingGateCost_compileSignedDeallocations,
    phaseLimbWidth, canonicalExtReg_width, phaseSplitLogicalWidth,
    isTopChunk, Nat.min_self, if_true,
    extraDelta_growExtRegTo _ _ _ _ hfit,
    signExtensionAllocationGateCount, RecursiveCost.phaseLimbWidth,
    topLimbWidth, Nat.add_sub_cancel]
  omega

end TableGeneration.RecursiveCost.ForShor
