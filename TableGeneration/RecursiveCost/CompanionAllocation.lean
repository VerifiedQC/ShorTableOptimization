import TableGeneration.RecursiveCost.CompanionCost
import FastMultiplication.ShorVerification.Implementation.GateCount.PhaseProduct.Lemmas

/-!
# What the companion's allocation bookkeeping actually costs

`Shor.compileSignedAllocations` is what a recursive node emits to widen its
limbs before the arithmetic, and `Shor.compileSignedDeallocations` unwinds them
afterwards. The companion proves the lowered circuit's cost under
`Shor.shorGateCostModel` equals `Shor.bookkeepingGateCost` of the emitted gate
exactly (`lgc_allocs`, `lgc_deallocs`), so that syntactic function *is* the
physical cost, not an estimate of it.

The companion bounds that cost (`bookkeepingGateCost_compileSignedAllocationsAux_le`
and friends, all of the form `<= 2 * n * W`). A bound is not enough here: the
planner charges a closed form for this (`signExtensionAllocationGateCount` in
`Model.lean`) and `AllocationAgreement.lean` proves the closed form **equal** to
what the compiler emits, so what it needs is the exact figure. That is what the
lemmas below evaluate: of the `k` chunks, only the most significant one carries
a sign, so only it costs anything, and it costs exactly the number of bits it is
extended by.

Nothing here restates a companion definition. Every symbol these lemmas mention
is the companion's own.
-/

namespace TableGeneration.RecursiveCost.Companion

open Shor

@[simp] theorem bookkeepingGateCost_allocChunkGate {k : Nat} (i : Fin k) (src dst : ExtReg) :
    bookkeepingGateCost (allocChunkGate i src dst)
      = if isTopChunk i then extraDelta src dst else 0 := by
  unfold allocChunkGate
  by_cases h0 : extraDelta src dst = 0 <;>
    by_cases htop : isTopChunk i <;> simp [h0, htop, bookkeepingGateCost]

@[simp] theorem bookkeepingGateCost_deallocChunkGate {k : Nat} (i : Fin k) (src dst : ExtReg) :
    bookkeepingGateCost (deallocChunkGate i src dst)
      = if isTopChunk i then extraDelta src dst else 0 := by
  unfold deallocChunkGate
  by_cases h0 : extraDelta src dst = 0 <;>
    by_cases htop : isTopChunk i <;> simp [h0, htop, bookkeepingGateCost]

/-- A prefix stopping short of the last chunk is free: every chunk it covers is
zero-extended, and zero extension costs nothing. -/
theorem bookkeepingGateCost_allocAux_of_lt {k : Nat} (src dst : LayoutState k) :
    ∀ (n : Nat) (hn : n ≤ k), n < k →
      bookkeepingGateCost (compileSignedAllocationsAux src dst n hn) = 0 := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ m ih =>
      intro hn hlt
      have hm : m ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self m)) hn
      have hmlt : m < k := Nat.lt_of_le_of_lt (Nat.le_succ m) hlt
      have hnotTop : ¬ isTopChunk (⟨m, Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hn⟩ : Fin k) := by
        simp only [isTopChunk]
        omega
      simp only [compileSignedAllocationsAux, bookkeepingGateCost,
        bookkeepingGateCost_allocChunkGate, if_neg hnotTop, ih hm hmlt]

theorem bookkeepingGateCost_deallocAux_of_lt {k : Nat} (src dst : LayoutState k) :
    ∀ (n : Nat) (hn : n ≤ k), n < k →
      bookkeepingGateCost (compileSignedDeallocationsAux src dst n hn) = 0 := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ m ih =>
      intro hn hlt
      have hm : m ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self m)) hn
      have hmlt : m < k := Nat.lt_of_le_of_lt (Nat.le_succ m) hlt
      have hnotTop : ¬ isTopChunk (⟨m, Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hn⟩ : Fin k) := by
        simp only [isTopChunk]
        omega
      simp only [compileSignedDeallocationsAux, bookkeepingGateCost,
        bookkeepingGateCost_deallocChunkGate, if_neg hnotTop, ih hm hmlt]

/-- The whole allocation prologue of one recursive node: the two top limbs,
each extended by however many bits it gains. -/
theorem bookkeepingGateCost_compileSignedAllocations {m : Nat}
    (src dst : LayoutState (m + 1)) :
    bookkeepingGateCost (compileSignedAllocations (m + 1) src dst)
      = extraDelta (src.xslot ⟨m, Nat.lt_succ_self m⟩) (dst.xslot ⟨m, Nat.lt_succ_self m⟩)
        + extraDelta (src.zslot ⟨m, Nat.lt_succ_self m⟩) (dst.zslot ⟨m, Nat.lt_succ_self m⟩) := by
  have hzero :=
    bookkeepingGateCost_allocAux_of_lt src dst m (Nat.le_succ m) (Nat.lt_succ_self m)
  have htop : isTopChunk (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := rfl
  simp only [compileSignedAllocations, compileSignedAllocationsAux, bookkeepingGateCost,
    bookkeepingGateCost_allocChunkGate, if_pos htop, hzero]
  omega

/-- The deallocation epilogue costs the same as the prologue it unwinds. -/
theorem bookkeepingGateCost_compileSignedDeallocations {m : Nat}
    (src dst : LayoutState (m + 1)) :
    bookkeepingGateCost (compileSignedDeallocations (m + 1) src dst)
      = extraDelta (src.xslot ⟨m, Nat.lt_succ_self m⟩) (dst.xslot ⟨m, Nat.lt_succ_self m⟩)
        + extraDelta (src.zslot ⟨m, Nat.lt_succ_self m⟩) (dst.zslot ⟨m, Nat.lt_succ_self m⟩) := by
  have hzero :=
    bookkeepingGateCost_deallocAux_of_lt src dst m (Nat.le_succ m) (Nat.lt_succ_self m)
  have htop : isTopChunk (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := rfl
  simp only [compileSignedDeallocations, compileSignedDeallocationsAux, bookkeepingGateCost,
    bookkeepingGateCost_deallocChunkGate, if_pos htop, hzero]
  omega

end TableGeneration.RecursiveCost.Companion
