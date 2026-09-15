import TableGeneration.RecursiveCost.ForShor.Layout

/-!
# The companion's allocation bookkeeping

Integrated from the companion Lean formalization at commit `d5a165b`: the `Gate`
language from `Framework/AbstractMachine/Gates.lean`, the allocation compiler
from `Implementation/PhaseProduct/Compiler/Compile.lean`, and
`bookkeepingGateCost` from
`Implementation/GateCount/PhaseProduct/Lemmas.lean`. Apache-2.0; declaration
names are the companion's.

This is what a recursive node pays to widen its limbs before the arithmetic and
to unwind them afterwards. The companion proves the lowered circuit's cost under
`shorGateCostModel` equals `bookkeepingGateCost` of the high-level gate exactly
(`lgc_allocs`, `lgc_deallocs`), so this syntactic function *is* the physical
cost, not an estimate of it.

The planner cannot call it directly -- it would have to build concrete `ExtReg`
layouts per node, which is O(width) work on a hot path -- so `Model.lean` keeps
a closed form, and `AllocationAgreement.lean` checks the two against each other.

Not taken: the lowering plans (`planCompileSignedAllocations` and friends) and
the `lgc_*` lemmas themselves, which are statements about the companion's
compiler rather than about cost.
-/

namespace TableGeneration.RecursiveCost.ForShor

/-- The companion's high-level gate language. Only the constructors are needed
here; the QFT and phase-product semantics are not. -/
inductive Gate : Type
  | id : Gate
  | seq : Gate → Gate → Gate
  | adj : Gate → Gate
  | H : Nat → Gate
  | X : Nat → Gate
  | CNOT : Nat → Nat → Gate
  | Toffoli : Nat → Nat → Nat → Gate
  | QFT : ExtReg → Gate
  | RadixReverse : (r : Reg) → (m : Nat) → Gate
  | SignedPhaseProd : (phi : Angle) → (x z : ExtReg) → Gate
  | CSignedPhaseProd : (ctrl : Nat) → (phi : Angle) → (x z : ExtReg) → Gate
  | CmpGeConst : (N : Nat) → (data scratch : ExtReg) → (flag : Nat) → Gate
  | CSubConst : (N : Nat) → (data scratch : ExtReg) → (flag : Nat) → Gate
  | ShiftL : (r : ExtReg) → (n : Nat) → Gate
  | ShiftR : (r : ExtReg) → (n : Nat) → Gate
  | Negate : (r : ExtReg) → Gate
  | AddScaled : (dst src : ExtReg) → (negSrc : Bool) → (shift : Nat) → Gate
  | zeroExtend : (r : ExtReg) → (n : Nat) → Gate
  | signExtend : (r : ExtReg) → (n : Nat) → Gate
  | zeroDealloc : (r : ExtReg) → (n : Nat) → Gate
  | signDealloc : (r : ExtReg) → (n : Nat) → Gate
  | idealCtrlModMul : (c N : Nat) → (data : Reg) → (ctrl : Nat) → Gate

namespace Gate

infixr:80 " ;; " => Gate.seq

end Gate

/-- Current chunk-to-register assignment for the paired `x` and `z` work arrays. -/
structure LayoutState (k : Nat) where
  xslot : Fin k → ExtReg
  zslot : Fin k → ExtReg

/-- Grow an extendable register just enough to reach target width `W`. -/
def growExtRegTo (e : ExtReg) (W : Nat) : ExtReg := e.grow (W - e.width)

/-- Final widened chunk views for the compiled signed body. -/
def targetSignedLayoutState {k : Nat} (src : LayoutState k) (need : NeededWidths k) :
    LayoutState k :=
  let Wwork := commonNeededWidth need
  { xslot := fun i => growExtRegTo (src.xslot i) Wwork, zslot := fun i => growExtRegTo (src.zslot i) Wwork }

/-- Allocation gate for a single chunk. Lower chunks are zero-extended;
    the top chunk is sign-extended. -/
def allocChunkGate {k : Nat} (i : Fin k) (src dst : ExtReg) : Gate :=
  let n := extraDelta src dst
  if _h0 : n = 0 then
    Gate.id
  else if _htop : isTopChunk i then
    Gate.signExtend src n
  else
    Gate.zeroExtend src n

/-- Matching deallocation gate for a single chunk. -/
def deallocChunkGate {k : Nat} (i : Fin k) (src dst : ExtReg) : Gate :=
  let n := extraDelta src dst
  if _h0 : n = 0 then
    Gate.id
  else if _htop : isTopChunk i then
    Gate.signDealloc src n
  else
    Gate.zeroDealloc src n

/-- Allocation program for the first `n` chunks, in increasing order `0,1,...,n-1`. -/
def compileSignedAllocationsAux {k : Nat} (src dst : LayoutState k) :
    ∀ (n : Nat), n ≤ k → Gate
  | 0, _ => Gate.id
  | n + 1, hn =>
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      compileSignedAllocationsAux src dst n hk' ;;
      allocChunkGate i (src.xslot i) (dst.xslot i) ;;
      allocChunkGate i (src.zslot i) (dst.zslot i)

/-- Emit all chunk allocations before the signed arithmetic body. -/
def compileSignedAllocations (k : Nat) (src dst : LayoutState k) : Gate :=
  compileSignedAllocationsAux src dst k (Nat.le_refl k)

/-- Deallocation program for the first `n` chunks, in decreasing order `n-1,...,1,0`. -/
def compileSignedDeallocationsAux {k : Nat} (src dst : LayoutState k) :
    ∀ (n : Nat), n ≤ k → Gate
  | 0, _ => Gate.id
  | n + 1, hn =>
      let hk' : n ≤ k := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n)) hn
      let i : Fin k := ⟨n, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
      deallocChunkGate i (src.zslot i) (dst.zslot i) ;;
      deallocChunkGate i (src.xslot i) (dst.xslot i) ;;
      compileSignedDeallocationsAux src dst n hk'

/-- Emit all chunk deallocations after the signed arithmetic body. -/
def compileSignedDeallocations (k : Nat) (src dst : LayoutState k) : Gate :=
  compileSignedDeallocationsAux src dst k (Nat.le_refl k)

/-- The fragment of high-level gates whose lowerings are pure allocation
bookkeeping. -/
def BookkeepingGate : Gate → Prop
  | Gate.id =>
      True
  | Gate.seq U V =>
      BookkeepingGate U ∧ BookkeepingGate V
  | Gate.zeroExtend _ _ =>
      True
  | Gate.signExtend _ _ =>
      True
  | Gate.zeroDealloc _ _ =>
      True
  | Gate.signDealloc _ _ =>
      True
  | _ =>
      False

/-- Cost of a bookkeeping gate tree.

Zero-extension and zero-deallocation are free -- the new qubits are already in
the zero state -- while sign extension and its unwinding each copy the sign bit
`n` times, one CNOT apiece. The companion proves the lowered circuit's cost
under `shorGateCostModel` equals this exactly. -/
def bookkeepingGateCost : Gate → Nat
  | Gate.id =>
      0
  | Gate.seq U V =>
      bookkeepingGateCost U + bookkeepingGateCost V
  | Gate.zeroExtend _ _ =>
      0
  | Gate.signExtend _ n =>
      n
  | Gate.zeroDealloc _ _ =>
      0
  | Gate.signDealloc _ n =>
      n
  | _ =>
      0

/-! ## What the bookkeeping actually costs

The companion proves the lowered circuit's cost equals `bookkeepingGateCost` of
the emitted gate. These lemmas evaluate that: of the `k` chunks, only the
most-significant one carries a sign, so only it costs anything, and it costs
exactly the number of bits it is extended by.
-/

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

end TableGeneration.RecursiveCost.ForShor
