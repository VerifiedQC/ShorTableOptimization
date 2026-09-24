import TableGeneration.ContractSoundness
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Math.Table_Generation.Core.Coverage

/-!
# Closing the contract's soundness gap against the companion

`TableGeneration/ContractSoundness.lean` states the submission contract with
Bool-valued fields (`progConsumesPts? ... = true`, `safeProg? ... = true`) where
the companion development states the same obligations as Props. That file's
docstring lists the two directions it does not prove:

* `progConsumesPts? = true -> ProgConsumesPts`,
* `safeProg? = true -> SafeProg`.

Both are proved here. The companion is a Lake dependency, so its Prop-valued
definitions are available -- and, because it pulls Mathlib in with it, this file
has to live under `TableGeneration/RecursiveCost/`, the only subtree
`scripts/check_mathlib_confinement.py` permits. Nothing on the submission path
imports it, so the `propext`-only audit on the two submission theorems is
untouched.

## Why the two sides line up

`Register`, `State` and therefore `start_state`, `setReg` and the register
algebra are the same definitions on both sides, and `abbrev` is reducible, so
states pass between them with no conversion at all. `Point` and `valid_ops`
have identical shapes but are nominally distinct inductives, so they need the
transports `toCompanionPoint` / `toCompanionOp` defined below.

The one place the two developments genuinely differ is `Register.shiftR?`: this
repository tests divisibility with a `List.finRange` fold so the check stays
decidable without Mathlib, while the companion writes the quantified
proposition and relies on `Fintype` decidability. `shiftR?_agree` shows the two
`ite`s pick the same branch, and everything downstream -- `applyOp?`, `run?`,
and both recursions -- follows from that.
-/

namespace TableGeneration.RecursiveCost.CompanionSoundness

/-! ## Transporting the syntax

`Point` and `valid_ops` are the only types that need converting; `State` and
`Register` are literally the companion's. -/

/-- This repository's `Point` as the companion's. -/
def toCompanionPoint : TableGeneration.Operations.Point → _root_.Operations.Point
  | .int z => .int z
  | .frac m => .frac m

/-- This repository's `valid_ops` as the companion's: the five constructors
correspond one for one. -/
def toCompanionOp {k : Nat} :
    TableGeneration.Operations.valid_ops k → _root_.Operations.valid_ops k
  | .shiftL i n => .shiftL i n
  | .shiftR i n => .shiftR i n
  | .negate i => .negate i
  | .addScaled dst src negSrc shift => .addScaled dst src negSrc shift
  | .phaseProduct i => .phaseProduct i

/-- A program transported operation by operation. -/
def toCompanionProg {k : Nat} (ops : TableGeneration.Prog k) : _root_.Prog k :=
  ops.map toCompanionOp

/-! ## The leaf conditions agree

`expectedRow` and `regEqExpected` are character-for-character the same
definitions on both sides, so once the `Point` is transported the row check is
the same Bool. -/

/-- The interpolation row a point asks for is the companion's row. -/
theorem expectedRow_agree {k : Nat} (pt : TableGeneration.Operations.Point) :
    TableGeneration.expectedRow (k := k) pt
      = _root_.expectedRow (k := k) (toCompanionPoint pt) := by
  cases pt <;> rfl

/-- Hence the register-against-row check is the companion's check. -/
theorem regEqExpected_agree {k : Nat} (r : TableGeneration.Register k)
    (pt : TableGeneration.Operations.Point) :
    TableGeneration.regEqExpected (k := k) r pt
      = _root_.regEqExpected (k := k) r (toCompanionPoint pt) := by
  cases pt <;> rfl

/-! ## The one real difference: the right-shift divisibility test -/

/-- This repository decides "every coefficient is divisible by `2^n`" with a
`List.finRange` fold, to stay Mathlib-free; the companion writes the quantifier
and uses `Fintype` decidability. The two `ite`s take the same branch, and the
register returned on success is the same function, so the partial operations
are equal. -/
theorem shiftR?_agree {k : Nat} (r : TableGeneration.Register k) (n : Nat) :
    TableGeneration.Register.shiftR? r n = _root_.Register.shiftR? r n := by
  have hiff : ((List.finRange k).all (fun j => decide (r j % (2 : Int) ^ n = 0)) = true)
      ↔ (∀ j : Fin k, r j % (2 : Int) ^ n = 0) := by
    constructor
    · intro hall j
      exact of_decide_eq_true (List.all_eq_true.mp hall j (List.mem_finRange j))
    · intro hall
      exact List.all_eq_true.mpr fun j _ => decide_eq_true (hall j)
  simp only [TableGeneration.Register.shiftR?, _root_.Register.shiftR?]
  by_cases h : (List.finRange k).all (fun j => decide (r j % (2 : Int) ^ n = 0)) = true
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg fun hc => h (hiff.mpr hc)]

/-- Lifted to states. -/
theorem shiftRReg?_agree {k : Nat} (σ : TableGeneration.State k) (i : Fin k) (n : Nat) :
    TableGeneration.State.shiftRReg? σ i n = _root_.State.shiftRReg? σ i n := by
  simp only [TableGeneration.State.shiftRReg?, _root_.State.shiftRReg?, shiftR?_agree]
  rfl

/-- One step of execution commutes with the transport. `shiftR` is the only
case that is not definitional. -/
theorem applyOp?_agree {k : Nat} (σ : TableGeneration.State k)
    (op : TableGeneration.Operations.valid_ops k) :
    TableGeneration.applyOp? σ op = _root_.applyOp? σ (toCompanionOp op) := by
  cases op with
  | shiftL i n => rfl
  | shiftR i n => exact shiftRReg?_agree σ i n
  | negate i => rfl
  | addScaled dst src negSrc shift => rfl
  | phaseProduct i => rfl

/-- The phase-product leaf condition is the companion's. -/
theorem matchesAt_agree {k : Nat} (hk : k > 0) (σ : TableGeneration.State k) (i : Fin k)
    (pt : TableGeneration.Operations.Point) :
    TableGeneration.matchesAt_pointRow_state (k := k) hk σ i pt
      = _root_.matchesAt_pointRow_state (k := k) hk σ i (toCompanionPoint pt) :=
  regEqExpected_agree (σ i) pt

/-! ## First obligation: ordered point consumption

The Bool recursion and the Prop recursion match case for case, and in each case
the Bool branch that succeeded supplies exactly the witness the existential
asks for. -/

/-- **Soundness of the Bool point-consumption checker.** If
`progConsumesPts?` accepts, the companion's `ProgConsumesPts` holds of the
transported program and point list.

Only this direction matters for the contract: completeness would govern whether
a valid policy could be wrongly rejected, not whether an accepted one is
sound. -/
theorem progConsumesPts?_sound {k : Nat} (hk : k > 0) :
    ∀ (ops : TableGeneration.Prog k) (σ : TableGeneration.State k)
      (pts : List TableGeneration.Operations.Point),
      TableGeneration.progConsumesPts? hk σ ops pts = true →
      _root_.ProgConsumesPts hk σ (toCompanionProg ops) (pts.map toCompanionPoint) := by
  intro ops
  induction ops with
  | nil =>
      intro σ pts h
      cases pts with
      | nil => show ([] : List _root_.Operations.Point) = []; rfl
      | cons pt rest => exact absurd h (by simp [TableGeneration.progConsumesPts?])
  | cons op ops ih =>
      intro σ pts h
      match op with
      | .phaseProduct i =>
          cases pts with
          | nil => exact absurd h (by simp [TableGeneration.progConsumesPts?])
          | cons pt rest =>
              have h2 : (TableGeneration.matchesAt_pointRow_state (k := k) hk σ i pt &&
                  TableGeneration.progConsumesPts? hk σ ops rest) = true := h
              obtain ⟨hm, hrest⟩ := Bool.and_eq_true _ _ |>.mp h2
              show ∃ pt' ptsTail,
                  (pt :: rest).map toCompanionPoint = pt' :: ptsTail ∧
                  _root_.matchesAt_pointRow_state (k := k) hk σ i pt' = true ∧
                  _root_.ProgConsumesPts hk σ (toCompanionProg ops) ptsTail
              exact ⟨toCompanionPoint pt, rest.map toCompanionPoint, rfl,
                (matchesAt_agree hk σ i pt) ▸ hm, ih σ rest hrest⟩
      | .shiftL i n =>
          show ∃ σ', _root_.applyOp? σ (_root_.Operations.valid_ops.shiftL i n) = some σ' ∧
              _root_.ProgConsumesPts hk σ' (toCompanionProg ops) (pts.map toCompanionPoint)
          exact ⟨_, rfl, ih _ pts h⟩
      | .negate i =>
          show ∃ σ', _root_.applyOp? σ (_root_.Operations.valid_ops.negate i) = some σ' ∧
              _root_.ProgConsumesPts hk σ' (toCompanionProg ops) (pts.map toCompanionPoint)
          exact ⟨_, rfl, ih _ pts h⟩
      | .addScaled dst src negSrc shift =>
          show ∃ σ', _root_.applyOp? σ
              (_root_.Operations.valid_ops.addScaled dst src negSrc shift) = some σ' ∧
              _root_.ProgConsumesPts hk σ' (toCompanionProg ops) (pts.map toCompanionPoint)
          exact ⟨_, rfl, ih _ pts h⟩
      | .shiftR i n =>
          have h2 : (match TableGeneration.State.shiftRReg? σ i n with
              | none => false
              | some τ => TableGeneration.progConsumesPts? hk τ ops pts) = true := h
          show ∃ σ', _root_.applyOp? σ (_root_.Operations.valid_ops.shiftR i n) = some σ' ∧
              _root_.ProgConsumesPts hk σ' (toCompanionProg ops) (pts.map toCompanionPoint)
          cases hr : TableGeneration.State.shiftRReg? σ i n with
          | none => rw [hr] at h2; exact absurd h2 (by simp)
          | some σ' =>
              rw [hr] at h2
              refine ⟨σ', ?_, ih σ' pts h2⟩
              show _root_.State.shiftRReg? σ i n = some σ'
              rw [← shiftRReg?_agree]; exact hr

/-! ## Second obligation: safety of scaled adds -/

/-- `wellFormed?` is a fold of `OpOK?`, so it bounds every operation in the
program. -/
theorem wellFormed?_mem {k : Nat} :
    ∀ (ops : TableGeneration.Prog k), TableGeneration.Prog.wellFormed? ops = true →
      ∀ op ∈ ops, TableGeneration.Prog.OpOK? op = true := by
  intro ops
  induction ops with
  | nil => intro _ op hop; cases hop
  | cons o os ih =>
      intro h op hop
      have h2 : (TableGeneration.Prog.OpOK? o && TableGeneration.Prog.wellFormed? os) = true := h
      obtain ⟨ho, hos⟩ := Bool.and_eq_true _ _ |>.mp h2
      cases hop with
      | head => exact ho
      | tail _ hmem => exact ih hos op hmem

/-- **Soundness of the Bool safety checker.** The companion states safety
positionally -- no `addScaled` anywhere in the program has `dst = src` -- while
this repository checks it by structural recursion. Membership in the transported
program pulls back through `List.map` to the operation the recursion checked. -/
theorem safeProg?_sound {k : Nat} (ops : TableGeneration.Prog k)
    (h : TableGeneration.safeProg? ops = true) :
    _root_.SafeProg (toCompanionProg ops) := by
  intro pre rest d s negSrc sh hEq
  have hmem : _root_.Operations.valid_ops.addScaled d s negSrc sh ∈ toCompanionProg ops := by
    rw [hEq]; simp
  rw [toCompanionProg, List.mem_map] at hmem
  obtain ⟨op, hop, hmapped⟩ := hmem
  have hok := wellFormed?_mem ops h op hop
  cases op with
  | shiftL i n => exact absurd hmapped (by simp [toCompanionOp])
  | shiftR i n => exact absurd hmapped (by simp [toCompanionOp])
  | negate i => exact absurd hmapped (by simp [toCompanionOp])
  | phaseProduct i => exact absurd hmapped (by simp [toCompanionOp])
  | addScaled d' s' b' sh' =>
      simp only [toCompanionOp, _root_.Operations.valid_ops.addScaled.injEq] at hmapped
      obtain ⟨rfl, rfl, -, -⟩ := hmapped
      simpa [TableGeneration.Prog.OpOK?] using hok

/-! ## Third obligation: the round trip

`ContractSoundness.returnsToStartCheck_iff` already shows the Bool round-trip
check is equivalent to `run? ops sigma = some sigma`, but in *this*
repository's `run?`. The companion asks for its own. They agree. -/

/-- Execution commutes with the transport. -/
theorem run?_agree {k : Nat} :
    ∀ (ops : TableGeneration.Prog k) (σ : TableGeneration.State k),
      TableGeneration.run? ops σ = _root_.run? (toCompanionProg ops) σ := by
  intro ops
  induction ops with
  | nil => intro σ; rfl
  | cons op ops ih =>
      intro σ
      show (match TableGeneration.applyOp? σ op with
            | none => none
            | some σ' => TableGeneration.run? ops σ') =
           (match _root_.applyOp? σ (toCompanionOp op) with
            | none => none
            | some σ' => _root_.run? (toCompanionProg ops) σ')
      rw [← applyOp?_agree]
      cases TableGeneration.applyOp? σ op with
      | none => rfl
      | some σ' => exact ih σ'

/-- The start states are the same function, so the contract's round-trip field
is the companion's `returns` obligation verbatim. -/
theorem returns_to_start_companion {k : Nat} {ops : TableGeneration.Prog k}
    (h : TableGeneration.returnsToStartCheck ops TableGeneration.State.start_state = true) :
    _root_.run? (toCompanionProg ops) _root_.State.start_state
      = some _root_.State.start_state := by
  have h' := (TableGeneration.returnsToStartCheck_iff ops TableGeneration.State.start_state).mp h
  rw [← run?_agree]
  exact h'

/-! ## The contract, discharged in the companion's own terms -/

/-- **The submission contract implies the companion's obligation structure.**
`TableGeneration.ProgConsumesPtsSafe` is the Bool-valued bundle a submitter
discharges by `decide`; `_root_.ProgConsumesPtsSafe` is the companion's
Prop-valued pair. This is the statement `ContractSoundness.lean` listed as
unproved. -/
theorem progConsumesPtsSafe_sound {k : Nat} {hk : k > 0}
    {σ : TableGeneration.State k} {ops : TableGeneration.Prog k}
    {pts : List TableGeneration.Operations.Point}
    (h : TableGeneration.ProgConsumesPtsSafe hk σ ops pts) :
    _root_.ProgConsumesPtsSafe hk σ (toCompanionProg ops) (pts.map toCompanionPoint) where
  consumes := progConsumesPts?_sound hk ops σ pts h.consumes
  safe_add := safeProg?_sound ops h.safe_add

/-- All three companion obligations at once, at the state the submission
contract is instantiated at. -/
theorem contract_sound_at_start {k : Nat} {hk : k > 0} {ops : TableGeneration.Prog k}
    {pts : List TableGeneration.Operations.Point}
    (h : TableGeneration.ProgConsumesPtsSafe hk TableGeneration.State.start_state ops pts) :
    _root_.ProgConsumesPtsSafe hk _root_.State.start_state
        (toCompanionProg ops) (pts.map toCompanionPoint) ∧
      _root_.run? (toCompanionProg ops) _root_.State.start_state
        = some _root_.State.start_state :=
  ⟨progConsumesPtsSafe_sound h, returns_to_start_companion h.returns_start⟩

end TableGeneration.RecursiveCost.CompanionSoundness
