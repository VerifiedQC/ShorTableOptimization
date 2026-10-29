import TableGeneration.RecursiveCost.BandedPolicy.Semantics
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Proofs.Compiler.WidthSoundness

/-!
# Register-width (capacity) soundness for banded policies (open item O1)

`evalPhase_correct` (Semantics.lean) is a statement about unbounded integers:
it holds for any child-width function and any radix (PROOF_AUDIT F1). This
file adds the capacity layer.

**Part A, one table, one operand (arity-free).** For an operand `x` that fits
`n` signed bits (`Shor.FitsSignedWidth n x`, i.e. `0 < n` and
`-2^(n-1) ≤ x < 2^(n-1)`: ForShor's signed node reads its width-`n` operand
register as two's complement), the top-heavy limbs fit their limb widths
(lower limbs unsigned in `n / k` bits, the top limb signed in
`n - (k-1)(n/k)` bits), and **every register value of every state the program
reaches** (so every `addScaled`, `shiftL`, `shiftR`, `negate` result, and
every `phaseProduct` checkpoint, i.e. every child operand) fits signed
`T.childWidth n = nextSignedWidth n n T.ops` bits. This is ForShor's
`allocated_widths_sound` (Proofs/Compiler/WidthSoundness.lean) restated over
STO's operation language and the mirror's limb split, with the integer
arithmetic taken from ForShor's own lemmas (`FitsSignedWidth_shiftL_raw`,
`…_shiftR_of_mul`, `…_neg_widen`, `…_addScaled_widen`, `…_mono`) and the
scan-prefix bound from ForShor's `prefix_foldl_updateWidthState_x_le_scanNeeded`
and `commonNeededWidth_ge_xneed`. Nothing here mentions the product mode:
each operand runs the same program on its own limbs, so the lemmas serve
`PhaseProduct` and `PhaseTripleProduct` alike.

**Part B, a register-level semantics that wraps.** `evalPhaseRegW P wd`
runs every operand on fixed-width registers: the width-`n` operand register
(`Shor.tcWrapInt n`), its limb fields (lower limbs read as unsigned
`n / k`-bit fields, the top limb as a signed field), then every operation of
the program on working registers of the *declared* width `wd T n`, each result
wrapped to `wd T n` bits, the checkpoints read off the wrapped registers, and
the children evaluated at width `wd T n`. `evalPhaseReg` is the instance
`wd = childWidth` (STO's Lean scan). Theorem `evalPhaseRegW_correct`: if the
policy is checked and the declared width is at least the scanned one wherever
a table is chosen, then for operands fitting `n` bits the wrapped evaluation
is exactly `φ · ∏ xs`; with `evalPhase_correct` this gives
`evalPhaseReg = evalPhase = φ · ∏ xs` (`evalPhaseReg_eq_evalPhase`).
`CapacityOK` states the per-level fits recursively down to the leaf and
`capacityOK_of_check` proves it.

**Part C, contraction on whole bands (F6).** `childWidth_le_shift`: the scan
satisfies `childWidth n ≤ n / k + childWidth (n % k)`, so above
`2 · max_{r<k} childWidth r + 2` every table with `k ≥ 2` contracts.
`bandsContract` checks the finitely many widths of each band's range below
that bound (the top band's range is unbounded: `[t₀, ∞)`); `bandsContract_sound`
proves that every table the policy chooses at any width contracts there. This
closes F6 for policies passing `bandsContract`, which is an advisory, not part
of `check` (a non-contracting band is still correct; it takes the leaf).

For `PhaseTripleProduct` everything here is soundness of the analogous register
model (each operand runs the same program), not of an existing circuit.
-/

namespace TableGeneration.PolicyMirror

open TableGeneration.Operations TableGeneration.RecursiveCost Finset

/-- Signed fit, ForShor's predicate: `0 < w ∧ -2^(w-1) ≤ z < 2^(w-1)`. -/
abbrev Fits (w : ℕ) (z : ℤ) : Prop := Shor.FitsSignedWidth w z

/-! ## Part A: one table, one operand -/

section PartA

variable {k : ℕ}

/-- ForShor's initial width state for two width-`n` operands (the balanced
signed node). Only the `x` component is used: every operand of the node has
width `n`, so every operand follows the same widths. -/
def initWS (k n : ℕ) : Shor.WidthState k :=
  Shor.initWidthState (Companion.canonicalExtReg n) (Companion.canonicalExtReg n) k

/-- The proof-only invariant (ForShor's `WidthStateSoundPlus`, `x` part):
every register's value fits one sign bit beyond its scanned width. -/
def RegFits (cur : Shor.WidthState k) (σ : State k) (L : Fin k → ℤ) : Prop :=
  ∀ i, Fits (cur.xw i + 1) (regValue (σ i) L)

theorem regValue_shiftL (r : Register k) (m : ℕ) (L : Fin k → ℤ) :
    regValue (Register.shiftL r m) L = 2 ^ m * regValue r L := by
  simp only [regValue, Register.shiftL, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem regValue_negate (r : Register k) (L : Fin k → ℤ) :
    regValue (Register.negate r) L = -regValue r L := by
  simp only [regValue, Register.negate, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem regValue_addScaled (d s : Register k) (ng : Bool) (sh : ℕ) (L : Fin k → ℤ) :
    regValue (Register.addScaled d s ng sh) L
      = regValue d L + (if ng then (-1 : ℤ) else 1) * 2 ^ sh * regValue s L := by
  simp only [regValue, Register.addScaled, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem regValue_shiftR {r r' : Register k} {m : ℕ} (h : Register.shiftR? r m = some r')
    (L : Fin k → ℤ) : regValue r L = 2 ^ m * regValue r' L := by
  simp only [Register.shiftR?] at h
  split at h
  · rename_i hall
    cases h
    simp only [regValue, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj := of_decide_eq_true (List.all_eq_true.mp hall j (List.mem_finRange j))
    have : r j = 2 ^ m * (r j / 2 ^ m) := (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hj)).symm
    rw [← mul_assoc, ← this]
  · cases h

theorem regValue_start (i : Fin k) (L : Fin k → ℤ) :
    regValue (State.start_state i) L = L i := by
  simp [regValue, State.start_state]

/-- The companion transition, unfolded at the transported operation. -/
theorem upd_eq (cur : Shor.WidthState k) (op : valid_ops k) :
    Companion.updateWidthState cur op = Shor.updateWidthState cur (Companion.toCompanionOp op) := rfl

/-- **One step** preserves the invariant under the scan's width transition
(ForShor's `widthStateSoundPlus_step`, over STO's operations). -/
theorem regFits_step {cur : Shor.WidthState k} {σ σ' : State k} {op : valid_ops k}
    {L : Fin k → ℤ} (hstep : applyOp? σ op = some σ') (h : RegFits cur σ L) :
    RegFits (Companion.updateWidthState cur op) σ' L := by
  intro j
  cases op with
  | shiftL i m =>
      simp only [applyOp?, Option.some.injEq] at hstep; subst hstep
      by_cases hji : j = i
      · subst hji
        simp only [upd_eq, Companion.toCompanionOp, Shor.updateWidthState, Function.update_self,
          State.shiftLReg, State.setReg, ↓reduceIte, regValue_shiftL]
        exact Shor.FitsSignedWidth_shiftL_raw (h j)
      · simpa [upd_eq, Companion.toCompanionOp, Shor.updateWidthState, Function.update_of_ne hji,
          State.shiftLReg, State.setReg, hji] using h j
  | shiftR i m =>
      simp only [applyOp?, State.shiftRReg?] at hstep
      cases hr : Register.shiftR? (σ i) m with
      | none => rw [hr] at hstep; cases hstep
      | some r' =>
          rw [hr] at hstep
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hstep
          subst hstep
          by_cases hji : j = i
          · subst hji
            simp only [upd_eq, Companion.toCompanionOp, Shor.updateWidthState, Function.update_self,
              State.setReg, ↓reduceIte]
            exact Shor.FitsSignedWidth_shiftR_of_mul (h j) (regValue_shiftR hr L)
          · simpa [upd_eq, Companion.toCompanionOp, Shor.updateWidthState, Function.update_of_ne hji,
              State.setReg, hji] using h j
  | negate i =>
      simp only [applyOp?, Option.some.injEq] at hstep; subst hstep
      by_cases hji : j = i
      · subst hji
        simp only [upd_eq, Companion.toCompanionOp, Shor.updateWidthState, Function.update_self,
          State.negateReg, State.setReg, ↓reduceIte, regValue_negate]
        have := Shor.FitsSignedWidth_neg_widen (h j)
        simpa [Nat.add_assoc] using this
      · simpa [upd_eq, Companion.toCompanionOp, Shor.updateWidthState, Function.update_of_ne hji,
          State.negateReg, State.setReg, hji] using h j
  | addScaled d s ng sh =>
      simp only [applyOp?, Option.some.injEq] at hstep; subst hstep
      by_cases hjd : j = d
      · subst hjd
        simp only [upd_eq, Companion.toCompanionOp, Shor.updateWidthState, Function.update_self,
          State.addScaledReg, State.setReg, ↓reduceIte, regValue_addScaled]
        have := Shor.FitsSignedWidth_addScaled_widen (sh := sh) ng (h j) (h s)
        have he : 1 + max (cur.xw j) (cur.xw s + sh) + 1 = max (cur.xw j) (cur.xw s + sh) + 2 := by
          omega
        rw [he]; exact this
      · simpa [upd_eq, Companion.toCompanionOp, Shor.updateWidthState, Function.update_of_ne hjd,
          State.addScaledReg, State.setReg, hjd] using h j
  | phaseProduct i =>
      simp only [applyOp?, Option.some.injEq] at hstep; subst hstep
      exact h j

/-- A whole run preserves the invariant (ForShor's `widthStateSoundPlus_run`). -/
theorem regFits_run {L : Fin k → ℤ} :
    ∀ (ops : TableGeneration.Prog k) (cur : Shor.WidthState k) (σ σ' : State k),
      run? ops σ = some σ' → RegFits cur σ L → RegFits (ops.foldl Companion.updateWidthState cur) σ' L
  | [], cur, σ, σ', hrun, h => by
      simp only [run?, Option.some.injEq] at hrun; subst hrun; exact h
  | op :: ops, cur, σ, σ', hrun, h => by
      simp only [run?] at hrun
      cases hs : applyOp? σ op with
      | none => rw [hs] at hrun; cases hrun
      | some σ1 =>
          rw [hs] at hrun
          exact regFits_run ops _ σ1 σ' hrun (regFits_step hs h)

/-- The scan bounds every prefix: the width of slot `i` after any prefix of
the program, plus the sign bit, is at most the child width
(ForShor's `prefix_foldl_updateWidthState_x_le_scanNeeded` and
`commonNeededWidth_ge_xneed`, transported). -/
theorem prefix_le_nextSignedWidth (n : ℕ) {ops pre rest : TableGeneration.Prog k}
    (hops : ops = pre ++ rest) (i : Fin k) :
    (pre.foldl Companion.updateWidthState (initWS k n)).xw i + 1 ≤ nextSignedWidth n n ops := by
  have hfold : pre.foldl Companion.updateWidthState (initWS k n)
      = (Companion.toCompanionProg pre).foldl Shor.updateWidthState (initWS k n) := by
    simp only [Companion.toCompanionProg, List.foldl_map]; rfl
  have hops' : Companion.toCompanionProg ops
      = Companion.toCompanionProg pre ++ Companion.toCompanionProg rest := by
    simp [Companion.toCompanionProg, hops]
  have h1 := Shor.prefix_foldl_updateWidthState_x_le_scanNeeded (Companion.canonicalExtReg n)
    (Companion.canonicalExtReg n) _ _ _ i hops'
  have h2 := Shor.commonNeededWidth_ge_xneed
    (Shor.scanNeededWidths (Companion.canonicalExtReg n) (Companion.canonicalExtReg n)
      (Companion.toCompanionProg ops)) i
  rw [hfold]
  exact le_trans (Nat.add_le_add_right h1 1) h2

/-! ### The limb split fits -/

theorem limbWidth_eq (T : PolicyTable) (n : ℕ) : T.limbWidth n = n / T.k := by
  simp [PolicyTable.limbWidth, phaseLimbWidth, Shor.phaseLimbWidthOfWidth]

theorem initWS_xw (k n : ℕ) (i : Fin k) :
    (initWS k n).xw i = if (i : ℕ) + 1 = k then n - (i : ℕ) * (n / k) else n / k := by
  simp [initWS, Shor.initWidthState, Shor.phaseSplitLogicalWidth, Shor.phaseLimbWidth,
    Shor.phaseLimbWidthOfWidth, Shor.isTopChunk]

theorem top_offset_lt {k n : ℕ} (hk : 0 < k) (hn : 0 < n) : (k - 1) * (n / k) < n := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := Nat.div_mul_le_self n (k' + 1)
  have he : (k' + 1 - 1) * (n / (k' + 1)) + n / (k' + 1) = n / (k' + 1) * (k' + 1) := by
    simp only [Nat.add_sub_cancel]; ring
  rcases Nat.eq_zero_or_pos (n / (k' + 1)) with h0 | h0
  · rw [h0]; simpa using hn
  · omega

/-- Floor division by `2^m` of a signed `n`-bit value is a signed
`(n - m)`-bit value (the top field of the register). -/
theorem fits_ediv_pow {n m : ℕ} {x : ℤ} (hx : Fits n x) (hm : m < n) :
    Fits (n - m) (x / 2 ^ m) := by
  obtain ⟨-, hlo, hhi⟩ := hx
  unfold Shor.signedMin at hlo
  unfold Shor.signedMax at hhi
  push_cast at hlo hhi
  have hp : (0 : ℤ) < 2 ^ m := by positivity
  have hsplit : (2 : ℤ) ^ (n - 1) = 2 ^ (n - m - 1) * 2 ^ m := by
    rw [← pow_add]; congr 1; omega
  refine ⟨by omega, ?_, ?_⟩
  · unfold Shor.signedMin; push_cast
    rw [Int.le_ediv_iff_mul_le hp]; nlinarith
  · unfold Shor.signedMax; push_cast
    rw [Int.ediv_lt_iff_lt_mul hp]; nlinarith

/-- **Limb widths.** A lower limb is an unsigned `n / k`-bit field. -/
theorem limb_lower_fits (k n : ℕ) (x : ℤ) (j : Fin k) (hj : (j : ℕ) + 1 ≠ k) :
    0 ≤ limbs k (2 ^ (n / k)) x j ∧ limbs k (2 ^ (n / k)) x j < 2 ^ (n / k) := by
  simp only [limbs, if_neg hj]
  exact ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩

/-- **Limb widths.** The top limb is a signed `n - (k-1)(n/k)`-bit field. -/
theorem limb_top_fits {k n : ℕ} {x : ℤ} (hk : 0 < k) (hx : Fits n x) (j : Fin k)
    (hj : (j : ℕ) + 1 = k) :
    Fits (n - (k - 1) * (n / k)) (limbs k (2 ^ (n / k)) x j) := by
  have hn : 0 < n := hx.1
  simp only [limbs, if_pos hj, ← pow_mul]
  have hjk : (j : ℕ) = k - 1 := by omega
  rw [hjk, mul_comm (n / k)]
  exact fits_ediv_pow hx (top_offset_lt hk hn)

/-- The start state fits the initial width state. -/
theorem regFits_start {k n : ℕ} {x : ℤ} (hk : 0 < k) (hx : Fits n x) :
    RegFits (initWS k n) State.start_state (limbs k (2 ^ (n / k)) x) := by
  intro i
  rw [regValue_start, initWS_xw]
  split
  · rename_i hi
    have hjk : (i : ℕ) = k - 1 := by omega
    rw [hjk]
    exact Shor.FitsSignedWidth_mono (Nat.le_succ _) (limb_top_fits hk hx i hi)
  · rename_i hi
    obtain ⟨h0, h1⟩ := limb_lower_fits k n x i hi
    have := Shor.FitsSignedWidth_of_nonneg_lt_pow (w := n / k)
      (n := (limbs k (2 ^ (n / k)) x i).toNat) (by
        have : ((limbs k (2 ^ (n / k)) x i).toNat : ℤ) < 2 ^ (n / k) := by
          rw [Int.toNat_of_nonneg h0]; exact h1
        exact_mod_cast this)
    rwa [Int.toNat_of_nonneg h0] at this

/-- **Capacity of one table (arity-free).** For an operand fitting `n`
signed bits, every register of every state the program reaches from the start
state (every prefix) holds a value fitting `T.childWidth n` signed bits. -/
theorem working_fits (T : PolicyTable) (hk : 0 < T.k) {n : ℕ} {x : ℤ} (hx : Fits n x)
    {pre rest : TableGeneration.Prog T.k} (hops : T.ops = pre ++ rest) {σ : State T.k}
    (hrun : run? pre State.start_state = some σ) (i : Fin T.k) :
    Fits (T.childWidth n) (regValue (σ i) (limbs T.k (2 ^ T.limbWidth n) x)) := by
  rw [limbWidth_eq]
  have h := regFits_run pre _ _ _ hrun (regFits_start (n := n) hk hx) i
  exact Shor.FitsSignedWidth_mono (prefix_le_nextSignedWidth n hops i) h

/-- Every checkpoint row is a register of a state reached by a prefix. -/
theorem checkpointRows_mem :
    ∀ (ops : TableGeneration.Prog k) (σ0 : State k) (rows : List (Register k)),
      checkpointRows σ0 ops = some rows → ∀ r ∈ rows,
        ∃ pre rest σ i, ops = pre ++ rest ∧ run? pre σ0 = some σ ∧ r = σ i
  | [], σ0, rows, h, r, hr => by
      simp only [checkpointRows, Option.some.injEq] at h; subst h; cases hr
  | op :: ops, σ0, rows, h, r, hr => by
      cases op with
      | phaseProduct i =>
          simp only [checkpointRows] at h
          cases h' : checkpointRows σ0 ops with
          | none => rw [h'] at h; cases h
          | some rs =>
              rw [h'] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              rcases List.mem_cons.mp hr with rfl | hr
              · exact ⟨[], .phaseProduct i :: ops, σ0, i, rfl, rfl, rfl⟩
              · obtain ⟨pre, rest, σ, j, hops, hrun, hrj⟩ := checkpointRows_mem ops σ0 rs h' r hr
                refine ⟨.phaseProduct i :: pre, rest, σ, j, by simp [hops], ?_, hrj⟩
                simp [run?, applyOp?, hrun]
      | _ =>
          simp only [checkpointRows] at h
          split at h
          · cases h
          · rename_i σ1 hs
            obtain ⟨pre, rest, σ, j, hops, hrun, hrj⟩ := checkpointRows_mem ops σ1 rows h r hr
            exact ⟨_ :: pre, rest, σ, j, by rw [hops]; rfl, by simp only [run?]; rw [hs]; exact hrun, hrj⟩

/-- **Child operands fit.** Every child operand a checkpoint produces fits
`T.childWidth n` signed bits. -/
theorem childOperand_fits (T : PolicyTable) (hk : 0 < T.k) {n : ℕ} {x : ℤ} (hx : Fits n x)
    {rows : List (Register T.k)} (hrows : checkpointRows State.start_state T.ops = some rows)
    (t : ℕ) : Fits (T.childWidth n) (T.childOperand n (rows.getD t (Register.zero T.k)) x) := by
  by_cases ht : t < rows.length
  · rw [List.getD_eq_getElem _ _ ht]
    obtain ⟨pre, rest, σ, i, hops, hrun, hr⟩ :=
      checkpointRows_mem T.ops _ rows hrows _ (List.getElem_mem ht)
    rw [hr]
    exact working_fits T hk hx hops hrun i
  · rw [List.getD_eq_default _ _ (by omega)]
    have : T.childOperand n (Register.zero T.k) x = 0 := by
      simp [PolicyTable.childOperand, regValue, Register.zero]
    rw [this]
    have hpos := nextSignedWidth_pos (k := T.k) n n T.ops
    refine ⟨hpos, ?_, ?_⟩ <;> simp [Shor.signedMin, Shor.signedMax]

end PartA

/-! ## Part B: a register-level semantics that wraps at the declared widths -/

section PartB

/-- Signed wrap to `w` bits: ForShor's `tcWrapInt` (reduce mod `2^w`, decode
as two's complement), the map from an integer to what a `w`-qubit register
holds. -/
abbrev wrap (w : ℕ) (z : ℤ) : ℤ := Shor.tcWrapInt w z

theorem wrap_of_fits {w : ℕ} {z : ℤ} (h : Fits w z) : wrap w z = z :=
  Shor.tcWrapInt_eq_of_fits h.1 h

variable {k : ℕ}

/-- One operation on working registers of width `W` holding **values** (one
operand), every result wrapped to `W` bits. Right shift is the arithmetic
(floor) shift a register performs; nothing here looks at symbolic rows. -/
def regOp (W : ℕ) (v : Fin k → ℤ) : valid_ops k → Fin k → ℤ
  | .shiftL i m => Function.update v i (wrap W (v i * 2 ^ m))
  | .shiftR i m => Function.update v i (wrap W (v i / 2 ^ m))
  | .negate i => Function.update v i (wrap W (-v i))
  | .addScaled d s ng sh =>
      Function.update v d (wrap W (v d + (if ng then -1 else 1) * 2 ^ sh * v s))
  | .phaseProduct _ => v

/-- The values the `phaseProduct` checkpoints read, running the program on
width-`W` registers from the register contents `v`. -/
def regCheckpoints (W : ℕ) : (Fin k → ℤ) → TableGeneration.Prog k → List ℤ
  | _, [] => []
  | v, op :: ops =>
      (match op with
        | .phaseProduct i => [v i]
        | _ => []) ++ regCheckpoints W (regOp W v op) ops

/-- If the exact next state fits `W`, the wrapped register step is the exact
step read on values. -/
theorem regOp_sim {W : ℕ} {σ σ' : State k} {op : valid_ops k} {L : Fin k → ℤ}
    (hstep : applyOp? σ op = some σ') (hfit : ∀ i, Fits W (regValue (σ' i) L)) :
    regOp W (fun i => regValue (σ i) L) op = fun i => regValue (σ' i) L := by
  funext j
  cases op with
  | shiftL i m =>
      simp only [applyOp?, Option.some.injEq] at hstep; subst hstep
      by_cases hji : j = i
      · subst hji
        have h := hfit j
        simp only [State.shiftLReg, State.setReg, ↓reduceIte, regValue_shiftL] at h
        simp only [regOp, Function.update_self, State.shiftLReg, State.setReg, ↓reduceIte,
          regValue_shiftL, mul_comm (regValue (σ j) L)]
        exact wrap_of_fits h
      · simp [regOp, Function.update_of_ne hji, State.shiftLReg, State.setReg, hji]
  | shiftR i m =>
      simp only [applyOp?, State.shiftRReg?] at hstep
      cases hr : Register.shiftR? (σ i) m with
      | none => rw [hr] at hstep; cases hstep
      | some r' =>
          rw [hr] at hstep
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hstep
          subst hstep
          by_cases hji : j = i
          · subst hji
            have h := hfit j
            simp only [State.setReg, ↓reduceIte] at h
            simp only [regOp, Function.update_self, State.setReg, ↓reduceIte,
              regValue_shiftR hr L]
            rw [Int.mul_ediv_cancel_left _ (by positivity)]
            exact wrap_of_fits h
          · simp [regOp, Function.update_of_ne hji, State.setReg, hji]
  | negate i =>
      simp only [applyOp?, Option.some.injEq] at hstep; subst hstep
      by_cases hji : j = i
      · subst hji
        have h := hfit j
        simp only [State.negateReg, State.setReg, ↓reduceIte, regValue_negate] at h
        simp only [regOp, Function.update_self, State.negateReg, State.setReg, ↓reduceIte,
          regValue_negate]
        exact wrap_of_fits h
      · simp [regOp, Function.update_of_ne hji, State.negateReg, State.setReg, hji]
  | addScaled d s ng sh =>
      simp only [applyOp?, Option.some.injEq] at hstep; subst hstep
      by_cases hjd : j = d
      · subst hjd
        have h := hfit j
        simp only [State.addScaledReg, State.setReg, ↓reduceIte, regValue_addScaled] at h
        simp only [regOp, Function.update_self, State.addScaledReg, State.setReg, ↓reduceIte,
          regValue_addScaled]
        exact wrap_of_fits h
      · simp [regOp, Function.update_of_ne hjd, State.addScaledReg, State.setReg, hjd]
  | phaseProduct i =>
      simp only [applyOp?, Option.some.injEq] at hstep; subst hstep
      rfl

/-- **Simulation.** While every state the scan reaches fits `W`, the wrapped
register run reads, at its checkpoints, exactly the exact values of the
checkpoint rows. -/
theorem regCheckpoints_sim {W : ℕ} {L : Fin k → ℤ} :
    ∀ (ops : TableGeneration.Prog k) (σ : State k) (cur : Shor.WidthState k)
      (rows : List (Register k)),
      RegFits cur σ L →
      (∀ pre rest, ops = pre ++ rest → ∀ i,
          (pre.foldl Companion.updateWidthState cur).xw i + 1 ≤ W) →
      checkpointRows σ ops = some rows →
      regCheckpoints W (fun i => regValue (σ i) L) ops = rows.map (fun r => regValue r L)
  | [], σ, cur, rows, _, _, h => by
      simp only [checkpointRows, Option.some.injEq] at h; subst h; rfl
  | op :: ops, σ, cur, rows, hfit, hb, h => by
      have hb0 : ∀ i, (Companion.updateWidthState cur op).xw i + 1 ≤ W :=
        hb [op] ops rfl
      have hbt : ∀ pre rest, ops = pre ++ rest → ∀ i,
          (pre.foldl Companion.updateWidthState (Companion.updateWidthState cur op)).xw i + 1 ≤ W :=
        fun pre rest he i => hb (op :: pre) rest (by rw [he]; rfl) i
      cases op with
      | phaseProduct i =>
          simp only [checkpointRows] at h
          cases h' : checkpointRows σ ops with
          | none => rw [h'] at h; cases h
          | some rs =>
              rw [h'] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              have ih := regCheckpoints_sim ops σ _ rs hfit hbt h'
              simp only [regCheckpoints, regOp, List.singleton_append, List.map_cons]
              rw [ih]
      | _ =>
          simp only [checkpointRows] at h
          split at h
          · cases h
          · rename_i σ1 hs
            have hfit1 := regFits_step hs hfit
            have hsim := regOp_sim (W := W) hs fun i =>
              Shor.FitsSignedWidth_mono (hb0 i) (hfit1 i)
            simp only [regCheckpoints, List.nil_append]
            rw [hsim]
            exact regCheckpoints_sim ops σ1 _ rows hfit1 hbt h

/-- The operand register (`n` bits, two's complement) split into its limb
fields and placed on width-`W` working registers: lower limbs are the
unsigned `limbWidth`-bit fields, the top limb the signed remaining field
(`n - (k-1)·limbWidth` bits); every field is then extended to `W` bits. -/
def PolicyTable.regLimbs (T : PolicyTable) (n W : ℕ) (x : ℤ) : Fin T.k → ℤ := fun j =>
  wrap W
    (if (j : ℕ) + 1 = T.k then
      wrap (n - (T.k - 1) * T.limbWidth n) (limbs T.k (2 ^ T.limbWidth n) (wrap n x) j)
    else limbs T.k (2 ^ T.limbWidth n) (wrap n x) j)

/-- The wrapped checkpoint value of the `t`-th child for one operand. -/
def PolicyTable.regChild (T : PolicyTable) (n W : ℕ) (x : ℤ) (t : ℕ) : ℤ :=
  (regCheckpoints W (T.regLimbs n W x) T.ops).getD t 0

/-- **Register-level semantics.** The phase the recursive construction
applies when every register has the declared width: operands of width `n`,
working registers and children of width `wd T n`. All arithmetic wraps. -/
noncomputable def BandedPolicy.evalPhaseRegW (P : BandedPolicy) (wd : PolicyTable → ℕ → ℕ)
    (n : ℕ) (φ : ℚ) (xs : Fin P.mode.arity → ℤ) : ℚ :=
  match P.choose n with
  | none => φ * ∏ s, ((wrap n (xs s) : ℤ) : ℚ)
  | some T =>
      if _h : wd T n < n then
        ∑ t : Fin T.pts.length,
          P.evalPhaseRegW wd (wd T n) (φ * T.coeff n t) (fun s => T.regChild n (wd T n) (xs s) t)
      else φ * ∏ s, ((wrap n (xs s) : ℤ) : ℚ)
termination_by n

/-- The register semantics at STO's scanned widths (`childWidth`, i.e.
`nextSignedWidth n n ops`). -/
noncomputable def BandedPolicy.evalPhaseReg (P : BandedPolicy) (n : ℕ) (φ : ℚ)
    (xs : Fin P.mode.arity → ℤ) : ℚ :=
  P.evalPhaseRegW (fun T n => T.childWidth n) n φ xs

theorem BandedPolicy.evalPhaseRegW_of_choose_none (P : BandedPolicy) (wd : PolicyTable → ℕ → ℕ)
    {n : ℕ} (hc : P.choose n = none) (φ : ℚ) (xs : Fin P.mode.arity → ℤ) :
    P.evalPhaseRegW wd n φ xs = φ * ∏ s, ((wrap n (xs s) : ℤ) : ℚ) := by
  rw [BandedPolicy.evalPhaseRegW, hc]

theorem BandedPolicy.evalPhaseRegW_node (P : BandedPolicy) (wd : PolicyTable → ℕ → ℕ) {n : ℕ}
    {T : PolicyTable} (hc : P.choose n = some T) (hlt : wd T n < n) (φ : ℚ)
    (xs : Fin P.mode.arity → ℤ) :
    P.evalPhaseRegW wd n φ xs = ∑ t : Fin T.pts.length,
      P.evalPhaseRegW wd (wd T n) (φ * T.coeff n t) (fun s => T.regChild n (wd T n) (xs s) t) := by
  rw [BandedPolicy.evalPhaseRegW, hc]
  simp only [dif_pos hlt]

/-- With working width at least the scan, the register limbs are the exact
limbs. -/
theorem regLimbs_eq (T : PolicyTable) (hk : 0 < T.k) {n W : ℕ} (hW : T.childWidth n ≤ W)
    {x : ℤ} (hx : Fits n x) :
    T.regLimbs n W x = fun j => regValue (State.start_state j) (limbs T.k (2 ^ T.limbWidth n) x) := by
  funext j
  rw [regValue_start]
  simp only [PolicyTable.regLimbs, wrap_of_fits hx]
  have hinit : Fits ((initWS T.k n).xw j + 1) (limbs T.k (2 ^ T.limbWidth n) x j) := by
    have := regFits_start (n := n) hk hx j
    rwa [regValue_start, ← limbWidth_eq] at this
  have hb := prefix_le_nextSignedWidth (pre := []) (rest := T.ops) n rfl j
  have hfitW : Fits W (limbs T.k (2 ^ T.limbWidth n) x j) :=
    Shor.FitsSignedWidth_mono (le_trans hb hW) hinit
  split
  · rename_i hj
    have htop := limb_top_fits hk hx j hj
    rw [← limbWidth_eq] at htop
    rw [wrap_of_fits htop, wrap_of_fits hfitW]
  · exact wrap_of_fits hfitW

/-- **The node, on registers.** For a checked table, a working width at least
the scan and an operand fitting `n` bits, the `t`-th wrapped checkpoint value
is exactly the `t`-th child operand. -/
theorem regChild_eq (mode : ProductMode) (T : PolicyTable) (hT : T.check mode = true)
    {n W : ℕ} (hW : T.childWidth n ≤ W) {x : ℤ} (hx : Fits n x) (t : Fin T.pts.length) :
    T.regChild n W x t = T.childOperand n (expectedRow (T.pts.get t)) x := by
  obtain ⟨hk2, _, hsafe⟩ := (PolicyTable.check_iff mode T).mp hT
  have hk : 0 < T.k := by omega
  have hrows := checkpointRows_of_consumes (positive_of_ge_two hk2) T.ops State.start_state T.pts
    hsafe.consumes
  have hsim := regCheckpoints_sim (W := W) (L := limbs T.k (2 ^ T.limbWidth n) x) T.ops
    State.start_state (initWS T.k n) _ (by rw [limbWidth_eq]; exact regFits_start hk hx)
    (fun pre rest he i => le_trans (prefix_le_nextSignedWidth n he i) hW) hrows
  unfold PolicyTable.regChild
  rw [regLimbs_eq T hk hW hx, hsim, List.getD_eq_getElem _ _ (by simp)]
  simp [PolicyTable.childOperand]

/-- **Register-width soundness (PP and PTP).** If every band's table passes
STO's contract and the declared working width is at least STO's scanned
width wherever the policy chooses a table, then for operands that fit `n`
signed bits the wrapped, fixed-width evaluation applies exactly `φ · ∏ xs`:
no register anywhere in the recursion, down to the leaf, overflows. -/
theorem evalPhaseRegW_correct (P : BandedPolicy)
    (hP : ∀ b ∈ P.bands, b.table.check P.mode = true) (wd : PolicyTable → ℕ → ℕ)
    (hwd : ∀ n T, P.choose n = some T → T.childWidth n ≤ wd T n) :
    ∀ (n : ℕ) (φ : ℚ) (xs : Fin P.mode.arity → ℤ), (∀ s, Fits n (xs s)) →
      P.evalPhaseRegW wd n φ xs = φ * ∏ s, (xs s : ℚ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro φ xs hxs
    rw [BandedPolicy.evalPhaseRegW]
    split
    · simp only [wrap_of_fits (hxs _)]
    · rename_i T hc
      have hW := hwd n T hc
      obtain ⟨b, hb, rfl⟩ := BandedPolicy.choose_mem hc
      have hT := hP b hb
      split
      · rename_i hlt
        obtain ⟨hk2, _, _⟩ := (PolicyTable.check_iff P.mode b.table).mp hT
        have hk : 0 < b.table.k := by omega
        rw [← node_identity P.mode b.table hT n φ xs]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [regChild_eq P.mode b.table hT hW (hxs _)]
        rw [ih _ hlt]
        intro s
        have hrows := checkpointRows_of_consumes (positive_of_ge_two hk2) b.table.ops
          State.start_state b.table.pts ((PolicyTable.check_iff P.mode b.table).mp hT).2.2.consumes
        have h := childOperand_fits b.table hk (hxs s) hrows t
        have hget : (b.table.pts.map expectedRow).getD t (Register.zero b.table.k)
            = expectedRow (b.table.pts.get t) := by
          rw [List.getD_eq_getElem _ _ (by simp)]; simp
        rw [hget] at h
        exact Shor.FitsSignedWidth_mono hW h
      · simp only [wrap_of_fits (hxs _)]

/-- **Register-width soundness at the scanned widths**, and agreement of the
three semantics: `evalPhaseReg = evalPhase = φ · ∏ xs` on operands fitting `n`
signed bits. -/
theorem evalPhaseReg_correct (P : BandedPolicy) (h : P.check = true) (n : ℕ) (φ : ℚ)
    (xs : Fin P.mode.arity → ℤ) (hxs : ∀ s, Fits n (xs s)) :
    P.evalPhaseReg n φ xs = φ * ∏ s, (xs s : ℚ) :=
  evalPhaseRegW_correct P (BandedPolicy.check_tables h) _ (fun _ _ _ => le_refl _) n φ xs hxs

theorem evalPhaseReg_eq_evalPhase (P : BandedPolicy) (h : P.check = true) (n : ℕ) (φ : ℚ)
    (xs : Fin P.mode.arity → ℤ) (hxs : ∀ s, Fits n (xs s)) :
    P.evalPhaseReg n φ xs = P.evalPhase n φ xs := by
  rw [evalPhaseReg_correct P h n φ xs hxs, evalPhase_correct_of_check P h]

/-! ### Capacity at every level, stated recursively -/

/-- The fits at one node for one operand: limbs fit their limb widths, and
every register value of every reachable state fits the working width. -/
def NodeFits (T : PolicyTable) (n : ℕ) (x : ℤ) : Prop :=
  (∀ j : Fin T.k, (j : ℕ) + 1 ≠ T.k →
      0 ≤ limbs T.k (2 ^ T.limbWidth n) x j ∧ limbs T.k (2 ^ T.limbWidth n) x j < 2 ^ T.limbWidth n) ∧
  (∀ j : Fin T.k, (j : ℕ) + 1 = T.k →
      Fits (n - (T.k - 1) * T.limbWidth n) (limbs T.k (2 ^ T.limbWidth n) x j)) ∧
  (∀ pre rest σ, T.ops = pre ++ rest → run? pre State.start_state = some σ →
      ∀ i, Fits (T.childWidth n) (regValue (σ i) (limbs T.k (2 ^ T.limbWidth n) x)))

/-- **Capacity, recursively down to the leaf.** The operands fit `n` bits;
at a node, every operand's limbs and every intermediate register fit, and every
child (whose operands are the checkpoint values) satisfies the same at the
child width. -/
def BandedPolicy.CapacityOK (P : BandedPolicy) (n : ℕ) (xs : Fin P.mode.arity → ℤ) : Prop :=
  (∀ s, Fits n (xs s)) ∧
  match P.choose n with
  | none => True
  | some T =>
      if _h : T.childWidth n < n then
        (∀ s, NodeFits T n (xs s)) ∧
        ∀ t : Fin T.pts.length,
          P.CapacityOK (T.childWidth n) (fun s => T.childOperand n (expectedRow (T.pts.get t)) (xs s))
      else True
termination_by n

theorem nodeFits_of (T : PolicyTable) (hk : 0 < T.k) {n : ℕ} {x : ℤ} (hx : Fits n x) :
    NodeFits T n x := by
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun pre rest σ hops hrun i => working_fits T hk hx hops hrun i⟩
  · rw [limbWidth_eq]; exact limb_lower_fits T.k n x j hj
  · rw [limbWidth_eq]; exact limb_top_fits hk hx j hj

/-- **Every checked policy is capacity-sound at every width**, for operands
fitting `n` signed bits (PP; for PTP, in the analogous register model). -/
theorem capacityOK_of_check (P : BandedPolicy) (h : P.check = true) :
    ∀ (n : ℕ) (xs : Fin P.mode.arity → ℤ), (∀ s, Fits n (xs s)) → P.CapacityOK n xs := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro xs hxs
    rw [BandedPolicy.CapacityOK]
    refine ⟨hxs, ?_⟩
    split
    · trivial
    · rename_i T hc
      obtain ⟨b, hb, rfl⟩ := BandedPolicy.choose_mem hc
      have hT := BandedPolicy.check_tables h b hb
      obtain ⟨hk2, _, hsafe⟩ := (PolicyTable.check_iff P.mode b.table).mp hT
      have hk : 0 < b.table.k := by omega
      split
      · rename_i hlt
        refine ⟨fun s => nodeFits_of b.table hk (hxs s), fun t => ih _ hlt _ fun s => ?_⟩
        have hrows := checkpointRows_of_consumes (positive_of_ge_two hk2) b.table.ops
          State.start_state b.table.pts hsafe.consumes
        have hc' := childOperand_fits b.table hk (hxs s) hrows t
        have hget : (b.table.pts.map expectedRow).getD t (Register.zero b.table.k)
            = expectedRow (b.table.pts.get t) := by
          rw [List.getD_eq_getElem _ _ (by simp)]; simp
        rwa [hget] at hc'
      · trivial

end PartB

/-! ## Part C: contraction on every width of every band (F6) -/

section PartC

variable {k : ℕ}

/-- `a ≤ b + d` slot by slot. -/
def LeW (d : ℕ) (a b : Shor.WidthState k) : Prop :=
  ∀ i, a.xw i ≤ b.xw i + d ∧ a.zw i ≤ b.zw i + d

def LeN (d : ℕ) (a b : Shor.NeededWidths k) : Prop :=
  ∀ i, a.xneed i ≤ b.xneed i + d ∧ a.zneed i ≤ b.zneed i + d

/-- Every width transition is monotone and adds at most the offset
(`(w + d) - m ≤ (w - m) + d` for the right shift). -/
theorem leW_update {d : ℕ} {a b : Shor.WidthState k} (h : LeW d a b)
    (op : _root_.Operations.valid_ops k) :
    LeW d (Shor.updateWidthState a op) (Shor.updateWidthState b op) := by
  intro j
  cases op with
  | shiftL i m =>
      by_cases hji : j = i
      · subst hji; simp [Shor.updateWidthState]; have := h j; omega
      · simp [Shor.updateWidthState, Function.update_of_ne hji]; exact h j
  | shiftR i m =>
      by_cases hji : j = i
      · subst hji; simp [Shor.updateWidthState]; have := h j; omega
      · simp [Shor.updateWidthState, Function.update_of_ne hji]; exact h j
  | negate i =>
      by_cases hji : j = i
      · subst hji; simp [Shor.updateWidthState]; have := h j; omega
      · simp [Shor.updateWidthState, Function.update_of_ne hji]; exact h j
  | addScaled dd ss ng sh =>
      by_cases hji : j = dd
      · subst hji; simp [Shor.updateWidthState]; have := h j; have := h ss; omega
      · simp [Shor.updateWidthState, Function.update_of_ne hji]; exact h j
  | phaseProduct i => exact h j

theorem leN_scanAux {d : ℕ} :
    ∀ (ops : List (_root_.Operations.valid_ops k)) (a b : Shor.WidthState k)
      (ma mb : Shor.NeededWidths k), LeW d a b → LeN d ma mb →
      LeN d (Shor.scanNeededWidthsAux a ma ops) (Shor.scanNeededWidthsAux b mb ops)
  | [], _, _, _, _, _, hm => hm
  | op :: ops, a, b, ma, mb, h, hm => by
      simp only [Shor.scanNeededWidthsAux]
      have h' := leW_update h op
      refine leN_scanAux ops _ _ _ _ h' fun i => ?_
      simp only [Shor.mergeNeededWidths, Shor.widthsOfState]
      have := hm i; have := h' i; omega

theorem common_le {d : ℕ} {a b : Shor.NeededWidths k} (h : LeN d a b) :
    Shor.commonNeededWidth a ≤ Shor.commonNeededWidth b + d := by
  unfold Shor.commonNeededWidth
  have : Finset.univ.sup (fun i : Fin k => max (a.xneed i) (a.zneed i))
      ≤ Finset.univ.sup (fun i : Fin k => max (b.xneed i) (b.zneed i)) + d := by
    refine Finset.sup_le fun i _ => ?_
    have hle : max (b.xneed i) (b.zneed i)
        ≤ Finset.univ.sup (fun i : Fin k => max (b.xneed i) (b.zneed i)) :=
      Finset.le_sup (f := fun i : Fin k => max (b.xneed i) (b.zneed i)) (Finset.mem_univ i)
    have := h i
    omega
  omega

theorem initWS_zw (k n : ℕ) (i : Fin k) :
    (initWS k n).zw i = if (i : ℕ) + 1 = k then n - (i : ℕ) * (n / k) else n / k := by
  simp [initWS, Shor.initWidthState, Shor.phaseSplitLogicalWidth, Shor.phaseLimbWidth,
    Shor.phaseLimbWidthOfWidth, Shor.isTopChunk]

/-- The initial widths at `n` are those at `n % k` shifted by `n / k`. -/
theorem leW_init (n : ℕ) : LeW (n / k) (initWS k n) (initWS k (n % k)) := by
  intro i
  have hr : n % k / k = 0 := Nat.div_eq_of_lt (Nat.mod_lt _ (by have := i.2; omega))
  have hdm := Nat.div_add_mod n k
  rw [initWS_xw, initWS_xw, initWS_zw, initWS_zw, hr]
  split
  · rename_i hi
    have he := Nat.succ_mul (i : ℕ) (n / k)
    rw [Nat.succ_eq_add_one, hi] at he
    simp only [Nat.mul_zero, Nat.sub_zero]
    generalize n / k = q at *
    generalize n % k = r at *
    constructor <;> omega
  · constructor <;> omega

/-- **The scan is sub-translational.** `childWidth n ≤ n / k + childWidth (n % k)`. -/
theorem childWidth_le_shift (T : PolicyTable) (n : ℕ) :
    T.childWidth n ≤ n / T.k + T.childWidth (n % T.k) := by
  have h := common_le (leN_scanAux (Companion.toCompanionProg T.ops) _ _
    (Shor.widthsOfState (initWS T.k n)) (Shor.widthsOfState (initWS T.k (n % T.k)))
    (leW_init (k := T.k) n) (fun i => leW_init (k := T.k) n i))
  rw [Nat.add_comm (n / T.k)]
  exact h

/-- Running maximum of `f 0, …, f (m-1)`. -/
def maxUpTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => max (maxUpTo f m) (f m)

theorem le_maxUpTo (f : ℕ → ℕ) : ∀ {r m : ℕ}, r < m → f r ≤ maxUpTo f m
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | r, m + 1, h => by
      simp only [maxUpTo]
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
      · exact le_trans (le_maxUpTo f h) (le_max_left _ _)
      · exact le_max_right _ _

/-- Above this width the table certainly contracts. -/
def PolicyTable.contractBound (T : PolicyTable) : ℕ := 2 * maxUpTo T.childWidth T.k + 2

theorem PolicyTable.contracts_large (T : PolicyTable) (hk : 2 ≤ T.k) {n : ℕ}
    (hn : T.contractBound ≤ n) : T.childWidth n < n := by
  have h1 := childWidth_le_shift T n
  have h2 := le_maxUpTo T.childWidth (Nat.mod_lt n (by omega : 0 < T.k))
  have h3 : n / T.k ≤ n / 2 := Nat.div_le_div_left hk (by norm_num)
  unfold PolicyTable.contractBound at hn
  omega

/-- Explicit check of `childWidth n < n` for `n ∈ [lo, hi)`. -/
def PolicyTable.contractsOn (T : PolicyTable) (lo hi : ℕ) : Bool :=
  (List.range (hi - lo)).all fun j => decide (T.childWidth (lo + j) < lo + j)

/-- One band, covering `[lo, hi)` (`hi = none`: unbounded): `k ≥ 2` and an
explicit check below `contractBound`. -/
def PolicyTable.bandSafe (T : PolicyTable) (lo : ℕ) (hi : Option ℕ) : Bool :=
  decide (2 ≤ T.k) &&
    T.contractsOn lo (match hi with
      | none => T.contractBound
      | some h => min h T.contractBound)

theorem PolicyTable.bandSafe_sound (T : PolicyTable) {lo : ℕ} {hi : Option ℕ}
    (h : T.bandSafe lo hi = true) {n : ℕ} (hlo : lo ≤ n) (hhi : ∀ m, hi = some m → n < m) :
    T.childWidth n < n := by
  simp only [PolicyTable.bandSafe, Bool.and_eq_true, decide_eq_true_eq,
    PolicyTable.contractsOn, List.all_eq_true, List.mem_range] at h
  obtain ⟨hk, hall⟩ := h
  by_cases hb : T.contractBound ≤ n
  · exact T.contracts_large hk hb
  · have hj := hall (n - lo) (by
      cases hi with
      | none => simp only; omega
      | some m => have := hhi m rfl; simp only; omega)
    have he : lo + (n - lo) = n := by omega
    rw [he] at hj
    exact hj

/-- Walk the bands, widest first, each covering `[threshold, previous threshold)`. -/
def bandsContractAux : Option ℕ → List Band → Bool
  | _, [] => true
  | hi, b :: bs => b.table.bandSafe b.threshold hi && bandsContractAux (some b.threshold) bs

/-- **F6 check**: every band contracts at every width of its range (the top
band's range is unbounded), not only on the chain from a target. Decidable;
it evaluates the scan only at widths below each table's `contractBound`. -/
def BandedPolicy.bandsContract (P : BandedPolicy) : Bool := bandsContractAux none P.bands

theorem bandsContractAux_sound {n : ℕ} {T : PolicyTable} :
    ∀ (bs : List Band) (hi : Option ℕ), (∀ m, hi = some m → n < m) →
      bandsContractAux hi bs = true →
      (bs.find? (fun b => decide (b.threshold ≤ n))).map Band.table = some T →
      T.childWidth n < n
  | [], _, _, _, h => by simp at h
  | b :: bs, hi, hhi, hok, h => by
      simp only [bandsContractAux, Bool.and_eq_true] at hok
      by_cases hle : b.threshold ≤ n
      · simp only [List.find?_cons, hle, decide_true, Option.map_some, Option.some.injEq] at h
        subst h
        exact b.table.bandSafe_sound hok.1 hle hhi
      · simp only [List.find?_cons, hle, decide_false] at h
        exact bandsContractAux_sound bs (some b.threshold)
          (fun m hm => by cases hm; omega) hok.2 h

/-- **F6 closed.** If `bandsContract` holds, every table the policy chooses,
at any width, strictly contracts: the recursion falls to the leaf only below
the lowest threshold. -/
theorem bandsContract_sound (P : BandedPolicy) (h : P.bandsContract = true) {n : ℕ}
    {T : PolicyTable} (hc : P.choose n = some T) : T.childWidth n < n :=
  bandsContractAux_sound P.bands none (fun _ hm => by cases hm) h hc

/-- `bandsContract` implies the chain advisory from every width. -/
theorem chainContracts_of_bandsContract (P : BandedPolicy) (h : P.bandsContract = true) (n : ℕ) :
    P.chainContracts n = true := by
  have key : ∀ f m, m < f → P.chainFuel f m = true := by
    intro f
    induction f with
    | zero => intro m hm; omega
    | succ f ih =>
      intro m hm
      simp only [BandedPolicy.chainFuel]
      split
      · rfl
      · rename_i T hc
        have hlt := bandsContract_sound P h hc
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hlt, ih _ (by omega)⟩
  exact key (n + 1) n (by omega)

end PartC

/-! ## Part D: a declared ladder of working widths (the site's `ladder`)

A cost model prices every gate at a register width. The site's policy records
carry a `ladder` `[(width, k), …]`: the operand width at each recursion level,
so the width of level `i + 1` is the working (and child) width the cost model
assumes at level `i`. `declOK` checks that no declared width is below STO's
scan; `declared_correct` is register-width soundness at the declared widths.
A ladder that under-declares a working width fails `declOK`, and the fault
challenge shows such a declaration can make the wrapped evaluation wrong. -/

section PartD

/-- The declared next width after `n`, if `n` occurs (first occurrence) with a
successor in the ladder. -/
def nextDeclared : List (ℕ × Option ℕ) → ℕ → Option ℕ
  | (w, _) :: (w', k') :: rest, n => if w = n then some w' else nextDeclared ((w', k') :: rest) n
  | _, _ => none

/-- Working widths read off a declared ladder; STO's scan where the ladder
says nothing. -/
def ladderWidth (decl : List (ℕ × Option ℕ)) (T : PolicyTable) (n : ℕ) : ℕ :=
  (nextDeclared decl n).getD (T.childWidth n)

/-- What the recursion does at width `w`: `some k` when the chosen table (with
`k` limbs) recurses there, `none` at a leaf width. -/
def BandedPolicy.levelK (P : BandedPolicy) (w : ℕ) : Option ℕ :=
  match P.choose w with
  | none => none
  | some T => if T.childWidth w < w then some T.k else none

/-- The declared-ladder check. Every entry's `k` tag is what the recursion
does at that width (`levelK`, including leaf widths and the last entry), and
every declared step from a width where a table is chosen goes to a smaller
width `w' < w` that is at least the table's scanned working width. It does
**not** require the ladder to be the policy's own chain, and the scan is a
conservative bound: a ladder below the scan is rejected even where it would be
safe (FaultChallenge: 12 bits suffice at `n = 20`, the scan says 13). -/
def BandedPolicy.declOK (P : BandedPolicy) : List (ℕ × Option ℕ) → Bool
  | (w, kd) :: (w', k') :: rest =>
      decide (kd = P.levelK w) &&
      (match P.choose w with
        | none => true
        | some T => decide (T.childWidth w ≤ w') && decide (w' < w)) &&
      P.declOK ((w', k') :: rest)
  | [(w, kd)] => decide (kd = P.levelK w)
  | [] => true

theorem declOK_le (P : BandedPolicy) :
    ∀ (decl : List (ℕ × Option ℕ)), P.declOK decl = true → ∀ {n : ℕ} {T : PolicyTable},
      P.choose n = some T → T.childWidth n ≤ ladderWidth decl T n
  | [], _, n, T, _ => by simp [ladderWidth, nextDeclared]
  | [_], _, n, T, _ => by simp [ladderWidth, nextDeclared]
  | (w, kd) :: (w', k') :: rest, h, n, T, hc => by
      simp only [BandedPolicy.declOK, Bool.and_eq_true] at h
      unfold ladderWidth nextDeclared
      by_cases hw : w = n
      · subst hw
        have h2 := h.1.2
        rw [hc] at h2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
        simpa using h2.1
      · simp only [if_neg hw]
        exact declOK_le P _ h.2 hc

/-- **Register-width soundness at declared widths.** If the policy is checked
and its declared ladder never under-declares a working width, the wrapped
evaluation at the declared widths applies exactly `φ · ∏ xs` on operands
fitting `n` bits. -/
theorem declared_correct (P : BandedPolicy) (h : P.check = true) (decl : List (ℕ × Option ℕ))
    (hd : P.declOK decl = true) (n : ℕ) (φ : ℚ) (xs : Fin P.mode.arity → ℤ)
    (hxs : ∀ s, Fits n (xs s)) :
    P.evalPhaseRegW (ladderWidth decl) n φ xs = φ * ∏ s, (xs s : ℚ) :=
  evalPhaseRegW_correct P (BandedPolicy.check_tables h) _
    (fun _ _ hc => declOK_le P decl hd hc) n φ xs hxs

end PartD

end TableGeneration.PolicyMirror
