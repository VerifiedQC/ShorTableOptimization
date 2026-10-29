import TableGeneration.RecursiveCost.BandedPolicy.Defs
import TableGeneration.RecursiveCost.BandedPolicy.Interp

/-!
# What a banded policy computes, and the correctness theorem

`BandedPolicy.evalPhase P n φ xs` is the **total phase** the recursive
construction applies to the operands `xs` (two for `PhaseProduct`, three for
`PhaseTripleProduct`) when it is asked for the phase product with angle `φ`
at operand width `n`. It is a denotation of the circuit's structure, not of
its gates:

* **leaf** (no band, or the chosen table does not shrink the width):
  the direct product, phase `φ · ∏ xs`;
* **node** with table `T`: each operand is split top-heavy into `T.k` limbs
  at the limb width `n / k` (ForShor's split), the program `T.ops` is **run**
  from `State.start_state`, and at the `t`-th `phaseProduct` checkpoint the
  register it names, read as a linear form in the limbs, gives the `t`-th
  child operand of every operand; the child is the same construction at the
  child width (STO's Lean width scan) with phase `φ · cₜ`, where `cₜ` is the
  interpolation weight of the `t`-th declared point at radix `2^(n / k)`
  (ForShor's `ToomCookMath.interpCoeff`); the node's phase is the sum of its
  children's.

The children are read from the program's execution (`checkpointRows`), the
weights from the declared point list. Nothing ties the two together except
the per-table check, which is why the correctness theorem needs it.

The phases are exact rationals (no reduction mod 1), so the theorem below is
the exact identity, which is stronger than equality of the unitaries
`exp(2πi · phase)`.

## Scope (after the independent refute pass, HG7)

The theorem certifies the **algebra** of the recursive Toom–Cook composition
over unbounded integers. It does not depend on the child-width function or on
the radix: it would stay true for any `childWidth` with `childWidth n < n` and
any radix `2^w`. So it says nothing about register-width or capacity
soundness by itself; that is `Capacity.lean` (`evalPhaseReg_correct`,
`capacityOK_of_check`: a wrapping fixed-width register semantics equals
`evalPhase` on operands fitting `n` signed bits). The control
structure mirrored is ForShor's balanced, uncontrolled signed node: the same
`choose`, stop rule, checkpoint-to-coefficient order, top-heavy `n / k` split
and `nextSignedWidth` child width. Not modelled: the `+1` zero-extended root
of `PhaseProdUsing`, unbalanced root operands, controlled variants,
workspace layout, and circuit-level equivalence with ForShor's lowering.
-/

noncomputable section

namespace TableGeneration.PolicyMirror

open TableGeneration.Operations Finset

/-- A register read as a linear form in the limb values. -/
def regValue {k : Nat} (r : Register k) (L : Fin k → ℤ) : ℤ :=
  ∑ j, r j * L j

namespace PolicyTable

/-- The interpolation weight of the `t`-th declared point at radix
`2^(limbWidth n)`. -/
def coeff (T : PolicyTable) (n : Nat) (t : Fin T.pts.length) : ℚ :=
  ToomCookMath.interpCoeff (pointRowQ T.pts.length) (fun i : Fin T.pts.length => T.pts.get i)
    ((2 : ℚ) ^ T.limbWidth n) t

/-- The child operand a checkpoint row produces from an operand `x` at
width `n`: the row applied to `x`'s top-heavy limbs. -/
def childOperand (T : PolicyTable) (n : Nat) (row : Register T.k) (x : ℤ) : ℤ :=
  regValue row (limbs T.k ((2 : ℤ) ^ T.limbWidth n) x)

end PolicyTable

namespace BandedPolicy

/-- The total phase the policy's recursive construction applies at width `n`
with angle `φ` to operands `xs`. -/
def evalPhase (P : BandedPolicy) (n : Nat) (φ : ℚ) (xs : Fin P.mode.arity → ℤ) : ℚ :=
  match P.choose n with
  | none => φ * ∏ s, (xs s : ℚ)
  | some T =>
      if _h : T.childWidth n < n then
        match checkpointRows State.start_state T.ops with
        | none => φ * ∏ s, (xs s : ℚ)
        | some rows =>
            ∑ t : Fin T.pts.length,
              P.evalPhase (T.childWidth n) (φ * T.coeff n t)
                (fun s => T.childOperand n (rows.getD t (Register.zero T.k)) (xs s))
      else φ * ∏ s, (xs s : ℚ)
termination_by n

end BandedPolicy

namespace BandedPolicy

/-- Unfolding at a leaf width. -/
theorem evalPhase_of_choose_none (P : BandedPolicy) {n : Nat} (hc : P.choose n = none)
    (φ : ℚ) (xs : Fin P.mode.arity → ℤ) : P.evalPhase n φ xs = φ * ∏ s, (xs s : ℚ) := by
  rw [evalPhase, hc]

/-- Unfolding at a node, with the rows the program actually produces (no
check assumed). -/
theorem evalPhase_of_rows (P : BandedPolicy) {n : Nat} {T : PolicyTable}
    (hc : P.choose n = some T) (hlt : T.childWidth n < n) {rows : List (Register T.k)}
    (hrows : checkpointRows State.start_state T.ops = some rows)
    (φ : ℚ) (xs : Fin P.mode.arity → ℤ) :
    P.evalPhase n φ xs =
      ∑ t : Fin T.pts.length,
        P.evalPhase (T.childWidth n) (φ * T.coeff n t)
          (fun s => T.childOperand n (rows.getD t (Register.zero T.k)) (xs s)) := by
  rw [evalPhase, hc]
  simp only [dif_pos hlt, hrows]

end BandedPolicy

theorem expectedRow_cast {k : Nat} (pt : Point) (j : Fin k) :
    ((expectedRow (k := k) pt j : ℤ) : ℚ) = projV pt ^ (j : ℕ) * projW pt ^ (k - 1 - (j : ℕ)) := by
  cases pt <;> simp [expectedRow, projV, projW]

/-- The node identity for one checked table: the weighted sum of the exact
child products is the exact product of the operands. -/
theorem node_identity (mode : ProductMode) (T : PolicyTable) (hT : T.check mode = true)
    (n : Nat) (φ : ℚ) (xs : Fin mode.arity → ℤ) :
    ∑ t : Fin T.pts.length,
        φ * T.coeff n t *
          ∏ s, ((T.childOperand n (expectedRow (T.pts.get t)) (xs s) : ℤ) : ℚ)
      = φ * ∏ s, (xs s : ℚ) := by
  obtain ⟨hk, ⟨hlen, hnodup, _⟩, _⟩ := (PolicyTable.check_iff mode T).mp hT
  have hk0 : 0 < T.k := by omega
  have hlen' : T.pts.length = mode.arity * (T.k - 1) + 1 := by
    rw [hlen, pointCount_eq_arity mode T.k hk0]
  have hd := pairwise_distinct_of_nodup hnodup
  set B : ℤ := (2 : ℤ) ^ T.limbWidth n with hB
  have key := toomCook_exact mode.arity T.k hk0 T.pts hlen' hd ((2 : ℚ) ^ T.limbWidth n)
    (fun s => limbs T.k B (xs s))
  have hrad : ∀ s, ∑ j : Fin T.k, ((limbs T.k B (xs s) j : ℤ) : ℚ) * ((2 : ℚ) ^ T.limbWidth n) ^ (j : ℕ)
      = (xs s : ℚ) := by
    intro s
    have h := sum_limbs T.k hk0 B (by positivity) (xs s)
    have h' : ((∑ j : Fin T.k, limbs T.k B (xs s) j * B ^ (j : ℕ) : ℤ) : ℚ) = (xs s : ℚ) := by
      rw [h]
    push_cast [hB] at h'
    exact h'
  simp_rw [hrad] at key
  rw [← key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [PolicyTable.childOperand, regValue, Int.cast_sum, Int.cast_mul, expectedRow_cast]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- **Correctness of a banded policy (PP and PTP).** If every band's table
passes STO's per-table contract for the policy's mode, then at every operand
width `n`, for every phase angle `φ` and all integer operands `xs`, the
recursively evaluated policy applies exactly the phase `φ · ∏ xs`: the phase
product (`PhaseProduct`, two operands) or the phase triple product
(`PhaseTripleProduct`, three operands). -/
theorem evalPhase_correct (P : BandedPolicy)
    (hP : ∀ b ∈ P.bands, b.table.check P.mode = true) :
    ∀ (n : Nat) (φ : ℚ) (xs : Fin P.mode.arity → ℤ),
      P.evalPhase n φ xs = φ * ∏ s, (xs s : ℚ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro φ xs
    rw [BandedPolicy.evalPhase]
    split
    · rfl
    · rename_i T hc
      obtain ⟨b, hb, rfl⟩ := BandedPolicy.choose_mem hc
      have hT := hP b hb
      split
      · rename_i hlt
        obtain ⟨hk, _, hsafe⟩ := (PolicyTable.check_iff P.mode b.table).mp hT
        have hrows := checkpointRows_of_consumes (positive_of_ge_two hk) b.table.ops
          State.start_state b.table.pts hsafe.consumes
        rw [hrows]
        simp only
        simp_rw [ih _ hlt]
        rw [← node_identity P.mode b.table hT n φ xs]
        refine Finset.sum_congr rfl fun t _ => ?_
        have hget : (b.table.pts.map expectedRow).getD t (Register.zero b.table.k)
            = expectedRow (b.table.pts.get t) := by
          rw [List.getD_eq_getElem _ _ (by simp)]
          simp
        rw [hget]
      · rfl

/-- The acceptance check suffices. -/
theorem evalPhase_correct_of_check (P : BandedPolicy) (h : P.check = true) :
    ∀ (n : Nat) (φ : ℚ) (xs : Fin P.mode.arity → ℤ),
      P.evalPhase n φ xs = φ * ∏ s, (xs s : ℚ) :=
  evalPhase_correct P (BandedPolicy.check_tables h)

/-- **PhaseProduct.** A checked `PhaseProduct` policy applies phase `φ·a·b`. -/
theorem phaseProduct_correct (P : BandedPolicy) (hmode : P.mode = .PhaseProduct)
    (h : P.check = true) (n : Nat) (φ : ℚ) (a b : ℤ) :
    P.evalPhase n φ (fun s => if (s : ℕ) = 0 then a else b) = φ * a * b := by
  rw [evalPhase_correct_of_check P h]
  have harity : P.mode.arity = 2 := by rw [hmode]; rfl
  rw [Fin.prod_univ_eq_prod_range (fun i => ((if i = 0 then a else b : ℤ) : ℚ)) P.mode.arity,
    harity]
  simp [Finset.prod_range_succ, mul_assoc]

/-- **PhaseTripleProduct.** A checked `PhaseTripleProduct` policy applies
phase `φ·a·b·c`. -/
theorem phaseTripleProduct_correct (P : BandedPolicy) (hmode : P.mode = .PhaseTripleProduct)
    (h : P.check = true) (n : Nat) (φ : ℚ) (a b c : ℤ) :
    P.evalPhase n φ (fun s => if (s : ℕ) = 0 then a else if (s : ℕ) = 1 then b else c)
      = φ * a * b * c := by
  rw [evalPhase_correct_of_check P h]
  have harity : P.mode.arity = 3 := by rw [hmode]; rfl
  rw [Fin.prod_univ_eq_prod_range
      (fun i => ((if i = 0 then a else if i = 1 then b else c : ℤ) : ℚ)) P.mode.arity, harity]
  simp [Finset.prod_range_succ, mul_assoc]

/-- **The recursion really uses the table.** At a width where the chosen
table shrinks the width, the evaluation is the sum over the table's declared
points of the children at the child width, each child operand being the
operand's limb polynomial evaluated (homogeneously) at that point. -/
theorem evalPhase_node (P : BandedPolicy) (hP : P.check = true) {n : Nat} {T : PolicyTable}
    (hc : P.choose n = some T) (hlt : T.childWidth n < n) (φ : ℚ) (xs : Fin P.mode.arity → ℤ) :
    P.evalPhase n φ xs =
      ∑ t : Fin T.pts.length,
        P.evalPhase (T.childWidth n) (φ * T.coeff n t)
          (fun s => T.childOperand n (expectedRow (T.pts.get t)) (xs s)) := by
  obtain ⟨b, hb, rfl⟩ := BandedPolicy.choose_mem hc
  have hT := BandedPolicy.check_tables hP b hb
  obtain ⟨hk, _, hsafe⟩ := (PolicyTable.check_iff P.mode b.table).mp hT
  have hrows := checkpointRows_of_consumes (positive_of_ge_two hk) b.table.ops
    State.start_state b.table.pts hsafe.consumes
  rw [BandedPolicy.evalPhase, hc]
  simp only [dif_pos hlt, hrows]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hget : (b.table.pts.map expectedRow).getD t (Register.zero b.table.k)
      = expectedRow (b.table.pts.get t) := by
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  rw [hget]

/-- Along a contracting chain the node equation applies at every level: the
next width again satisfies `chainContracts`. -/
theorem chainContracts_step (P : BandedPolicy) {n : Nat} {T : PolicyTable}
    (h : P.chainContracts n = true) (hc : P.choose n = some T) :
    T.childWidth n < n ∧ P.chainContracts (T.childWidth n) = true := by
  unfold BandedPolicy.chainContracts at h
  simp only [BandedPolicy.chainFuel, hc, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlt, hrest⟩ := h
  refine ⟨hlt, ?_⟩
  -- any fuel above the width is enough, so the step can re-fuel to `c + 1`
  have mono : ∀ f m, P.chainFuel f m = true → ∀ g, m < g → P.chainFuel g m = true := by
    intro f
    induction f with
    | zero => intro m hf; simp [BandedPolicy.chainFuel] at hf
    | succ f ihf =>
      intro m hf g hg
      obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      simp only [BandedPolicy.chainFuel] at hf ⊢
      split at hf
      · rfl
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hf ⊢
        exact ⟨hf.1, ihf _ hf.2 g (by omega)⟩
  exact mono n _ hrest (T.childWidth n + 1) (by omega)

end TableGeneration.PolicyMirror
