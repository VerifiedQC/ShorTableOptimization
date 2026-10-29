import TableGeneration.RecursiveCost.BandedPolicy.Tight

/-!
# The threshold acceptance rule at exact widths

A banded policy says which table to use at each width (`choose`: the first band whose
threshold is `≤ w`). Its semantics (`evalPhaseRegW`, `evalPhase`) silently fall back to the
leaf when the chosen table does not shrink the width, so a threshold set too low is not a
correctness fault of the semantics: it is a policy that does not do what it declares. The
harness rejects such a policy. This file states the rule it applies.

`chainContractsTight P n` (a `Bool`, decided by the kernel in the certificate): on the
exact-width recursion from `n` (`ladderTight`), every band chosen

* strictly shrinks the width (`T.tightWidth w < w`), and
* is applied only where its limbs are not degenerate (`T.k ≤ w`; below that the lower limbs
  `w / k` have width 0).

`chainContractsTight_iff_reach` restates it without the ladder: for every width `m` the exact
recursion from `n` reaches (`ExactReach`) and every table `T` chosen there,
`T.k ≤ m ∧ T.tightWidth m < m`. `chainContractsTight_iff` is the one-step unfolding.

`declThresholdOK P decl`: the same rule on a submitted declared ladder (with `declOKTight`).

The rule looks only at the recursion actually taken from `n`: a band whose threshold is too low
at widths the chain never visits is not rejected (HG7 T2); a policy with no band chosen at `n`
passes vacuously (T3). `k ≤ w` is implied by the shrink for every table (T4: the start state's
top-limb row alone forces `tightWidth w ≥ w` when `w < k`); it is kept as the stated rule.
-/

namespace TableGeneration.PolicyMirror

namespace BandedPolicy

/-- One rung of the exact ladder is admissible: a `none` rung is a genuine leaf (no band is
chosen there, rather than a chosen band failing to shrink), and a `some k` rung has `k ≤ w`. -/
def rungOK (P : BandedPolicy) : ℕ × Option ℕ → Bool
  | (w, none) => (P.choose w).isNone
  | (w, some k) => decide (k ≤ w)

/-- **The threshold acceptance rule at exact widths.** Every band chosen on the exact-width
recursion from `n` strictly shrinks the width and is applied at a width `≥ k`. -/
def chainContractsTight (P : BandedPolicy) (n : ℕ) : Bool :=
  (P.ladderTight n).all P.rungOK

/-- **The threshold rule on a declared ladder** (HG7 T1). A declared ladder is the cost model's
claimed recursion; it must obey the same rule as the exact ladder: every rung passes `rungOK`
(a `none` rung is a genuine leaf, a `some k` rung has `k ≤ w`), and only the last rung may be
`none` (nothing is declared after the leaf). Together with `declOKTight` (every declared step goes
to a smaller width that is at least the exact width, with matching `k` tags), every band the
declared recursion applies strictly shrinks the width and none is applied below its `k`. -/
def declThresholdOK (P : BandedPolicy) (decl : List (ℕ × Option ℕ)) : Bool :=
  decl.all P.rungOK && decl.dropLast.all (fun r => r.2.isSome)

/-- Widths the exact-width recursion from `n` visits (every chosen table, shrinking or not). -/
inductive ExactReach (P : BandedPolicy) (n : ℕ) : ℕ → Prop
  | refl : ExactReach P n n
  | step {m : ℕ} {T : PolicyTable} : ExactReach P n m → P.choose m = some T →
      ExactReach P n (T.tightWidth m)

theorem ladderTightFuel_fuel (P : BandedPolicy) :
    ∀ (f g m : ℕ), m < f → m < g → P.ladderTightFuel f m = P.ladderTightFuel g m
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, g + 1, m, hf, hg => by
      simp only [ladderTightFuel]
      split
      · rfl
      · rename_i T _
        by_cases h : T.tightWidth m < m
        · rw [if_pos h, if_pos h,
            ladderTightFuel_fuel P f g (T.tightWidth m) (by omega) (by omega)]
        · rw [if_neg h, if_neg h]

theorem ladderTight_none (P : BandedPolicy) {n : ℕ} (hc : P.choose n = none) :
    P.ladderTight n = [(n, none)] := by
  simp only [ladderTight, ladderTightFuel, hc]

theorem ladderTight_stuck (P : BandedPolicy) {n : ℕ} {T : PolicyTable} (hc : P.choose n = some T)
    (h : ¬ T.tightWidth n < n) : P.ladderTight n = [(n, none)] := by
  simp only [ladderTight, ladderTightFuel, hc, if_neg h]

theorem ladderTight_step (P : BandedPolicy) {n : ℕ} {T : PolicyTable} (hc : P.choose n = some T)
    (h : T.tightWidth n < n) :
    P.ladderTight n = (n, some T.k) :: P.ladderTight (T.tightWidth n) := by
  unfold ladderTight
  conv_lhs => simp only [ladderTightFuel, hc, if_pos h]
  rw [ladderTightFuel_fuel P n (T.tightWidth n + 1) (T.tightWidth n) h (by omega)]

/-- One-step unfolding of the rule. -/
theorem chainContractsTight_iff (P : BandedPolicy) (n : ℕ) :
    P.chainContractsTight n = true ↔
      ∀ T, P.choose n = some T →
        T.k ≤ n ∧ T.tightWidth n < n ∧ P.chainContractsTight (T.tightWidth n) = true := by
  rcases hc : P.choose n with _ | T
  · simp [chainContractsTight, ladderTight_none P hc, rungOK, hc]
  · by_cases h : T.tightWidth n < n
    · simp only [chainContractsTight, ladderTight_step P hc h, List.all_cons, rungOK,
        Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq]
      constructor
      · rintro ⟨h1, h2⟩ T' rfl
        exact ⟨h1, h, h2⟩
      · intro H
        obtain ⟨h1, -, h2⟩ := H T rfl
        exact ⟨h1, h2⟩
    · simp only [chainContractsTight, ladderTight_stuck P hc h, List.all_cons, List.all_nil,
        rungOK, hc, Option.isNone_some, Bool.and_true, Bool.false_eq_true, false_iff, not_forall]
      exact ⟨T, rfl, fun H => h H.2.1⟩

theorem ExactReach.trans_step {P : BandedPolicy} {n m : ℕ} {T : PolicyTable}
    (hc : P.choose n = some T) (h : P.ExactReach (T.tightWidth n) m) : P.ExactReach n m := by
  induction h with
  | refl => exact .step .refl hc
  | step _ hc' ih => exact .step ih hc'

/-- **The rule, without the ladder**: `chainContractsTight P n` holds iff every table chosen at
every width the exact recursion from `n` reaches has `k ≤ m` and strictly shrinks the width. -/
theorem chainContractsTight_iff_reach (P : BandedPolicy) (n : ℕ) :
    P.chainContractsTight n = true ↔
      ∀ (m : ℕ) (T : PolicyTable), P.ExactReach n m → P.choose m = some T →
        T.k ≤ m ∧ T.tightWidth m < m := by
  constructor
  · intro H m T hr hc
    have key : ∀ m, P.ExactReach n m → P.chainContractsTight m = true := by
      intro m hr
      induction hr with
      | refl => exact H
      | step _ hc' ih => exact (((chainContractsTight_iff P _).mp ih) _ hc').2.2
    obtain ⟨h1, h2, -⟩ := (chainContractsTight_iff P m).mp (key m hr) T hc
    exact ⟨h1, h2⟩
  · induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro H
      refine (chainContractsTight_iff P n).mpr fun T hc => ?_
      obtain ⟨h1, h2⟩ := H n T .refl hc
      exact ⟨h1, h2, ih _ h2 fun m T' hr hc' => H m T' (ExactReach.trans_step hc hr) hc'⟩

end BandedPolicy

end TableGeneration.PolicyMirror
