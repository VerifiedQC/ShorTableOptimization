import TableGeneration.RecursiveCost.BandedPolicy.Instances.FaultChallenge

/-!
# Fault challenge for the exact width

Same accepted `k = 2` table as the width fault in `FaultChallenge.lean`
(`fixedTable`: checkpoints `x₀`, `x₀ + x₁`, `x₁`), at `n = 20`. The scan gives
working width `13`; the exact width is `12` (`tight_20`): the widest reachable
value is `x₀ + x₁ ∈ [-512, 1534]` (lower limb `x₀ ∈ [0, 1023]`, top limb
`x₁ ∈ [-512, 511]`), and `1534 < 2^11`.

* `20 → 12` passes `declOKTight` (`tight_ladder_ok`) and the register semantics
  there is exact for every operand pair fitting 20 bits (`tight_ladder_correct`),
  although the scan check rejects it (`FaultChallenge.declared_12_rejected`).
* `20 → 11`, one bit below the exact width, fails `declOKTight`
  (`tight_under_rejected`), and on the witness `a = b = 2^19 - 1`, the operand
  that attains the upper end `1534` of the range, the wrapped evaluation is not
  `a · b` (`tight_under_wrong`: `1534` wraps to `-514`).
* The exact ladder the report uses is kernel-evaluated (`ladderTight_20`).

The discrimination of `tightWidth` itself is carried by `tight_20`,
`tight_ladder_ok`/`tight_ladder_correct` (exact for all operands at 12) and
`tight_under_rejected` (11 rejected). `witness_overflows`, `tight_under_value`
and `tight_under_wrong` do not mention `tightWidth` (the declared 11 comes from
the ladder): they show that the rejected width really is wrong, on one operand.
-/

namespace TableGeneration.PolicyMirror.Instances.TightChallenge

open TableGeneration TableGeneration.Operations TableGeneration.PolicyMirror
open TableGeneration.PolicyMirror.Instances.FaultChallenge

theorem tight_20 : fixedTable.tightWidth 20 = 12 := by decide +kernel
theorem scan_20 : fixedTable.childWidth 20 = 13 := by decide +kernel
theorem ladderTight_20 : fixed.ladderTight 20 = [(20, some 2), (12, none)] := by decide +kernel

def ladder12 : List (ℕ × Option ℕ) := [(20, some 2), (12, none)]

theorem tight_ladder_ok : fixed.declOKTight ladder12 = true := by decide +kernel

/-- Twelve bits suffice: the register semantics at `20 → 12` is exact. -/
theorem tight_ladder_correct (φ : ℚ) (xs : Fin fixed.mode.arity → ℤ) (hxs : ∀ s, Fits 20 (xs s)) :
    fixed.evalPhaseRegW (ladderWidthTight ladder12) 20 φ xs = φ * ∏ s, (xs s : ℚ) :=
  declaredTight_correct fixed fixed_accepted ladder12 tight_ladder_ok 20 φ xs hxs

/-- One bit below the exact width is rejected. -/
theorem tight_under_rejected : fixed.declOKTight ladderUnder = false := by decide +kernel

/-- Minimality at this table, concretely: at 11 bits the checkpoint `x₀ + x₁` of the
witness `2^19 - 1` (`= 511 · 2^10 + 1023`) does not fit. -/
theorem witness_overflows :
    ¬ Fits 11 (regValue (expectedRow (Point.int 1) : Register 2) (limbs 2 (2 ^ 10) big)) := by
  have : regValue (expectedRow (Point.int 1) : Register 2) (limbs 2 (2 ^ 10) big) = 1534 := by
    decide +kernel
  rw [this]
  rintro ⟨-, -, h⟩
  simp [Shor.signedMax] at h

theorem ladderUnderTight_width : ladderWidthTight ladderUnder fixedTable 20 = 11 := by decide +kernel

/-- At the under-declared ladder the wrapped evaluation is wrong on the witness. -/
theorem tight_under_value :
    fixed.evalPhaseRegW (ladderWidthTight ladderUnder) 20 1 (fun _ => big)
      = (1 - 2 ^ 10) * 1023 ^ 2 + 2 ^ 10 * 514 ^ 2 + ((2 ^ 10) ^ 2 - 2 ^ 10) * 511 ^ 2 := by
  have hlt : ladderWidthTight ladderUnder fixedTable 20 < 20 := by
    rw [ladderUnderTight_width]; decide
  rw [BandedPolicy.evalPhaseRegW_node fixed _ (T := fixedTable) rfl hlt]
  have hleaf : fixed.choose (ladderWidthTight ladderUnder fixedTable 20) = none := by
    rw [ladderUnderTight_width]; rfl
  simp only [BandedPolicy.evalPhaseRegW_of_choose_none fixed _ hleaf]
  simp only [ladderUnderTight_width]
  show ∑ t : Fin 3, _ = _
  rw [Fin.sum_univ_three]
  simp only [regChild_under, wrap11, fixed_coeff_values]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]  -- v4.36 port: before arity unfolds
  simp [fixed, ProductMode.arity]

theorem tight_under_wrong :
    fixed.evalPhaseRegW (ladderWidthTight ladderUnder) 20 1 (fun _ => big)
      ≠ 1 * ∏ _s : Fin fixed.mode.arity, (big : ℚ) := by
  rw [tight_under_value]
  norm_num [fixed, ProductMode.arity, big]

end TableGeneration.PolicyMirror.Instances.TightChallenge
