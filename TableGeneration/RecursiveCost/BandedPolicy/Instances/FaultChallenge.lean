import TableGeneration.RecursiveCost.BandedPolicy

/-!
# Fault challenge: the check is load-bearing

A tautology check for `evalPhase_correct` (ResearchSkills evidence-content
review; fault challenge with the reference held fixed). If the theorem were
true by construction — if `evalPhase` returned `φ · ∏ xs` whatever the table
did — then a policy that fails the check would still evaluate to `φ · ∏ xs`.
It does not.

The faulty table is a valid `k = 2` program that consumes its checkpoints in
the order `0, 1, ∞`, but declares the points in the order `0, ∞, 1` (the
order of the reference band). Everything else — the evaluator, the weights,
the reference `φ · ∏ xs` — is unchanged. STO's check rejects it
(`faulty_rejected`), and at width `20` with `a = b = 1` it applies phase
`(2^10 - 1)^2 = 1046529` instead of `1` (`faulty_wrong`).

The same table with the declared order corrected to `0, 1, ∞` passes the
check (`fixed_accepted`), so the defect is the point order alone.
-/

namespace TableGeneration.PolicyMirror.Instances.FaultChallenge

open TableGeneration TableGeneration.Operations TableGeneration.PolicyMirror

/-- Consumes `0`, then `1` (`x₀ + x₁`), then `∞` (`x₁`). -/
def ops : TableGeneration.Prog 2 :=
  [ .phaseProduct ⟨0, by decide⟩
  , .addScaled ⟨0, by decide⟩ ⟨1, by decide⟩ false 0
  , .phaseProduct ⟨0, by decide⟩
  , .addScaled ⟨0, by decide⟩ ⟨1, by decide⟩ true 0
  , .phaseProduct ⟨1, by decide⟩ ]

/-- Declares `0, ∞, 1`: the wrong order for `ops`. -/
abbrev faultyTable : PolicyTable := ⟨2, [Point.int 0, Point.frac 0, Point.int 1], ops⟩

/-- Declares `0, 1, ∞`: the order `ops` consumes. -/
abbrev fixedTable : PolicyTable := ⟨2, [Point.int 0, Point.int 1, Point.frac 0], ops⟩

def faulty : BandedPolicy := ⟨.PhaseProduct, [⟨20, faultyTable⟩]⟩
def fixed : BandedPolicy := ⟨.PhaseProduct, [⟨20, fixedTable⟩]⟩
-- Lean v4.36 port: `faultyTable` and `fixedTable` are `abbrev` (were `def`, same values) so that
-- tactics, which now check goals at reducible/instances transparency, see `….k = 2` (the
-- literals in this file are `Register 2`).

theorem faulty_rejected : faulty.check = false := by decide +kernel
theorem fixed_accepted : fixed.check = true := by decide +kernel

theorem childWidth_20 : faultyTable.childWidth 20 = 13 := by decide +kernel

/-- The interpolation matrix of `0, ∞, 1` and its inverse. -/
theorem inv_matrix :
    (ToomCookMath.interpMatrix (pointRowQ 3) (fun i : Fin 3 => faultyTable.pts.get i))⁻¹ =
      !![1, 0, 0; -1, -1, 1; 0, 1, 0] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ToomCookMath.interpMatrix, pointRowQ, faultyTable, Matrix.mul_apply, Fin.sum_univ_three]

theorem coeff_values (t : Fin 3) :
    faultyTable.coeff 20 t = ![1 - 2 ^ 10, (2 ^ 10) ^ 2 - 2 ^ 10, 2 ^ 10] t := by
  have hw : faultyTable.limbWidth 20 = 10 := by decide +kernel
  unfold PolicyTable.coeff ToomCookMath.interpCoeff
  simp only [hw]
  have h3 : faultyTable.pts.length = 3 := rfl
  -- the matrix is the 3 × 3 one above
  change (ToomCookMath.radixRow 3 ((2 : ℚ) ^ 10) *
      (ToomCookMath.interpMatrix (pointRowQ 3) (fun i : Fin 3 => faultyTable.pts.get i))⁻¹) 0 t = _
  rw [inv_matrix]
  fin_cases t <;> simp [ToomCookMath.radixRow, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- The rows the faulty program actually produces: `e₀`, `e₀ + e₁`, `e₁`. -/
theorem rows : checkpointRows State.start_state faultyTable.ops =
    some ([![1, 0], ![1, 1], ![0, 1]] : List (Register 2)) := by decide +kernel

theorem child0 : faultyTable.childOperand 20 ![1, 0] 1 = 1 := by decide +kernel
theorem child1 : faultyTable.childOperand 20 ![1, 1] 1 = 1 := by decide +kernel
theorem child2 : faultyTable.childOperand 20 ![0, 1] 1 = 0 := by decide +kernel

/-- The faulty policy at width 20 on `a = b = 1` applies phase `1046529`, not `1`. -/
theorem faulty_value : faulty.evalPhase 20 1 (fun _ => 1) = 1046529 := by
  have hlt : faultyTable.childWidth 20 < 20 := by rw [childWidth_20]; decide
  rw [BandedPolicy.evalPhase_of_rows faulty (T := faultyTable) rfl hlt rows]
  have hleaf : faulty.choose (faultyTable.childWidth 20) = none := by
    rw [childWidth_20]; rfl
  simp only [BandedPolicy.evalPhase_of_choose_none faulty hleaf]
  show ∑ t : Fin 3, _ = _
  rw [Fin.sum_univ_three]
  simp only [coeff_values]
  have hl : faultyTable.pts.length = 3 := rfl
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]  -- v4.36 port: before arity unfolds
  simp [hl, child0, child1, child2, faulty, ProductMode.arity]
  norm_num

/-- The check is load-bearing: a policy failing it can evaluate wrongly. -/
theorem faulty_wrong : faulty.evalPhase 20 1 (fun _ => 1) ≠ 1 * ∏ _s : Fin faulty.mode.arity, (1 : ℚ) := by
  rw [faulty_value]
  norm_num [faulty, ProductMode.arity]

/-! ## Width fault: an under-declared working width

The fixed (accepted) policy, evaluated on registers whose working width is
declared by a ladder. The Lean scan gives working width `13` at `n = 20`
(`childWidth_20`). The ladder `20 → 13` is accepted (`declared_ok`); the ladder
`20 → 11` is below the scan and is rejected (`declared_under_rejected`). The scan is
conservative: 12 bits would in fact suffice here, and `20 → 12` is also rejected. On the
operands `a = b = 2^19 - 1` (both fit 20 signed bits) the program's
intermediate `x₀ + x₁ = 1023 + 511 = 1534` does not fit 11 bits and wraps to
`-514`, so the wrapped evaluation is not `a · b` (`width_fault_wrong`). The
same evaluator at the declared-ok ladder gives `a · b`
(`declared_correct` instance `width_fixed_correct`). -/

def ladderOK : List (ℕ × Option ℕ) := [(20, some 2), (13, none)]
def ladderUnder : List (ℕ × Option ℕ) := [(20, some 2), (11, none)]

theorem declared_ok : fixed.declOK ladderOK = true := by decide +kernel
theorem declared_under_rejected : fixed.declOK ladderUnder = false := by decide +kernel

/-- Conservative: one bit below the scan is rejected too (12 bits would suffice). -/
theorem declared_12_rejected : fixed.declOK [(20, some 2), (12, none)] = false := by decide +kernel
/-- A wrong `k` tag, even at a leaf width, is rejected. -/
theorem declared_badk_rejected : fixed.declOK [(20, some 2), (13, some 7)] = false := by decide +kernel
/-- A declared step that does not shrink is rejected. -/
theorem declared_nonshrink_rejected : fixed.declOK [(20, some 2), (25, none)] = false := by decide +kernel

theorem ladderUnder_width : ladderWidth ladderUnder fixedTable 20 = 11 := by decide +kernel

/-- The operand `2^19 - 1 = 511 · 2^10 + 1023`. -/
def big : ℤ := 524287

theorem big_fits : Fits 20 big := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> simp [Shor.signedMin, Shor.signedMax, big]

/-- The wrapped checkpoint values at working width 11: `1023`, `1534 ↦ -514`, `511`. -/
theorem regChild_under (t : Fin 3) :
    fixedTable.regChild 20 11 big t = ![1023, -514, 511] t := by
  fin_cases t <;> decide +kernel

theorem wrap11 (t : Fin 3) : wrap 11 (![1023, -514, 511] t) = ![1023, -514, 511] t := by
  fin_cases t <;> decide +kernel

theorem fixed_inv_matrix :
    (ToomCookMath.interpMatrix (pointRowQ 3) (fun i : Fin 3 => fixedTable.pts.get i))⁻¹ =
      !![1, 0, 0; -1, 1, -1; 0, 0, 1] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ToomCookMath.interpMatrix, pointRowQ, fixedTable, Matrix.mul_apply, Fin.sum_univ_three]

theorem fixed_coeff_values (t : Fin 3) :
    fixedTable.coeff 20 t = ![1 - 2 ^ 10, 2 ^ 10, (2 ^ 10) ^ 2 - 2 ^ 10] t := by
  have hw : fixedTable.limbWidth 20 = 10 := by decide +kernel
  unfold PolicyTable.coeff ToomCookMath.interpCoeff
  simp only [hw]
  change (ToomCookMath.radixRow 3 ((2 : ℚ) ^ 10) *
      (ToomCookMath.interpMatrix (pointRowQ 3) (fun i : Fin 3 => fixedTable.pts.get i))⁻¹) 0 t = _
  rw [fixed_inv_matrix]
  fin_cases t <;> simp [ToomCookMath.radixRow, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- At the under-declared ladder the wrapped evaluation is `(1 - B)·1023² + B·514² + (B² - B)·511²`
with `B = 2^10`. -/
theorem width_fault_value :
    fixed.evalPhaseRegW (ladderWidth ladderUnder) 20 1 (fun _ => big)
      = (1 - 2 ^ 10) * 1023 ^ 2 + 2 ^ 10 * 514 ^ 2 + ((2 ^ 10) ^ 2 - 2 ^ 10) * 511 ^ 2 := by
  have hlt : ladderWidth ladderUnder fixedTable 20 < 20 := by rw [ladderUnder_width]; decide
  rw [BandedPolicy.evalPhaseRegW_node fixed _ (T := fixedTable) rfl hlt]
  have hleaf : fixed.choose (ladderWidth ladderUnder fixedTable 20) = none := by
    rw [ladderUnder_width]; rfl
  simp only [BandedPolicy.evalPhaseRegW_of_choose_none fixed _ hleaf]
  simp only [ladderUnder_width]
  show ∑ t : Fin 3, _ = _
  rw [Fin.sum_univ_three]
  simp only [regChild_under, wrap11, fixed_coeff_values]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]  -- v4.36 port: before arity unfolds
  simp [fixed, ProductMode.arity]

/-- **The width fault is real**: an under-declared working width makes the
wrapped evaluation wrong on operands that fit `n` bits. -/
theorem width_fault_wrong :
    fixed.evalPhaseRegW (ladderWidth ladderUnder) 20 1 (fun _ => big)
      ≠ 1 * ∏ _s : Fin fixed.mode.arity, (big : ℚ) := by
  rw [width_fault_value]
  norm_num [fixed, ProductMode.arity, big]

/-- The same evaluator at the accepted ladder is exact, for every operand pair fitting 20 bits. -/
theorem width_fixed_correct (φ : ℚ) (xs : Fin fixed.mode.arity → ℤ) (hxs : ∀ s, Fits 20 (xs s)) :
    fixed.evalPhaseRegW (ladderWidth ladderOK) 20 φ xs = φ * ∏ s, (xs s : ℚ) :=
  declared_correct fixed fixed_accepted ladderOK declared_ok 20 φ xs hxs

end TableGeneration.PolicyMirror.Instances.FaultChallenge
