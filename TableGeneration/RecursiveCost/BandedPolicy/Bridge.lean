import TableGeneration.RecursiveCost.BandedPolicy.Semantics
import TableGeneration.RecursiveCost.CompanionSoundness
import FastMultiplication.ShorVerification.Framework.Policy
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Coefficients

/-!
# One PhaseProduct policy, the same object in both repositories

For `PhaseProduct`, an accepted STO banded policy is transported to ForShor's
own policy object, and the transport is shown to preserve every ingredient
ForShor's recursion reads:

* **the submission** — `toShorPolicySubmission` builds a
  `Shor.ShorPolicySubmission` (every band a `Shor.ShorLoweringSetup` with
  C1–C4 discharged from STO's contract, thresholds strictly decreasing), so
  ForShor's generic `Shor.policy_submission_correct` applies to it in a
  ForShor build; its `policy` is `toForShor`;
* **the band choice** — `choose_toForShor`: ForShor's `choose` picks the
  transported table exactly where STO's picks the table, and the leaf exactly
  where STO's takes the leaf;
* **the child width** — `childWidth_eq_forshor`: STO's scan is ForShor's
  `Shor.nextSignedWidth` on two width-`n` registers, by `rfl`;
* **the limb width** — `limbWidth_eq_forshor`;
* **the phase coefficients** — `coeff_eq_forshor`: the weight a child
  receives here is ForShor's `phaseCoeffFromPtsWidth` at the same index.

`PhaseTripleProduct` has no ForShor counterpart and is not bridged.
-/

namespace TableGeneration.PolicyMirror

open TableGeneration.Operations TableGeneration.RecursiveCost

/-! ## Tables -/

theorem pointCount_pp (k : Nat) : ProductMode.PhaseProduct.pointCount k = Shor.q k := rfl

/-- C2 at size `m`, phrased with `listToFin` (as ForShor phrases it). -/
theorem pointRowQ_good_fin (pts : List Point) (m : Nat) (hm : pts.length = m)
    (h : pts.Pairwise DistinctPair) :
    ToomCookMath.GoodInterpolationPoints (row := pointRowQ m)
      (pts := ToomCookMath.listToFin pts hm) := by
  subst hm
  exact pointRowQ_good pts h

theorem interpEntry_transport (k : Nat) (p : Point) (j : Fin (Shor.q k)) :
    Shor.interpEntry k (Companion.toCompanionPoint p) j = pointRowQ (Shor.q k) p j := by
  cases p <;> rfl

theorem listToFin_transport (pts : List Point) (m : Nat) (h : pts.length = m)
    (h' : (Companion.toCompanionPoints pts).length = m) (i : Fin m) :
    ToomCookMath.listToFin (Companion.toCompanionPoints pts) h' i
      = Companion.toCompanionPoint (ToomCookMath.listToFin pts h i) := by
  simp [ToomCookMath.listToFin, Companion.toCompanionPoints]

/-- What a checked `PhaseProduct` table gives ForShor: `1 < k` and C1. -/
theorem check_pp_facts {T : PolicyTable} (h : T.check .PhaseProduct = true) :
    1 < T.k ∧ T.pts.length = Shor.q T.k := by
  obtain ⟨hk, ⟨hl, _, _⟩, _⟩ := (PolicyTable.check_iff _ T).mp h
  exact ⟨by omega, hl⟩

/-- A checked `PhaseProduct` table as a ForShor submission record, C1–C4
discharged from STO's contract. -/
def PolicyTable.toSetup (T : PolicyTable) (h : T.check .PhaseProduct = true) :
    Shor.ShorLoweringSetup where
  k := T.k
  hk := (check_pp_facts h).1
  pts := Companion.toCompanionPoints T.pts
  hpts := by simpa [Companion.toCompanionPoints] using (check_pp_facts h).2
  good := by
    obtain ⟨_, ⟨_, hn, _⟩, _⟩ := (PolicyTable.check_iff _ T).mp h
    have hg := pointRowQ_good_fin T.pts (Shor.q T.k) (check_pp_facts h).2
      (pairwise_distinct_of_nodup hn)
    unfold Shor.GoodToomCookPoints
    refine ToomCookMath.GoodInterpolationPoints.congr_matrix (fun i j => ?_) hg
    rw [listToFin_transport T.pts (Shor.q T.k) (check_pp_facts h).2, interpEntry_transport]
  ops := Companion.toCompanionProg T.ops
  consumes := by
    obtain ⟨hk, _, hsafe⟩ := (PolicyTable.check_iff _ T).mp h
    exact (CompanionSoundness.contract_sound_at_start hsafe).1
  returns := by
    obtain ⟨hk, _, hsafe⟩ := (PolicyTable.check_iff _ T).mp h
    exact (CompanionSoundness.contract_sound_at_start (hk := positive_of_ge_two hk) hsafe).2

/-! ## Policies -/

/-- Bands with their checks, transported band by band. -/
def bandsToSetups : (bs : List Band) → (∀ b ∈ bs, b.table.check .PhaseProduct = true) →
    List (Nat × Shor.ShorLoweringSetup)
  | [], _ => []
  | b :: bs, h =>
      (b.threshold, b.table.toSetup (h b List.mem_cons_self)) ::
        bandsToSetups bs (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))

theorem bandsToSetups_fst : ∀ (bs : List Band) (h : ∀ b ∈ bs, b.table.check .PhaseProduct = true),
    (bandsToSetups bs h).map Prod.fst = bs.map Band.threshold
  | [], _ => rfl
  | b :: bs, h => by simp [bandsToSetups, bandsToSetups_fst bs]

theorem check_pp_tables {P : BandedPolicy} (h : P.check = true) (hmode : P.mode = .PhaseProduct) :
    ∀ b ∈ P.bands, b.table.check .PhaseProduct = true := by
  rw [← hmode]; exact BandedPolicy.check_tables h

/-- **An accepted STO `PhaseProduct` policy is a ForShor policy submission.**
`Shor.policy_submission_correct` (ForShor `Submission/Correct.lean`) is generic
in the submission, so it applies to this value in a ForShor build. -/
def toShorPolicySubmission (P : BandedPolicy) (h : P.check = true)
    (hmode : P.mode = .PhaseProduct) : Shor.ShorPolicySubmission where
  bands := bandsToSetups P.bands (check_pp_tables h hmode)
  sorted := by rw [bandsToSetups_fst]; exact BandedPolicy.check_sorted h

/-- The ForShor policy an accepted STO `PhaseProduct` policy denotes. -/
def toForShor (P : BandedPolicy) (h : P.check = true) (hmode : P.mode = .PhaseProduct) :
    Shor.ShorLoweringPolicy :=
  (toShorPolicySubmission P h hmode).policy

/-- It is admissible in ForShor's sense (every band C1–C4). -/
theorem toForShor_admissible (P : BandedPolicy) (h : P.check = true)
    (hmode : P.mode = .PhaseProduct) : (toForShor P h hmode).Admissible :=
  (toShorPolicySubmission P h hmode).policy_admissible

theorem choose_bands : ∀ (bs : List Band) (h : ∀ b ∈ bs, b.table.check .PhaseProduct = true)
    (n : Nat),
    ((bs.find? (fun b => decide (b.threshold ≤ n))).map Band.table = none ∧
        (((bandsToSetups bs h).map (fun b => (⟨b.1, b.2.table⟩ : Shor.PolicyBand))).find?
          (fun b => decide (b.threshold ≤ n))).map Shor.PolicyBand.table = none) ∨
      ∃ (T : PolicyTable) (hT : T.check .PhaseProduct = true),
        (bs.find? (fun b => decide (b.threshold ≤ n))).map Band.table = some T ∧
        (((bandsToSetups bs h).map (fun b => (⟨b.1, b.2.table⟩ : Shor.PolicyBand))).find?
          (fun b => decide (b.threshold ≤ n))).map Shor.PolicyBand.table = some (T.toSetup hT).table
  | [], _, _ => Or.inl ⟨rfl, rfl⟩
  | b :: bs, h, n => by
      by_cases hb : b.threshold ≤ n
      · refine Or.inr ⟨b.table, h b List.mem_cons_self, ?_, ?_⟩
        · simp [hb]
        · simp [bandsToSetups, hb]
      · rcases choose_bands bs (fun b' hb' => h b' (List.mem_cons_of_mem _ hb')) n with
          ⟨h1, h2⟩ | ⟨T, hT, h1, h2⟩
        · left
          constructor
          · simp only [List.find?_cons, hb, decide_false]; exact h1
          · simp only [bandsToSetups, List.map_cons, List.find?_cons, hb, decide_false]; exact h2
        · right
          refine ⟨T, hT, ?_, ?_⟩
          · simp only [List.find?_cons, hb, decide_false]; exact h1
          · simp only [bandsToSetups, List.map_cons, List.find?_cons, hb, decide_false]; exact h2

/-- **Same band choice.** Where STO's policy takes the leaf, so does ForShor's;
where STO's picks a table, ForShor's picks that table, transported. -/
theorem choose_toForShor (P : BandedPolicy) (h : P.check = true) (hmode : P.mode = .PhaseProduct)
    (n : Nat) :
    (P.choose n = none ∧ (toForShor P h hmode).choose n = none) ∨
      ∃ (T : PolicyTable) (hT : T.check .PhaseProduct = true),
        P.choose n = some T ∧ (toForShor P h hmode).choose n = some (T.toSetup hT).table :=
  choose_bands P.bands (check_pp_tables h hmode) n

/-! ## Widths and coefficients -/

/-- **Same child width**: STO's scan is ForShor's `nextSignedWidth` on two
width-`n` registers (by `rfl`). -/
theorem childWidth_eq_forshor (T : PolicyTable) (hT : T.check .PhaseProduct = true) (n : Nat) :
    T.childWidth n = Shor.nextSignedWidth (Companion.canonicalExtReg n)
      (Companion.canonicalExtReg n) (T.toSetup hT).table.ops := rfl

/-- **Same limb width.** -/
theorem limbWidth_eq_forshor (T : PolicyTable) (n : Nat) :
    T.limbWidth n = Shor.phaseLimbWidth (Companion.canonicalExtReg n)
      (Companion.canonicalExtReg n) T.k :=
  phaseLimbWidth_eq_forshor n n T.k

theorem interpCoeff_reindex (pts : List Point) (m : Nat) (hm : pts.length = m) (B : ℚ)
    (t : Fin pts.length) :
    ToomCookMath.interpCoeff (pointRowQ pts.length) (fun i : Fin pts.length => pts.get i) B t
      = ToomCookMath.interpCoeff (pointRowQ m) (ToomCookMath.listToFin pts hm) B (Fin.cast hm t) := by
  subst hm
  rfl

/-- **Same phase coefficients**: the weight the `t`-th child receives is
ForShor's `phaseCoeffFromPtsWidth` at the same index and limb width. -/
theorem coeff_eq_forshor (T : PolicyTable) (hT : T.check .PhaseProduct = true) (n : Nat)
    (t : Fin T.pts.length) :
    T.coeff n t = Shor.phaseCoeffFromPtsWidth T.k (T.limbWidth n) (T.toSetup hT).pts
      (T.toSetup hT).hpts (Fin.cast (check_pp_facts hT).2 t) := by
  unfold PolicyTable.coeff
  rw [interpCoeff_reindex T.pts (Shor.q T.k) (check_pp_facts hT).2]
  unfold ToomCookMath.interpCoeff Shor.phaseCoeffFromPtsWidth Shor.phaseCoeffFromPts
  have hM : ToomCookMath.interpMatrix (pointRowQ (Shor.q T.k))
        (ToomCookMath.listToFin T.pts (check_pp_facts hT).2)
      = Shor.interpMatrix T.k (Shor.ptsToFin T.k (T.toSetup hT).pts (T.toSetup hT).hpts) := by
    ext i j
    simp only [ToomCookMath.interpMatrix, Shor.interpMatrix, Shor.ptsToFin, PolicyTable.toSetup]
    have := listToFin_transport T.pts (Shor.q T.k) (check_pp_facts hT).2
      (by simpa [Companion.toCompanionPoints] using (check_pp_facts hT).2) i
    simp only [ToomCookMath.listToFin] at this
    rw [this, interpEntry_transport]
    rfl
  simp only [hM]

end TableGeneration.PolicyMirror
