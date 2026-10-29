import TableGeneration.RecursiveCost.PlanCore
import TableGeneration.RecursiveCost.PTP.Exact

/-!
# A Lean planner for banded PTP policies, and validity of every output

The PhaseTripleProduct analogue of the mirror's `BandedPolicy/Plan.lean`, against
`PTPPolicy.check` (sorted thresholds, every band passes `PTPTable.contract`).
`plan tables n o` walks from `n` at the exact PTP widths `ptpTightWidth`, taking at
each width the table the oracle names (an index into `tables`), stops at the leaf
when the oracle names nothing or a non-contracting table, and merges consecutive
bands with equal table INDEX keeping the lower threshold (`seed_policies.canonical`,
which merges by digest; the bridge passes a deduplicated list).

Headline (every oracle, every `n`): `plan_check`, `plan_correct`
(`evalPhase_correct`), `plan_correct_w` (`evalPhaseW_correct`), `plan_correct_tight`
(`evalPhaseTight_correct`), `plan_ladder` (`ladderX n` is the oracle's (width, k) ladder), `plan_choose_visit`
(at every visited width the plan selects the oracle's table),
`plan_ne_of_unsorted`, `plan_ne_of_foreign`.
-/

namespace TableGeneration.PTP

open TableGeneration TableGeneration.Operations TableGeneration.PlanCore
open TableGeneration.PolicyMirror (sortedDesc)

deriving instance DecidableEq for PTPTable
deriving instance DecidableEq for PTPBand
deriving instance DecidableEq for PTPPolicy

namespace Planner

/-- A choice oracle: at each width, an index into the verified PTP table list, or `none`. -/
abbrev Oracle (tables : List PTPTable) := Nat → Option (Fin tables.length)

def idxWidth (wd : PTPTable → Nat → Nat) (tables : List PTPTable) :
    Fin tables.length → Nat → Nat :=
  fun i w => wd (tables.get i) w

/-- The PTP planner at width rule `wd`. -/
def planWith (wd : PTPTable → Nat → Nat) (tables : List PTPTable) (n : Nat)
    (o : Oracle tables) : PTPPolicy where
  bands := (planList (idxWidth wd tables) o n).map fun p => ⟨p.1, tables.get p.2⟩

/-- **The PTP planner at exact widths.** -/
def plan (tables : List PTPTable) (n : Nat) (o : Oracle tables) : PTPPolicy :=
  planWith ptpTightWidth tables n o

/-- The PTP planner at scanned widths. -/
def planScan (tables : List PTPTable) (n : Nat) (o : Oracle tables) : PTPPolicy :=
  planWith (fun T w => childWidth w T.ops) tables n o

/-- An oracle from a finite table `(width, index)`; a missing width or an index out of
range is the leaf. -/
def oracleOfList (tables : List PTPTable) (L : List (Nat × Nat)) : Oracle tables :=
  fun w =>
    match L.find? (fun p => decide (p.1 = w)) with
    | none => none
    | some p => if h : p.2 < tables.length then some ⟨p.2, h⟩ else none

theorem planWith_sorted (wd : PTPTable → Nat → Nat) (tables : List PTPTable) (n : Nat)
    (o : Oracle tables) :
    sortedDesc ((planWith wd tables n o).bands.map PTPBand.threshold) = true := by
  have : (planWith wd tables n o).bands.map PTPBand.threshold =
      (planList (idxWidth wd tables) o n).map Prod.fst := by
    simp [planWith, List.map_map, Function.comp_def]
  rw [this]; exact planList_sorted _ _ _

theorem planWith_bands_mem (wd : PTPTable → Nat → Nat) (tables : List PTPTable) (n : Nat)
    (o : Oracle tables) :
    ∀ b ∈ (planWith wd tables n o).bands,
      b.table ∈ tables ∧ b.threshold ≤ n ∧
      (∃ i, o b.threshold = some i ∧ tables.get i = b.table) ∧
      wd b.table b.threshold < b.threshold := by
  intro b hb
  simp only [planWith, List.mem_map] at hb
  obtain ⟨p, hp, rfl⟩ := hb
  obtain ⟨hle, ho, hlt⟩ := planList_mem _ _ _ p hp
  exact ⟨List.get_mem _ _, hle, ⟨p.2, ho, rfl⟩, hlt⟩

theorem planWith_check (wd : PTPTable → Nat → Nat) (tables : List PTPTable)
    (htab : ∀ T ∈ tables, T.contract = true) (n : Nat) (o : Oracle tables) :
    (planWith wd tables n o).check = true := by
  unfold PTPPolicy.check
  rw [planWith_sorted, Bool.true_and, List.all_eq_true]
  intro b hb
  exact htab _ (planWith_bands_mem wd tables n o b hb).1

/-- **`plan_check` (PTP): every planner output passes `PTPPolicy.check`.** -/
theorem plan_check (tables : List PTPTable) (htab : ∀ T ∈ tables, T.contract = true) (n : Nat)
    (o : Oracle tables) : (plan tables n o).check = true :=
  planWith_check _ tables htab n o

theorem plan_check_of_all (tables : List PTPTable) (htab : tables.all PTPTable.contract = true)
    (n : Nat) (o : Oracle tables) : (plan tables n o).check = true :=
  plan_check tables (fun T hT => List.all_eq_true.mp htab T hT) n o

theorem plan_sorted (tables : List PTPTable) (n : Nat) (o : Oracle tables) :
    sortedDesc ((plan tables n o).bands.map PTPBand.threshold) = true :=
  planWith_sorted _ tables n o

theorem plan_bands_mem (tables : List PTPTable) (n : Nat) (o : Oracle tables) :
    ∀ b ∈ (plan tables n o).bands,
      b.table ∈ tables ∧ b.threshold ≤ n ∧
      (∃ i, o b.threshold = some i ∧ tables.get i = b.table) ∧
      ptpTightWidth b.table b.threshold < b.threshold :=
  planWith_bands_mem _ tables n o

/-- **`plan_correct` (PTP).** -/
theorem plan_correct (tables : List PTPTable) (htab : ∀ T ∈ tables, T.contract = true) (n : Nat)
    (o : Oracle tables) :
    ∀ (m : ℕ) (φ : ℚ) (x : Fin 3 → ℤ), (plan tables n o).evalPhase m φ x = φ * x 0 * x 1 * x 2 :=
  evalPhase_correct _ (plan_check tables htab n o)

/-- Wrapping-register correctness of every PTP planner output at the scanned widths. -/
theorem plan_correct_w (tables : List PTPTable) (htab : ∀ T ∈ tables, T.contract = true) (n : Nat)
    (o : Oracle tables) :
    ∀ (m : ℕ) (φ : ℚ) (x : Fin 3 → ℤ), (∀ s, Shor.FitsSignedWidth m (x s)) →
      (plan tables n o).evalPhaseW m φ x = φ * x 0 * x 1 * x 2 :=
  evalPhaseW_correct _ (plan_check tables htab n o)

/-- **`plan_correct_tight` (PTP).** Every PTP planner output is correct on the exact board. -/
theorem plan_correct_tight (tables : List PTPTable) (htab : ∀ T ∈ tables, T.contract = true)
    (n : Nat) (o : Oracle tables) :
    ∀ (m : ℕ) (φ : ℚ) (x : Fin 3 → ℤ), (∀ s, Shor.FitsSignedWidth m (x s)) →
      (plan tables n o).evalPhaseTight m φ x = φ * x 0 * x 1 * x 2 :=
  evalPhaseTight_correct _ (plan_check tables htab n o)

theorem planWith_choose (wd : PTPTable → Nat → Nat) (tables : List PTPTable) (n : Nat)
    (o : Oracle tables) (m : Nat) :
    (planWith wd tables n o).choose m =
      (chooseL (planList (idxWidth wd tables) o n) m).map tables.get := by
  simp only [PTPPolicy.choose, planWith, chooseL, List.find?_map, Option.map_map]
  rfl

theorem ladderFuelX_eq (P : PTPPolicy) :
    ∀ f w, P.ladderFuelX f w = ladderOf P.choose ptpTightWidth PTPTable.k f w
  | 0, _ => rfl
  | f + 1, w => by
      simp only [PTPPolicy.ladderFuelX, ladderOf]
      cases P.choose w with
      | none => rfl
      | some T =>
          simp only
          split
          · rw [ladderFuelX_eq P f]
          · rfl

/-- **`plan_ladder` (PTP).** On the exact board the plan takes exactly the oracle's choices. -/
theorem plan_ladder (tables : List PTPTable) (n : Nat) (o : Oracle tables) :
    (plan tables n o).ladderX n =
      ladderOf (fun w => (o w).map tables.get) ptpTightWidth PTPTable.k (n + 1) n := by
  unfold PTPPolicy.ladderX
  rw [ladderFuelX_eq]
  have hch : (plan tables n o).choose =
      fun m => (chooseL (planList (idxWidth ptpTightWidth tables) o n) m).map tables.get :=
    funext (planWith_choose _ tables n o)
  rw [hch, ladderOf_map, ladderOf_map]
  exact ladder_planList _ _ _ n


/-- **`plan_choose_visit`.** At every width `w` the exact-width walk from `n` visits,
the planned policy selects exactly the table the oracle names at `w` (the oracle's
choice `i` there contracts, and `choose w = tables[i]`), merge notwithstanding. -/
theorem plan_choose_visit (tables : List PTPTable) (n : Nat)
    (o : Oracle tables) (w : Nat) (i : Fin tables.length)
    (hv : (w, i) ∈ walk (idxWidth ptpTightWidth tables) o (n + 1) n) :
    o w = some i ∧ ptpTightWidth (tables.get i) w < w ∧
      (plan tables n o).choose w = some (tables.get i) := by
  refine ⟨(walk_mem _ o _ _ _ hv).1, (walk_mem _ o _ _ _ hv).2, ?_⟩
  rw [plan, planWith_choose, chooseL_planList_visit _ o n (w, i) hv]
  rfl

theorem plan_ne_of_unsorted (tables : List PTPTable) (n : Nat) (P : PTPPolicy)
    (hP : sortedDesc (P.bands.map PTPBand.threshold) = false) :
    ∀ o : Oracle tables, plan tables n o ≠ P := by
  intro o h
  have := plan_sorted tables n o
  rw [h, hP] at this
  cases this

theorem plan_ne_of_foreign (tables : List PTPTable) (n : Nat) (P : PTPPolicy) (b : PTPBand)
    (hb : b ∈ P.bands) (hT : b.table ∉ tables) :
    ∀ o : Oracle tables, plan tables n o ≠ P := by
  intro o h
  subst h
  exact hT (plan_bands_mem tables n o b hb).1

end Planner

end TableGeneration.PTP
