import TableGeneration.RecursiveCost.PlanCore
import TableGeneration.RecursiveCost.BandedPolicy.Tight

/-!
# A Lean planner for banded policies, and validity of every output

`plan tables mode n o` is the output contract of the site planner
(`sto_site/engine/tcost/planner.py::optimal_policy (widths="exact")` followed by
`site_engine/seed_policies.py::canonical`): from the target width `n`, at each
visited width `w` take the table the oracle `o` names, emit the band `(w, table)`
and continue at the exact child width `tightWidth table w`; stop (leaf) when the
oracle names nothing or a non-contracting table; then merge consecutive bands with
the same table INDEX, keeping the lower threshold (equal tables at different indices
are not merged; the bridge passes a deduplicated list, as `canonical` merges by digest).

The **oracle** replaces the Python objective. It returns an index into `tables`
(`Fin tables.length`), so a table outside the given list cannot be named: that is
a typing fact, not a hypothesis.

Headline (for every oracle, every `n`):
* `plan_check`: if every table in `tables` passes `PolicyTable.check mode`, the plan
  passes `BandedPolicy.check`;
* `plan_correct`, `plan_correct_reg`, `plan_correct_tight`: the plan computes
  `φ · ∏ xs` (ideal semantics; wrapping registers at scanned widths; at exact widths);
* `plan_ladder`: the plan's exact-width ladder from `n` (widths and table sizes `k`)
  is the oracle's ladder; `plan_choose_visit`: at every visited width the plan selects
  exactly the table the oracle names there;
* `plan_sorted`, `plan_bands_mem` (no table hypothesis), and the rejections
  `plan_ne_of_unsorted`, `plan_ne_of_foreign`.

`planWith wd` is the same planner at an arbitrary width rule; `plan_check` and the
correctness corollaries hold for every `wd` (`planWith_check`).
-/

namespace TableGeneration.PolicyMirror

open TableGeneration TableGeneration.Operations TableGeneration.PlanCore

deriving instance DecidableEq for PolicyTable
deriving instance DecidableEq for Band
deriving instance DecidableEq for BandedPolicy

namespace Planner

/-- A choice oracle: at each width, an index into the verified table list, or
`none` (take the leaf). -/
abbrev Oracle (tables : List PolicyTable) := Nat → Option (Fin tables.length)

/-- The width rule on indices. -/
def idxWidth (wd : PolicyTable → Nat → Nat) (tables : List PolicyTable) :
    Fin tables.length → Nat → Nat :=
  fun i w => wd (tables.get i) w

/-- The planner at width rule `wd`. -/
def planWith (wd : PolicyTable → Nat → Nat) (tables : List PolicyTable) (mode : ProductMode)
    (n : Nat) (o : Oracle tables) : BandedPolicy where
  mode := mode
  bands := (planList (idxWidth wd tables) o n).map fun p => ⟨p.1, tables.get p.2⟩

/-- **The planner at exact widths** (the site's `widths="exact"`). -/
def plan (tables : List PolicyTable) (mode : ProductMode) (n : Nat) (o : Oracle tables) :
    BandedPolicy :=
  planWith PolicyTable.tightWidth tables mode n o

/-- The planner at scanned widths (the site's `widths="scan"`). -/
def planScan (tables : List PolicyTable) (mode : ProductMode) (n : Nat) (o : Oracle tables) :
    BandedPolicy :=
  planWith PolicyTable.childWidth tables mode n o

/-- An oracle from a finite table `(width, index)` (first entry for a width wins);
an index out of range, or a width not listed, is the leaf. -/
def oracleOfList (tables : List PolicyTable) (L : List (Nat × Nat)) : Oracle tables :=
  fun w =>
    match L.find? (fun p => decide (p.1 = w)) with
    | none => none
    | some p => if h : p.2 < tables.length then some ⟨p.2, h⟩ else none

theorem planWith_bands (wd : PolicyTable → Nat → Nat) (tables : List PolicyTable)
    (mode : ProductMode) (n : Nat) (o : Oracle tables) :
    (planWith wd tables mode n o).bands.map Band.threshold =
      (planList (idxWidth wd tables) o n).map Prod.fst := by
  simp [planWith, List.map_map, Function.comp_def]

/-- Thresholds strictly decrease, for every oracle, with no hypothesis on the tables. -/
theorem planWith_sorted (wd : PolicyTable → Nat → Nat) (tables : List PolicyTable)
    (mode : ProductMode) (n : Nat) (o : Oracle tables) :
    sortedDesc ((planWith wd tables mode n o).bands.map Band.threshold) = true := by
  rw [planWith_bands]; exact planList_sorted _ _ _

/-- Every band of a plan uses a table of the list, at a threshold `≤ n` where the
oracle named exactly that table and the table contracts. -/
theorem planWith_bands_mem (wd : PolicyTable → Nat → Nat) (tables : List PolicyTable)
    (mode : ProductMode) (n : Nat) (o : Oracle tables) :
    ∀ b ∈ (planWith wd tables mode n o).bands,
      b.table ∈ tables ∧ b.threshold ≤ n ∧
      (∃ i, o b.threshold = some i ∧ tables.get i = b.table) ∧
      wd b.table b.threshold < b.threshold := by
  intro b hb
  simp only [planWith, List.mem_map] at hb
  obtain ⟨p, hp, rfl⟩ := hb
  obtain ⟨hle, ho, hlt⟩ := planList_mem _ _ _ p hp
  exact ⟨List.get_mem _ _, hle, ⟨p.2, ho, rfl⟩, hlt⟩

/-- **Validity at any width rule.** -/
theorem planWith_check (wd : PolicyTable → Nat → Nat) (tables : List PolicyTable)
    (mode : ProductMode) (htab : ∀ T ∈ tables, T.check mode = true) (n : Nat)
    (o : Oracle tables) : (planWith wd tables mode n o).check = true := by
  unfold BandedPolicy.check
  rw [planWith_sorted, Bool.true_and, List.all_eq_true]
  intro b hb
  exact htab _ (planWith_bands_mem wd tables mode n o b hb).1

/-! ## The exact-width planner -/

/-- **`plan_check`: every planner output is a valid banded policy.** If every table
in `tables` passes STO's table contract for `mode`, then for every oracle and every
target width the planned policy passes `BandedPolicy.check`. -/
theorem plan_check (tables : List PolicyTable) (mode : ProductMode)
    (htab : ∀ T ∈ tables, T.check mode = true) (n : Nat) (o : Oracle tables) :
    (plan tables mode n o).check = true :=
  planWith_check _ tables mode htab n o

/-- The table hypothesis as one decidable `Bool` (what a kernel check discharges). -/
theorem plan_check_of_all (tables : List PolicyTable) (mode : ProductMode)
    (htab : tables.all (fun T => T.check mode) = true) (n : Nat) (o : Oracle tables) :
    (plan tables mode n o).check = true :=
  plan_check tables mode (fun T hT => List.all_eq_true.mp htab T hT) n o

theorem plan_sorted (tables : List PolicyTable) (mode : ProductMode) (n : Nat) (o : Oracle tables) :
    sortedDesc ((plan tables mode n o).bands.map Band.threshold) = true :=
  planWith_sorted _ tables mode n o

theorem plan_bands_mem (tables : List PolicyTable) (mode : ProductMode) (n : Nat) (o : Oracle tables) :
    ∀ b ∈ (plan tables mode n o).bands,
      b.table ∈ tables ∧ b.threshold ≤ n ∧
      (∃ i, o b.threshold = some i ∧ tables.get i = b.table) ∧
      b.table.tightWidth b.threshold < b.threshold :=
  planWith_bands_mem _ tables mode n o

/-- **`plan_correct`.** Every planner output computes `φ · ∏ xs` at every width. -/
theorem plan_correct (tables : List PolicyTable) (mode : ProductMode)
    (htab : ∀ T ∈ tables, T.check mode = true) (n : Nat) (o : Oracle tables) :
    ∀ (m : Nat) (φ : ℚ) (xs : Fin mode.arity → ℤ),
      (plan tables mode n o).evalPhase m φ xs = φ * ∏ s, (xs s : ℚ) :=
  evalPhase_correct_of_check _ (plan_check tables mode htab n o)

/-- Register-width soundness of every planner output at the scanned widths. -/
theorem plan_correct_reg (tables : List PolicyTable) (mode : ProductMode)
    (htab : ∀ T ∈ tables, T.check mode = true) (n : Nat) (o : Oracle tables) :
    ∀ (m : Nat) (φ : ℚ) (xs : Fin mode.arity → ℤ), (∀ s, Fits m (xs s)) →
      (plan tables mode n o).evalPhaseReg m φ xs = φ * ∏ s, (xs s : ℚ) :=
  fun m φ xs hxs => evalPhaseReg_correct _ (plan_check tables mode htab n o) m φ xs hxs

/-- **`plan_correct_tight`.** Every planner output, run on wrapping registers at the
exact widths, computes `φ · ∏ xs` on operands fitting `m` signed bits. -/
theorem plan_correct_tight (tables : List PolicyTable) (mode : ProductMode)
    (htab : ∀ T ∈ tables, T.check mode = true) (n : Nat) (o : Oracle tables) :
    ∀ (m : Nat) (φ : ℚ) (xs : Fin mode.arity → ℤ), (∀ s, Fits m (xs s)) →
      (plan tables mode n o).evalPhaseRegTight m φ xs = φ * ∏ s, (xs s : ℚ) :=
  fun m φ xs hxs => evalPhaseRegTight_correct _ (plan_check tables mode htab n o) m φ xs hxs

/-! ## The plan executes the oracle's choices -/

theorem planWith_choose (wd : PolicyTable → Nat → Nat) (tables : List PolicyTable)
    (mode : ProductMode) (n : Nat) (o : Oracle tables) (m : Nat) :
    (planWith wd tables mode n o).choose m =
      (chooseL (planList (idxWidth wd tables) o n) m).map tables.get := by
  simp only [BandedPolicy.choose, planWith, chooseL, List.find?_map, Option.map_map]
  rfl

theorem ladderTightFuel_eq (P : BandedPolicy) :
    ∀ f w, P.ladderTightFuel f w = ladderOf P.choose PolicyTable.tightWidth PolicyTable.k f w
  | 0, _ => rfl
  | f + 1, w => by
      simp only [BandedPolicy.ladderTightFuel, ladderOf]
      cases P.choose w with
      | none => rfl
      | some T =>
          simp only
          split
          · rw [ladderTightFuel_eq P f]
          · rfl

/-- **`plan_ladder`.** The planned policy, recursing at the exact widths from `n`,
uses at every node exactly the table the oracle names there and stops exactly where
the oracle stops (or names a non-contracting table). The merge of equal consecutive
bands changes nothing. -/
theorem plan_ladder (tables : List PolicyTable) (mode : ProductMode) (n : Nat)
    (o : Oracle tables) :
    (plan tables mode n o).ladderTight n =
      ladderOf (fun w => (o w).map tables.get) PolicyTable.tightWidth PolicyTable.k (n + 1) n := by
  unfold BandedPolicy.ladderTight
  rw [ladderTightFuel_eq]
  have hch : (plan tables mode n o).choose =
      fun m => (chooseL (planList (idxWidth PolicyTable.tightWidth tables) o n) m).map tables.get :=
    funext (planWith_choose _ tables mode n o)
  rw [hch, ladderOf_map, ladderOf_map]
  exact ladder_planList _ _ _ n


/-- **`plan_choose_visit`.** At every width `w` the exact-width walk from `n` visits,
the planned policy selects exactly the table the oracle names at `w` (the oracle's
choice `i` there contracts, and `choose w = tables[i]`), merge notwithstanding. -/
theorem plan_choose_visit (tables : List PolicyTable) (mode : ProductMode) (n : Nat)
    (o : Oracle tables) (w : Nat) (i : Fin tables.length)
    (hv : (w, i) ∈ walk (idxWidth PolicyTable.tightWidth tables) o (n + 1) n) :
    o w = some i ∧ (tables.get i).tightWidth w < w ∧
      (plan tables mode n o).choose w = some (tables.get i) := by
  refine ⟨(walk_mem _ o _ _ _ hv).1, (walk_mem _ o _ _ _ hv).2, ?_⟩
  rw [plan, planWith_choose, chooseL_planList_visit _ o n (w, i) hv]
  rfl

/-! ## What can never be a planner output -/

/-- A policy whose thresholds do not strictly decrease is the output of no oracle. -/
theorem plan_ne_of_unsorted (tables : List PolicyTable) (mode : ProductMode) (n : Nat)
    (P : BandedPolicy) (hP : sortedDesc (P.bands.map Band.threshold) = false) :
    ∀ o : Oracle tables, plan tables mode n o ≠ P := by
  intro o h
  have := plan_sorted tables mode n o
  rw [h, hP] at this
  cases this

/-- A policy with a band whose table is not in the list is the output of no oracle. -/
theorem plan_ne_of_foreign (tables : List PolicyTable) (mode : ProductMode) (n : Nat)
    (P : BandedPolicy) (b : Band) (hb : b ∈ P.bands) (hT : b.table ∉ tables) :
    ∀ o : Oracle tables, plan tables mode n o ≠ P := by
  intro o h
  subst h
  exact hT (plan_bands_mem tables mode n o b hb).1

end Planner

end TableGeneration.PolicyMirror
