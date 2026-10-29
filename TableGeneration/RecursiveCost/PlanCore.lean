import TableGeneration.RecursiveCost.BandedPolicy.Defs

/-!
# A planner skeleton for banded policies, generic over the table type

This file is shared verbatim by the STO policy mirror (`BandedPolicy/Plan.lean`,
PhaseProduct / PhaseTripleProduct over `PolicyTable`) and the PTP suite
(`PTP/Plan.lean`, over `PTPTable`). It is Mathlib-free.

A planner in the sense of the site (`sto_site/engine/tcost/planner.py`,
`optimal_policy` followed by `seed_policies.canonical`) does two things:

1. **walk** (`_extract`): from the target width `n`, repeatedly pick a table at the
   current width `w`, emit the band `(w, table)` and continue at the child width
   `wd table w`; stop (leaf) when no table is picked or the picked table does not
   contract (`wd table w < w` fails). The Python DP only ever picks contracting
   tables (`if w2 < w`), and only ever picks from its candidate list.
2. **merge** (`canonical`): merge consecutive bands with the same table, keeping
   the lower threshold. Here "same" is equality of the element type `α`; the
   planners instantiate `α` with an index `Fin tables.length`, so two equal tables at
   different indices are NOT merged (the bridge passes a deduplicated list, as
   Python's `canonical`, which merges by digest).

Here the per-width choice is an arbitrary **oracle** `o : ℕ → Option α`. The
objective (T count, the delta fixed point, the one-table-per-k repair) only
affects *which* oracle the Python planner realises; every theorem below holds
for every oracle and every width function `wd`.

Main facts (all oracles, all `wd`):
* `walk_sorted`, `merge_sorted`: the thresholds strictly decrease;
* `walk_mem`, `merge_mem`: every emitted entry is an oracle choice at its threshold
  that contracts there;
* `chooseL_merge`: merging does not change first-match selection (`choose`) at any width;
* `ladder_walk`: any chooser that agrees with first-match selection on the walk
  produces exactly the oracle's ladder.
-/

namespace TableGeneration.PlanCore

open TableGeneration.PolicyMirror

variable {α : Type}

/-- The walk down from width `w` with fuel `f`: at each width the oracle's choice,
kept only when it contracts. -/
def walk (wd : α → Nat → Nat) (o : Nat → Option α) : Nat → Nat → List (Nat × α)
  | 0, _ => []
  | f + 1, w =>
      match o w with
      | none => []
      | some a => if wd a w < w then (w, a) :: walk wd o f (wd a w) else []

/-- Merge consecutive entries carrying the same table, keeping the later (lower)
threshold: `seed_policies.canonical`. -/
def merge [DecidableEq α] : List (Nat × α) → List (Nat × α)
  | [] => []
  | p :: rest =>
      match merge rest with
      | [] => [p]
      | q :: r => if p.2 = q.2 then q :: r else p :: q :: r

/-- First-match selection on a list of `(threshold, table)` (ForShor's `choose`). -/
def chooseL (L : List (Nat × α)) (m : Nat) : Option α :=
  (L.find? (fun p => decide (p.1 ≤ m))).map Prod.snd

/-- The ladder a chooser produces from `w` under width rule `wd`, recording `key`
(the table size `k`) at each recursive node: the shape of `ladderTightFuel`. -/
def ladderOf (ch : Nat → Option α) (wd : α → Nat → Nat) (key : α → Nat) :
    Nat → Nat → List (Nat × Option Nat)
  | 0, w => [(w, none)]
  | f + 1, w =>
      match ch w with
      | none => [(w, none)]
      | some a => if wd a w < w then (w, some (key a)) :: ladderOf ch wd key f (wd a w)
                  else [(w, none)]

/-! ## Sortedness -/

theorem sortedDesc_cons (a : Nat) (l : List Nat) :
    sortedDesc (a :: l) = true ↔ (∀ b ∈ l.head?, b < a) ∧ sortedDesc l = true := by
  cases l with
  | nil => simp [sortedDesc]
  | cons b t => simp [sortedDesc]

theorem sortedDesc_lt_head : ∀ (a : Nat) (l : List Nat), sortedDesc (a :: l) = true → ∀ b ∈ l, b < a
  | _, [], _, _, hb => by simp at hb
  | a, c :: t, h, b, hb => by
      rw [sortedDesc_cons] at h
      have hc : c < a := h.1 c (by simp)
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hc
      · exact Nat.lt_trans (sortedDesc_lt_head c t h.2 b hb') hc

theorem walk_le (wd : α → Nat → Nat) (o : Nat → Option α) :
    ∀ (f w : Nat), ∀ p ∈ walk wd o f w, p.1 ≤ w
  | 0, _, p, hp => by simp [walk] at hp
  | f + 1, w, p, hp => by
      simp only [walk] at hp
      split at hp
      · simp at hp
      · rename_i a _
        split at hp
        · rename_i hlt
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact Nat.le_refl _
          · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (walk_le wd o f _ p hp') hlt)
        · simp at hp

/-- Every entry of the walk is the oracle's choice at its threshold, and contracts there. -/
theorem walk_mem (wd : α → Nat → Nat) (o : Nat → Option α) :
    ∀ (f w : Nat), ∀ p ∈ walk wd o f w, o p.1 = some p.2 ∧ wd p.2 p.1 < p.1
  | 0, _, p, hp => by simp [walk] at hp
  | f + 1, w, p, hp => by
      simp only [walk] at hp
      split at hp
      · simp at hp
      · rename_i a ho
        split at hp
        · rename_i hlt
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact ⟨ho, hlt⟩
          · exact walk_mem wd o f _ p hp'
        · simp at hp

theorem walk_sorted (wd : α → Nat → Nat) (o : Nat → Option α) :
    ∀ (f w : Nat), sortedDesc ((walk wd o f w).map Prod.fst) = true
  | 0, _ => by simp [walk, sortedDesc]
  | f + 1, w => by
      simp only [walk]
      split
      · simp [sortedDesc]
      · rename_i a _
        split
        · rename_i hlt
          simp only [List.map_cons]
          rw [sortedDesc_cons]
          refine ⟨?_, walk_sorted wd o f _⟩
          intro b hb
          cases hL : walk wd o f (wd a w) with
          | nil => rw [hL] at hb; simp at hb
          | cons q r =>
              rw [hL] at hb
              simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hb
              subst hb
              exact Nat.lt_of_le_of_lt (walk_le wd o f _ q (by rw [hL]; simp)) hlt
        · simp [sortedDesc]

theorem merge_mem [DecidableEq α] : ∀ (L : List (Nat × α)), ∀ q ∈ merge L, q ∈ L
  | [], q, hq => by simp [merge] at hq
  | p :: rest, q, hq => by
      have ih := merge_mem rest
      simp only [merge] at hq
      split at hq
      · simp only [List.mem_singleton] at hq; subst hq; simp
      · rename_i q' r hm
        split at hq
        · exact List.mem_cons_of_mem _ (ih q (by rw [hm]; exact hq))
        · rcases List.mem_cons.mp hq with rfl | hq'
          · simp
          · exact List.mem_cons_of_mem _ (ih q (by rw [hm]; exact hq'))

theorem merge_sorted [DecidableEq α] :
    ∀ (L : List (Nat × α)), sortedDesc (L.map Prod.fst) = true →
      sortedDesc ((merge L).map Prod.fst) = true
  | [], _ => by simp [merge, sortedDesc]
  | p :: rest, h => by
      have hs : sortedDesc (rest.map Prod.fst) = true := ((sortedDesc_cons _ _).mp h).2
      have ih := merge_sorted rest hs
      have hlt : ∀ q ∈ rest, q.1 < p.1 := fun q hq =>
        sortedDesc_lt_head p.1 (rest.map Prod.fst) h q.1 (List.mem_map_of_mem hq)
      simp only [merge]
      split
      · simp [sortedDesc]
      · rename_i q r hm
        rw [hm] at ih
        split
        · exact ih
        · simp only [List.map_cons] at ih ⊢
          rw [sortedDesc_cons]
          refine ⟨?_, ih⟩
          intro b hb
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
          subst hb
          exact hlt q (merge_mem rest q (by rw [hm]; simp))

/-! ## Selection -/

theorem chooseL_nil (m : Nat) : chooseL ([] : List (Nat × α)) m = none := rfl

theorem chooseL_cons (p : Nat × α) (L : List (Nat × α)) (m : Nat) :
    chooseL (p :: L) m = if p.1 ≤ m then some p.2 else chooseL L m := by
  unfold chooseL
  by_cases h : p.1 ≤ m <;> simp [h]

/-- Merging consecutive equal tables does not change first-match selection at any
width (on a strictly decreasing list). -/
theorem chooseL_merge [DecidableEq α] :
    ∀ (L : List (Nat × α)), sortedDesc (L.map Prod.fst) = true →
      ∀ m, chooseL (merge L) m = chooseL L m
  | [], _, _ => rfl
  | p :: rest, h, m => by
      have hs : sortedDesc (rest.map Prod.fst) = true := ((sortedDesc_cons _ _).mp h).2
      have ih := chooseL_merge rest hs m
      have hlt : ∀ q ∈ rest, q.1 < p.1 := fun q hq =>
        sortedDesc_lt_head p.1 (rest.map Prod.fst) h q.1 (List.mem_map_of_mem hq)
      rw [chooseL_cons]
      simp only [merge]
      split
      · rename_i hm
        rw [hm] at ih
        rw [chooseL_cons, ← ih]
      · rename_i q r hm
        rw [hm] at ih
        split
        · rename_i heq
          have hq : q.1 < p.1 := hlt q (merge_mem rest q (by rw [hm]; simp))
          by_cases hpm : p.1 ≤ m
          · rw [if_pos hpm, chooseL_cons, if_pos (Nat.le_trans (Nat.le_of_lt hq) hpm), heq]
          · rw [if_neg hpm, ih]
        · rw [chooseL_cons, ← ih]

theorem chooseL_walk_cons (wd : α → Nat → Nat) (o : Nat → Option α) (f w : Nat) (a : Nat × α)
    {m : Nat} (hm : m < a.1) :
    chooseL (a :: walk wd o f w) m = chooseL (walk wd o f w) m := by
  rw [chooseL_cons, if_neg (Nat.not_le_of_lt hm)]


/-- At every width the walk visits, first-match selection on the walk returns exactly
the table the oracle named there. -/
theorem chooseL_walk_of_mem (wd : α → Nat → Nat) (o : Nat → Option α) :
    ∀ (f v : Nat) (p : Nat × α), p ∈ walk wd o f v → chooseL (walk wd o f v) p.1 = some p.2
  | 0, _, p, hp => by simp [walk] at hp
  | f + 1, v, p, hp => by
      simp only [walk] at hp ⊢
      split at hp
      · simp at hp
      · rename_i a ho
        split at hp
        · rename_i hlt
          rw [if_pos hlt]
          rcases List.mem_cons.mp hp with rfl | hp'
          · rw [chooseL_cons, if_pos (Nat.le_refl _)]
          · have hle := walk_le wd o f _ p hp'
            rw [chooseL_cons, if_neg (Nat.not_le_of_lt (Nat.lt_of_le_of_lt hle hlt))]
            exact chooseL_walk_of_mem wd o f _ p hp'
        · simp at hp

/-! ## The ladder of the planned chooser is the oracle's ladder -/

/-- Any chooser that agrees, at every width `≤ w`, with first-match selection on the
walk from `w` produces exactly the oracle's ladder from `w`. -/
theorem ladder_walk (wd : α → Nat → Nat) (o : Nat → Option α) (key : α → Nat)
    (ch : Nat → Option α) :
    ∀ (f w : Nat), (∀ m ≤ w, ch m = chooseL (walk wd o f w) m) →
      ladderOf ch wd key f w = ladderOf o wd key f w
  | 0, _, _ => rfl
  | f + 1, w, hch => by
      have hw := hch w (Nat.le_refl _)
      simp only [walk] at hw hch
      simp only [ladderOf]
      cases ho : o w with
      | none =>
          rw [ho] at hw
          simp only at hw
          rw [hw]; rfl
      | some a =>
          rw [ho] at hw hch
          simp only at hw hch
          by_cases hlt : wd a w < w
          · rw [if_pos hlt] at hw hch
            rw [chooseL_cons, if_pos (Nat.le_refl _)] at hw
            rw [hw]
            simp only [if_pos hlt]
            congr 1
            refine ladder_walk wd o key ch f (wd a w) (fun m hm => ?_)
            rw [hch m (Nat.le_trans hm (Nat.le_of_lt hlt))]
            exact chooseL_walk_cons wd o f (wd a w) (w, a) (Nat.lt_of_le_of_lt hm hlt)
          · rw [if_neg hlt] at hw
            rw [hw]
            simp only [if_neg hlt]
            rfl

/-- Transport of a ladder along a map of table types. -/
theorem ladderOf_map {β : Type} (g : α → β) (ch : Nat → Option α) (wd : β → Nat → Nat)
    (key : β → Nat) :
    ∀ (f w : Nat), ladderOf (fun m => (ch m).map g) wd key f w =
      ladderOf ch (fun a => wd (g a)) (fun a => key (g a)) f w
  | 0, _ => rfl
  | f + 1, w => by
      simp only [ladderOf]
      cases ch w with
      | none => rfl
      | some a =>
          simp only [Option.map_some]
          split
          · rw [ladderOf_map g ch wd key f]
          · rfl

/-- The planned list: walk from `n` with fuel `n + 1`, then merge. -/
def planList [DecidableEq α] (wd : α → Nat → Nat) (o : Nat → Option α) (n : Nat) :
    List (Nat × α) :=
  merge (walk wd o (n + 1) n)

theorem planList_sorted [DecidableEq α] (wd : α → Nat → Nat) (o : Nat → Option α) (n : Nat) :
    sortedDesc ((planList wd o n).map Prod.fst) = true :=
  merge_sorted _ (walk_sorted wd o _ _)

theorem planList_mem [DecidableEq α] (wd : α → Nat → Nat) (o : Nat → Option α) (n : Nat) :
    ∀ p ∈ planList wd o n, p.1 ≤ n ∧ o p.1 = some p.2 ∧ wd p.2 p.1 < p.1 := fun p hp =>
  have hp' := merge_mem _ p hp
  ⟨walk_le wd o _ _ p hp', walk_mem wd o _ _ p hp'⟩

theorem ladder_planList [DecidableEq α] (wd : α → Nat → Nat) (o : Nat → Option α) (key : α → Nat)
    (n : Nat) :
    ladderOf (chooseL (planList wd o n)) wd key (n + 1) n = ladderOf o wd key (n + 1) n :=
  ladder_walk wd o key _ _ _ (fun m _ => chooseL_merge _ (walk_sorted wd o _ _) m)

/-- On the planned list, selection at every visited width is the oracle's choice there
(the merge is invisible to `choose`). -/
theorem chooseL_planList_visit [DecidableEq α] (wd : α → Nat → Nat) (o : Nat → Option α) (n : Nat)
    (p : Nat × α) (hp : p ∈ walk wd o (n + 1) n) :
    chooseL (planList wd o n) p.1 = some p.2 := by
  unfold planList
  rw [chooseL_merge _ (walk_sorted wd o _ _)]
  exact chooseL_walk_of_mem wd o _ _ p hp

end TableGeneration.PlanCore
