import TableGeneration.RecursiveCost.PlanCore
/-! Tautology / load-bearing checks for `PlanCore` (run: lake env lean scripts/plan_mutations/Mutations.lean).
Each mutation removes one ingredient and the corresponding theorem fails on a concrete instance. -/
open TableGeneration.PlanCore TableGeneration.PolicyMirror

/-- M1: the walk WITHOUT the contraction guard. -/
def walkNG (wd : Nat → Nat → Nat) (o : Nat → Option Nat) : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | f + 1, w => match o w with
    | none => []
    | some a => (w, a) :: walkNG wd o f (wd a w)

-- a table that never contracts (child width w + 1), alternating names so merge cannot hide it
example : sortedDesc ((merge (walkNG (fun _ w => w + 1) (fun w => some (w % 2)) 4 3)).map Prod.fst) = false := by decide
-- the real walk on the same data: the guard stops at once (leaf), output sorted
example : walk (fun (_ : Nat) w => w + 1) (fun w => some (w % 2)) 4 3 = [] := by decide

/-- M2: merge keeping the FIRST (higher) threshold of a run. -/
def mergeFirst : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | p :: rest => match mergeFirst rest with
    | [] => [p]
    | q :: r => if p.2 = q.2 then p :: r else p :: q :: r

-- choose changes at width 7 (10 > 7 ≥ 5): the real merge preserves it, the mutant does not
example : chooseL (merge [(10, 0), (5, 0)]) 7 = some 0 := by decide
example : chooseL (mergeFirst [(10, 0), (5, 0)]) 7 = none := by decide

/-- M3: a merge on a list that is NOT sorted can change selection: `chooseL_merge` needs its hypothesis. -/
example : chooseL (merge [(3, 1), (10, 1)]) 5 ≠ chooseL [(3, 1), (10, 1)] 5 := by decide
