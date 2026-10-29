import TableGeneration.Policy
import TableGeneration.RecursiveCost.Model

/-!
# Banded policies over STO tables: data and the decidable check

A **banded policy** is the object ForShor calls a `ShorLoweringPolicy`
(`Framework/Policy.lean`): a list of `(threshold, table)` bands, widest first,
whose thresholds strictly decrease; at operand width `n` the policy uses the
table of the first band with `threshold ≤ n`, and below the lowest threshold
it takes the schoolbook leaf. The recursion at width `n` with table `T`
recurses at the child width `nextSignedWidth n n T.ops` when that is `< n`
and otherwise takes the leaf (ForShor's `ShorLoweringPolicy.Stops`).

What this file adds over ForShor's object:

* the tables are STO tables (`TableGeneration.Operations.valid_ops`,
  `TableGeneration.Operations.Point`) and the per-table check is STO's own
  contract, `ValidPointList ∧ ProgConsumesPtsSafe … State.start_state`
  (`PolicyTable.check_iff`);
* the mode is explicit. `PhaseProduct` is ForShor's object. `PhaseTripleProduct`
  has **no ForShor counterpart**: it is defined here by analogy, with STO's
  `ProductMode.pointCount .PhaseTripleProduct k = 3k - 2` points, arity `3`,
  and the same width scan (the scan reads only the operation list and the
  common operand width, never operand data, so a third operand of the same
  width has the same transitions);
* the child width is STO's `RecursiveCost.nextSignedWidth n n ops`, which is
  the companion's `Shor.nextSignedWidth` on canonical registers of width `n`
  (definitionally), i.e. the balanced case of ForShor's `nextW`.

Everything here is computable and the check is a `Bool` the kernel reduces
(`decide +kernel`), with no `native_decide`.
-/

namespace TableGeneration.PolicyMirror

open TableGeneration.Operations

/-- Arity of the product: two operands for `PhaseProduct`, three for
`PhaseTripleProduct`. -/
def _root_.TableGeneration.ProductMode.arity : ProductMode → Nat
  | .PhaseProduct => 2
  | .PhaseTripleProduct => 3

theorem pointCount_eq_arity (mode : ProductMode) (k : Nat) (hk : 0 < k) :
    mode.pointCount k = mode.arity * (k - 1) + 1 := by
  cases mode <;> simp [ProductMode.pointCount, ProductMode.arity] <;> omega

/-- One table: `k` limb registers, the interpolation points **in the order
the program's `phaseProduct` checkpoints consume them** (STO's
`generatePointsInOrder`), and the program. -/
structure PolicyTable where
  k : Nat
  pts : List Point
  ops : TableGeneration.Prog k

/-- One band: use `table` whenever `threshold ≤ n`. -/
structure Band where
  threshold : Nat
  table : PolicyTable

/-- A banded policy for one product mode. -/
structure BandedPolicy where
  mode : ProductMode
  bands : List Band

namespace PolicyTable

/-- Width of the lower limbs at operand width `n`: ForShor's `phaseLimbWidth`
on two width-`n` operands (`= n / k`). -/
def limbWidth (T : PolicyTable) (n : Nat) : Nat :=
  RecursiveCost.phaseLimbWidth n n T.k

/-- Width of the recursive children at operand width `n`: STO's Lean width
scan, `RecursiveCost.nextSignedWidth n n T.ops`. -/
def childWidth (T : PolicyTable) (n : Nat) : Nat :=
  RecursiveCost.nextSignedWidth n n T.ops

/-- STO's per-table contract for `mode`, as one `Bool`: `k ≥ 2`, the point
list is a `ValidPointList` (right length, normalized-distinct, every point
`0` or a signed power of two), and the program consumes the points in order
from `State.start_state`, is `addScaled`-safe and returns to the start. -/
def check (mode : ProductMode) (T : PolicyTable) : Bool :=
  if hk : 2 ≤ T.k then
    decide (T.pts.length = mode.pointCount T.k) &&
    decide ((T.pts.map normalizePoint).Nodup) &&
    T.pts.all validPoint? &&
    progConsumesPts? (k := T.k) (by omega) State.start_state T.ops T.pts &&
    safeProg? T.ops &&
    returnsToStartCheck T.ops State.start_state
  else false

/-- `check` is exactly STO's submission contract for one table. -/
theorem check_iff (mode : ProductMode) (T : PolicyTable) :
    T.check mode = true ↔
      ∃ hk : 2 ≤ T.k, ValidPointList mode T.k T.pts ∧
        ProgConsumesPtsSafe (positive_of_ge_two hk) State.start_state T.ops T.pts := by
  unfold check
  by_cases hk : 2 ≤ T.k
  · rw [dif_pos hk]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨⟨⟨⟨hl, hn⟩, ha⟩, hc⟩, hs⟩, hr⟩
      exact ⟨hk, ⟨hl, hn, ha⟩, ⟨hc, hs, hr⟩⟩
    · rintro ⟨_, ⟨hl, hn, ha⟩, ⟨hc, hs, hr⟩⟩
      exact ⟨⟨⟨⟨⟨hl, hn⟩, ha⟩, hc⟩, hs⟩, hr⟩
  · rw [dif_neg hk]
    simp [hk]

/-- A table drawn from an STO `GeneratorPolicy` at a handled `(mode, k)`:
the points in consumption order and the generated program. -/
def ofGenerator (G : GeneratorPolicy) (mode : ProductMode) (k : Nat) (hk : k ≥ 2) :
    PolicyTable where
  k := k
  pts := G.generatePointsInOrder mode k hk
  ops := G.generate mode k hk

/-- Every table an STO generator policy proves correct passes `check`. The
proofs a `GeneratorPolicy` carries are exactly what `check` decides, modulo the
permutation between generated and consumed point orders. -/
theorem ofGenerator_check (G : GeneratorPolicy) (mode : ProductMode) (k : Nat) (hk : k ≥ 2)
    (h : G.handles mode k = true) : (ofGenerator G mode k hk).check mode = true := by
  rw [check_iff]
  obtain ⟨hl, hn, ha⟩ := G.generatedPoints_valid mode k hk h
  obtain ⟨hperm, hsafe⟩ := G.generate_safe mode k hk h
  refine ⟨hk, ⟨?_, ?_, ?_⟩, hsafe⟩
  · simp only [ofGenerator]; rw [hperm.length_eq]; exact hl
  · simp only [ofGenerator]; exact ((hperm.map normalizePoint).nodup_iff).mpr hn
  · simp only [ofGenerator, List.all_eq_true] at ha ⊢
    exact fun p hp => ha p (hperm.mem_iff.mp hp)

end PolicyTable

/-- Thresholds strictly decrease (ForShor's `sorted`), as a `Bool`. -/
def sortedDesc : List Nat → Bool
  | a :: b :: rest => decide (b < a) && sortedDesc (b :: rest)
  | _ => true

theorem sortedDesc_iff (l : List Nat) : sortedDesc l = true ↔ l.IsChain (· > ·) := by
  induction l with
  | nil => simp [sortedDesc]
  | cons a t ih =>
    cases t with
    | nil => simp [sortedDesc]
    | cons b rest =>
      simp only [sortedDesc, Bool.and_eq_true, decide_eq_true_eq, List.isChain_cons_cons]
      rw [ih]

namespace BandedPolicy

/-- The table at operand width `n`: the first band whose threshold is `≤ n`.
`none` is the leaf. Literally ForShor's `ShorLoweringPolicy.choose`. -/
def choose (P : BandedPolicy) (n : Nat) : Option PolicyTable :=
  (P.bands.find? (fun b => decide (b.threshold ≤ n))).map Band.table

theorem choose_mem {P : BandedPolicy} {n : Nat} {T : PolicyTable} (h : P.choose n = some T) :
    ∃ b ∈ P.bands, b.table = T := by
  unfold choose at h
  rcases hb : P.bands.find? (fun b => decide (b.threshold ≤ n)) with _ | b
  · rw [hb] at h; cases h
  · rw [hb] at h
    exact ⟨b, List.mem_of_find?_eq_some hb, by simpa using h⟩

/-- **The acceptance check**: thresholds strictly decrease and every band's
table passes STO's contract for the policy's mode. -/
def check (P : BandedPolicy) : Bool :=
  sortedDesc (P.bands.map Band.threshold) && P.bands.all (fun b => b.table.check P.mode)

theorem check_tables {P : BandedPolicy} (h : P.check = true) :
    ∀ b ∈ P.bands, b.table.check P.mode = true := by
  unfold check at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact h.2

theorem check_sorted {P : BandedPolicy} (h : P.check = true) :
    (P.bands.map Band.threshold).IsChain (· > ·) := by
  unfold check at h
  simp only [Bool.and_eq_true] at h
  exact (sortedDesc_iff _).mp h.1

/-- Fuelled walk down the recursion from width `n`: `true` when every table
the policy selects strictly shrinks the width, so the recursion reaches the
leaf only below the lowest threshold. -/
def chainFuel (P : BandedPolicy) : Nat → Nat → Bool
  | 0, _ => false
  | f + 1, n =>
      match P.choose n with
      | none => true
      | some T => decide (T.childWidth n < n) && chainFuel P f (T.childWidth n)

/-- Every band selected on the recursion from width `n` strictly contracts
(advisory, like ForShor's `bandShrinks`, but along the chain actually taken
from `n`). The fuel `n + 1` is enough because the width strictly decreases. -/
def chainContracts (P : BandedPolicy) (n : Nat) : Bool :=
  chainFuel P (n + 1) n

/-- The widths and table sizes the recursion from `n` visits (for reports). -/
def ladderFuel (P : BandedPolicy) : Nat → Nat → List (Nat × Option Nat)
  | 0, n => [(n, none)]
  | f + 1, n =>
      match P.choose n with
      | none => [(n, none)]
      | some T =>
          if T.childWidth n < n then (n, some T.k) :: ladderFuel P f (T.childWidth n)
          else [(n, none)]

def ladder (P : BandedPolicy) (n : Nat) : List (Nat × Option Nat) :=
  ladderFuel P (n + 1) n

end BandedPolicy

/-! ## Checkpoints -/

/-- The register contents at each `phaseProduct` checkpoint, running the
program from `σ`; `none` when a right shift is inexact. -/
def checkpointRows {k : Nat} : State k → TableGeneration.Prog k → Option (List (Register k))
  | _, [] => some []
  | σ, op :: ops =>
      match op with
      | .phaseProduct i => (checkpointRows σ ops).map (fun rows => σ i :: rows)
      | _ =>
          match applyOp? σ op with
          | none => none
          | some σ' => checkpointRows σ' ops

theorem regEqExpected_eq {k : Nat} {r : Register k} {pt : Point}
    (h : regEqExpected r pt = true) : r = expectedRow pt := by
  unfold regEqExpected at h
  funext j
  exact of_decide_eq_true (List.all_eq_true.mp h j (List.mem_finRange j))

/-- STO's point-consumption check pins every checkpoint: the `t`-th
`phaseProduct` finds its register holding exactly `expectedRow pts[t]`. -/
theorem checkpointRows_of_consumes {k : Nat} (hk : k > 0) :
    ∀ (ops : TableGeneration.Prog k) (σ : State k) (pts : List Point),
      progConsumesPts? hk σ ops pts = true →
        checkpointRows σ ops = some (pts.map expectedRow)
  | [], σ, pts, h => by
      cases pts with
      | nil => rfl
      | cons _ _ => simp [progConsumesPts?] at h
  | op :: ops, σ, pts, h => by
      cases op with
      | phaseProduct i =>
          cases pts with
          | nil => simp [progConsumesPts?] at h
          | cons pt rest =>
              simp only [progConsumesPts?, Bool.and_eq_true] at h
              obtain ⟨hm, hr⟩ := h
              have hrow : σ i = expectedRow pt := regEqExpected_eq hm
              simp [checkpointRows, checkpointRows_of_consumes hk ops σ rest hr, hrow]
      | shiftL i n =>
          simp only [progConsumesPts?, applyOp?] at h
          simp only [checkpointRows, applyOp?]
          exact checkpointRows_of_consumes hk ops _ pts h
      | shiftR i n =>
          simp only [progConsumesPts?] at h
          simp only [checkpointRows]
          cases hσ : applyOp? σ (.shiftR i n) with
          | none => rw [hσ] at h; cases h
          | some σ' =>
              rw [hσ] at h
              exact checkpointRows_of_consumes hk ops σ' pts h
      | negate i =>
          simp only [progConsumesPts?, applyOp?] at h
          simp only [checkpointRows, applyOp?]
          exact checkpointRows_of_consumes hk ops _ pts h
      | addScaled d s b sh =>
          simp only [progConsumesPts?, applyOp?] at h
          simp only [checkpointRows, applyOp?]
          exact checkpointRows_of_consumes hk ops _ pts h

end TableGeneration.PolicyMirror
