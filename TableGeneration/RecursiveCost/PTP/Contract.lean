import TableGeneration.RecursiveCost.BandedPolicy.Defs

/-!
# PhaseTripleProduct (PTP): table contract, width scan, banded policy

PTP-specific definitions. Nothing here is borrowed from the PhaseProduct
mirror except two arity-free STO facts reused in proofs (`checkpointRows`,
`regEqExpected_eq`, in `BandedPolicy/Defs.lean`) and the `sortedDesc` helper.

## Table contract (`PTPTable.contract`)

STO's `Spec.lean` fixes the PTP point count at `ProductMode.pointCount
.PhaseTripleProduct k = 3 * k - 2` (`pointCount_spec`, by `rfl`). That is
`3 (k - 1) + 1`: three limb polynomials of degree `≤ k - 1` multiply to a
polynomial of degree `≤ 3 (k - 1)`, which `3 (k - 1) + 1` distinct projective
points determine. The contract is STO's `ValidPointList .PhaseTripleProduct`
plus `ProgConsumesPtsSafe` from `State.start_state` (`contract_iff`).

## Width scan (`Widths`, `wStep`, `childWidth3`)

A *magnitude* bound: `w` for a register means `|value| < 2 ^ w`. The
transitions are the ones the soundness lemmas in `PTP/Width.lean` prove:

* `shiftL i n`: `w + n`; `shiftR i n` (exact): `w - n`;
* `negate i`: `w` (negation preserves `|·|`; PhaseProduct's scan, ForShor's
  `updateWidthState`, charges `+ 1` here, which is sound but not needed under
  a magnitude invariant);
* `addScaled d s _ sh`: `1 + max (w d) (w s + sh)`.

The three operands are scanned separately, each from its own top-heavy split:
the common limb width is `W = min (n₀/k) (n₁/k) (n₂/k)` (the lower limbs must
fit in all three operands), lower limbs have bound `W` (unsigned `< 2^W`) and
the top limb `nₛ - (k-1) W` (signed). The child width is one sign bit above
the largest bound any of the three operands reaches anywhere in the program:
`childWidth3 n ops = 1 + max_s scanMax (initW nₛ W k) ops`. Every register of
the node, for every operand, is allocated at that width, so it is also the
working width of every `addScaled`, `negate` and shift.

## Banded policy (`PTPPolicy`)

Bands widest first, strictly decreasing thresholds; at width `n` the first
band with `threshold ≤ n` is used (ForShor's `choose`), and the node recurses
at `childWidth n T.ops` when that is `< n`, else takes the 3-way grid leaf.
-/

namespace TableGeneration.PTP

open TableGeneration TableGeneration.Operations

/-! ## Table contract -/

/-- One PTP table: `k` limb registers, the interpolation points in the order the
program's `phaseProduct` checkpoints consume them, and the program. -/
structure PTPTable where
  k : Nat
  pts : List Point
  ops : TableGeneration.Prog k

/-- PTP point count: `3 k - 2`. -/
def pointCount (k : Nat) : Nat := 3 * k - 2

/-- The count agrees with STO's `Spec.lean` (pinned by `rfl`). -/
theorem pointCount_spec (k : Nat) :
    pointCount k = ProductMode.pointCount .PhaseTripleProduct k := rfl

theorem pointCount_eq (k : Nat) (hk : 0 < k) : pointCount k = 3 * (k - 1) + 1 := by
  unfold pointCount; omega

namespace PTPTable

/-- The PTP table contract as one kernel-reducible `Bool`. -/
def contract (T : PTPTable) : Bool :=
  if hk : 2 ≤ T.k then
    decide (T.pts.length = pointCount T.k) &&
    decide ((T.pts.map normalizePoint).Nodup) &&
    T.pts.all validPoint? &&
    progConsumesPts? (k := T.k) (by omega) State.start_state T.ops T.pts &&
    safeProg? T.ops &&
    returnsToStartCheck T.ops State.start_state
  else false

/-- `contract` is exactly STO's per-table PTP contract. -/
theorem contract_iff (T : PTPTable) :
    T.contract = true ↔
      ∃ hk : 2 ≤ T.k, ValidPointList .PhaseTripleProduct T.k T.pts ∧
        ProgConsumesPtsSafe (positive_of_ge_two hk) State.start_state T.ops T.pts := by
  unfold contract
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

end PTPTable

/-! ## Width scan -/

/-- Magnitude-bit bounds of the `k` limb registers of one operand, as a list
indexed by register (length `k`; see `wStep_length`). A list rather than a
function so that both the kernel and compiled reports evaluate the scan in
linear time (a closure chain re-evaluates the new bound on every lookup). -/
abbrev Widths := List Nat

/-- The bound of register `i`. -/
def wget {k : Nat} (w : Widths) (i : Fin k) : Nat := w.getD i.1 0

/-- One transition of the PTP magnitude scan (per operand). -/
def wStep {k : Nat} (w : Widths) : valid_ops k → Widths
  | .shiftL i n => w.set i.1 (wget w i + n)
  | .shiftR i n => w.set i.1 (wget w i - n)
  | .negate _ => w
  | .addScaled d s _ sh => w.set d.1 (1 + max (wget w d) (wget w s + sh))
  | .phaseProduct _ => w

/-- Largest bound in a state. -/
def wMax (w : Widths) : Nat := w.foldl max 0

/-- Largest bound reached anywhere along the program (initial state included). -/
def scanMax {k : Nat} : Widths → Prog k → Nat
  | w, [] => wMax w
  | w, op :: ops => max (wMax w) (scanMax (wStep w op) ops)

/-- Common lower-limb width of three operands: `min (n₀/k) (n₁/k) (n₂/k)`. -/
def limbWidth3 (n : Fin 3 → Nat) (k : Nat) : Nat :=
  min (n 0 / k) (min (n 1 / k) (n 2 / k))

/-- Initial bounds of a width-`nW` operand split top-heavy at lower width `W`. -/
def initW (nW W k : Nat) : Widths :=
  List.ofFn (n := k) fun i => if i.1 + 1 = k then nW - (k - 1) * W else W

/-- **PTP child width** for operand widths `n` (three, possibly unequal). -/
def childWidth3 {k : Nat} (n : Fin 3 → Nat) (ops : Prog k) : Nat :=
  let W := limbWidth3 n k
  1 + max (scanMax (initW (n 0) W k) ops)
        (max (scanMax (initW (n 1) W k) ops) (scanMax (initW (n 2) W k) ops))

/-- Balanced PTP child width (all three operands of width `n`). -/
def childWidth {k : Nat} (n : Nat) (ops : Prog k) : Nat := childWidth3 (fun _ => n) ops

/-- Balanced lower-limb width `n / k`. -/
def limbWidth (n k : Nat) : Nat := limbWidth3 (fun _ => n) k

theorem limbWidth_eq (n k : Nat) : limbWidth n k = n / k := by
  simp [limbWidth, limbWidth3]

/-! ## Banded PTP policy -/

structure PTPBand where
  threshold : Nat
  table : PTPTable

/-- A banded PhaseTripleProduct policy (the mode is fixed). -/
structure PTPPolicy where
  bands : List PTPBand

namespace PTPPolicy

/-- First band with `threshold ≤ n` (ForShor's `choose`). -/
def choose (P : PTPPolicy) (n : Nat) : Option PTPTable :=
  (P.bands.find? (fun b => decide (b.threshold ≤ n))).map PTPBand.table

theorem choose_mem {P : PTPPolicy} {n : Nat} {T : PTPTable} (h : P.choose n = some T) :
    ∃ b ∈ P.bands, b.table = T := by
  unfold choose at h
  rcases hb : P.bands.find? (fun b => decide (b.threshold ≤ n)) with _ | b
  · rw [hb] at h; cases h
  · rw [hb] at h
    exact ⟨b, List.mem_of_find?_eq_some hb, by simpa using h⟩

/-- **The PTP policy check**: thresholds strictly decrease and every band's
table passes the PTP contract. -/
def check (P : PTPPolicy) : Bool :=
  PolicyMirror.sortedDesc (P.bands.map PTPBand.threshold) &&
    P.bands.all (fun b => b.table.contract)

theorem check_tables {P : PTPPolicy} (h : P.check = true) :
    ∀ b ∈ P.bands, b.table.contract = true := by
  unfold check at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact h.2

theorem check_sorted {P : PTPPolicy} (h : P.check = true) :
    (P.bands.map PTPBand.threshold).IsChain (· > ·) := by
  unfold check at h
  simp only [Bool.and_eq_true] at h
  exact (PolicyMirror.sortedDesc_iff _).mp h.1

/-- Fuelled walk: every table selected from `n` strictly shrinks the width. -/
def chainFuel (P : PTPPolicy) : Nat → Nat → Bool
  | 0, _ => false
  | f + 1, n =>
      match P.choose n with
      | none => true
      | some T => decide (childWidth n T.ops < n) && chainFuel P f (childWidth n T.ops)

def chainContracts (P : PTPPolicy) (n : Nat) : Bool := chainFuel P (n + 1) n

def ladderFuel (P : PTPPolicy) : Nat → Nat → List (Nat × Option Nat)
  | 0, n => [(n, none)]
  | f + 1, n =>
      match P.choose n with
      | none => [(n, none)]
      | some T =>
          if childWidth n T.ops < n then (n, some T.k) :: ladderFuel P f (childWidth n T.ops)
          else [(n, none)]

/-- Widths and table sizes visited from `n` (reports). -/
def ladder (P : PTPPolicy) (n : Nat) : List (Nat × Option Nat) := ladderFuel P (n + 1) n

end PTPPolicy

end TableGeneration.PTP
