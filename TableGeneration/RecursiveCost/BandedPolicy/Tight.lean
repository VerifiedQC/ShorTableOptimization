import TableGeneration.RecursiveCost.BandedPolicy.Capacity

/-!
# Exact ("tight") register widths for banded policies

`evalPhaseRegW_correct` (Capacity.lean) proves the wrapping register semantics
correct under `T.childWidth n ≤ wd T n`, where `childWidth` is STO's scan
`nextSignedWidth n n ops`, which adds a bit at every `addScaled`/`negate`
whether or not the value grows. That is sufficient, not necessary
(FaultChallenge: 12 bits suffice at `n = 20`, the scan says 13).

This file defines the **exact** width and proves it is the right one.

* `PolicyTable.tightWidth T n`: the least `W` such that every register of
  every state the program reaches from the start state (every prefix; every
  checkpoint, so every child operand, is one of them) fits signed `W` bits for
  every operand fitting signed `n` bits. Computed by interval arithmetic on the
  coefficient rows: register `r` holds `∑ⱼ r j · Lⱼ`, the limbs `Lⱼ` range
  independently over a box (lower limbs `[0, 2^(n/k) - 1]`, the top limb
  `[-2^(t-1), 2^(t-1) - 1]` with `t = n - (k-1)(n/k)`, floor limbs: ForShor's
  `phaseSplitLogicalWidth`), so the row's range is `[rowLo, rowHi]` with
  coordinatewise min/max, and both ends are attained. The width is
  `1 + ⌈log₂ D⌉`, `D` the largest `max(-rowLo, rowHi + 1)` over reachable rows.
  This is sto_site's `tight_width.tight_width_closed_form(ops, k, n)` (floor
  limbs, no zero-extension). It is **not** sto_site's padded rule R2
  (`TightRule.at_n`, operands zero-extended to `k·⌈n/k⌉`): that is a different
  limb layout, differs in both directions, and nothing here certifies it.
* `tightWidth_le_iff` (soundness and minimality together): for `0 < k`,
  `0 < n`, `tightWidth T n ≤ W` **iff** every reachable register value fits `W`
  for every operand fitting `n`. `tightWidth_minimal`: at `tightWidth T n - 1`
  some reachable value of some operand does not fit (attainment).
* `tightWidth_le_childWidth`: the exact width never exceeds the scan.
* `evalPhaseRegW_tight_correct`: the wrapping register semantics at any
  `wd ≥ tightWidth` (where a table is chosen) applies exactly `φ · ∏ xs` on
  operands fitting `n`; `evalPhaseRegTight_correct` is the instance
  `wd = tightWidth`. Both go through `evalPhaseRegW_correct_of_reach`, whose
  hypothesis is the bare fit condition (`ReachFits`); the scan theorem
  `evalPhaseRegW_correct` (Capacity.lean, proved there through the width-state
  invariant) is also derivable from it with `tightWidth_le_childWidth`.
* `declOKTight` / `declaredTight_correct`: a declared ladder certified
  against `tightWidth` instead of the scan.

Everything is mode-generic: Parts on one table are per operand, and the
policy-level theorems quantify over any `BandedPolicy` (PP, and PTP in the
analogous register model; no PTP circuit exists).

Minimality is minimality for **no overflow**. The wrapped semantics may still
be right one bit below (an overflow can be cancelled by later ring operations
before it is read), so `tightWidth` is not claimed to be the least width at
which `evalPhaseRegW` is correct; the fault challenge exhibits a table where
one bit below `tightWidth` the wrapped result is wrong.
-/

namespace TableGeneration.PolicyMirror

open TableGeneration.Operations TableGeneration.RecursiveCost Finset

/-! ## Reachable states -/

section Reach

variable {k : ℕ}

/-- The states a run visits: the state before each operation and the final
one; the list stops at an inexact right shift (where `run?` fails). For a table
passing `check` this never happens (`checkpointRows_of_consumes`: the whole run
succeeds); for an unchecked table `tightWidth` then covers only the prefix that
runs, which is also all `ReachFits` quantifies over. -/
def reachStates : State k → TableGeneration.Prog k → List (State k)
  | σ, [] => [σ]
  | σ, op :: ops =>
      σ :: (match applyOp? σ op with
        | none => []
        | some σ' => reachStates σ' ops)

theorem mem_reachStates :
    ∀ (pre rest : TableGeneration.Prog k) (σ0 σ : State k),
      run? pre σ0 = some σ → σ ∈ reachStates σ0 (pre ++ rest)
  | [], rest, σ0, σ, h => by
      simp only [run?, Option.some.injEq] at h; subst h
      cases rest <;> simp [reachStates]
  | op :: pre, rest, σ0, σ, h => by
      simp only [run?] at h
      cases hs : applyOp? σ0 op with
      | none => rw [hs] at h; cases h
      | some σ1 =>
          rw [hs] at h
          simp only [List.cons_append, reachStates, hs]
          exact List.mem_cons_of_mem _ (mem_reachStates pre rest σ1 σ h)

theorem run_of_mem_reachStates :
    ∀ (ops : TableGeneration.Prog k) (σ0 σ : State k), σ ∈ reachStates σ0 ops →
      ∃ pre rest, ops = pre ++ rest ∧ run? pre σ0 = some σ
  | [], σ0, σ, h => by
      simp only [reachStates, List.mem_singleton] at h; subst h
      exact ⟨[], [], rfl, rfl⟩
  | op :: ops, σ0, σ, h => by
      simp only [reachStates] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨[], op :: ops, rfl, rfl⟩
      · cases hs : applyOp? σ0 op with
        | none => rw [hs] at h; cases h
        | some σ1 =>
            rw [hs] at h
            obtain ⟨pre, rest, he, hr⟩ := run_of_mem_reachStates ops σ1 σ h
            exact ⟨op :: pre, rest, by rw [he]; rfl, by simp only [run?, hs]; exact hr⟩

end Reach

/-! ## The limb box and row ranges -/

section Box

variable {k : ℕ}

/-- Width of the top limb field at operand width `n`. -/
def topWidth (k n : ℕ) : ℕ := n - (k - 1) * (n / k)

/-- Least value of limb `j` (lower limbs unsigned, top limb signed). -/
def limbLo (k n : ℕ) (j : Fin k) : ℤ :=
  if (j : ℕ) + 1 = k then -2 ^ (topWidth k n - 1) else 0

/-- Greatest value of limb `j`. -/
def limbHi (k n : ℕ) (j : Fin k) : ℤ :=
  if (j : ℕ) + 1 = k then 2 ^ (topWidth k n - 1) - 1 else 2 ^ (n / k) - 1

/-- Least value of the row `r` over the limb box (computed as a list sum). -/
def rowLo (k n : ℕ) (r : Register k) : ℤ :=
  ((List.finRange k).map fun j => min (r j * limbLo k n j) (r j * limbHi k n j)).sum

/-- Greatest value of the row `r` over the limb box. -/
def rowHi (k n : ℕ) (r : Register k) : ℤ :=
  ((List.finRange k).map fun j => max (r j * limbLo k n j) (r j * limbHi k n j)).sum

/-- How much magnitude the row demands: a signed `W`-bit register holds it iff
`rowDemand ≤ 2^(W-1)` (`fits_of_demand`). -/
def rowDemand (k n : ℕ) (r : Register k) : ℕ :=
  max (-rowLo k n r).toNat (rowHi k n r + 1).toNat

/-- The largest demand of a list of rows. -/
def maxDemand (k n : ℕ) : List (Register k) → ℕ
  | [] => 0
  | r :: rs => max (rowDemand k n r) (maxDemand k n rs)

theorem rowLo_eq (n : ℕ) (r : Register k) :
    rowLo k n r = ∑ j, min (r j * limbLo k n j) (r j * limbHi k n j) :=
  (Fin.sum_univ_def _).symm

theorem rowHi_eq (n : ℕ) (r : Register k) :
    rowHi k n r = ∑ j, max (r j * limbLo k n j) (r j * limbHi k n j) :=
  (Fin.sum_univ_def _).symm

theorem le_maxDemand (n : ℕ) : ∀ {rs : List (Register k)} {r : Register k}, r ∈ rs →
    rowDemand k n r ≤ maxDemand k n rs
  | [], _, h => by cases h
  | r' :: rs, r, h => by
      simp only [maxDemand]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (le_maxDemand n h) (le_max_right _ _)

theorem exists_maxDemand (n : ℕ) : ∀ {rs : List (Register k)}, 0 < maxDemand k n rs →
    ∃ r ∈ rs, rowDemand k n r = maxDemand k n rs
  | [], h => by simp [maxDemand] at h
  | r :: rs, h => by
      simp only [maxDemand] at h ⊢
      rcases le_total (rowDemand k n r) (maxDemand k n rs) with hle | hle
      · rw [max_eq_right hle]
        obtain ⟨r', hr', he⟩ := exists_maxDemand n (rs := rs) (by rw [max_eq_right hle] at h; exact h)
        exact ⟨r', List.mem_cons_of_mem _ hr', he⟩
      · exact ⟨r, List.mem_cons_self, (max_eq_left hle).symm⟩

theorem limbLo_le_limbHi (n : ℕ) (j : Fin k) : limbLo k n j ≤ limbHi k n j := by
  unfold limbLo limbHi
  split
  · have : (1 : ℤ) ≤ 2 ^ (topWidth k n - 1) := one_le_pow₀ (by norm_num)
    linarith
  · have : (1 : ℤ) ≤ 2 ^ (n / k) := one_le_pow₀ (by norm_num)
    linarith

/-- The limbs of an operand fitting `n` bits lie in the box. -/
theorem limbs_box (hk : 0 < k) {n : ℕ} {x : ℤ} (hx : Fits n x) (j : Fin k) :
    limbLo k n j ≤ limbs k (2 ^ (n / k)) x j ∧ limbs k (2 ^ (n / k)) x j ≤ limbHi k n j := by
  unfold limbLo limbHi
  by_cases hj : (j : ℕ) + 1 = k
  · simp only [if_pos hj]
    obtain ⟨-, hlo, hhi⟩ := limb_top_fits hk hx j hj
    unfold Shor.signedMin at hlo
    unfold Shor.signedMax at hhi
    push_cast at hlo hhi
    unfold topWidth
    constructor <;> omega
  · simp only [if_neg hj]
    obtain ⟨h0, h1⟩ := limb_lower_fits k n x j hj
    constructor <;> omega

theorem term_bounds {c l lo hi : ℤ} (h1 : lo ≤ l) (h2 : l ≤ hi) :
    min (c * lo) (c * hi) ≤ c * l ∧ c * l ≤ max (c * lo) (c * hi) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left h1 hc),
      le_trans (mul_le_mul_of_nonneg_left h2 hc) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left h2 hc),
      le_trans (mul_le_mul_of_nonpos_left h1 hc) (le_max_left _ _)⟩

/-- **Interval soundness.** A row's value at limbs in the box lies in `[rowLo, rowHi]`. -/
theorem row_bounds (n : ℕ) (r : Register k) {L : Fin k → ℤ}
    (hL : ∀ j, limbLo k n j ≤ L j ∧ L j ≤ limbHi k n j) :
    rowLo k n r ≤ regValue r L ∧ regValue r L ≤ rowHi k n r := by
  rw [rowLo_eq, rowHi_eq]
  unfold regValue
  exact ⟨Finset.sum_le_sum fun j _ => (term_bounds (c := r j) (hL j).1 (hL j).2).1,
    Finset.sum_le_sum fun j _ => (term_bounds (c := r j) (hL j).1 (hL j).2).2⟩

theorem fits_of_demand {W : ℕ} {z lo hi : ℤ} (hW : 0 < W) (hlo : lo ≤ z) (hhi : z ≤ hi)
    (hd : max (-lo).toNat (hi + 1).toNat ≤ 2 ^ (W - 1)) : Fits W z := by
  have h1 : (-lo).toNat ≤ 2 ^ (W - 1) := le_trans (le_max_left _ _) hd
  have h2 : (hi + 1).toNat ≤ 2 ^ (W - 1) := le_trans (le_max_right _ _) hd
  have e1 := Int.self_le_toNat (-lo)
  have e2 := Int.self_le_toNat (hi + 1)
  have c1 : ((-lo).toNat : ℤ) ≤ ((2 ^ (W - 1) : ℕ) : ℤ) := by exact_mod_cast h1
  have c2 : ((hi + 1).toNat : ℤ) ≤ ((2 ^ (W - 1) : ℕ) : ℤ) := by exact_mod_cast h2
  refine ⟨hW, ?_, ?_⟩
  · unfold Shor.signedMin; omega
  · unfold Shor.signedMax; omega

end Box

/-! ## Attainment: every point of the box is the limb vector of an operand -/

section Attain

theorem digits_lt {B : ℤ} (hB : 0 < B) (w : ℕ → ℤ) :
    ∀ m, (∀ i < m, 0 ≤ w i ∧ w i < B) →
      0 ≤ ∑ i ∈ range m, w i * B ^ i ∧ ∑ i ∈ range m, w i * B ^ i < B ^ m
  | 0, _ => by simp
  | m + 1, h => by
      obtain ⟨ih0, ih1⟩ := digits_lt hB w m fun i hi => h i (by omega)
      obtain ⟨h0, h1⟩ := h m (by omega)
      have hp : 0 < B ^ m := pow_pos hB m
      rw [sum_range_succ, pow_succ]
      constructor
      · nlinarith
      · nlinarith

theorem sum_split (B : ℤ) (w : ℕ → ℤ) (j m : ℕ) :
    ∑ i ∈ range (j + m), w i * B ^ i
      = ∑ i ∈ range j, w i * B ^ i + B ^ j * ∑ i ∈ range m, w (j + i) * B ^ i := by
  rw [sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_add]; ring

theorem ediv_digits {B : ℤ} (hB : 0 < B) (w : ℕ → ℤ) (j m : ℕ)
    (hlow : ∀ i < j, 0 ≤ w i ∧ w i < B) :
    (∑ i ∈ range (j + m), w i * B ^ i) / B ^ j = ∑ i ∈ range m, w (j + i) * B ^ i := by
  rw [sum_split, Int.add_mul_ediv_left _ _ (pow_pos hB j).ne']
  obtain ⟨h0, h1⟩ := digits_lt hB w j hlow
  rw [Int.ediv_eq_zero_of_lt h0 h1, zero_add]

theorem emod_head {B : ℤ} (hB : 0 < B) (u : ℕ → ℤ) (m : ℕ) (h0 : 0 ≤ u 0) (h1 : u 0 < B) :
    (∑ i ∈ range (m + 1), u i * B ^ i) % B = u 0 := by
  rw [sum_range_succ']
  have : ∑ i ∈ range m, u (i + 1) * B ^ (i + 1) = B * ∑ i ∈ range m, u (i + 1) * B ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ]; ring
  rw [this, pow_zero, mul_one, add_comm, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt h0 h1

/-- **Attainment.** Every point of the limb box is the limb vector of some
operand fitting `n` signed bits. -/
theorem box_surj {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (v : Fin k → ℤ)
    (hv : ∀ j, limbLo k n j ≤ v j ∧ v j ≤ limbHi k n j) :
    ∃ x, Fits n x ∧ ∀ j, limbs k (2 ^ (n / k)) x j = v j := by
  set B : ℤ := 2 ^ (n / k) with hBdef
  have hB : 0 < B := by positivity
  let w : ℕ → ℤ := fun i => if h : i < k then v ⟨i, h⟩ else 0
  have hw : ∀ j : Fin k, w j = v j := fun j => by simp [w, j.2]
  have hlow : ∀ i, i + 1 < k → 0 ≤ w i ∧ w i < B := by
    intro i hi
    have h := hv ⟨i, by omega⟩
    have hne : (⟨i, by omega⟩ : Fin k).val + 1 ≠ k := by simp; omega
    simp only [limbLo, limbHi, if_neg hne] at h
    simp only [w, dif_pos (show i < k by omega)]
    constructor <;> omega
  refine ⟨∑ i ∈ range k, w i * B ^ i, ?_, fun j => ?_⟩
  · -- the operand fits `n` bits
    have hsplit := sum_split B w (k - 1) 1
    rw [show k - 1 + 1 = k by omega] at hsplit
    simp only [sum_range_one, pow_zero, mul_one, add_zero] at hsplit
    rw [hsplit]
    obtain ⟨hs0, hs1⟩ := digits_lt hB w (k - 1) fun i hi => hlow i (by omega)
    have ht := hv ⟨k - 1, by omega⟩
    have htop : (⟨k - 1, by omega⟩ : Fin k).val + 1 = k := by simp; omega
    simp only [limbLo, limbHi, if_pos htop] at ht
    have hwt : w (k - 1) = v ⟨k - 1, by omega⟩ := by simp [w, show k - 1 < k by omega]
    rw [hwt]
    have hoff := top_offset_lt hk hn
    have hexp : (2 : ℤ) ^ (n - 1) = B ^ (k - 1) * 2 ^ (topWidth k n - 1) := by
      rw [hBdef, ← pow_mul, ← pow_add]
      congr 1
      unfold topWidth
      rw [Nat.mul_comm (n / k) (k - 1)]
      omega
    have hP : 0 < B ^ (k - 1) := pow_pos hB _
    refine ⟨hn, ?_, ?_⟩
    · unfold Shor.signedMin; push_cast; rw [hexp]; nlinarith
    · unfold Shor.signedMax; push_cast; rw [hexp]; nlinarith
  · -- the limbs are `v`
    have hjk : (j : ℕ) + (k - j) = k := by omega
    have hx : ∑ i ∈ range k, w i * B ^ i = ∑ i ∈ range (j + (k - j)), w i * B ^ i := by rw [hjk]
    unfold limbs
    rw [hx, ediv_digits hB w j (k - j) fun i hi => hlow i (by omega)]
    split
    · rename_i htop
      rw [show k - j = 0 + 1 by omega, sum_range_one, pow_zero, mul_one, add_zero, hw]
    · rename_i hne
      rw [show k - j = (k - j - 1) + 1 by omega,
        emod_head hB (fun i => w (j + i)) _ (hlow j (by omega)).1 (hlow j (by omega)).2]
      simp only [add_zero, hw]

/-- The upper end of a row's range is attained. -/
theorem row_attain_hi {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (r : Register k) :
    ∃ x, Fits n x ∧ regValue r (limbs k (2 ^ (n / k)) x) = rowHi k n r := by
  obtain ⟨x, hx, hl⟩ := box_surj hk hn (fun j => if 0 ≤ r j then limbHi k n j else limbLo k n j)
    fun j => by
      have := limbLo_le_limbHi (k := k) n j
      split <;> constructor <;> omega
  refine ⟨x, hx, ?_⟩
  rw [rowHi_eq]
  unfold regValue
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hl j]
  have hle := limbLo_le_limbHi (k := k) n j
  split
  · rename_i h; exact (max_eq_right (mul_le_mul_of_nonneg_left hle h)).symm
  · rename_i h; exact (max_eq_left (mul_le_mul_of_nonpos_left hle (by omega))).symm

/-- The lower end of a row's range is attained. -/
theorem row_attain_lo {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (r : Register k) :
    ∃ x, Fits n x ∧ regValue r (limbs k (2 ^ (n / k)) x) = rowLo k n r := by
  obtain ⟨x, hx, hl⟩ := box_surj hk hn (fun j => if 0 ≤ r j then limbLo k n j else limbHi k n j)
    fun j => by
      have := limbLo_le_limbHi (k := k) n j
      split <;> constructor <;> omega
  refine ⟨x, hx, ?_⟩
  rw [rowLo_eq]
  unfold regValue
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hl j]
  have hle := limbLo_le_limbHi (k := k) n j
  split
  · rename_i h; exact (min_eq_left (mul_le_mul_of_nonneg_left hle h)).symm
  · rename_i h; exact (min_eq_right (mul_le_mul_of_nonpos_left hle (by omega))).symm

end Attain

/-! ## The exact width -/

/-- Least `e ≥ e₀` with `D ≤ 2^e`, searching at most `f` steps. -/
def leastExp (D : ℕ) : ℕ → ℕ → ℕ
  | 0, e => e
  | f + 1, e => if D ≤ 2 ^ e then e else leastExp D f (e + 1)

theorem leastExp_spec (D : ℕ) : ∀ (f e : ℕ), D ≤ 2 ^ (e + f) → (∀ e' < e, ¬ D ≤ 2 ^ e') →
    D ≤ 2 ^ leastExp D f e ∧ ∀ e' < leastExp D f e, ¬ D ≤ 2 ^ e'
  | 0, e, h, hm => ⟨by simpa [leastExp] using h, hm⟩
  | f + 1, e, h, hm => by
      simp only [leastExp]
      split
      · exact ⟨‹_›, hm⟩
      · rename_i hne
        refine leastExp_spec D f (e + 1) (by rwa [show e + 1 + f = e + (f + 1) by omega]) ?_
        intro e' he'
        rcases Nat.lt_succ_iff_lt_or_eq.mp he' with h' | rfl
        · exact hm e' h'
        · exact hne

namespace PolicyTable

/-- Every coefficient row the program holds in some register of some reachable state. -/
def reachRows (T : PolicyTable) : List (Register T.k) :=
  (reachStates State.start_state T.ops).flatMap fun σ => (List.finRange T.k).map σ

/-- The largest demand over the reachable rows at operand width `n`. -/
def demand (T : PolicyTable) (n : ℕ) : ℕ := maxDemand T.k n T.reachRows

/-- **The exact working width**: `1 + ⌈log₂ (demand)⌉`, i.e. the least `W ≥ 1`
with `demand ≤ 2^(W-1)` (`tightWidth_spec`). -/
def tightWidth (T : PolicyTable) (n : ℕ) : ℕ := 1 + leastExp (T.demand n) (T.demand n) 0

theorem tightWidth_spec (T : PolicyTable) (n : ℕ) :
    T.demand n ≤ 2 ^ (T.tightWidth n - 1) ∧
      ∀ e < T.tightWidth n - 1, ¬ T.demand n ≤ 2 ^ e := by
  have h := leastExp_spec (T.demand n) (T.demand n) 0 (by simpa using Nat.lt_two_pow_self.le)
    (fun _ h => absurd h (Nat.not_lt_zero _))
  simpa [tightWidth] using h

theorem tightWidth_pos (T : PolicyTable) (n : ℕ) : 0 < T.tightWidth n := by
  unfold tightWidth; omega

theorem mem_reachRows (T : PolicyTable) {pre rest : TableGeneration.Prog T.k} {σ : State T.k}
    (hops : T.ops = pre ++ rest) (hrun : run? pre State.start_state = some σ) (i : Fin T.k) :
    σ i ∈ T.reachRows := by
  unfold reachRows
  rw [List.mem_flatMap]
  exact ⟨σ, hops ▸ mem_reachStates pre rest _ σ hrun, List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩⟩

/-- The fit condition at one node: every register value of every reachable
state fits `W` bits, for every operand fitting `n` bits. -/
def ReachFits (T : PolicyTable) (n W : ℕ) : Prop :=
  ∀ x, Fits n x → ∀ (pre rest : TableGeneration.Prog T.k) (σ : State T.k),
    T.ops = pre ++ rest → run? pre State.start_state = some σ →
      ∀ i, Fits W (regValue (σ i) (limbs T.k (2 ^ T.limbWidth n) x))

/-- **Soundness of the exact width.** -/
theorem tight_fits (T : PolicyTable) (hk : 0 < T.k) {n W : ℕ} (hW : T.tightWidth n ≤ W) :
    T.ReachFits n W := by
  intro x hx pre rest σ hops hrun i
  have hmem := T.mem_reachRows hops hrun i
  have hd : rowDemand T.k n (σ i) ≤ 2 ^ (W - 1) :=
    le_trans (le_maxDemand n hmem) (le_trans (T.tightWidth_spec n).1
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
  rw [limbWidth_eq]
  obtain ⟨hlo, hhi⟩ := row_bounds n (σ i) (limbs_box hk hx)
  exact fits_of_demand (by have := T.tightWidth_pos n; omega) hlo hhi hd

/-- **Minimality (attainment).** At one bit below the exact width, some register
of some reachable state holds, for some operand fitting `n` bits, a value that
does not fit. -/
theorem tightWidth_minimal (T : PolicyTable) (hk : 0 < T.k) {n : ℕ} (hn : 0 < n) :
    ∃ x, Fits n x ∧ ∃ (pre rest : TableGeneration.Prog T.k) (σ : State T.k) (i : Fin T.k),
      T.ops = pre ++ rest ∧ run? pre State.start_state = some σ ∧
        ¬ Fits (T.tightWidth n - 1) (regValue (σ i) (limbs T.k (2 ^ T.limbWidth n) x)) := by
  rw [limbWidth_eq]
  obtain ⟨_, hmin⟩ := T.tightWidth_spec n
  by_cases he : T.tightWidth n - 1 = 0
  · refine ⟨0, ⟨hn, ?_, ?_⟩, [], T.ops, State.start_state, ⟨0, hk⟩, rfl, rfl, ?_⟩
    · simp [Shor.signedMin]
    · simp [Shor.signedMax]
    · rw [he]; exact fun h => absurd h.1 (Nat.lt_irrefl 0)
  · set e := T.tightWidth n - 1 with he'
    have hnot : ¬ T.demand n ≤ 2 ^ (e - 1) := hmin (e - 1) (by omega)
    have hpos : 0 < T.demand n := by
      rcases Nat.eq_zero_or_pos (T.demand n) with h | h
      · rw [h] at hnot; exact absurd (Nat.zero_le _) hnot
      · exact h
    obtain ⟨r, hr, hrd⟩ := exists_maxDemand n hpos
    obtain ⟨σ, hσ, hrσ⟩ := List.mem_flatMap.mp hr
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hrσ
    obtain ⟨pre, rest, hops, hrun⟩ := run_of_mem_reachStates _ _ _ hσ
    have hgt : 2 ^ (e - 1) < rowDemand T.k n (σ i) := by
      unfold demand at hnot; rw [← hrd] at hnot; omega
    unfold rowDemand at hgt
    rcases lt_max_iff.mp hgt with hlo | hhi
    · obtain ⟨x, hx, hv⟩ := row_attain_lo hk hn (σ i)
      refine ⟨x, hx, pre, rest, σ, i, hops, hrun, fun hf => ?_⟩
      obtain ⟨-, hf1, -⟩ := hf
      rw [hv] at hf1
      unfold Shor.signedMin at hf1
      have := Int.lt_toNat.mp hlo
      push_cast at hf1 this
      omega
    · obtain ⟨x, hx, hv⟩ := row_attain_hi hk hn (σ i)
      refine ⟨x, hx, pre, rest, σ, i, hops, hrun, fun hf => ?_⟩
      obtain ⟨-, -, hf2⟩ := hf
      rw [hv] at hf2
      unfold Shor.signedMax at hf2
      have := Int.lt_toNat.mp hhi
      push_cast at hf2 this
      omega

/-- **The exact width is exactly the least width that holds every reachable
value**: `tightWidth T n ≤ W ↔ ReachFits T n W` (soundness and minimality). -/
theorem tightWidth_le_iff (T : PolicyTable) (hk : 0 < T.k) {n : ℕ} (hn : 0 < n) (W : ℕ) :
    T.tightWidth n ≤ W ↔ T.ReachFits n W := by
  refine ⟨T.tight_fits hk, fun h => ?_⟩
  by_contra hlt
  obtain ⟨x, hx, pre, rest, σ, i, hops, hrun, hnf⟩ := T.tightWidth_minimal hk hn
  exact hnf (Shor.FitsSignedWidth_mono (by omega) (h x hx pre rest σ hops hrun i))

/-- **The exact width never exceeds the scan.** -/
theorem tightWidth_le_childWidth (T : PolicyTable) (hk : 0 < T.k) {n : ℕ} (hn : 0 < n) :
    T.tightWidth n ≤ T.childWidth n :=
  (T.tightWidth_le_iff hk hn _).mpr fun _ hx _ _ _ hops hrun i => working_fits T hk hx hops hrun i

end PolicyTable

/-! ## Register-width soundness from the bare fit condition -/

section Sim

variable {k : ℕ}

/-- **Simulation from the fit condition.** If every register of every state
reached from `σ` fits `W`, the wrapped register run reads the exact checkpoint
values. -/
theorem regCheckpoints_sim_reach {W : ℕ} {L : Fin k → ℤ} :
    ∀ (ops : TableGeneration.Prog k) (σ : State k) (rows : List (Register k)),
      (∀ (pre rest : TableGeneration.Prog k) (σ' : State k), ops = pre ++ rest →
          run? pre σ = some σ' → ∀ i, Fits W (regValue (σ' i) L)) →
      checkpointRows σ ops = some rows →
      regCheckpoints W (fun i => regValue (σ i) L) ops = rows.map (fun r => regValue r L)
  | [], σ, rows, _, h => by
      simp only [checkpointRows, Option.some.injEq] at h; subst h; rfl
  | op :: ops, σ, rows, hf, h => by
      have hstep : ∀ σ1, applyOp? σ op = some σ1 → ∀ i, Fits W (regValue (σ1 i) L) :=
        fun σ1 hs i => hf [op] ops σ1 rfl (by simp only [run?, hs]) i
      have htail : ∀ σ1, applyOp? σ op = some σ1 →
          ∀ (pre rest : TableGeneration.Prog k) (σ' : State k), ops = pre ++ rest →
            run? pre σ1 = some σ' → ∀ i, Fits W (regValue (σ' i) L) :=
        fun σ1 hs pre rest σ' he hr => hf (op :: pre) rest σ' (by rw [he]; rfl)
          (by simp only [run?, hs]; exact hr)
      cases op with
      | phaseProduct i =>
          simp only [checkpointRows] at h
          cases h' : checkpointRows σ ops with
          | none => rw [h'] at h; cases h
          | some rs =>
              rw [h'] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              have ih := regCheckpoints_sim_reach ops σ rs (htail σ rfl) h'
              simp only [regCheckpoints, regOp, List.singleton_append, List.map_cons]
              rw [ih]
      | _ =>
          simp only [checkpointRows] at h
          split at h
          · cases h
          · rename_i σ1 hs
            have hsim := regOp_sim (W := W) hs (hstep σ1 hs)
            simp only [regCheckpoints, List.nil_append]
            rw [hsim]
            exact regCheckpoints_sim_reach ops σ1 rows (htail σ1 hs) h

theorem regLimbs_eq_of_fits (T : PolicyTable) (hk : 0 < T.k) {n W : ℕ} {x : ℤ} (hx : Fits n x)
    (h0 : ∀ j, Fits W (regValue (State.start_state j) (limbs T.k (2 ^ T.limbWidth n) x))) :
    T.regLimbs n W x = fun j => regValue (State.start_state j) (limbs T.k (2 ^ T.limbWidth n) x) := by
  funext j
  have hfitW := h0 j
  rw [regValue_start] at hfitW ⊢
  simp only [PolicyTable.regLimbs, wrap_of_fits hx]
  split
  · rename_i hj
    have htop := limb_top_fits hk hx j hj
    rw [← limbWidth_eq] at htop
    rw [wrap_of_fits htop, wrap_of_fits hfitW]
  · exact wrap_of_fits hfitW

theorem regChild_eq_of_reach (mode : ProductMode) (T : PolicyTable) (hT : T.check mode = true)
    {n W : ℕ} {x : ℤ} (hx : Fits n x)
    (hreach : ∀ (pre rest : TableGeneration.Prog T.k) (σ : State T.k), T.ops = pre ++ rest →
      run? pre State.start_state = some σ →
        ∀ i, Fits W (regValue (σ i) (limbs T.k (2 ^ T.limbWidth n) x)))
    (t : Fin T.pts.length) :
    T.regChild n W x t = T.childOperand n (expectedRow (T.pts.get t)) x := by
  obtain ⟨hk2, _, hsafe⟩ := (PolicyTable.check_iff mode T).mp hT
  have hk : 0 < T.k := by omega
  have hrows := checkpointRows_of_consumes (positive_of_ge_two hk2) T.ops State.start_state T.pts
    hsafe.consumes
  have hsim := regCheckpoints_sim_reach (W := W) (L := limbs T.k (2 ^ T.limbWidth n) x) T.ops
    State.start_state _ hreach hrows
  unfold PolicyTable.regChild
  rw [regLimbs_eq_of_fits T hk hx (hreach [] T.ops State.start_state rfl rfl), hsim,
    List.getD_eq_getElem _ _ (by simp)]
  simp [PolicyTable.childOperand]

/-- **Register-width soundness from the fit condition.** If every band's table
passes STO's contract and, wherever a table is chosen, the declared working
width holds every reachable register value (`ReachFits`), the wrapped
evaluation applies exactly `φ · ∏ xs` on operands fitting `n` bits. -/
theorem evalPhaseRegW_correct_of_reach (P : BandedPolicy)
    (hP : ∀ b ∈ P.bands, b.table.check P.mode = true) (wd : PolicyTable → ℕ → ℕ)
    (hwd : ∀ n T, P.choose n = some T → T.ReachFits n (wd T n)) :
    ∀ (n : ℕ) (φ : ℚ) (xs : Fin P.mode.arity → ℤ), (∀ s, Fits n (xs s)) →
      P.evalPhaseRegW wd n φ xs = φ * ∏ s, (xs s : ℚ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro φ xs hxs
    rw [BandedPolicy.evalPhaseRegW]
    split
    · simp only [wrap_of_fits (hxs _)]
    · rename_i T hc
      have hW := hwd n T hc
      obtain ⟨b, hb, rfl⟩ := BandedPolicy.choose_mem hc
      have hT := hP b hb
      split
      · rename_i hlt
        obtain ⟨hk2, _, hsafe⟩ := (PolicyTable.check_iff P.mode b.table).mp hT
        rw [← node_identity P.mode b.table hT n φ xs]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [regChild_eq_of_reach P.mode b.table hT (hxs _) (hW _ (hxs _))]
        rw [ih _ hlt]
        intro s
        have hrows := checkpointRows_of_consumes (positive_of_ge_two hk2) b.table.ops
          State.start_state b.table.pts hsafe.consumes
        have hmem : (expectedRow (b.table.pts.get t) : Register b.table.k) ∈
            b.table.pts.map expectedRow :=
          List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩
        obtain ⟨pre, rest, σ, i, hops, hrun, hr⟩ :=
          checkpointRows_mem b.table.ops _ _ hrows _ hmem
        unfold PolicyTable.childOperand
        rw [hr]
        exact hW _ (hxs s) pre rest σ hops hrun i
      · simp only [wrap_of_fits (hxs _)]

/-- **Register-width soundness at any width ≥ the exact width.** -/
theorem evalPhaseRegW_tight_correct (P : BandedPolicy)
    (hP : ∀ b ∈ P.bands, b.table.check P.mode = true) (wd : PolicyTable → ℕ → ℕ)
    (hwd : ∀ n T, P.choose n = some T → T.tightWidth n ≤ wd T n) :
    ∀ (n : ℕ) (φ : ℚ) (xs : Fin P.mode.arity → ℤ), (∀ s, Fits n (xs s)) →
      P.evalPhaseRegW wd n φ xs = φ * ∏ s, (xs s : ℚ) :=
  evalPhaseRegW_correct_of_reach P hP wd fun n T hc => by
    obtain ⟨b, hb, rfl⟩ := BandedPolicy.choose_mem hc
    obtain ⟨hk2, _⟩ := (PolicyTable.check_iff P.mode b.table).mp (hP b hb)
    exact b.table.tight_fits (by omega) (hwd n _ hc)

/-- The register semantics at the exact widths. -/
noncomputable def BandedPolicy.evalPhaseRegTight (P : BandedPolicy) (n : ℕ) (φ : ℚ)
    (xs : Fin P.mode.arity → ℤ) : ℚ :=
  P.evalPhaseRegW (fun T n => T.tightWidth n) n φ xs

/-- **Register-width soundness at the exact widths**: a checked policy, run on
wrapping registers whose working width at every node is the exact width,
applies exactly `φ · ∏ xs` on operands fitting `n` signed bits. -/
theorem evalPhaseRegTight_correct (P : BandedPolicy) (h : P.check = true) (n : ℕ) (φ : ℚ)
    (xs : Fin P.mode.arity → ℤ) (hxs : ∀ s, Fits n (xs s)) :
    P.evalPhaseRegTight n φ xs = φ * ∏ s, (xs s : ℚ) :=
  evalPhaseRegW_tight_correct P (BandedPolicy.check_tables h) _ (fun _ _ _ => le_refl _) n φ xs hxs

theorem evalPhaseRegTight_eq_evalPhase (P : BandedPolicy) (h : P.check = true) (n : ℕ) (φ : ℚ)
    (xs : Fin P.mode.arity → ℤ) (hxs : ∀ s, Fits n (xs s)) :
    P.evalPhaseRegTight n φ xs = P.evalPhase n φ xs := by
  rw [evalPhaseRegTight_correct P h n φ xs hxs, evalPhase_correct_of_check P h]

/-- Under `bandsContract`, every chosen table also contracts at the exact width. -/
theorem tight_contracts (P : BandedPolicy) (h : P.check = true) (hb : P.bandsContract = true)
    {n : ℕ} {T : PolicyTable} (hc : P.choose n = some T) (hn : 0 < n) : T.tightWidth n < n := by
  obtain ⟨b, hbm, rfl⟩ := BandedPolicy.choose_mem hc
  obtain ⟨hk2, _⟩ := (PolicyTable.check_iff P.mode b.table).mp (BandedPolicy.check_tables h b hbm)
  exact lt_of_le_of_lt (b.table.tightWidth_le_childWidth (by omega) hn) (bandsContract_sound P hb hc)

end Sim

/-! ## Declared ladders certified against the exact width -/

section Decl

/-- What the recursion at the exact widths does at width `w`. -/
def BandedPolicy.levelKTight (P : BandedPolicy) (w : ℕ) : Option ℕ :=
  match P.choose w with
  | none => none
  | some T => if T.tightWidth w < w then some T.k else none

/-- Working widths read off a declared ladder; the exact width where the ladder
says nothing. -/
def ladderWidthTight (decl : List (ℕ × Option ℕ)) (T : PolicyTable) (n : ℕ) : ℕ :=
  (nextDeclared decl n).getD (T.tightWidth n)

/-- The declared-ladder check against the exact width: every `k` tag is
`levelKTight`, and every declared step from a width where a table is chosen goes
to a smaller width that is at least the exact width. By `tightWidth_le_iff` (for
`0 < w`) the width part is the weakest per-step condition under which no register
overflows; the shrink `w' < w` and the `k` tags are additional bookkeeping
constraints. -/
def BandedPolicy.declOKTight (P : BandedPolicy) : List (ℕ × Option ℕ) → Bool
  | (w, kd) :: (w', k') :: rest =>
      decide (kd = P.levelKTight w) &&
      (match P.choose w with
        | none => true
        | some T => decide (T.tightWidth w ≤ w') && decide (w' < w)) &&
      P.declOKTight ((w', k') :: rest)
  | [(w, kd)] => decide (kd = P.levelKTight w)
  | [] => true

theorem declOKTight_le (P : BandedPolicy) :
    ∀ (decl : List (ℕ × Option ℕ)), P.declOKTight decl = true → ∀ {n : ℕ} {T : PolicyTable},
      P.choose n = some T → T.tightWidth n ≤ ladderWidthTight decl T n
  | [], _, n, T, _ => by simp [ladderWidthTight, nextDeclared]
  | [_], _, n, T, _ => by simp [ladderWidthTight, nextDeclared]
  | (w, kd) :: (w', k') :: rest, h, n, T, hc => by
      simp only [BandedPolicy.declOKTight, Bool.and_eq_true] at h
      unfold ladderWidthTight nextDeclared
      by_cases hw : w = n
      · subst hw
        have h2 := h.1.2
        rw [hc] at h2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
        simpa using h2.1
      · simp only [if_neg hw]
        exact declOKTight_le P _ h.2 hc

/-- **Register-width soundness at a declared ladder certified against the exact width.** -/
theorem declaredTight_correct (P : BandedPolicy) (h : P.check = true) (decl : List (ℕ × Option ℕ))
    (hd : P.declOKTight decl = true) (n : ℕ) (φ : ℚ) (xs : Fin P.mode.arity → ℤ)
    (hxs : ∀ s, Fits n (xs s)) :
    P.evalPhaseRegW (ladderWidthTight decl) n φ xs = φ * ∏ s, (xs s : ℚ) :=
  evalPhaseRegW_tight_correct P (BandedPolicy.check_tables h) _
    (fun _ _ hc => declOKTight_le P decl hd hc) n φ xs hxs

/-- The exact-width recursion ladder from `n` (for reports and the site). -/
def BandedPolicy.ladderTightFuel (P : BandedPolicy) : ℕ → ℕ → List (ℕ × Option ℕ)
  | 0, n => [(n, none)]
  | f + 1, n =>
      match P.choose n with
      | none => [(n, none)]
      | some T =>
          if T.tightWidth n < n then (n, some T.k) :: P.ladderTightFuel f (T.tightWidth n)
          else [(n, none)]

def BandedPolicy.ladderTight (P : BandedPolicy) (n : ℕ) : List (ℕ × Option ℕ) :=
  P.ladderTightFuel (n + 1) n

end Decl

end TableGeneration.PolicyMirror
