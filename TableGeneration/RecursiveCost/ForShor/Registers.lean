/-!
# Register types from the companion development

Integrated from the companion Lean formalization at commit `d5a165b`, file
`FastMultiplication/ShorVerification/Framework/Quantum/Registers.lean`.
The companion is licensed Apache-2.0; these declarations keep their original
names so the correspondence is exact and greppable.

Only what the gate cost model needs is taken: the two register structures and
their widths. The companion's file also carries the quantum semantics --
basis encodings, amplitudes, `Complex`, `InnerProductSpace` -- and the register
algebra (`append`, `slice`, `get`, ...). None of that participates in gate
counting, so none of it is here, and this repository stays free of Mathlib.

## The one deviation

The companion writes `Reg.Disjoint a b := a.qubits.Disjoint b.qubits`, but
`List.Disjoint` lives in Batteries rather than Lean core. `ListDisjoint` below
inlines the same statement so the slice builds with no dependency. Every other
declaration is the companion's, verbatim up to `Nat` for `ℕ`.
-/

namespace TableGeneration.RecursiveCost.ForShor

/-- `List.Disjoint` is not in Lean core; this is its statement, inlined. -/
def ListDisjoint (a b : List Nat) : Prop := ∀ x, x ∈ a → x ∉ b

/-- An ordered register: the qubit at position `i` represents bit `i`.
Physical contiguity is not required. -/
structure Reg where
  qubits : List Nat
  nodup : qubits.Nodup
deriving DecidableEq

namespace Reg

/-- The empty register. -/
def empty : Reg := ⟨[], by simp⟩

/-- Logical width, i.e. the number of physical qubits in the ordered list. -/
def width (r : Reg) : Nat := r.qubits.length

end Reg

/-- Alias used by the companion's older files for the logical width. -/
def regSize (r : Reg) : Nat := r.width

/-- Physical disjointness of two ordered registers. -/
def Disjoint (a b : Reg) : Prop := ListDisjoint a.qubits b.qubits

/-- An active register together with exclusively owned inactive workspace.
`reserve` is ordered from the next high bit onward. -/
structure ExtReg where
  active : Reg
  reserve : Reg
  active_reserve_disjoint : Disjoint active reserve
deriving DecidableEq

namespace ExtReg

/-- Width of the currently active part. -/
def width (e : ExtReg) : Nat := regSize e.active

/-- Number of reserve bits still available for future growth. -/
def capacity (e : ExtReg) : Nat := regSize e.reserve

end ExtReg

/-! ## Width-indexed registers

The companion's cost functions take an `ExtReg`, but read only its width. The
recursive planner in this repository is indexed by a bare `Nat` width, so it
needs a canonical register of a requested width to apply those functions to.
`canonicalExtReg_width` is what makes that substitution sound.
-/

/-- The register on physical qubits `0, 1, ..., w-1`.

Used only in theorem statements and tests -- never on the planner's hot path,
where a register construction would cost O(w) per query. The width-indexed
`negateResourcesAtWidth` is what the planner calls. -/
def canonicalReg (w : Nat) : Reg := ⟨List.range w, List.nodup_range⟩

@[simp] theorem canonicalReg_width (w : Nat) : (canonicalReg w).width = w :=
  List.length_range

/-- A width-`w` register with no reserve, for applying the companion's
width-dependent costs at a width the planner supplies. -/
def canonicalExtReg (w : Nat) : ExtReg where
  active := canonicalReg w
  reserve := Reg.empty
  active_reserve_disjoint := by intro x _ hx; cases hx

@[simp] theorem canonicalExtReg_width (w : Nat) :
    (canonicalExtReg w).width = w :=
  List.length_range

end TableGeneration.RecursiveCost.ForShor
