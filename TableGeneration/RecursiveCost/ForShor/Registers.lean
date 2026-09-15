import Mathlib.Data.List.Nodup
import Batteries.Data.List.Lemmas

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

Every declaration is the companion's, verbatim up to `Nat` for `ℕ`. An earlier
revision inlined `List.Disjoint`, which lives in Batteries, to keep this
repository dependency-free; Mathlib is now a dependency of the cost model, so
the real one is used.
-/

namespace TableGeneration.RecursiveCost.ForShor

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

/-- The first `n` logical qubits. -/
def take (r : Reg) (n : Nat) : Reg :=
  {
    qubits := r.qubits.take n
    nodup := r.nodup.sublist (List.take_sublist n r.qubits)
  }

/-- The logical qubits following the first `n`. -/
def drop (r : Reg) (n : Nat) : Reg :=
  {
    qubits := r.qubits.drop n
    nodup := r.nodup.sublist (List.drop_sublist n r.qubits)
  }

end Reg

/-- Alias used by the companion's older files for the logical width. -/
def regSize (r : Reg) : Nat := r.width

/-- Physical disjointness of two ordered registers. -/
def Disjoint (a b : Reg) : Prop := a.qubits.Disjoint b.qubits

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

/-- The reserve has at least `n` bits available. -/
def CanGrow (e : ExtReg) (n : Nat) : Prop := n ≤ e.capacity

/-- The next `n` reserve bits that will become active after growth. -/
def newBits (e : ExtReg) (n : Nat) : Reg := e.reserve.take n

/-- Reserve bits left after growing by `n`. -/
def remainingReserve (e : ExtReg) (n : Nat) : Reg := e.reserve.drop n

end ExtReg

namespace Reg

/-- Append two physically disjoint registers, preserving logical order. -/
def append
    (left right : Reg)
    (h : Disjoint left right) :
    Reg :=
  {
    qubits := left.qubits ++ right.qubits
    nodup := by
      exact List.Nodup.append left.nodup right.nodup h
  }

end Reg

namespace ExtReg

/-- Activate the next `n` reserve qubits, leaving the remaining reserve inactive. -/
def grow (e : ExtReg) (n : Nat) : ExtReg :=
  {
    active :=
      Reg.append e.active (e.newBits n) (by
        have hdisj := e.active_reserve_disjoint
        rw [Disjoint, List.disjoint_left] at hdisj ⊢
        intro q hqActive hqNew
        exact hdisj hqActive
          (List.mem_of_mem_take hqNew))

    reserve :=
      e.remainingReserve n

    active_reserve_disjoint := by
      rw [Disjoint, List.disjoint_left]
      intro q hqActiveGrow hqReserve
      rw [ExtReg.remainingReserve, Reg.drop] at hqReserve
      rw [Reg.append, List.mem_append] at hqActiveGrow
      rcases hqActiveGrow with hqActive | hqNew
      · have hdisj := e.active_reserve_disjoint
        rw [Disjoint, List.disjoint_left] at hdisj
        exact hdisj hqActive
          (List.mem_of_mem_drop hqReserve)
      · have htake_drop :
            (List.take n e.reserve.qubits).Disjoint
              (List.drop n e.reserve.qubits) :=
          List.disjoint_take_drop e.reserve.nodup (Nat.le_refl n)
        rw [List.disjoint_left] at htake_drop
        exact htake_drop hqNew hqReserve
  }

/-- All physical qubits owned by an extendable register, active first and
reserve second. -/
def ownedQubits (e : ExtReg) : List Nat := e.active.qubits ++ e.reserve.qubits

/-- Disjointness of all owned qubits, including reserve/workspace bits. -/
def OwnedDisjoint (x z : ExtReg) : Prop := x.ownedQubits.Disjoint z.ownedQubits

@[simp] theorem width_grow (e : ExtReg) (n : Nat) (hcap : e.CanGrow n) :
    width (e.grow n) = width e + n := by
  simp [width, grow, Reg.append, newBits, Reg.take, regSize, Reg.width,
    CanGrow, capacity] at hcap ⊢
  omega

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
  active_reserve_disjoint := by simp [Disjoint, Reg.empty]

@[simp] theorem canonicalExtReg_width (w : Nat) :
    (canonicalExtReg w).width = w :=
  List.length_range

end TableGeneration.RecursiveCost.ForShor
