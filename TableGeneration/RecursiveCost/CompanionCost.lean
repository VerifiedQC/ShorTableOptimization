import TableGeneration.RecursiveCost.CompanionTransport
import FastMultiplication.ShorVerification.Framework.Gatecount.ResourceModel
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Compiler.Widths
import FastMultiplication.ShorVerification.Implementation.GateCount.Definitions

/-!
# The companion's cost model, at the widths and in the language this planner uses

The companion development is a Lake dependency, so `Shor.cuccaroModAddResources`,
`Shor.shorGateCostModel`, `Shor.nextSignedWidth` and the rest are used directly.
This file adds only the two things the companion does not supply, and nothing
that duplicates something it does.

**A `Nat`-indexed face.** The companion's cost and width functions take an
`ExtReg`, but read only `ExtReg.width` off it. The recursive planner is indexed
by a bare `Nat`, and constructing a register per cost query would be `O(w)` work
on a hot path. `canonicalExtReg` is the register of a requested width, and
`canonicalExtReg_width` is what makes substituting it sound;
`negateResourcesAtWidth` is the companion's `negateResources` body with the
width substituted directly, and `negateResources_eq_atWidth` is `rfl`.

**The operation language does not cross.** `Shor.updateWidthState`,
`Shor.nextSignedWidth` and `Shor.phaseArithmeticOpCost` are stated over
`_root_.Operations.valid_ops`; this repository has its own, because the
submission path must stay Mathlib-free. The wrappers below apply the companion's
functions to a transported program, through the single bridge in
`CompanionTransport.lean`.

The closed forms `9w - 16` and `10w - 14` are stated here as **theorems about
the companion's own resource records**, never as definitions, so that quoting
them cannot drift from what the companion charges.
-/

namespace TableGeneration.RecursiveCost.Companion

/-! ## Width-indexed registers -/

/-- The register on physical qubits `0, 1, ..., w-1`.

Used only in theorem statements and tests -- never on the planner's hot path,
where a register construction would cost `O(w)` per query. The width-indexed
`negateResourcesAtWidth` is what the planner calls. -/
def canonicalReg (w : Nat) : Shor.Reg := ⟨List.range w, List.nodup_range⟩

@[simp] theorem canonicalReg_width (w : Nat) : (canonicalReg w).width = w :=
  List.length_range

/-- A width-`w` register with no reserve, for applying the companion's
width-dependent costs at a width the planner supplies. -/
def canonicalExtReg (w : Nat) : Shor.ExtReg where
  active := canonicalReg w
  reserve := Shor.Reg.empty
  active_reserve_disjoint := by simp [Shor.Disjoint, Shor.Reg.empty]

@[simp] theorem canonicalExtReg_width (w : Nat) :
    Shor.ExtReg.width (canonicalExtReg w) = w :=
  List.length_range

/-! ## The width scan, over this repository's programs

`Shor.updateWidthState` and `Shor.nextSignedWidth` consume the companion's
`valid_ops`; these are the same functions fed a transported program. -/

/-- The companion's symbolic width transition, for one of this repository's
operations. -/
def updateWidthState {k : Nat} (st : Shor.WidthState k)
    (op : TableGeneration.Operations.valid_ops k) : Shor.WidthState k :=
  Shor.updateWidthState st (toCompanionOp op)

/-- The companion's width scan, over one of this repository's programs. -/
def scanNeededWidths {k : Nat} (x z : Shor.ExtReg) (ops : TableGeneration.Prog k) :
    Shor.NeededWidths k :=
  Shor.scanNeededWidths x z (toCompanionProg ops)

/-- The width every recursive child of a PhaseProduct node receives, for one of
this repository's programs. This is the function the planner's `childWidth` must
agree with. -/
def nextSignedWidth {k : Nat} (x z : Shor.ExtReg) (ops : TableGeneration.Prog k) : Nat :=
  Shor.nextSignedWidth x z (toCompanionProg ops)

@[simp] theorem nextSignedWidth_eq_commonNeededWidth {k : Nat}
    (x z : Shor.ExtReg) (ops : TableGeneration.Prog k) :
    nextSignedWidth x z ops = Shor.commonNeededWidth (scanNeededWidths x z ops) := rfl

/-- A `phaseProduct` checkpoint is a recursion marker, not an arithmetic
operation, so it moves no widths. -/
@[simp] theorem updateWidthState_phaseProduct {k : Nat}
    (st : Shor.WidthState k) (i : Fin k) :
    updateWidthState st (.phaseProduct i) = st := rfl

/-! ## The recurrence-level arithmetic cost

The companion has two cost layers and both are live. `Shor.phaseArithmeticOpCost`
is the second one: a per-node cost over the symbolic operation list, charging the
conservative `Shor.rippleAdderGateBound` rather than the exact Cuccaro resources,
because a clean affine cost is what makes its recurrence solvable in closed form.

This planner charges the exact figure instead (`Model.lean`), and
`Model.phaseArithmeticOpCost_le` records that the companion's own
exact-below-bound inequality carries over. -/

/-- The companion's recurrence-level arithmetic cost, for one of this
repository's operations. -/
def phaseArithmeticOpCost {k : Nat} (W : Nat)
    (op : TableGeneration.Operations.valid_ops k) : Nat :=
  Shor.phaseArithmeticOpCost W (toCompanionOp op)

/-! ## Gate costs at a bare width -/

/-- `Shor.negateResources` with the register replaced by its width.

This is the companion's body with `ExtReg.width r` substituted by `w`;
`negateResources_eq_atWidth` below is `rfl`. It exists because the planner is
indexed by a bare `Nat` and must not pay an `O(w)` register construction per
cost query. -/
def negateResourcesAtWidth (w : Nat) : Shor.GateResources :=
  let a := Shor.cuccaroModAddResources w
  { h := a.h
    x := w + a.x + 2
    cnot := a.cnot
    toffoli := a.toffoli
    rz := a.rz
    cleanAnc := w + a.cleanAnc }

theorem negateResources_eq_atWidth (r : Shor.ExtReg) :
    Shor.negateResources r = negateResourcesAtWidth (Shor.ExtReg.width r) := rfl

/-- The operative model's `negate` field is a function of width alone. -/
theorem shorGateCostModel_negate_atWidth (r : Shor.ExtReg) :
    (Shor.negateResources r).totalGates
      = (negateResourcesAtWidth (Shor.ExtReg.width r)).totalGates := rfl

/-! ## Closed forms, as consequences

These are the numbers this project's cost model and the accompanying write-up
quote. They are theorems about the companion's definitions, not definitions of
their own, so quoting them cannot drift from what the companion actually
charges.

Truncated `Nat` subtraction below `w = 3` is deliberate and matches the
companion: its definitions are over `Nat` too, and the published Cuccaro formula
is only claimed for `w >= 3`. -/

theorem cuccaroModAddResources_totalGates (w : Nat) (hw : 3 <= w) :
    (Shor.cuccaroModAddResources w).totalGates = 9 * w - 16 := by
  show 0 + (2 * w - 6) + (5 * w - 7) + (2 * w - 3) + 0 = 9 * w - 16
  omega

theorem negateResourcesAtWidth_totalGates (w : Nat) (hw : 3 <= w) :
    (negateResourcesAtWidth w).totalGates = 10 * w - 14 := by
  show 0 + (w + (2 * w - 6) + 2) + (5 * w - 7) + (2 * w - 3) + 0 = 10 * w - 14
  omega

theorem negateResources_totalGates (r : Shor.ExtReg) (hw : 3 <= Shor.ExtReg.width r) :
    (Shor.negateResources r).totalGates = 10 * Shor.ExtReg.width r - 14 := by
  show 0 + (Shor.ExtReg.width r + (2 * Shor.ExtReg.width r - 6) + 2)
        + (5 * Shor.ExtReg.width r - 7)
        + (2 * Shor.ExtReg.width r - 3) + 0 = 10 * Shor.ExtReg.width r - 14
  omega

/-! ## The companion's exact-below-bound facts

Reproductions of the companion's
`cuccaroModAddResources_totalGates_le_rippleAdderGateBound` and
`negateResources_totalGates_le_negateGateBound`. They are what makes the two
cost layers coherent: the operative model never charges more than the recurrence
layer assumes. -/

theorem cuccaroModAddResources_totalGates_le_rippleAdderGateBound (w : Nat) :
    (Shor.cuccaroModAddResources w).totalGates <= Shor.rippleAdderGateBound w := by
  show 0 + (2 * w - 6) + (5 * w - 7) + (2 * w - 3) + 0 <= 9 * w + 2
  omega

theorem negateResourcesAtWidth_totalGates_le_negateGateBound (w : Nat) :
    (negateResourcesAtWidth w).totalGates <= w + Shor.rippleAdderGateBound w := by
  show 0 + (w + (2 * w - 6) + 2) + (5 * w - 7) + (2 * w - 3) + 0 <= w + (9 * w + 2)
  omega

/-- Sign extension by `n` bits costs `n` CNOTs, and zero extension is free.
This is the primitive behind the planner's per-node allocation charge. -/
@[simp] theorem shorGateResourceModel_signExtend_totalGates (r : Shor.ExtReg) (n : Nat) :
    (Shor.shorGateResourceModel.signExtend r n).totalGates = n :=
  Nat.zero_add n

@[simp] theorem shorGateResourceModel_zeroExtend_totalGates (r : Shor.ExtReg) (n : Nat) :
    (Shor.shorGateResourceModel.zeroExtend r n).totalGates = 0 := rfl

end TableGeneration.RecursiveCost.Companion
