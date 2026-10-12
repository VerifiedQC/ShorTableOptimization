import TableGeneration.Language
import FastMultiplication.ShorVerification.Framework.ToomCookTable

/-!
# Transporting this repository's operation language into the companion's

The companion development is a Lake dependency, so its definitions are used
directly rather than copied. One thing cannot be shared: the operation language.
`TableGeneration.Operations.valid_ops` (`TableGeneration/Basic.lean`) and
`_root_.Operations.valid_ops` (the companion's
`Framework/ToomCookTable.lean`) are two distinct inductive types of identical
shape, and the same holds for `Point`. The submission path must stay
Mathlib-free, so this repository keeps its own; everything under
`TableGeneration/RecursiveCost/` that hands a program to the companion goes
through the maps below.

This is the single bridge. It is deliberately total, computable, and
bidirectional with round-trip lemmas, because two different consumers need it:

* the cost model, which evaluates the companion's width scan and gate costs on a
  submitted program (`CompanionCost.lean`, `Model.lean`);
* the soundness bridge, which restates the submission contract in the
  companion's own Props (`CompanionSoundness.lean`);

and a third is anticipated: packaging a submission as a `Shor.ShorLoweringSetup`
needs exactly `toCompanionProg`, `toCompanionPoints` and the length lemma below
to supply `ops`, `pts` and `hpts`. Nothing here is `private` or specialised to
one caller.
-/

namespace TableGeneration.RecursiveCost.Companion

/-! ## Points -/

/-- This repository's `Point` as the companion's. -/
def toCompanionPoint : TableGeneration.Operations.Point → _root_.Operations.Point
  | .int z => .int z
  | .frac m => .frac m

/-- The companion's `Point` as this repository's. -/
def ofCompanionPoint : _root_.Operations.Point → TableGeneration.Operations.Point
  | .int z => .int z
  | .frac m => .frac m

/-- A point list transported pointwise. This is the `pts` field a
`Shor.ShorLoweringSetup` asks for. -/
def toCompanionPoints (pts : List TableGeneration.Operations.Point) :
    List _root_.Operations.Point :=
  pts.map toCompanionPoint

/-- A companion point list read back. -/
def ofCompanionPoints (pts : List _root_.Operations.Point) :
    List TableGeneration.Operations.Point :=
  pts.map ofCompanionPoint

/-! ## Operations -/

/-- This repository's `valid_ops` as the companion's: the five constructors
correspond one for one. -/
def toCompanionOp {k : Nat} :
    TableGeneration.Operations.valid_ops k → _root_.Operations.valid_ops k
  | .shiftL i n => .shiftL i n
  | .shiftR i n => .shiftR i n
  | .negate i => .negate i
  | .addScaled dst src negSrc shift => .addScaled dst src negSrc shift
  | .phaseProduct i => .phaseProduct i

/-- The companion's `valid_ops` as this repository's. -/
def ofCompanionOp {k : Nat} :
    _root_.Operations.valid_ops k → TableGeneration.Operations.valid_ops k
  | .shiftL i n => .shiftL i n
  | .shiftR i n => .shiftR i n
  | .negate i => .negate i
  | .addScaled dst src negSrc shift => .addScaled dst src negSrc shift
  | .phaseProduct i => .phaseProduct i

/-- A program transported operation by operation. This is the `ops` field a
`Shor.ShorLoweringSetup` asks for. -/
def toCompanionProg {k : Nat} (ops : TableGeneration.Prog k) : _root_.Prog k :=
  ops.map toCompanionOp

/-- A companion program read back. -/
def ofCompanionProg {k : Nat} (ops : _root_.Prog k) : TableGeneration.Prog k :=
  ops.map ofCompanionOp

/-! ## The transports are inverse, and preserve length

Length is what `hpts : pts.length = q k` needs; the round trips are what lets a
caller move in either direction without a second bridge. -/

@[simp] theorem ofCompanionPoint_toCompanionPoint
    (pt : TableGeneration.Operations.Point) :
    ofCompanionPoint (toCompanionPoint pt) = pt := by
  cases pt <;> rfl

@[simp] theorem toCompanionPoint_ofCompanionPoint (pt : _root_.Operations.Point) :
    toCompanionPoint (ofCompanionPoint pt) = pt := by
  cases pt <;> rfl

@[simp] theorem ofCompanionOp_toCompanionOp {k : Nat}
    (op : TableGeneration.Operations.valid_ops k) :
    ofCompanionOp (toCompanionOp op) = op := by
  cases op <;> rfl

@[simp] theorem toCompanionOp_ofCompanionOp {k : Nat}
    (op : _root_.Operations.valid_ops k) :
    toCompanionOp (ofCompanionOp op) = op := by
  cases op <;> rfl

theorem toCompanionOp_injective {k : Nat} :
    Function.Injective (toCompanionOp (k := k)) := by
  intro a b h
  rw [← ofCompanionOp_toCompanionOp a, ← ofCompanionOp_toCompanionOp b, h]

theorem toCompanionPoint_injective : Function.Injective toCompanionPoint := by
  intro a b h
  rw [← ofCompanionPoint_toCompanionPoint a, ← ofCompanionPoint_toCompanionPoint b, h]

@[simp] theorem toCompanionProg_nil {k : Nat} :
    toCompanionProg (k := k) [] = [] := rfl

@[simp] theorem toCompanionProg_cons {k : Nat}
    (op : TableGeneration.Operations.valid_ops k) (ops : TableGeneration.Prog k) :
    toCompanionProg (op :: ops) = toCompanionOp op :: toCompanionProg ops := rfl

@[simp] theorem toCompanionProg_append {k : Nat}
    (ops ops' : TableGeneration.Prog k) :
    toCompanionProg (ops ++ ops') = toCompanionProg ops ++ toCompanionProg ops' :=
  List.map_append ..

@[simp] theorem toCompanionProg_length {k : Nat} (ops : TableGeneration.Prog k) :
    (toCompanionProg ops).length = ops.length :=
  List.length_map ..

@[simp] theorem ofCompanionProg_toCompanionProg {k : Nat}
    (ops : TableGeneration.Prog k) :
    ofCompanionProg (toCompanionProg ops) = ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih => simp [ofCompanionProg, toCompanionProg] at ih ⊢; exact ih

@[simp] theorem toCompanionPoints_nil : toCompanionPoints [] = [] := rfl

@[simp] theorem toCompanionPoints_cons (pt : TableGeneration.Operations.Point)
    (pts : List TableGeneration.Operations.Point) :
    toCompanionPoints (pt :: pts) = toCompanionPoint pt :: toCompanionPoints pts := rfl

/-- What discharges a submission's `hpts : pts.length = q k`: transporting the
points does not change how many there are. -/
@[simp] theorem toCompanionPoints_length
    (pts : List TableGeneration.Operations.Point) :
    (toCompanionPoints pts).length = pts.length :=
  List.length_map ..

@[simp] theorem ofCompanionPoints_toCompanionPoints
    (pts : List TableGeneration.Operations.Point) :
    ofCompanionPoints (toCompanionPoints pts) = pts := by
  induction pts with
  | nil => rfl
  | cons pt pts ih => simp [ofCompanionPoints, toCompanionPoints] at ih ⊢; exact ih

/-- Membership transports, which is what a positional side condition stated over
the companion's program needs in order to be pulled back to the operation this
repository checked. -/
theorem mem_toCompanionProg {k : Nat} {ops : TableGeneration.Prog k}
    {op : _root_.Operations.valid_ops k} (h : op ∈ toCompanionProg ops) :
    ofCompanionOp op ∈ ops := by
  rw [toCompanionProg, List.mem_map] at h
  obtain ⟨op', hop', rfl⟩ := h
  simpa using hop'

end TableGeneration.RecursiveCost.Companion
