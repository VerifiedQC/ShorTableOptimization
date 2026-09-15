import TableGeneration.RecursiveCost.ForShor.LowGate

/-!
# The companion's concrete resource model

Integrated from the companion Lean formalization at commit `d5a165b`, file
`FastMultiplication/ShorVerification/Framework/Gatecount/ResourceModel.lean`.
Apache-2.0; declaration names are the companion's.

`shorGateCostModel` is the operative model: the one the companion's own
`ShorOrderFindingProgram.frameworkGateCount` evaluates against a compiled
circuit. Everything the recursive planner in this repository charges is
computed from the definitions below rather than quoted from them, so the
familiar closed forms `9w - 16` and `10w - 14` appear here as *theorems*
(`cuccaroModAddResources_totalGates`, `negateResources_totalGates`) and not as
definitions.

## Not taken

* `phaseProductCostModel`, the companion's former operative model. It was
  **deleted** upstream at `89c45ee`: it charged the loose bounds for arithmetic
  and treated sign extension as free. Nothing here reproduces it.
* `directCSignedPhaseProductGateCount = 9xz`. Dead in the companion -- its only
  occurrence is its own definition -- and the recursion here only ever reaches
  the signed leaf.
* Every proof, the lowering, and the compiler.
-/


namespace TableGeneration.RecursiveCost.ForShor

/-! ## The companion's conservative bounds

These are not the cost model. The companion keeps them as the loose linear
bounds its asymptotic proofs are stated against, and bridges them to the exact
Cuccaro resources with `cuccaroModAddResources_totalGates_le_rippleAdderGateBound`.
They are integrated because the companion still defines them, and because its
recurrence-level `phaseArithmeticOpCost` charges them.

The model that packaged these into a `LowGateCostModel` -- `phaseProductCostModel`,
which also treated sign extension as free -- was **deleted** upstream and is not
reproduced here.
-/

/-- Conservative linear bound for one ripple-adder on `w` qubits. -/
def rippleAdderGateBound (w : Nat) : Nat := 9 * w + 2

/-- Negation is bounded by sign-width handling plus one ripple-adder. -/
def negateGateBound (r : ExtReg) : Nat :=
  ExtReg.width r + rippleAdderGateBound (ExtReg.width r)

/-- Direct signed PhaseProduct base-case cost, quadratic in the operand widths.

The companion proves this is *exact* rather than declared: its
`gateCount_Naive_SignedPhaseProd` shows the naive leaf costs
`5 * width x * width z` under **any** cost model, because the leaf is literally
`width x * width z` controlled-phase macros of five gates each. -/
def directSignedPhaseProductGateCount (x z : ExtReg) : Nat :=
  5 * ExtReg.width x * ExtReg.width z

/-- Concrete logical resources used by a lowered circuit.

`cleanAnc` is a peak-space quantity rather than a gate count, so sequential
composition takes the maximum rather than the sum. -/
structure GateResources where
  h : Nat := 0
  x : Nat := 0
  cnot : Nat := 0
  toffoli : Nat := 0
  rz : Nat := 0
  cleanAnc : Nat := 0
deriving Repr, DecidableEq

namespace GateResources

def zero : GateResources := {}

def seq (a b : GateResources) : GateResources where
  h := a.h + b.h
  x := a.x + b.x
  cnot := a.cnot + b.cnot
  toffoli := a.toffoli + b.toffoli
  rz := a.rz + b.rz
  cleanAnc := max a.cleanAnc b.cleanAnc

/-- Total number of logical unitary gates when every elementary gate has unit
cost. Ancilla usage is intentionally not included. -/
def totalGates (r : GateResources) : Nat :=
  r.h + r.x + r.cnot + r.toffoli + r.rz

end GateResources

/-- Structural resource model for low-level gates.

Unlike `LowGateCostModel`, this records the decomposition into logical
elementary resources instead of immediately collapsing everything to a `Nat`. -/
structure LowGateResourceModel where
  shiftL : ExtReg → Nat → GateResources
  shiftR : ExtReg → Nat → GateResources
  negate : ExtReg → GateResources
  addScaled : ExtReg → ExtReg → Bool → Nat → GateResources
  zeroExtend : ExtReg → Nat → GateResources
  signExtend : ExtReg → Nat → GateResources
  zeroDealloc : ExtReg → Nat → GateResources
  signDealloc : ExtReg → Nat → GateResources
  radixReverse : Reg → Nat → GateResources

namespace LowGate

/-- Walk a lowered gate tree accumulating structural resources. -/
def resources (M : LowGateResourceModel) : LowGate → GateResources
  | .id => {}
  | .seq U V => GateResources.seq (resources M U) (resources M V)
  | .adj U => resources M U
  | .H _ => { h := 1 }
  | .X _ => { x := 1 }
  | .ShiftL r n => M.shiftL r n
  | .ShiftR r n => M.shiftR r n
  | .Negate r => M.negate r
  | .AddScaled dst src negSrc shift => M.addScaled dst src negSrc shift
  | .Phase _ _ => { rz := 1 }
  | .CNOT _ _ => { cnot := 1 }
  | .Toffoli _ _ _ => { toffoli := 1 }
  | .zeroExtend r n => M.zeroExtend r n
  | .signExtend r n => M.signExtend r n
  | .zeroDealloc r n => M.zeroDealloc r n
  | .signDealloc r n => M.signDealloc r n
  | .RadixReverse r m => M.radixReverse r m

end LowGate

namespace LowGateResourceModel

/-- Forget the resource decomposition, keeping only total gate counts. -/
def toCostModel (M : LowGateResourceModel) : LowGateCostModel where
  shiftL := fun r n => (M.shiftL r n).totalGates
  shiftR := fun r n => (M.shiftR r n).totalGates
  negate := fun r => (M.negate r).totalGates
  addScaled := fun dst src negSrc shift => (M.addScaled dst src negSrc shift).totalGates
  zeroExtend := fun r n => (M.zeroExtend r n).totalGates
  signExtend := fun r n => (M.signExtend r n).totalGates
  zeroDealloc := fun r n => (M.zeroDealloc r n).totalGates
  signDealloc := fun r n => (M.signDealloc r n).totalGates
  radixReverse := fun r m => (M.radixReverse r m).totalGates

end LowGateResourceModel

/-! ## The concrete arithmetic

Truncated `Nat` subtraction below `w = 3` is deliberate and matches the
companion: its definitions are over `Nat` too, and the published Cuccaro
formula is only claimed for `w >= 3`.
-/

/-- Exact resource count of the Cuccaro modulo-`2^w` ripple-carry adder, as
stated in Sec. 4.1 of Cuccaro et al. This published formula applies for
`w >= 3`. -/
def cuccaroModAddResources (w : Nat) : GateResources where
  h := 0
  x := 2 * w - 6
  cnot := 5 * w - 7
  toffoli := 2 * w - 3
  rz := 0
  cleanAnc := 1

/-- Two's-complement negation is `-x = (~x) + 1 (mod 2^w)`: apply `X` to all `w`
data qubits, prepare a clean `w`-bit register holding 1, apply a Cuccaro modulo
adder, then erase the constant-one register. -/
def negateResources (r : ExtReg) : GateResources :=
  let w := ExtReg.width r
  let a := cuccaroModAddResources w
  { h := a.h
    -- `w` X gates for bitwise complement; 2 more to prepare/erase |1>.
    x := w + a.x + 2
    cnot := a.cnot
    toffoli := a.toffoli
    rz := a.rz
    -- `w` clean bits for the constant-one register + Cuccaro carry.
    cleanAnc := w + a.cleanAnc }

/-- `negateResources` with the register replaced by its width.

This is the companion's `negateResources` body with `ExtReg.width r` substituted
by `w`; `negateResources_eq_atWidth` below is `rfl`. It exists because the
planner is indexed by a bare `Nat` and must not pay an O(w) register
construction per cost query. -/
def negateResourcesAtWidth (w : Nat) : GateResources :=
  let a := cuccaroModAddResources w
  { h := a.h
    x := w + a.x + 2
    cnot := a.cnot
    toffoli := a.toffoli
    rz := a.rz
    cleanAnc := w + a.cleanAnc }

theorem negateResources_eq_atWidth (r : ExtReg) :
    negateResources r = negateResourcesAtWidth (ExtReg.width r) := rfl

/-- The operative model's `negate` field is a function of width alone. -/
theorem shorGateCostModel_negate_atWidth (r : ExtReg) :
    (negateResources r).totalGates
      = (negateResourcesAtWidth (ExtReg.width r)).totalGates := rfl

/-- Toom-Cook linear combinations are formed with ordinary in-place additions;
`negSrc` needs no different count, since subtraction is the inverse of the
corresponding reversible addition circuit, and `shift` is a wiring offset. -/
def addScaledResources
    (dst _src : ExtReg) (_negSrc : Bool) (_shift : Nat) : GateResources :=
  cuccaroModAddResources (ExtReg.width dst)

/-- Radix reversal as `floor(m/2)` pairwise SWAPs, each three CNOTs. -/
def radixReverseResources (_r : Reg) (m : Nat) : GateResources :=
  {
    cnot := 3 * (m / 2)
  }

/-- The companion's operative structural model: shifts and zero-extension are
free wiring, sign extension and deallocation cost one CNOT per bit, and
arithmetic is Cuccaro. -/
def shorGateResourceModel : LowGateResourceModel where
  shiftL := fun _ _ => {}
  shiftR := fun _ _ => {}
  negate := negateResources
  addScaled := addScaledResources
  zeroExtend := fun _ _ => {}
  signExtend := fun _ n => { cnot := n }
  zeroDealloc := fun _ _ => {}
  signDealloc := fun _ n => { cnot := n }
  radixReverse := radixReverseResources

/-- Concrete scalar gate-count model obtained by forgetting the resource
decomposition of `shorGateResourceModel`. This is the operative model. -/
def shorGateCostModel : LowGateCostModel :=
  shorGateResourceModel.toCostModel

/-! ## Closed forms, as consequences

These are the numbers this project's cost model and the accompanying write-up
quote. They are theorems about the definitions above, not definitions of their
own, so quoting them cannot drift from what the companion actually charges.
-/

theorem cuccaroModAddResources_totalGates (w : Nat) (hw : 3 <= w) :
    (cuccaroModAddResources w).totalGates = 9 * w - 16 := by
  show 0 + (2 * w - 6) + (5 * w - 7) + (2 * w - 3) + 0 = 9 * w - 16
  omega

theorem negateResourcesAtWidth_totalGates (w : Nat) (hw : 3 <= w) :
    (negateResourcesAtWidth w).totalGates = 10 * w - 14 := by
  show 0 + (w + (2 * w - 6) + 2) + (5 * w - 7) + (2 * w - 3) + 0 = 10 * w - 14
  omega

theorem negateResources_totalGates (r : ExtReg) (hw : 3 <= ExtReg.width r) :
    (negateResources r).totalGates = 10 * ExtReg.width r - 14 := by
  show 0 + (ExtReg.width r + (2 * ExtReg.width r - 6) + 2) + (5 * ExtReg.width r - 7)
        + (2 * ExtReg.width r - 3) + 0 = 10 * ExtReg.width r - 14
  omega

/-- Sign extension by `n` bits costs `n` CNOTs, and zero extension is free.
This is the primitive behind the planner's per-node allocation charge. -/
@[simp] theorem shorGateResourceModel_signExtend_totalGates (r : ExtReg) (n : Nat) :
    (shorGateResourceModel.signExtend r n).totalGates = n :=
  Nat.zero_add n

@[simp] theorem shorGateResourceModel_zeroExtend_totalGates (r : ExtReg) (n : Nat) :
    (shorGateResourceModel.zeroExtend r n).totalGates = 0 := rfl

end TableGeneration.RecursiveCost.ForShor
