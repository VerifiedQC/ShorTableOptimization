import TableGeneration.RecursiveCost.ForShor.Registers

/-!
# The low-level gate language and its cost interface

Integrated from the companion Lean formalization at commit `d5a165b`, files
`FastMultiplication/ShorVerification/Framework/AbstractMachine/Angle.lean`,
`.../AbstractMachine/LowGate.lean` and `.../Gatecount/CostModel.lean`.
Apache-2.0; declaration names are the companion's.

`LowGate` is the target language a lowered circuit is written in, and
`gateCount` is the single evaluator that reads a cost model off it. The
companion's semantics for this language -- `Angle.toReal`, state vectors,
`Complex` -- is not taken: gate counting never evaluates a circuit, it only
walks its syntax.
-/


namespace TableGeneration.RecursiveCost.ForShor

/-- An angle in units of `π`: `a : Angle` denotes `a * π` radians. Storing the
rational coefficient rather than the real number is what makes the gate
language computable; the companion recovers the real angle via `Angle.toReal`,
which gate counting does not need. -/
abbrev Angle := Rat

/-- Low-level target gate language for lowering. `LowGate` mirrors primitive
high-level gates and includes explicit nodes for allocation, deallocation,
phase-product fallbacks, and radix reversal. -/
inductive LowGate : Type
  | id : LowGate
  | seq : LowGate → LowGate → LowGate
  | adj : LowGate → LowGate
  | H : Nat → LowGate
  | X : Nat → LowGate
  | Phase : Nat → Angle → LowGate
  | CNOT : Nat → Nat → LowGate
  | Toffoli : Nat → Nat → Nat → LowGate
  | ShiftL : (r : ExtReg) → (n : Nat) → LowGate
  | ShiftR : (r : ExtReg) → (n : Nat) → LowGate
  | Negate : (r : ExtReg) → LowGate
  | AddScaled : (dst src : ExtReg) → (negSrc : Bool) → (shift : Nat) → LowGate
  | zeroExtend : (r : ExtReg) → (n : Nat) → LowGate
  | signExtend : (r : ExtReg) → (n : Nat) → LowGate
  | zeroDealloc : (r : ExtReg) → (n : Nat) → LowGate
  | signDealloc : (r : ExtReg) → (n : Nat) → LowGate
  | RadixReverse : (r : Reg) → (m : Nat) → LowGate
deriving Inhabited

/-- Sequential composition notation for low gates. -/
infixr:80 " ;; " => LowGate.seq

/-- A table of costs for each primitive low-level gate family. Sequencing,
adjoint, and elementary one-qubit gates are handled uniformly by `gateCount`;
the fields here are exactly the operations whose costs depend on registers,
payloads, or the concrete arithmetic model. -/
structure LowGateCostModel where
  shiftL : ExtReg → Nat → Nat
  shiftR : ExtReg → Nat → Nat
  negate : ExtReg → Nat
  addScaled : ExtReg → ExtReg → Bool → Nat → Nat
  zeroExtend : ExtReg → Nat → Nat
  signExtend : ExtReg → Nat → Nat
  zeroDealloc : ExtReg → Nat → Nat
  signDealloc : ExtReg → Nat → Nat
  radixReverse : Reg → Nat → Nat

namespace LowGate

/-- Evaluate a lowered gate tree against a cost model. Structural gates add or
preserve cost, elementary `H`/`X` gates cost one, and model-dependent
operations are delegated to `LowGateCostModel`. -/
def gateCount (M : LowGateCostModel) : LowGate → Nat
  | .id => 0
  | .seq U V => gateCount M U + gateCount M V
  | .adj U => gateCount M U
  | .H _ => 1
  | .X _ => 1
  | .ShiftL r n => M.shiftL r n
  | .ShiftR r n => M.shiftR r n
  | .Negate r => M.negate r
  | .AddScaled dst src negSrc shift => M.addScaled dst src negSrc shift
  | .Phase _ _ => 1
  | .CNOT _ _ => 1
  | .Toffoli _ _ _ => 1
  | .zeroExtend r n => M.zeroExtend r n
  | .signExtend r n => M.signExtend r n
  | .zeroDealloc r n => M.zeroDealloc r n
  | .signDealloc r n => M.signDealloc r n
  | .RadixReverse r m => M.radixReverse r m

end LowGate

end TableGeneration.RecursiveCost.ForShor
