import TableGeneration.RecursiveCost.PTP.Contract
import TableGeneration.RecursiveCost.PTP.Width
import TableGeneration.RecursiveCost.PTP.Semantics
import TableGeneration.RecursiveCost.PTP.Leaf
import TableGeneration.RecursiveCost.PTP.LeafSandwich
import TableGeneration.RecursiveCost.PTP.Node
import TableGeneration.RecursiveCost.PTP.Census
import TableGeneration.RecursiveCost.PTP.Exact
import TableGeneration.RecursiveCost.PTP.Recursion
import TableGeneration.RecursiveCost.PTP.Build
import TableGeneration.RecursiveCost.PTP.CensusFull
import TableGeneration.RecursiveCost.PTP.ExactNode
import TableGeneration.RecursiveCost.PTP.ExactRecursion
import TableGeneration.RecursiveCost.PTP.ExactBuild
import TableGeneration.RecursiveCost.PTP.Threshold

/-!
# PhaseTripleProduct (PTP) verification suite

Standalone PTP definitions and theorems (no reuse of PhaseProduct's width scan):

* `Contract.lean`: PTP table contract (`3k - 2` points, pinned to STO's
  `Spec.lean`), PTP magnitude width scan over three operands, banded PTP policy
  and its check;
* `Width.lean`: register-width soundness, wrapping = exact (`node_width_sound`);
* `Semantics.lean`: exact and wrapping-register PTP semantics, functional
  correctness (`evalPhase_correct`, `evalPhaseW_correct`);
* `Leaf.lean`: the CCPhase 3-way grid leaf in ForShor's `LowGate` (documented alternative,
  `evalL_ptpLeafCCPhase_ket`, 5 Rz per cell) and the shared grid algebra;
* `LeafSandwich.lean`: the default compute–rotate–uncompute leaf (`evalL_ptpLeafSandwich_ket`,
  1 Rz per cell, two clean ancillas; census `ptpLeafSandwich_resources`);
* `Node.lean`: one recursion level in `LowGate` (`evalL_ptpNode_ket` sandwich leaves,
  `evalL_ptpNodeCCPhase_ket`,
  `evalL_nodeBody_ket` for any children meeting `ChildSpec`);
* `Census.lean`: gate census and qubits from the lowering (`ptpNode_resources`);
* `Recursion.lean`, `Build.lean`, `CensusFull.lean` (O2): in-place split + extension
  (`SplitLayout`), a node meets the child contract given a clean reserve (`specOn_ptpSubNode`),
  gate-level recursion following a policy (`PolicyImpl`), its existence for every checked policy
  and width (`exists_policyImpl`), correctness and full census at every depth (`ptp_gate_full`);
  `RecursionWitness.lean` (not imported here: it imports FaultChallenge) is a concrete instance;
* `Exact.lean`: exact widths `ptpTightWidth` (soundness, minimality, `≤` scan) and the exact board
  `evalPhaseTight_correct`;
* `ExactNode.lean`, `ExactRecursion.lean`, `ExactBuild.lean` (O5): every gate-level theorem at any
  width ≥ exact (`ptpTightWidth`): the layout floor is implied (`floor_le_tight`, `exactWidth_eq`),
  `evalL_ptpNode_ket_exact`, `specOn_ptpSubNode_exact`, `PolicyImplD` for any admissible width rule,
  `ptp_gate_full_exact` (exact board: existence, correctness, census `ptpResourcesX` …); the scan
  theorems re-derived as corollaries (`*_scan`, `ptp_gate_full_of_D`); `Instances/ExactFault.lean`
  (not imported here) is the gate-level fault one bit below exact;
* `Threshold.lean`: the threshold acceptance rule at exact widths (`chainContractsTight`: every band
  chosen on the exact recursion from the target strictly shrinks the width and has `k ≤ w`;
  `chainContractsTight_iff_reach`).
-/
