import TableGeneration.RecursiveCost.PTP.Instances.PTPSubmitted
import TableGeneration.RecursiveCost.PTP.Census
import TableGeneration.RecursiveCost.PTP.CensusFull
import TableGeneration.RecursiveCost.PTP.Exact
import TableGeneration.RecursiveCost.PTP.ExactBuild
import TableGeneration.RecursiveCost.PTP.Threshold

/-! Evaluation-tier report for check_ptp_policy.py (diagnostics, not a proof):
PTP-derived ladder, the PP-borrowed ladder (mirror's `nextSignedWidth` scan) for
comparison, per-band contract and child widths, and the census/qubit formulas
at the target width.

  lake env lean --run scripts/PTPPolicyReport.lean -- <target width>
-/

open TableGeneration TableGeneration.PTP

def ppTable (T : PTPTable) : PolicyMirror.PolicyTable := ⟨T.k, T.pts, T.ops⟩

def ppLadder (P : PTPPolicy) (n : Nat) : List (Nat × Option Nat) :=
  (PolicyMirror.BandedPolicy.ladder ⟨.PhaseTripleProduct, P.bands.map fun b => ⟨b.threshold, ppTable b.table⟩⟩ n)

def rungs (l : List (Nat × Option Nat)) : String :=
  ",".intercalate (l.map fun (w, k) =>
    "{\"width\":" ++ toString w ++ ",\"k\":" ++ (match k with | some k => toString k | none => "null") ++ "}")

def census (c : Census) : String :=
  "{\"h\":" ++ toString c.h ++ ",\"x\":" ++ toString c.x ++ ",\"cnot\":" ++ toString c.cnot ++
  ",\"toffoli\":" ++ toString c.toffoli ++ ",\"rz\":" ++ toString c.rz ++ ",\"total\":" ++ toString c.total ++ "}"

/-- The first rung of the exact ladder that fails the threshold rule (`rungOK`), as JSON. -/
def thresholdFailure (P : PTPPolicy) (n : Nat) : String :=
  match (P.ladderX n).find? (fun r => !P.rungOK r) with
  | none => "null"
  | some (w, _) =>
    match P.choose w with
    | none => "null"
    | some T =>
      let i := P.bands.findIdx (fun b => decide (b.threshold ≤ w))
      let thr := (P.bands[i]?.map PTPBand.threshold).getD 0
      "{\"band\":" ++ toString i ++ ",\"threshold\":" ++ toString thr ++ ",\"k\":" ++ toString T.k ++
        ",\"width\":" ++ toString w ++ ",\"child_width\":" ++ toString (ptpTightWidth T w) ++
        ",\"kind\":\"" ++ (if w < T.k then "degenerate_limbs" else "no_shrink") ++ "\"}"

def main (args : List String) : IO UInt32 := do
  let args := match args with | "--" :: rest => rest | _ => args
  let n := (args.head? >>= String.toNat?).getD 2048
  let P := Instances.PTPSubmitted.policy
  let bands := P.bands.map fun b =>
    "{\"threshold\":" ++ toString b.threshold ++ ",\"k\":" ++ toString b.table.k ++
      ",\"contract\":" ++ toString b.table.contract ++
      ",\"ptp_child_width_at_threshold\":" ++ toString (childWidth b.threshold b.table.ops) ++
      ",\"exact_width_at_threshold\":" ++ toString (ptpTightWidth b.table b.threshold) ++
      ",\"pp_scan_child_width_at_threshold\":" ++ toString ((ppTable b.table).childWidth b.threshold) ++
      ",\"adds\":" ++ toString (addCount b.table.ops) ++ ",\"negates\":" ++ toString (negCount b.table.ops) ++
      ",\"checkpoints\":" ++ toString (cpCount b.table.ops) ++
      ",\"ops\":" ++ toString b.table.ops.length ++ ",\"points\":" ++ toString b.table.pts.length ++ "}"
  IO.println ("{\"target_width\":" ++ toString n ++ ",\"ladder\":[" ++ rungs (P.ladder n) ++
    "],\"ladder_exact\":[" ++ rungs (P.ladderX n) ++ "],\"chain_contracts_exact\":" ++ toString (P.chainContractsX n) ++
    ",\"chain_contracts_tight\":" ++ toString (P.chainContractsTight n) ++
    ",\"threshold_failure\":" ++ thresholdFailure P n ++
    ",\"ladder_pp_scan\":[" ++ rungs (ppLadder P n) ++ "],\"bands\":[" ++ ",".intercalate bands ++
    "],\"check\":" ++ toString P.check ++ ",\"chain_contracts\":" ++ toString (P.chainContracts n) ++
    ",\"census\":" ++ census (ptpResources P n) ++
    ",\"cnot_with_extension\":" ++ toString (ptpCnotFull P n) ++
    ",\"toffoli_uncompute\":" ++ toString (ptpAndDag P n) ++
    ",\"census_ccphase_leaf\":" ++ census (ptpResourcesCCPhase P n) ++
    ",\"reserve_need_per_operand\":" ++ toString (ptpReserveNeed P n) ++
    ",\"clean_ancilla_peak\":" ++ toString (ptpCleanAnc P n) ++
    ",\"qubits\":" ++ toString (ptpQubits P n) ++
    ",\"qubits_ccphase_leaf\":" ++ toString (ptpQubitsCCPhase P n) ++
    ",\"qubits_bound_scan\":" ++ toString (3 * n + ptpWorkspace P n) ++
    ",\"census_exact\":" ++ census (ptpResourcesX P n) ++
    ",\"cnot_with_extension_exact\":" ++ toString (ptpCnotFullX P n) ++
    ",\"toffoli_uncompute_exact\":" ++ toString (ptpAndDagX P n) ++
    ",\"workspace_exact\":" ++ toString (ptpWorkspaceX P n) ++
    ",\"qubits_bound_exact\":" ++ toString (3 * n + ptpWorkspaceX P n) ++ "}")
  return 0
