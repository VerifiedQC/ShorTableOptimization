import TableGeneration.RecursiveCost.BandedPolicy.Instances.Submitted

/-! Evaluation-tier report for the harness (not a proof): the recursion ladder
from a target width, and the per-band child width at its own threshold.

  lake env lean --run scripts/BandedPolicyReport.lean -- <target width>
-/

open TableGeneration TableGeneration.PolicyMirror

/-- The first rung of the exact ladder that fails the threshold rule (`rungOK`), as JSON:
the band chosen there, its `k`, the width, the band's exact child width there, and why. -/
def thresholdFailure (P : BandedPolicy) (n : Nat) : String :=
  match (P.ladderTight n).find? (fun r => !P.rungOK r) with
  | none => "null"
  | some (w, _) =>
    match P.choose w with
    | none => "null"
    | some T =>
      let i := P.bands.findIdx (fun b => decide (b.threshold ≤ w))
      let thr := (P.bands[i]?.map Band.threshold).getD 0
      "{\"band\":" ++ toString i ++ ",\"threshold\":" ++ toString thr ++ ",\"k\":" ++ toString T.k ++
        ",\"width\":" ++ toString w ++ ",\"child_width\":" ++ toString (T.tightWidth w) ++
        ",\"kind\":\"" ++ (if w < T.k then "degenerate_limbs" else "no_shrink") ++ "\"}"

def main (args : List String) : IO UInt32 := do
  let args := match args with | "--" :: rest => rest | _ => args
  let n := (args.head? >>= String.toNat?).getD 2048
  let P := Instances.Submitted.policy
  let rungs := (P.ladder n).map fun (w, k) =>
    "{\"width\":" ++ toString w ++ ",\"k\":" ++ (match k with | some k => toString k | none => "null") ++ "}"
  let rungsT := (P.ladderTight n).map fun (w, k) =>
    "{\"width\":" ++ toString w ++ ",\"k\":" ++ (match k with | some k => toString k | none => "null") ++ "}"
  let bands := P.bands.map fun b =>
    "{\"threshold\":" ++ toString b.threshold ++ ",\"k\":" ++ toString b.table.k ++
      ",\"child_width_at_threshold\":" ++ toString (b.table.childWidth b.threshold) ++
      ",\"tight_width_at_threshold\":" ++ toString (b.table.tightWidth b.threshold) ++
      ",\"check\":" ++ toString (b.table.check P.mode) ++ ",\"ops\":" ++ toString b.table.ops.length ++ ",\"points\":" ++ toString b.table.pts.length ++ "}"
  IO.println ("{\"mode\":\"" ++ (match P.mode with | .PhaseProduct => "PhaseProduct" | .PhaseTripleProduct => "PhaseTripleProduct") ++ "\",\"target_width\":" ++ toString n ++ ",\"ladder\":[" ++ ",".intercalate rungs ++
    "],\"tight_ladder\":[" ++ ",".intercalate rungsT ++ "],\"bands\":[" ++ ",".intercalate bands ++ "],\"check\":" ++ toString P.check ++
    ",\"chain_contracts\":" ++ toString (P.chainContracts n) ++
    ",\"chain_contracts_tight\":" ++ toString (P.chainContractsTight n) ++
    ",\"threshold_failure\":" ++ thresholdFailure P n ++
    ",\"bands_contract\":" ++ toString P.bandsContract ++
    ",\"declared_ok\":" ++ (match Instances.Submitted.declared? with
      | some d => toString (P.declOK d) | none => "null") ++
    ",\"declared_threshold_ok\":" ++ (match Instances.Submitted.declared? with
      | some d => toString (P.declThresholdOK d) | none => "null") ++
    ",\"declared_tight_ok\":" ++ (match Instances.Submitted.declared? with
      | some d => toString (P.declOKTight d) | none => "null") ++ "}")
  return 0
