import TableGeneration.RecursiveCost.BandedPolicy.Defs
import TableGeneration.RecursiveCost.BandedPolicy.Interp
import TableGeneration.RecursiveCost.BandedPolicy.Semantics
import TableGeneration.RecursiveCost.BandedPolicy.Submission
import TableGeneration.RecursiveCost.BandedPolicy.Bridge
import TableGeneration.RecursiveCost.BandedPolicy.Capacity
import TableGeneration.RecursiveCost.BandedPolicy.Tight
import TableGeneration.RecursiveCost.BandedPolicy.Threshold

/-!
# Banded-policy mirror (PhaseProduct and PhaseTripleProduct)

Policy-level mirror of ForShor's `ShorLoweringPolicy` over STO tables.
See `Defs.lean` (data, the check), `Interp.lean` (the arity-`r` Toom–Cook
identity), `Semantics.lean` (what a policy computes; `evalPhase_correct`),
`Submission.lean` (the entry point a harness instantiates), `Bridge.lean`
(PhaseProduct: the same policy as a ForShor `ShorPolicySubmission`),
`Capacity.lean` (register-width soundness: a wrapping register semantics
`evalPhaseReg` that equals `evalPhase`, and contraction on whole bands),
`Tight.lean` (the exact reachable-value width `tightWidth`: sound, minimal, ≤ the scan;
`evalPhaseRegTight_correct`, `declOKTight`),
`Threshold.lean` (the threshold acceptance rule at exact widths: `chainContractsTight`,
`chainContractsTight_iff_reach`).
-/
