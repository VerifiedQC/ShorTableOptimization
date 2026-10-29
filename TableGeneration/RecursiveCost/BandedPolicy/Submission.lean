import TableGeneration.RecursiveCost.BandedPolicy.Semantics

/-!
# Submission entry point for a banded policy

The analogue of ForShor's `Submission/PolicyTemplate.lean` +
`PolicyCheck.lean`, for STO tables and both product modes.

A submission is **data plus one kernel-reduced `Bool`**:

```lean
def policy : BandedPolicy := { mode := .PhaseProduct, bands := [⟨2048, band0⟩, …] }
theorem accepted : policy.check = true := by decide +kernel
```

`scripts/policy_json_to_lean.py` writes exactly that file from the site's
policy JSON, plus `correct` (the certificate, a one-line application of the
generic theorem) and, when a target width is given, `chain_contracts`
(the advisory: every band the recursion from the target selects shrinks the
width). There is no per-band proof to write: `check` *is* STO's per-table
contract (`PolicyTable.check_iff`), and `decide +kernel` reduces it in the
kernel without the elaborator's `whnf`, which is what keeps `k = 5, 6`
tables and several bands cheap (ForShor's heartbeat cost is in its IR
extraction, which this mirror does not do).

Nothing here is evaluation-tier: `accepted` and `chain_contracts` are kernel
proofs, and `PolicySubmission.correct` is a theorem generic in the policy.
-/

namespace TableGeneration.PolicyMirror

/-- A banded-policy submission: the policy and its accepted check. -/
structure PolicySubmission where
  policy : BandedPolicy
  accepted : policy.check = true

namespace PolicySubmission

/-- The certificate: an accepted policy computes `φ · ∏ xs` at every width. -/
theorem correct (S : PolicySubmission) :
    ∀ (n : Nat) (φ : ℚ) (xs : Fin S.policy.mode.arity → ℤ),
      S.policy.evalPhase n φ xs = φ * ∏ s, (xs s : ℚ) :=
  evalPhase_correct_of_check S.policy S.accepted

/-- Thresholds of an accepted submission strictly decrease. -/
theorem sorted (S : PolicySubmission) :
    (S.policy.bands.map Band.threshold).IsChain (· > ·) :=
  BandedPolicy.check_sorted S.accepted

end PolicySubmission

end TableGeneration.PolicyMirror
