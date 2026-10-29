import TableGeneration.RecursiveCost.BandedPolicy.Bridge
import FastMultiplication.ShorVerification.Submission.Correct

/-!
# Bridge closure: an accepted STO `PhaseProduct` policy is ForShor-correct

`Bridge.lean` (ported unchanged from the STO policy mirror) transports an
accepted STO banded policy to ForShor's `Shor.ShorPolicySubmission`. This
module applies ForShor's own end-to-end certificate,
`Shor.policy_submission_correct` (`Submission/Correct.lean`), to that value.

So: for every STO `BandedPolicy` with `check = true` (one `decide +kernel`) in
`PhaseProduct` mode, the reference order-finding program ForShor compiles from
the transported policy meets ForShor's declared single-run success bound at
the fixed precision, for every order-finding instance and every complete
continued-fraction search.

Which widths: whatever ForShor's compiler uses. Built on an unmodified ForShor
checkout that is the scan (`nextWidth`); built on the exact-width drop-in it
is the exact width. The statement is the same text in both builds.
-/

namespace TableGeneration.PolicyMirror

open Shor Reference

noncomputable section

/-- **Every accepted STO `PhaseProduct` policy is ForShor-correct.** -/
theorem sto_pp_policy_forshor_correct
    {qs : QSemantics} [RegEncoding qs.Basis] [MeasureClass qs]
    [GateSemanticsFacts qs] [LowerGateClass qs]
    (P : BandedPolicy) (h : P.check = true) (hmode : P.mode = .PhaseProduct) :
    ∀ (T : ℕ → ℕ), ContinuedFractionSearchComplete T →
    ∀ inst : ShorOrderFindingInstance,
      referenceSuccessProbabilityAt submissionPrecision inst.N ≤
        probability_of_success
          (qs := qs)
          (evalC := LowerGateClass.evalL (qs := qs))
          (T := T)
          (verify := fun d => decide ((inst.a ^ d) % inst.N = 1))
          (x := (referenceProgramAt (toForShor P h hmode) (toForShor_admissible P h hmode)
            submissionPrecision inst).output)
          (r := ord inst.a inst.N inst.coprime)
          (Q := ASize (referenceProgramAt (toForShor P h hmode) (toForShor_admissible P h hmode)
            submissionPrecision inst).output)
          (C := (referenceProgramAt (toForShor P h hmode) (toForShor_admissible P h hmode)
            submissionPrecision inst).circuit)
          (ψ := qs.ket (RegEncoding.zero (Basis := qs.Basis))) :=
  Shor.policy_submission_correct (qs := qs) (toShorPolicySubmission P h hmode)

end

end TableGeneration.PolicyMirror
