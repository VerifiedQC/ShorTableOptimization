import TableGeneration.Submission.Policy.Helper

namespace TableGeneration.Submission.Policy

/-!
This is the editable submission entry point. Replace `implementation` with a
`GeneratorPolicy` for the targets handled by the submission; helper files may be
added as needed.

This particular submission handles no target. It exists to exercise the
submission workflow end to end -- preflight, the syntax gate over more than one
file, the Lean build and the axiom audit -- and is expected to stop at the
target-coverage check, so nothing is archived or promoted.
-/

/-- Replace this empty policy with the submitted implementation. -/
def implementation : TableGeneration.GeneratorPolicy :=
  .empty

/-- Keeps the helper module in the import closure so the build really compiles
    it from the submission tree. Not part of the policy. -/
def helperPoints : List TableGeneration.Operations.Point :=
  Helper.canonicalFor .PhaseProduct 3

end TableGeneration.Submission.Policy
