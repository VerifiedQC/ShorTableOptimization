import TableGeneration.Policy

namespace TableGeneration.Submission.Policy.Helper

open Operations

/-!
A helper module that exists to exercise the multi-file submission path in CI.

It is deliberately inert: nothing here changes which targets the submission
handles. What it does cover is the shape a real multi-file submission has --
`Policy.lean` importing `TableGeneration.Submission.Policy.*`, with the helper
compiled from the submission tree rather than from the restored base-branch
cache -- and the ordinary Lean structure (`section`, `variable`) that the
submission syntax gate has to admit.
-/

section

variable (mode : ProductMode)

/-- The canonical construction, unchanged. A submission that returns this
    handles no target better than the baseline, which is the point. -/
def canonicalFor (k : Nat) : List Point :=
  canonicalPoints mode k

end

end TableGeneration.Submission.Policy.Helper
