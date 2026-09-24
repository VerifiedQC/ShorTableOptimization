import Lake
open Lake DSL

package ShorTableOptimization where

/--
Mathlib is pinned to the revision the companion development uses, so that the
companion's own definitions elaborate here unchanged -- `Function.update` in the
width scan and `Finset.univ.sup` in `commonNeededWidth` have no Lean-core
equivalent.

This `require` is listed first so the root pin governs: the companion's own
Mathlib requirement carries no revision, and Lake resolves a package name once.

The import is deliberately confined to `TableGeneration/RecursiveCost/**`, and
CI enforces that. Everything the submission contract depends on stays
Mathlib-free, which is what keeps `#print axioms` on the two submission theorems
reporting `propext` alone.
-/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "fadcf92bfcfe7575bbdf04c6f83ab3ada53e3d42"

/--
The companion development supplies the gate cost model. It was previously
carved out into `TableGeneration/RecursiveCost/ForShor/` and kept in step by a
hand-run drift check; sourcing it here removes the copy and the drift.

The package is named `Fast_multiplication` and its library is
`FastMultiplication`; neither is spelled "ForShor", which is only the repository
name. The same confinement applies as to Mathlib: nothing outside
`TableGeneration/RecursiveCost/**` may import it.
-/
require «Fast_multiplication» from git
  "https://github.com/VerifiedQC/ForShor.git" @ "main"

@[default_target]
lean_lib TableGeneration where
  moreLeanArgs := #["-s", "1048576"]
