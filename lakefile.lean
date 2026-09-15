import Lake
open Lake DSL

package ShorTableOptimization where

/--
Mathlib is pinned to the revision the companion development uses, so the cost
model integrated under `TableGeneration/RecursiveCost/ForShor/` can reproduce
the companion's definitions verbatim -- `Function.update` in the width scan and
`Finset.univ.sup` in `commonNeededWidth` have no Lean-core equivalent.

The import is deliberately confined to `TableGeneration/RecursiveCost/**`, and
CI enforces that. Everything the submission contract depends on stays
Mathlib-free, which is what keeps `#print axioms` on the two submission theorems
reporting `propext` alone.
-/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "fadcf92bfcfe7575bbdf04c6f83ab3ada53e3d42"

@[default_target]
lean_lib TableGeneration where
  moreLeanArgs := #["-s", "1048576"]
