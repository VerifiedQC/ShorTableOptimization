import Lake
open Lake DSL

package ShorTableOptimization where

/--
Pinned to the revision the companion uses, so the companion's own definitions
elaborate here unchanged -- `Function.update` in the width scan and
`Finset.univ.sup` in `commonNeededWidth` have no Lean-core equivalent. The
companion pins Mathlib too, so the two pins move together; `update-forshor`
fails if they drift apart.

Listed first because Lake resolves a package name once, so the root pin wins.

CI confines the import to `TableGeneration/RecursiveCost/**`. That is necessary
for the propext-only axiom audit but not sufficient: core Lean can route an
instance through a classical definition with no Mathlib in sight (v4.36.0-rc1
did exactly that to `BEq Int`). The audit itself is the check.
-/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "4dc43842a11f257ffba2a611c943a133a65cb4b2"

/--
Supplies the gate cost model, confined to `TableGeneration/RecursiveCost/**`
like Mathlib.

The library is `FastMultiplication`; the PACKAGE is named `Fast_multiplication`
here and in `lake-manifest.json`, but upstream now declares `package «ForShor»`.
Resolution works anyway because lake takes the name from the manifest, not from
the remote lakefile. Renaming is cosmetic and costs the build cache (D3).
-/
require «Fast_multiplication» from git
  "https://github.com/VerifiedQC/ForShor.git" @ "main"

@[default_target]
lean_lib TableGeneration where
  moreLeanArgs := #["-s", "1048576"]
