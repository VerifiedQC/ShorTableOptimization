# Agent Guidelines

This repository contains a minimal Lean verifier for table-generation
submissions.

## Code Boundaries

- Protected verifier code lives in `TableGeneration/Basic.lean`,
  `TableGeneration/Language.lean`, `TableGeneration/Spec.lean`,
  `TableGeneration/Metrics.lean`, `TableGeneration/Baseline.lean`,
  `TableGeneration/Policy.lean`, and `TableGeneration/BestKnown.lean`.
- Submission-facing code lives in `TableGeneration/Submission/`.
- Submitters implement `GeneratorPolicy` in
  `TableGeneration/Submission/Policy.lean`; optional helper Lean files may be
  added elsewhere under `TableGeneration/Submission/` and imported there.
- `TableGeneration/Submission/Defs.lean` and `Correctness.lean` are fixed
  adapters.

## Verifier Contract

- Preserve the theorem statements checked by `scripts/verifier.py`.
- A submitted policy bundles its generator, handled targets, and proofs.
- `submissionHandles mode k = true` identifies the implemented cases; submitted
  definitions may be general across modes and `k`, or specialized to selected
  targets with fallback elsewhere.
- Submission adapters and verifier entry points must match the template.
- The verifier should reject `sorry`, `admit`, new `axiom` or `constant`
  declarations, `unsafe`, and compile-time execution commands in submission
  files.
- The verifier should use the base branch's `scripts/verifier.py` in CI.
- CI should run verifier preflight before installing Lean or building submitted
  Lean code.
- Leaderboard scoring should use `leaderboard/config.json`.
- Keep the concise benchmark contract in `BENCHMARK.md` synchronized with the
  configured targets, weights, and published result formats.
- A submission must handle at least one configured target; unhandled targets are
  skipped and do not receive scores.
- Successful results and submission source snapshots should be retained on the
  `submission-results` branch.
- Unhandled cases use the protected best-known generator; its final fallback is
  the general generator.
- Promotion must rebuild the composed generator, repeat trusted checks, and
  reproduce every promised benchmark metric before updating
  `automation/best-known`; only a maintainer merges that branch into `main`.

## Checks

- Run `lake exe cache get` once on a fresh checkout, before the first build:
  Mathlib is a dependency of the recursive cost model, and compiling it from
  source instead of fetching it takes hours.
- Run `lake build TableGeneration` after Lean changes.
- Run `node scripts/test_recursive_cost.js` after recursive planner or website
  calculator changes.
- CI runs `scripts/verifier.py` automatically for submission PRs.
- For local verification while changing the verifier or template, run
  `python3 scripts/verifier.py --out-dir artifacts`.
- For local preflight only, run
  `python3 scripts/verifier.py --out-dir artifacts --preflight-only`.
