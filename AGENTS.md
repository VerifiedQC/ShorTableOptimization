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
  `TableGeneration/Submission/Policy.lean`; optional helper Lean files go under
  `TableGeneration/Submission/Policy/`, at any depth, and are imported there. A
  helper placed directly under `TableGeneration/Submission/` is rejected by the
  changed-file check.
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
  reproduce every promised benchmark metric before it commits to `main`. It may
  only write the paths `scripts/promote.py` generates; anything else fails the
  job rather than being pushed.

## Which score you are optimizing

Two scores exist and they do not agree. Decide which one you are working on
before you start, because the better table under one can be the worse table
under the other.

**Per-target score**, `arithmetic_operation_count + 5 *
parallel_phase_product_layer_count`. Width-independent, so it judges a table on
its own. It decides champions and promotion, and it is what
`leaderboard/best-known.md` reports.

**Gate count**, the recursive planner's logical gate total at an operand width,
with 2048 bits as the headline. It is what the landing page of the site reports.

They disagree because an operation count cannot see how far a program
**contracts** its operands, and the child width applies to the entire subtree
below that node. Concretely, at `k = 4` the gate-cheaper table uses 28
operations where the other uses 26, because it contracts to 533 bits rather
than 534. Over the archive, ranking by operations picks the gate-worse table in
six (arity, width) cells.

If your goal is gate count:

- Optimize the **child width** first. `nextSignedWidth` in
  `TableGeneration/RecursiveCost/Model.lean` computes it: a running maximum over
  a scan of the program, roughly one bit per `addScaled`, `negate` or `shiftL`
  along a destination chain. It is not a function of how large the coefficients
  in the table look.
- Do not optimize the per-target score. A table that loses its target can still
  lower the gate count, and the planner will still use it: it searches every
  accepted `PhaseProduct` table, not just the champions.
- Do not buy gates with depth. The gate model charges nothing for layers, so
  adding sequential stages to save arithmetic would otherwise be free. A
  candidate deeper than the current champion at the same arity is kept out of
  `archivedCandidates`, the bounded catalogue the Lean planner searches by
  default. It is still archived, and it still reaches the website, which plans
  over `archivedCandidatesUnbounded`. So a deeper table can move the published
  number while the Lean default says it changed nothing; see
  [RECURSIVE_COST_MODEL.md](RECURSIVE_COST_MODEL.md) for which catalogue is
  which.
- Measure before submitting, both ways. They should agree; when they do not, the
  second is what the site will report:
  `lake env lean --run scripts/tests/RecursiveCostOracle.lean --model=v3
  --best-known 2048` and the same command with `--best-known-unbounded`.

Only `PhaseProduct` reaches the planner. `PhaseTripleProduct` has no gate model,
so those targets are scored structurally and never priced in gates.

## Writing a submission

- You are not required to build on the composed generator. A submission is its
  own `GeneratorPolicy` and may handle any subset of targets.
  `TableGeneration/BestKnown.lean` is the fallback for targets you do not
  handle, and is useful as a baseline to measure against, nothing more.
- You are not required to beat anything to be accepted. Validity is the bar:
  the proofs must compile. Whether the result is promoted, or used by the
  planner, is decided afterwards from the measurements.
- An incorrect table does not compile, so it cannot become a submission.
  `generatedPoints_valid` and `generate_safe` are proof fields of the same
  record, both guarded by `handles mode k = true`.
- `TableGeneration/RecursiveCost/ArchivedCatalog.lean` is generated by
  `scripts/promote.py`. Do not edit it by hand.

## Checks

- Run `lake exe cache get` once on a fresh checkout, before the first build:
  Mathlib is a dependency of the recursive cost model, and compiling it from
  source instead of fetching it takes hours.
- Run `lake build TableGeneration` after Lean changes.
- Run `node scripts/test_recursive_cost.js` after recursive planner or website
  calculator changes. It compares the Lean and JavaScript cost models exactly,
  over every accepted table, and separately checks that the two agree on the
  published plan over the unbounded catalogue. Takes a few minutes.
- CI runs `scripts/verifier.py` automatically for submission PRs.
- For local verification while changing the verifier or template, run
  `python3 scripts/verifier.py --out-dir artifacts`.
- For local preflight only, run
  `python3 scripts/verifier.py --out-dir artifacts --preflight-only`.
