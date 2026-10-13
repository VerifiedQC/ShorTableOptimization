# Shor Table Optimization

A benchmark for machine-found, machine-checked interpolation tables.

Recursive phase multiplication splits a large multiplication into smaller ones
using an interpolation table: a short program of symbolic operations that says
how to combine the pieces. A better table means a cheaper circuit. Finding one
is a search problem; checking that it is correct is a proof obligation.

This repository holds both halves. A submission is a Lean policy that generates
tables, together with the proofs that they are valid. The proofs are the
acceptance test: an incorrect table does not compile, so it never becomes a
submission. Accepted policies are scored, archived, and composed into a
best-known generator.

## Quick Start

```bash
lake exe cache get          # prebuilt Mathlib artifacts, minutes
lake build TableGeneration  # build the template
```

`lake exe cache get` is not optional on a fresh checkout. The recursive cost
model imports the `Fast_multiplication` companion, which depends on Mathlib.
Fetching the prebuilt artifacts takes a few minutes; compiling them from source
takes hours. Nothing the submission contract depends on imports Mathlib, so a
submission's own proofs stay Mathlib-free.

Three checks you can run locally:

```bash
python3 scripts/verifier.py --out-dir artifacts                  # the full verifier
python3 scripts/verifier.py --out-dir artifacts --preflight-only # structural checks only
node scripts/test_recursive_cost.js                              # Lean model vs browser calculator
```

The template passes preflight. The full verifier rejects it, because it handles
no benchmark targets yet.

## Writing a Submission

Replace `implementation` in `TableGeneration/Submission/Policy.lean`. That is
the only file you need to edit. Helper files may be added anywhere under
`TableGeneration/Submission/` and imported from `Policy.lean`:

```lean
import TableGeneration.Submission.Helpers
```

`implementation : GeneratorPolicy` bundles three things:

- the generated points, and the `(mode, k)` cases the policy handles;
- the point-consumption order, and the generated program;
- proofs of point validity, safe consumption, and return to the starting state.

A policy may be general or target-specific. CI scores only configured targets
where its `handles` field is true, and requires at least one. Generation for an
unhandled target falls through to the protected best-known policy, whose own
final fallback is the general generator.

### What a table has to satisfy

`generatedPoints` may be any mathematically distinct list of the required length
for the selected product mode and `k`. Each point must be one of:

```text
0, inf, +/- 2^n, or +/- 1/2^n
```

The program may consume the points in a different order, but that order must be
a permutation of the generated points. It must use only safe arithmetic
operations and return to the starting state.

### What you may not change

Leave the protected specification, language, metrics, and workflow files alone.
`Defs.lean` and `Correctness.lean` are fixed adapters.

The verifier rejects changed protected files, `sorry`, `admit`, new `axiom` or
`constant` declarations, `unsafe`, external implementation hooks, and
compile-time execution commands such as `#eval` in submitted code.

## Opening a Pull Request

The maintained submission base branch is `submission/template`:

```text
base:    submission/template
compare: submission/<name>
```

GitHub Actions runs a Python preflight over the submitted files first. If that
passes, it installs Lean using the base template's `lean-toolchain`, runs the
full verifier, posts a compact benchmark summary, and uploads the verifier
artifacts. The comment links to the workflow run, the readable and JSON results,
the website benchmark data, and an archived source snapshot on the
`submission-results` branch. Workflow artifacts and diagnostic logs are kept for
90 days. A successful submission PR is closed automatically only after its
results and source have been archived.

## Two scores, not one

A submission is measured two different ways, and they do not agree. Read this
before optimizing anything.

**Per-target score.** Each handled target gets
`arithmetic_operation_count + 5 * parallel_phase_product_layer_count`. It is
width-independent, which is the point: it scores a table on its own, without
reference to any operand size or to any other submission. This decides
champions and promotion. See [BENCHMARK.md](BENCHMARK.md).

**Gate count.** The recursive planner searches every accepted `PhaseProduct`
table and reports the lowest logical gate count for an operand width, with
RSA-2048 as the headline. See
[RECURSIVE_COST_MODEL.md](RECURSIVE_COST_MODEL.md).

The two disagree because an operation count cannot see how far a program
**contracts** its operands, and the child width applies to the whole subtree
below it. At `k = 4` the gate-cheaper table uses 28 operations against 26,
because it contracts to 533 bits rather than 534.

So a table can lose its target and still lower the gate count. The planner
searches the full accepted archive rather than the champions, so it will find
it. If you are optimizing for gates, optimize for gates.

## Results

Results are published on the
[leaderboard website](https://verifiedqc.github.io/ShorTableOptimization/).
The landing page is the RSA-2048 gate count and the plan that achieves it; the
per-target benchmark is on `targets.html`, linked from it. Both pages let you
plan any operand width.

Current promoted metrics are in
[`leaderboard/best-known.md`](leaderboard/best-known.md).

## Promotion

When a result becomes a per-target champion, trusted automation constructs the
complete best-known generator, rebuilds Lean, audits the target proofs,
reproduces the metrics, and updates `automation/best-known`. Its workflow
summary links to the
[comparison for creating a PR](https://github.com/VerifiedQC/ShorTableOptimization/compare/main...automation/best-known?expand=1)
for manual review and merging into `main`. Automation never pushes to `main`
directly.

## Repository Layout

The submission contract, which is protected and Mathlib-free:

- `TableGeneration/Basic.lean` defines symbolic registers, states, points, and
  primitive operations.
- `TableGeneration/Language.lean` defines programs, execution, row matching,
  ordered point consumption, and pretty printers.
- `TableGeneration/Spec.lean` defines protected product modes, default point
  lists, and validity checks for generated points.
- `TableGeneration/Metrics.lean` defines operation and layer counts.
- `TableGeneration/Policy.lean` defines the portable policy interface.
- `TableGeneration/Baseline.lean` defines the protected general fallback.
- `TableGeneration/Submission/Policy.lean` contains the submitted policy.

Everything downstream of acceptance:

- `TableGeneration/BestKnown.lean` selects promoted policies before the general
  fallback. It is generated by `scripts/promote.py`.
- `TableGeneration/RecursiveCost/` holds the recursive gate-count model and the
  policy planner. It is the only part of the tree that depends on Mathlib and on
  the `Fast_multiplication` companion.

Benchmark and tooling:

- `leaderboard/config.json` defines the active targets and score weights.
- `leaderboard/site/index.html` is the static leaderboard website.
- `scripts/verifier.py` is the CI verifier.
- `scripts/leaderboard.py` updates the website benchmark JSON from successful
  verifier artifacts.

## Further Reading

- [BENCHMARK.md](BENCHMARK.md) for targets, weights, and metric definitions.
- [RECURSIVE_COST_MODEL.md](RECURSIVE_COST_MODEL.md) for the gate-count model.
- [AGENTS.md](AGENTS.md) for the code boundaries automated contributors must
  respect.
