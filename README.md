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

Checks you can run locally. Only the last needs a built Lean tree; the rest
finish in under a second.

```bash
python3 scripts/verifier.py --out-dir artifacts                  # the full verifier
python3 scripts/verifier.py --out-dir artifacts --preflight-only # structural checks only
python3 scripts/test_verifier_hardening.py                       # scanner cannot be evaded
python3 scripts/test_archive_completeness.py                     # admitted files are archived
python3 scripts/test_publish_promotion.py                        # promotion may only write what it generates
python3 scripts/check_mathlib_confinement.py                     # Mathlib stays out of the contract
node scripts/test_recursive_cost.js                              # Lean model vs browser calculator
```

Every one of these runs in CI. Submissions are gated by the verifier plus the
hardening and archive checks; promotion by the promotion, confinement and
archive checks; and the Lean/JS differential runs in promotion and on the
ForShor dependency bump.

The template passes preflight. The full verifier rejects it, because it handles
no benchmark targets yet.

## Writing a Submission

Replace `implementation` in `TableGeneration/Submission/Policy.lean`. That is
the only file you need to edit. Helper files may be added at any depth under
`TableGeneration/Submission/Policy/` and imported from `Policy.lean`:

```lean
import TableGeneration.Submission.Policy.Helpers
```

A helper directly under `TableGeneration/Submission/` is **rejected**; the
changed-file check admits `Submission/Policy/` and nothing else beside it.

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
reproduces the metrics, and commits the result to `main`.

Nothing reviews that commit by hand, so the gates are in the job that makes it.
It runs on a checkout of `main` rather than of the submission, re-derives the
generator from the `submission-results` archive, and re-checks every claim the
archive makes. `scripts/ci/publish_promotion.py` then refuses to push if
promotion touched any path outside the ones `scripts/promote.py` generates:
`TableGeneration/BestKnown.lean`,
`TableGeneration/RecursiveCost/ArchivedCatalog.lean`,
`TableGeneration/Policies/Accepted/`, and `leaderboard/best-known.md`.

The ForShor dependency bump (`update-forshor.yml`) is the only other automation
that writes to `main`, and self-gates the same way: it refuses to push unless
the companion's cost model is byte-identical to
`scripts/tests/companion-cost-model.tsv`.

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
- `scripts/verifier.py` is the CI verifier.
- `scripts/leaderboard.py` builds the benchmark index from successful verifier
  artifacts. It is `scripts/promote.py`'s only input.

## Further Reading

- [BENCHMARK.md](BENCHMARK.md) for targets, weights, and metric definitions.
- [RECURSIVE_COST_MODEL.md](RECURSIVE_COST_MODEL.md) for the gate-count model.
- [AGENTS.md](AGENTS.md) for the code boundaries automated contributors must
  respect.
