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

Lean is installed with elan, at the toolchain `lean-toolchain` pins. CI does it
with `scripts/ci/install_lean.sh`, which pins the elan installer revision too;
locally, any elan install that honours `lean-toolchain` will do.

```bash
lake exe cache get          # prebuilt Mathlib artifacts, minutes
lake build TableGeneration  # build the library
```

`lake exe cache get` is not optional on a fresh checkout. The recursive cost
model imports the `Fast_multiplication` companion, which depends on Mathlib.
Fetching the prebuilt artifacts takes a few minutes; compiling them from source
takes hours. Nothing the submission contract depends on imports Mathlib, so a
submission's own proofs stay Mathlib-free.

Checks you can run locally:

```bash
python3 scripts/verifier.py --out-dir artifacts --preflight-only # structural checks only, seconds
python3 scripts/test_verifier_hardening.py                       # scanner cannot be evaded, seconds
python3 scripts/test_archive_completeness.py                     # admitted files are archived, seconds
python3 scripts/test_publish_promotion.py                        # promotion may only write what it generates, seconds
python3 scripts/check_mathlib_confinement.py                     # Mathlib stays out of the contract, seconds
python3 scripts/test_submission_syntax_gate.py                   # the parse-tree gate holds, seconds
python3 scripts/verifier.py --out-dir artifacts --axioms-only    # contract theorems still propext-only, needs a built tree
python3 scripts/verifier.py --out-dir artifacts                  # the full verifier: runs lake build, minutes
python3 scripts/test_cost_model_lean.py                          # Lean-only cost-model checks: drives Lean, minutes
```

The last two need a built Lean tree and are not quick: the full verifier runs
`lake build` and then elaborates generated Lean files, and the cost-model checks
drive the Lean oracle. `--axioms-only` needs a built tree too, but only
elaborates two `#print axioms` lines against it. The rest are pure Python over
the working tree.

Every one of these runs in CI. Submissions are gated by the verifier plus the
hardening, preflight, archive and parse-tree-gate checks; promotion by the
promotion, confinement and archive checks together with the axiom audit, which
runs on every pull request and every push to `main` so that a toolchain or
dependency change cannot loosen it unnoticed; and the Lean cost-model checks
run on the ForShor dependency bump (`update-forshor.yml`).

The template passes preflight. The full verifier rejects it, because it handles
no benchmark targets yet.

## Writing a Submission

Replace `implementation` in `TableGeneration/Submission/Policy.lean`. That is
the only file you need to edit, and the only one the changed-file check admits.
Helper files may be added at any depth under
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

The verifier rejects a changed protected file, and rejects these in submitted
code. This list is the one copy; `AGENTS.md` points here.

- `sorry`, `sorryAx`, `admit`;
- a new `axiom` or `constant` declaration;
- `unsafe`;
- compile-time execution and elaborator extension: `#eval`, `run_cmd`,
  `run_meta`, `run_elab`, `initialize`, `macro`, `macro_rules`, `elab`,
  `elab_rules`, `syntax`, `notation`, and the fixity commands;
- external implementation hooks: `extern`, `implemented_by`, `csimp`;
- non-kernel computation: `native_decide`, and `decide +native`;
- unbounded elaboration: `set_option maxHeartbeats 0`, or a ceiling of 10^10 or
  more.

The list above is a blocklist over the file's text. A submission must also pass
`scripts/ci/submission_syntax_gate.lean`, which parses it and judges the parse
tree instead: every top-level command must be one of an allowed set, so
`attribute` and anything not on that list are refused by kind rather than by
spelling, and `set_option` ceilings bind at command, term and tactic position
-- which is what stops `debug.skipKernelTC`, a setting the `#print axioms`
audit cannot see.

The accepted axiom set is `propext` alone, and a submitted file may import only
the contract modules and other accepted policies.

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
the benchmark index, and an archived source snapshot on the
`submission-results` branch. Workflow artifacts and diagnostic logs are kept for
90 days. A successful submission PR is closed automatically only after its
results and source have been archived.

## Two scores, not one

A submission is measured two ways and they do not agree: the per-target weighted
cost, which decides champions, and the recursive planner's logical gate count at
an operand width. A table can lose its target and still lower the gate count.
[BENCHMARK.md](BENCHMARK.md) describes both and why they disagree;
`AGENTS.md` says what to do about it if you are optimizing for gates.

## Results

`leaderboard/best-known.md` on `main` is the per-target champion table, written
by promotion. The per-policy results and source archives live on the
`submission-results` branch.

There is no leaderboard website. The tag `site-final` is the last commit that
carried one.

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

The submission contract. Every file here is unchangeable by a submission --
the changed-file rule admits only `Submission/Policy.lean` and `Submission/
Policy/**` -- and every file but the library roots is Mathlib-free. Most are
also in `verifier.py`'s `PROTECTED_FILES`; `ContractSoundness.lean` is not, and
is unchangeable by the changed-file rule alone.

- `TableGeneration/Basic.lean` defines symbolic registers, states, points, and
  primitive operations.
- `TableGeneration/Language.lean` defines programs, execution, row matching,
  ordered point consumption, and pretty printers.
- `TableGeneration/Spec.lean` defines protected product modes, default point
  lists, and validity checks for generated points.
- `TableGeneration/Metrics.lean` defines operation and layer counts.
- `TableGeneration/Policy.lean` defines the portable policy interface.
- `TableGeneration/Baseline.lean` defines the protected general fallback.
- `TableGeneration/ContractSoundness.lean` proves that the Bool-valued contract a
  submitter discharges by `decide` says what the companion's Prop-valued
  obligations say.
- `TableGeneration.lean` and `TableGeneration/Submission.lean` are the library
  roots. `TableGeneration.lean` imports `RecursiveCost.Correctness`, so it is
  the one file here that reaches Mathlib; `check_mathlib_confinement.py` carves
  out exactly that exception.

`TableGeneration/Submission/Policy.lean` is the submitted policy and the one file
a submission changes. It is not protected; `Defs.lean` and `Correctness.lean`
beside it are.

Everything downstream of acceptance:

- `TableGeneration/Policies/Accepted/` holds every accepted policy, installed
  verbatim at promotion under its own namespace.
- `TableGeneration/BestKnown.lean` selects promoted policies before the general
  fallback. It is generated by `scripts/promote.py`.
- `TableGeneration/RecursiveCost/` holds the recursive gate-count model and the
  policy planner, with the planner's candidate catalogue in
  `ArchivedCatalog.lean`, also generated by `scripts/promote.py`. It is the only
  part of the tree that depends on Mathlib and on the `Fast_multiplication`
  companion.

Benchmark and tooling:

- `leaderboard/config.json` defines the active targets and score weights.
- `scripts/verifier.py` is the CI verifier.
- `scripts/leaderboard.py` builds the benchmark index from successful verifier
  artifacts. That index is `scripts/promote.py`'s only input.
- `scripts/promote.py` constructs and re-checks the composed best-known
  generator and the planner catalogue from the archive.
- `scripts/ci/` holds what the workflows call: the Lean installer, the promotion
  push gate, the benchmark-config export and the PR report.
- `scripts/tests/` holds the Lean oracle the cost-model checks drive, the
  champion gate-count differential, and the pinned companion cost-model
  transcript.

## Further Reading

- [BENCHMARK.md](BENCHMARK.md) for targets, weights, and metric definitions.
- [RECURSIVE_COST_MODEL.md](RECURSIVE_COST_MODEL.md) for the gate-count model.
- [AGENTS.md](AGENTS.md) for the code boundaries automated contributors must
  respect.
