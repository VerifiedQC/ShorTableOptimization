# Table Generation Benchmark

The benchmark is provisional. Its targets and weights can be changed in
`leaderboard/config.json` as the challenge evolves.

## Current Configuration

The current benchmark evaluates both `PhaseProduct` and `PhaseTripleProduct` for
every `k` from 2 through 16, giving 30 independent targets. A submission may
handle any nonempty subset of those targets.

Each handled target receives its own weighted cost:

```text
weighted_cost = arithmetic_operation_count + 5 * parallel_phase_product_layer_count
```

The weight of 5 is a convention, not a derived constant. It sets an exchange
rate between circuit size and depth: five arithmetic operations for one
sequential phase-product layer. It has never changed a champion selection,
because every accepted table at a given arity has the same layer count, so the
term is a constant offset within a target and this ranking is currently
identical to ranking by `arithmetic_operation_count`.

This score is width-independent, which is its purpose: it judges a table on its
own, without reference to an operand size or to any other submission. It is
**not** the gate count. The two disagree, because an operation count cannot see
how far a program contracts its operands. See
[RECURSIVE_COST_MODEL.md](RECURSIVE_COST_MODEL.md) for the gate model and
`AGENTS.md` for which score to optimize.

There is no combined score: coverage and the vector of per-target costs describe
a policy. The benchmark records the champion or tied champions for each
`(mode, k)` target, so different policies may be optimal in different cells.

The report also includes the unweighted measurements used to understand a
submission:

| Metric | Meaning |
| --- | --- |
| Arithmetic operations | Program operations other than phase products. |
| Parallel phase-product layers | Consecutive phase-product runs separated by arithmetic operations. |
| Phase products | Phase-product operations in the program. |
| Total operations | All operations in the program. |
| Generated points | Points produced for the target. |

## Recursive Planning

The website also provides a separate, width-dependent estimate for recursive
multiplication. Given any positive integer bit length `n`, it automatically
selects a verified `PhaseProduct` policy and `k` at each recursion level to
minimize the ForShor-compatible logical gate count. It reports the selected
levels, gate contributions, recursive calls, and symbolic arithmetic operations,
with the exact archived policy operations available on demand.

This estimate is not the leaderboard's per-target weighted score. Its scope and
validation are documented in [RECURSIVE_COST_MODEL.md](RECURSIVE_COST_MODEL.md).

## Published Results

The current per-target champions are displayed on the
[leaderboard website](https://verifiedqc.github.io/ShorTableOptimization/).

For each successful submission, CI publishes:

- `results.json`: a compact record of the submission identity, benchmark weights,
  coverage, raw measurements, and per-target weighted costs.
- `results.md`: a short report containing the formula and a readable results
  table.
- `operations.json`: generated points, consumption order, and the complete
  operation sequence for every handled target. Operations use compact arrays of
  the form `[name, ...arguments]`; the file includes the argument names for each
  operation kind.
- `source.zip`: the portable policy Lean source, retained so it can be inspected
  or reprocessed later.
- `leaderboard/results.json`: the website-oriented policy registry and current
  per-target champions.
- `leaderboard/best-known.md`: the readable metric table generated with the
  promoted best-known policy.

The files are stored on the `submission-results` branch and linked from the PR
comment. Each successful policy commit has one archive directory; reruns update
it rather than duplicating the source. Full verifier output and diagnostic logs
remain available as workflow artifacts for 90 days.

Champion policies are composed with the general fallback and promoted through a
verified `automation/best-known` branch. Promotion rebuilds the policies, audits
their proof dependencies and target-specific correctness theorems, and requires
the published metrics to match before that branch is updated. A maintainer
reviews and merges it into `main`.
