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
sequential phase-product layer. Where the layer counts differ within a target,
it decides the champion. The archive holds one such case at `PhaseProduct`
`k=3`: a four-layer table with 9 arithmetic operations scores
`9 + 5*4 = 29` and loses to the two-layer champion's `11 + 5*2 = 21`, although
it uses fewer operations. Ranked on operations alone it would have won.

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

## Two scores, not one

A submission is measured two different ways, and they do not agree. This section
is the one description of that; `README.md` and `AGENTS.md` point here.

**Per-target score.** The weighted cost above. It is width-independent, which is
the point: it scores a table on its own, without reference to any operand size or
to any other submission. It decides champions and promotion, and it is what
`leaderboard/best-known.md` reports.

**Gate count.** The recursive planner's ForShor-compatible logical gate total at
one operand width, with 2048 bits as the headline. See
[RECURSIVE_COST_MODEL.md](RECURSIVE_COST_MODEL.md).

The two disagree because an operation count cannot see how far a program
**contracts** its operands, and the child width a table reaches governs the whole
subtree below it. A table can therefore lose its target and still lower the gate
count. The planner searches the accepted archive rather than the champions, so it
will find such a table -- provided the table is in the planner's catalogue, which
excludes one deeper than the champion at its arity.

If you are optimizing for gates, optimize for gates. `AGENTS.md` says how.

## Recursive Planning

The recursive planner provides a separate, width-dependent estimate for
multiplication. Given any positive integer bit length `n`, it selects a verified
`PhaseProduct` policy and `k` at each recursion level to minimize the
ForShor-compatible logical gate count, and reports the gate total, the recursion
height, the recursive-call and arithmetic-operation totals, and the policy, `k`
and child width chosen at the top level.

This estimate is not the leaderboard's per-target weighted score. Its scope and
validation are documented in [RECURSIVE_COST_MODEL.md](RECURSIVE_COST_MODEL.md).

## Published Results

The current per-target champions are in `leaderboard/best-known.md` on `main`.

For each successful submission, CI publishes five files. The first four go to
`results/policies/<policy commit>/`:

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
- `leaderboard/results.json`: the policy registry and current per-target
  champions. It is `scripts/promote.py`'s only input.

Those five paths are the whole of what the report job writes, and it writes them
to the `submission-results` branch; the PR comment links them.
`leaderboard/best-known.md` is not among them: promotion writes that file to
`main`, not the report. Each successful policy commit has one archive directory,
named by that commit; a rerun updates it rather than duplicating the source. Full
verifier output and diagnostic logs remain available as workflow artifacts for
90 days.

Champion policies are composed with the general fallback and committed to
`main` by trusted automation. Promotion rebuilds the policies, audits their
proof dependencies and target-specific correctness theorems, and requires the
published metrics to match before anything is pushed. The push is restricted to
the files promotion generates, so a promotion that changed anything else fails
instead of landing.
