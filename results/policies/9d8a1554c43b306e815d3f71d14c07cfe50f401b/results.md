<!-- table-generation-submission-result -->
### Table generation benchmark

Status: **SUCCESS**

Submission: PR #47 · commit `9d8a1554c43b`

Scoring: `weighted_cost = 1 * arithmetic_operation_count + 5 * parallel_phase_product_layer_count`.

Coverage: **1 of 30** targets.

| Target | Weighted cost | Arithmetic ops | Parallel layers | Phase products | Total ops | Generated points |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `PhaseProduct` `k=3` | **25** | 15 | 2 | 5 | 20 | 5 |

All correctness and safety checks passed.
