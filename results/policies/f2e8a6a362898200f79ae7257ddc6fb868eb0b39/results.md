<!-- table-generation-submission-result -->
### Table generation benchmark

Status: **SUCCESS**

Submission: PR #21 · commit `f2e8a6a36289`

Scoring: `weighted_cost = 1 * arithmetic_operation_count + 5 * parallel_phase_product_layer_count`.

Coverage: **1 of 30** targets.

| Target | Weighted cost | Arithmetic ops | Parallel layers | Phase products | Total ops | Generated points |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `PhaseTripleProduct` `k=3` | **34** | 19 | 3 | 7 | 26 | 7 |

All correctness and safety checks passed.
