<!-- table-generation-submission-result -->
### Table generation benchmark

Status: **SUCCESS**

Submission: PR #41 · commit `5e83e2c00c17`

Scoring: `weighted_cost = 1 * arithmetic_operation_count + 5 * parallel_phase_product_layer_count`.

Coverage: **1 of 30** targets.

| Target | Weighted cost | Arithmetic ops | Parallel layers | Phase products | Total ops | Generated points |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `PhaseProduct` `k=3` | **24** | 14 | 2 | 5 | 19 | 5 |

All correctness and safety checks passed.
