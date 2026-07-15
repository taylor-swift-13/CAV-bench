# Status: unverified

The current non-vacuous float-array specification has not been verified.

- Older runs either stopped on parser-incompatible system includes or generated an empty `VC_Correct` after using a contract-free source; those are not proofs of the current specification.
- The current program still requires supported float absolute-value semantics plus loop invariants for the two array scans and accumulated floating-point sums.
- No aligned generated goals and manual proof establish `problem_4_spec_fp32`.

Evidence: `results/kimicode/kimi-code__kimi-for-coding/thinking/verify_20260713_11395219594_p004_mean_absolute_deviation/logs/issues.md`.
