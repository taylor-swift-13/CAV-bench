# Status: unverified

The aligned non-vacuous case stops during float-array symbolic execution.

- QCP cannot derive the memory-read/write precondition at `even[i] = l[i * 2]`.
- The current `FloatArray` support lacks the strategy coverage needed by the copy, sort, and merge loops.
- Older apparent successes used a parser wrapper and an empty contract, so they do not prove `problem_37_spec_fp32`.

Evidence: `results/codex/gpt-5.4/low/verify_20260714_21024414775_p037_sort_even/logs/issues.md`.
