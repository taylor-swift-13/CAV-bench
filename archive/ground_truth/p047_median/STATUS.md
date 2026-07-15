# Status: unverified

The current meaningful median contract has not been proved.

- The recorded Kimi `Success` used a 114-byte bare `.v`, no function contract, and an empty `VC_Correct`; it is vacuous and does not match the aligned input specification.
- With the real contract, QCP needs a sound `qsort` specification and in-place permutation/sortedness reasoning; diagnostic runs next fail on array-memory reads.
- No accepted artifacts establish `problem_47_spec_fp32`.

Evidence: `results/codex/gpt-5.4/low/verify_20260713_05361130489_p047_median/logs/issues.md` and `results/kimicode/kimi-code__kimi-for-coding/thinking/verify_20260713_13300132577_p047_median/coq/generated/p047_median_goal.v`.
