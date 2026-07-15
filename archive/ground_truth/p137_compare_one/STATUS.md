# Status: unverified — contract/program mismatch

The current specification and executable program disagree semantically.

- The spec interprets decimal strings as exact mathematical reals.
- The C program converts strings using `atof` and compares rounded binary64 values.
- For example, string `"0.1"` and double `0.1` denote unequal exact reals in the spec but compare equal after C binary64 conversion, so the program returns the `None` branch contrary to the contract.
- Fixing this requires a contract or program decision, not another proof tactic.

Evidence: `results/codex/gpt-5.4/medium/verify_20260714_2241381090_p137_compare_one/logs/issues.md`.
