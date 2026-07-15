# Status: unverified

The current non-vacuous contract has not passed QCP verification.

- `symexec` first rejects the program's `abs` use on `float` as undeclared.
- Replacing that expression diagnostically allowed execution to reach the nested loop, but QCP then could not derive the first `FloatArray` memory-read precondition.
- A sound loop invariant must preserve the float-array resource and express that no close pair exists only in the already-scanned region. No accepted VC/proof set currently does this.

Evidence: `results/codex/gpt-5.4/low/verify_20260714_2040549868_p000_has_close_elements/logs/issues.md`.
