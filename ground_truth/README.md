# QCP 2.0.4 HumanEval ground truth

Each problem directory is a replayable ground-truth object.  A directory is
accepted only when its `verify_ground_truth.log` records successful symbolic
execution followed by `[OK]` for support, goal, proof_auto, proof_manual, and
goal_check under Coq 8.20.1.

Accepted cases (7):

- `p053_add`
- `p059_largest_prime_factor`
- `p060_sum_to_n`
- `p075_is_multiply_prime`
- `p077_iscuber`
- `p083_starts_one_ends`
- `p097_multiply`

Replay all accepted cases from the repository root with:

```bash
python3 scripts/legacy/verify_ground_truth_humaneval.py --timeout 180
```

Ground-truth directories must not contain `.vo`, `.vos`, `.vok`, `.glob`, or
`.aux` compilation products.
