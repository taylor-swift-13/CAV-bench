# CAV-Bench

A benchmark for code agents performing multi-stage C program verification with QCP and Rocq.

CAV-Bench combines executable C programs, functional contracts, auxiliary annotations, and reference proofs. Its paper evaluates agents that inspect repository code, revise annotations, generate verification conditions (VCs), and construct Rocq proofs. Acceptance combines verifier replay with checks on source integrity, proof artifacts, and permitted access.

## Paper and resources

- [Main paper](paper/main.pdf) · [Supplementary material](paper/appendix.pdf) · [Reproducibility checklist](paper/ReproducibilityChecklist.pdf)
- [Paper sources and build instructions](paper/README.md)
- [Author response](paper/rebuttal.md), including clearly marked AI-review and AC-letter drafts
- [Reference artifacts](ground_truth/) · [Reference layout](ground_truth/README.md)
- [Execution documentation](doc/run.md) · [Audit policy](doc/check_cheating.md)

The paper's consolidated corpus contains **140 tasks**, **5,562 generated VCs**, and **62,812 lines of nongenerated Rocq proof**. Under the audited 90-minute primary-task budget, GPT-5.5 xhigh with Codex succeeds on **78/140 tasks (55.7%)**. The frozen paper statistics specify the selected runs; historical files elsewhere in the repository are not a substitute for that selection.

## Task settings

| Setting | Supplied artifacts | Agent constructs | Runner |
| --- | --- | --- | --- |
| Primary: contract-to-proof | C implementation, fixed contract, required definitions | Auxiliary annotations and Rocq proofs | `scripts/run_verify.py` |
| End-to-end | Task description and C implementation | Contract, annotations, and proofs | `scripts/run_pipeline.py` |
| Proof-only | Implementation, contract, and reference annotations | Rocq proofs | `scripts/run_proof.py` |

The primary and proof-only settings keep their supplied inputs fixed. End-to-end contract adequacy is assessed separately from downstream verification. A model's completion message alone does not establish success.

## Project structure

```text
CAV-bench/
├── raw/                       # Natural-language task inputs
├── input/                     # C programs, contracts, and Rocq definitions
├── annotated_input/           # Pre-annotated inputs for proof-only tasks
├── ground_truth/              # Reference annotations and proof artifacts
├── QualifiedCProgramming/     # QCP upstream submodule
├── scripts/                   # Runners, metrics, and audit tools
├── skills/                    # Agent workflow instructions
├── config/                    # Agent configuration
├── doc/                       # Execution and auditing documentation
├── results/                   # Recorded primary-task experiment artifacts
└── paper/                     # TeX, PDFs, figures, audited statistics, rebuttal
```

Individual experiment branches contain different task cohorts and historical artifacts. The paper consolidates its audited cohort across `main`, `2.0.3`, and `2.0.4`.

## Requirements and setup

- Linux or WSL and Python 3.
- QCP's C/symbolic-execution toolchain and Rocq/Coq. The local experiments used Coq 8.20.1; follow the upstream build instructions for its dependencies.
- A supported agent CLI and provider access. The current runners support Codex, Claude Code, OpenCode, and Kimi Code; consult each branch's `--help` for available options.
- A LaTeX installation with BibTeX to rebuild the paper PDFs.

```bash
git clone --recurse-submodules https://github.com/taylor-swift-13/CAV-bench.git
cd CAV-bench
git submodule update --init --recursive
```

Build the dependency according to the [QCP instructions](QualifiedCProgramming/README.md). Agent configuration is handled by `scripts/agent_config.py`; runner options accept `--config`. Keep provider credentials in your local environment or local configuration rather than committing them.

## Running a task

Inspect the CLI options first:

```bash
python3 scripts/run_verify.py --help
python3 scripts/run_proof.py --help
python3 scripts/run_pipeline.py --help
```

Primary task:

```bash
python3 scripts/run_verify.py input/humaneval/p052_below_threshold.c \
  --function-name p052_below_threshold --timeout-seconds 5400
```

Proof-only task:

```bash
python3 scripts/run_proof.py input/humaneval/p052_below_threshold.c \
  --function-name p052_below_threshold \
  --annotated-input-c annotated_input/humaneval/p052_below_threshold.c \
  --timeout-seconds 5400
```

End-to-end task:

```bash
python3 scripts/run_pipeline.py raw/humaneval/p052_below_threshold.md \
  --function-name p052_below_threshold
```

Configure your model, agent CLI, and API access before running these commands. Use runner-specific options to reproduce the configuration and phase budgets of an experiment; the examples above are entry points, not a complete reproduction of every published configuration.

## Outputs and auditing

Runners create task workspaces containing staged inputs, annotated C, generated goals, automatic and manual proof files, and logs. `metrics.md` records status and resource use. Audited results additionally check the replayed verifier outcome and compliance with the task's access and editing rules.

For the paper, success requires an audited completion within **5,400 seconds**. Table 3 reports successful-run means and non-timeout means, the latter including failures. Frozen outcome and cost snapshots are provided under [`paper/figures/`](paper/figures/); see [`paper/README.md`](paper/README.md) before regenerating them.

## Related resources

- [QCP](https://github.com/QinxiangCao/QualifiedCProgramming): separation-logic C verification with automated solving and Rocq proof construction.
- [Coins](https://github.com/taylor-swift-13/Coins): Rocq specifications and specification-evaluation research used as a source in the benchmark construction. The paper details the adaptation of contracts and required memory/safety conditions.

See [`paper/references.bib`](paper/references.bib) for the cited works and upstream resource attribution. Third-party components retain their upstream licensing.
