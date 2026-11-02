# AAAI Rebuttal

Updated: 2026-10-31

## wFZw (Score 3) — Response: Corrected Statistics and Controlled Efficiency Comparisons

Q1. Thank you for identifying these inconsistencies. They arose from aggregation and transcription errors, not different runs. Corrections are bold.

Table 3:

|Model/effort/harness|W/140|F/T|SR (%)|
|---|---|---|---|
|GPT-5.4/xhigh/Codex|**53**/140|48/**39**|**37.9**|
|GLM-5.2/thinking/Claude Code|30/140|**77/33**|21.4|

Table 4:

|Model/effort/harness|F/T|Proof/VCG|
|---|---|---|
|GLM-5.2/thinking/Claude Code|**77/33**|73/4|
|Total|**841**/230|**744**/97|

37.9% matches Fig. 2(c) at 90 min. Other data, core contributions and conclusions remain unchanged.

Q2. Thank you for this suggestion. We compared jointly solved tasks using the same Codex harness and matching reasoning effort. GPT-5.5's reductions relative to GPT-5.4 are:

|Effort|Input tokens|Output tokens|Tool calls|
|---|---|---|---|
|medium|66.1%|53.6%|33.3%|
|xhigh|62.8%|57.0%|32.4%|

These gains remain substantial compared with the original, unmatched results. Full completion costs are unobserved for timeouts; including all 140 attempts with runtimes capped at 90 min gives:

|Effort|5.4 total min/success|5.5|Reduction|
|---|---|---|---|
|medium|165.8|105.0|36.7%|
|xhigh|153.4|95.1|38.0%|

Q3. We evaluate models and harnesses as integrated systems, using official integrations when available and Claude Code otherwise (GLM-5.2 and DeepSeek-V4-Pro). On previously solved GLM-5.2 tasks, RQ5 finds Claude Code retains more successes than Codex and OpenCode, supporting our harness choice.

## Cmct (Score 5) — Response: Long-Horizon Verification, Reusable Evaluation and Benchmark Novelty

Thank you for your questions.

Q1. We apologize for the ambiguity: "long-horizon" means sustained agent interaction, not repository evolution. Agents revise annotations/proofs via VCG/Rocq feedback, reading, writing and executing repository files. Even with code and contracts supplied, GPT-5.5 xhigh/Codex primary successes average 42.8 min, 55.8 turns, 119.7 tool calls (3.01 VCG/12.60 Rocq checks) and 9.1M/34.7K input/output tokens.

Q2. Yes. Others can reuse end-to-end evaluation without human adjudication. An LLM uses task descriptions, C code and Rocq definitions to judge contracts under a fixed rubric. It screens for restrictive preconds and weak postconds; final acceptance requires machine-checked proofs and deterministic auditing. We will release the rubric, prompt, model and config.

Q3. We agree that AlgoVeri is closely related and rigorous and will discuss it more precisely. In AlgoVeri, Dafny/Verus lack a separate ITP stage and use higher-level memory models than our C memory reasoning; Lean lacks C annotation-to-VC translation and raw-memory operations. CAV-Bench targets annotation–proof coupling within C verification workflow. We fix C code/contracts while varying annotations: inadequate annotations can yield unprovable VCs discovered during Rocq proof construction, prompting annotation repair and VC regeneration.

"GT Verified" means every task has a complete machine-checked reference. AlgoVeri reports expert curation and selected specification checks.

## knrA (Score 6) — Response: Evaluation Criteria, Annotation–Proof Interaction and Access Policy

Thank you for recognizing our verified corpus's value.

Q1. Corrected counts preserve conclusions; matched-task and all-attempt efficiency gains hold (please see wFZw Q1–Q2).

Q2. Contracts are judged automatically without human adjudication. GPT-5.5 xhigh receives the task description, C code, contract and Rocq definitions. All eight checks must pass: legal inputs, C safety, results, code consistency, input/output relations, memory effects, branches and full behavior. The rubric targets overly restrictive preconditions and weak postconditions. In a few manually inspected examples, it identified inadequate contracts better than a single binary judgment. We will release the rubric, prompt and judge configuration. Proofs require VCG, Rocq checks and deterministic auditing.

Q3. High costs (please see CWud Q1) limited each task/configuration to one trajectory; repeat-run variance was not measured.

Q4. The three settings need not follow a strict difficulty order: annotations affect VC difficulty. In p050 (decode_shift), one of eight reversals, generated invariants retain nonzero input/output-character facts for use at return; reference invariants require deriving them.

Q5. Instructions prohibit reference answers, prior results and other task workspaces. Current-task artifacts, supplied definitions, documentation and tutorial examples are allowed, including reference annotations in proof-only. This policy is stated explicitly to agents.

## CWud (Score 6) — Response: Task Scope, Harness Selection and Benchmark Construction

Thank you for recognizing our work.

Q1. Repository-level means reading, writing and executing many repository files (52K Rocq lines of specifications/dependencies; over 220K lines of permitted references). Long-horizon means iterative annotation/proof repair (please see Cmct Q1). SWE-bench evaluates repository repairs (34 lines/patch); we require formal proofs (449 lines/reference). GPT-5.5 xhigh/Codex averages $7.41/CAV success versus $1.93/SWE-Pro attempt (same setup); P3 reports $2.78/shared AlgoVeri success (effort unspecified). Costs and model limits motivate function-level tasks; transfer to evolving repositories is untested.

Q2. Main experiments evaluate integrated model–harness systems. RQ5 fixes the model and varies the harness (please see wFZw Q3).

Q3. RQ5 measures success retention on 30 previously solved GLM-5.2 tasks. Claude Code retained more successes than either alternative, supporting our choice (please see wFZw Q3). Costs limited full-benchmark and full model–harness testing; whether alternatives solve Claude Code failures remains untested.

Q4. Costs limited each task/configuration to one run; repeat-run variability is unmeasured.

Q5. Experts provided and reviewed specs, gave guidance when proofs stalled, and prohibited proof bypasses. GPT-5.5 xhigh/Codex wrote annotations and proofs. Spec writing/review took six person-months; proof construction took 30 min–20 h/task. Each task required expert consensus, regenerated VCs and Rocq acceptance.

## 6RZa (Score 6) — Response: Task Difficulty and the QCP/Rocq Verification Workflow

Thank you for recognizing our benchmark's value.

Q1. p117 (select_words) returns all words with n consonants in order, preserves input and owns allocated output strings. Its reference has 99 lemmas and 1,937 nonblank proof lines, using scan induction and recursive heap reasoning. GPT-5.4 xhigh completed 28 ITP obligations in 90 min, leaving 18 unfinished; no configuration passed the audit. The 140 references contain 5,562 VCs and 62,812 nongenerated proof lines.

Q2. GPT-5.5 xhigh/Codex successes average 3.0 VCG calls and 12.6 Rocq checks, showing repeated annotation/proof revision. Their difficulty is coupled: annotations determine VCs; proof failures guide annotation repair and VC regeneration. CBMC/ESBMC could complement QCP on suitable obligations. CBMC does not natively accept specifications expressed in separation logic and Rocq inductive definitions; translation must preserve semantics. Its standard workflow has no direct ITP handoff when automated solving fails. QCP exposes unresolved VCs to Rocq for proof construction and annotation repair.

Q3. QCP/Rocq directly supports C verification: separation logic tracks disjoint ownership; inductive predicates describe arbitrary-size heaps. Its SMT and ITP backends and explicit specification, annotation and proof stages support evaluating the full workflow and annotation–proof interaction. QCP now supports floating-point operations, but complex rounding/error proofs can exceed model capabilities within our budget.

## AI Review — Response: Reporting Corrections, Novelty and Evaluation Protocol

Thank you for your comments. The counts have been corrected, and matched-task/all-attempt analyses support the efficiency trend (please see wFZw Q1–Q2). All 140 references remain machine-checked; 744 of 841 non-timeout failures reached the proof stage.

Lemur already uses verifier feedback to generate and repair C invariants, and we will cite it. Our contribution is a verified C corpus and evaluation workflow coupling auxiliary annotations with explicit Rocq proof construction: annotations shape VCs, and proof feedback guides annotation repair and VC regeneration (please see Cmct Q3).

In p050, generated invariants retain nonzero-character facts needed at return, whereas reference invariants require deriving them. This illustrates how annotations change proof obligations. The example and single-run design are discussed in knrA Q3–Q4; repeat-run variability remains unmeasured.

Contract adequacy is assessed automatically under a fixed LLM rubric; proof acceptance is checked separately. Please see knrA Q2 for the rubric and limited manual inspection, and Q5 for access rules. Audited success requires both accepted proofs and protocol compliance.

CWud Q1/Q5 explain repository interaction, costs and reference construction; 6RZa Q1/Q3 describe p117 and QCP's SMT/ITP workflow. We will clarify task inputs and acceptance paths, show the omitted i declaration and rename "Manual Rocq proof LOC" to "nongenerated Rocq proof LOC".

## Letter to the Area Chair

Dear Area Chair,

Thank you for coordinating the reviews. We would appreciate a reassessment of wFZw's score of 3 in light of the corrected results and additional analyses.

The discrepancies arose from aggregation and transcription errors. We appreciate the reviewer's careful checks. Crucially, all 140 machine-checked references remain valid, and the benchmark's core contributions are unaffected. The findings of substantial verification headroom and predominantly proof-stage failures remain unchanged.

For RQ2, we compared jointly solved tasks using the same Codex harness and matching reasoning effort. These controlled comparisons confirm substantial token and tool reductions. Amortized time per success also decreases when all 140 attempts, including timeouts, are counted with each run capped at 90 minutes.

We appreciate that wFZw recognizes the motivation, clear task design and verification artifacts. We note that knrA raises related concerns about counts and efficiency, while also recognizing the verified corpus and fixed-contract task and recommending acceptance. We hope these clarifications provide useful context for the final assessment.

Given that the central findings and verified corpus remain intact, we respectfully ask the AC to weigh the remaining concerns against the benchmark's core contributions when reconsidering the clear-rejection recommendation.

Thank you for your consideration.
