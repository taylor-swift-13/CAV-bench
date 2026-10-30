# AAAI Rebuttal

Updated: 2026-10-31

## wFZw (Score 3)

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

The 37.9% matches Fig. 2(c) at 90 min. Other data, core contributions and conclusions remain unchanged.

Q2. Thank you for this suggestion. We compared jointly solved tasks using the same Codex harness and matching reasoning effort. GPT-5.5's reductions relative to GPT-5.4 are:

|Effort|Input tokens|Output tokens|Tool calls|
|---|---|---|---|
|medium|66.1%|53.6%|33.3%|
|xhigh|62.8%|57.0%|32.4%|

These gains exceed the original comparison over each model's own successes. Full completion costs are unobserved for timeouts; including all 140 attempts with runtimes capped at 90 min gives:

|Effort|5.4 total min/success|5.5|Reduction|
|---|---|---|---|
|medium|165.8|105.0|36.7%|
|xhigh|153.4|95.1|38.0%|

Q3. We evaluate models and harnesses as integrated systems, using official integrations when available and Claude Code otherwise (GLM-5.2 and DeepSeek-V4-Pro). On previously solved GLM-5.2 tasks, RQ5 finds Claude Code retains more successes than Codex and OpenCode, supporting our harness choice.

## Cmct (Score 5)

Thank you for your questions.

Q1. We apologize for the ambiguity: "long-horizon" means sustained agent interaction, not repository evolution. Agents revise annotations/proofs via VCG/Rocq feedback, reading, writing and executing repository files. Even with code and contracts supplied, GPT-5.5 xhigh/Codex primary successes average 42.8 min, 55.8 turns, 119.7 tool calls (3.01 VCG/12.60 Rocq checks) and 9.1M/34.7K input/output tokens.

Q2. Yes. Others can reuse end-to-end evaluation without human adjudication. An LLM judge checks whether contracts capture intended behavior and screens for overly restrictive preconditions and weak postconditions. Acceptance requires VCG, Rocq checks and auditing, which the judge cannot bypass. We will release the rubric, prompt, model and configuration.

Q3. We agree that AlgoVeri is closely related and rigorous and will discuss it more precisely. In AlgoVeri, Dafny/Verus lack a separate ITP stage and use higher-level memory models than our C memory reasoning; Lean lacks C annotation-to-VC translation and raw-memory operations. CAV-Bench targets annotation–proof coupling within C verification workflow. We fix C code/contracts while varying annotations: inadequate annotations can yield unprovable VCs discovered during Rocq proof construction, prompting annotation repair and VC regeneration.

"GT Verified" means every task has a complete machine-checked reference. AlgoVeri reports expert curation and selected specification checks.

## knrA (Score 6)

Thank you for recognizing our verified corpus's value.

Q1. Corrected counts preserve conclusions; matched-task and all-attempt efficiency gains hold (please see wFZw Q1–Q2).

Q2. Contracts are judged automatically without human adjudication. GPT-5.5 xhigh receives the task description, C code, contract and Rocq definitions. All eight checks must pass: legal inputs, C safety, results, code consistency, input/output relations, memory effects, branches and full behavior. The rubric targets overly restrictive preconditions and weak postconditions. In a few manually inspected examples, it identified inadequate contracts better than a single binary judgment. We will release the rubric, prompt and judge configuration. Proofs require VCG, Rocq checks and deterministic auditing.

Q3. High costs (please see CWud Q1) limited each task/configuration to one trajectory; repeat-run variance was not measured.

Q4. The three settings need not follow a strict difficulty order: annotations affect VC difficulty. In p050 (decode_shift), one of eight reversals, generated invariants retain nonzero input/output-character facts for use at return; reference invariants require deriving them.

Q5. Instructions prohibit reference answers, prior results and other task workspaces. Current-task artifacts, supplied definitions, documentation and listed examples are allowed, including reference annotations in proof-only. This policy is stated explicitly to agents.

## CWud (Score 6)

Thank you for recognizing our work.

Q1. Repository-level means reading, writing and executing many repository files (52K Rocq lines of specifications/dependencies; over 220K lines of permitted reference code). Long-horizon means iterative annotation/proof repair (please see Cmct Q1). SWE-bench evaluates repository repairs (34 lines/patch); we require formal proofs (449 lines/reference). GPT-5.5 xhigh/Codex averages $7.41/CAV success versus $1.93/SWE-Pro attempt (same setup); P3 reports $2.78/shared AlgoVeri success (effort unspecified). Costs and model limits motivate function-level tasks; transfer to evolving repositories is untested.

Q2. Main experiments evaluate integrated model–harness systems. RQ5 fixes the model and varies the harness (please see wFZw Q3).

Q3. RQ5 measures success retention on 30 previously solved GLM-5.2 tasks. Claude Code retained more successes than either alternative, supporting our choice (please see wFZw Q3). Costs limited full-benchmark and full model–harness testing; whether alternatives solve Claude Code failures remains untested.

Q4. Costs limited each task/configuration to one run; repeat-run variability is unmeasured.

Q5. Experts provided reviewed specs, gave guidance when proofs stalled, and prohibited proof bypasses. GPT-5.5 xhigh/Codex wrote annotations and proofs. Spec writing/review took six person-months; proof construction took 30 min–20 h/task. Each task required expert consensus, regenerated VCs and Rocq acceptance.

## 6RZa (Score 6)

Thank you for recognizing our benchmark's value.

Q1. p117 (select_words) returns all words with n consonants in order, preserves input and owns allocated output strings. Its reference has 99 lemmas and 1,937 nonblank proof lines, using scan induction and recursive heap reasoning. GPT-5.4 xhigh completed 28 ITP obligations in 90 min, leaving 18 unfinished; no configuration passed the audit. The 140 references contain 5,562 VCs and 62,812 nongenerated proof lines.

Q2. GPT-5.5 xhigh/Codex successes average 3.0 VCG calls and 12.6 Rocq checks, showing repeated annotation/proof revision. Their difficulty is coupled: annotations determine VCs; proof failures guide annotation repair and VC regeneration. CBMC/ESBMC could complement QCP on suitable obligations. CBMC does not natively accept specifications expressed in separation logic and Rocq inductive definitions; translation must preserve semantics. Its standard workflow has no direct ITP handoff when automated solving fails. QCP exposes unresolved VCs to Rocq for proof construction and annotation repair.

Q3. QCP/Rocq directly supports C verification: separation logic tracks disjoint ownership; inductive predicates describe arbitrary-size heaps. Its SMT and ITP backends and explicit specification, annotation and proof stages support evaluating the full workflow and annotation–proof interaction. Full floating-point proofs add rounding/error challenges; we found no suitable alternative combining both.

## AI Review

Thank you. wFZw Q1–Q2 detail reporting corrections and controlled RQ2 analyses. All 140 references are machine-checked. The corrected 744/841 proof-stage failures support the reported verification bottleneck.

Lemur uses verifier feedback to generate and repair C invariants. We will cite it. CAV-Bench covers broader auxiliary annotations coupled with explicit Rocq proofs: annotations determine VCs, while ITP feedback guides annotation repair and VC regeneration. Our contribution is this verified corpus and coupled evaluation workflow.

In p050, generated invariants retain character-nonzero facts for the return proof, whereas the reference invariant requires deriving them. knrA Q3–Q4 discuss this example, the complementary task settings and the cost-constrained single-trajectory design.

End-to-end contract assessment is automated with a fixed LLM rubric; proof acceptance separately requires VCG and Rocq checks. Methods can reuse the judge protocol. The rubric screens for vacuous or weak contracts. Audited success combines proof acceptance with compliance with the stated access and input-preservation rules.

CWud Q1 and Q5 detail repository interaction, construction effort and costs; 6RZa Q1–Q3 explain p117 and the combined SMT and ITP workflow. We will clarify task inputs, generated artifacts and acceptance paths, show the omitted i declaration, and label proof size as "nongenerated Rocq proof LOC."

## Letter to the Area Chair

Dear Area Chair,


Thank you for coordinating the reviews. We respectfully ask that wFZw’s score of 3 be reconsidered in light of the corrected results and additional analyses in our response.

The discrepancies arose from aggregation and transcription errors. We appreciate the reviewer’s careful checks. All 140 machine-checked references remain valid, and the central findings of substantial verification headroom and predominantly proof-stage failures remain unchanged.

To address the RQ2 concerns, we compared results while controlling task composition, harness and reasoning effort. Token and tool savings are larger on matched tasks, and budgeted time per success decreases when all attempts, including timeouts, are counted.

We appreciate that wFZw recognizes the motivation, clear task design and verification artifacts. knrA raises related concerns about counts and efficiency while recommending acceptance and recognizing the verified corpus and fixed-contract task. Given these shared concerns, we hope the corrected results and additional analyses can help reconcile the differing overall assessments.

We respectfully ask the AC to weigh the corrected evidence and additional analyses alongside the verified corpus, task design and evaluation methodology, and consider whether the remaining concerns warrant a clear-rejection recommendation. Thank you for your consideration.
