# AAAI Rebuttal

Updated: 2026-10-30

## wFZw (Score 3)

Thank you for checking our statistics and RQ2.

Q1 (statistics). The discrepancies arose from aggregation and transcription errors, not different runs.

Table 3 (140 tasks each; W/F/T=success/non-timeout failure/timeout; bold=corrected):

|Model/effort/harness|W/F/T|
|---|---|
|GPT-5.5/xhigh/Codex|80/31/29|
|GPT-5.5/medium/Codex|59/61/20|
|GPT-5.4/xhigh/Codex|**53**/48/**39**|
|GPT-5.4/high/Codex|40/96/4|
|GPT-5.4/medium/Codex|20/120/0|
|GPT-5.4/low/Codex|16/124/0|
|GPT-5.4-mini/medium/Codex|8/130/2|
|GLM-5.2/thinking/Claude Code|30/**77**/**33**|
|DeepSeek-V4-Pro/thinking/Claude Code|5/55/80|
|kimi-2.7-code/thinking/Kimi Code|18/99/23|

Non-timeout failures total 841: 744 proof-stage (88.5%) and 97 VCG-stage (11.5%), matching RQ4. GPT-5.4 xhigh's 37.9% matches Fig. 2(c) at 90 min. Affected costs, plots and text will be synchronized; other data and our core contributions and conclusions remain unchanged.

Q2 (efficiency). Matching tasks controls task composition and shows larger efficiency gains. With Codex and effort fixed, GPT-5.5 uses fewer input/output tokens and tool calls than GPT-5.4 on jointly solved tasks, by 66.1%/53.6%/33.3% at medium and 62.8%/57.0%/32.4% at xhigh. Input tokens fall on 14/15 medium and 35/39 xhigh pairs. Across 140 attempts, budgeted minutes/success fall 165.8→105.0 (medium) and 153.4→95.1 (xhigh). This is total attempt time divided by successes; timeouts count as 90 min and other times are capped at 90.

## Cmct (Score 5)

Thank you for your questions. We clarify scope and novelty below.

Q1. Long-horizon means sustained interaction within fixed tasks, not evolving repositories. GPT-5.5 xhigh/Codex primary successes average 42.8 min, 55.8 turns, 119.7 tool calls (3.01 VCG/12.60 Rocq checks) and 9.1M/34.7K input/output tokens.

Q2. Yes. Other studies can reuse end-to-end evaluation without human adjudication. Primary acceptance is deterministic; proofs require VCG, Rocq kernel checks and auditing. We will release the LLM judge's rubric, prompt, model and configuration so methods assess contract adequacy under the same settings. End-to-end need not be harder or longer than primary (knrA).

Q3. AlgoVeri (arXiv:2602.09464) uses SMT in Dafny/Verus without our ITP stage; its Lean setting lacks C annotation-to-VC translation and raw-memory operations. Our settings share C memory semantics, including aliasing and ownership, and tools; primary and proof-only fix code/contracts while varying annotations. In p050, generated invariants retain nonzero-character facts needed at return; reference invariants require deriving them (knrA). Inadequate annotations can yield unprovable VCs exposed during Rocq proof construction, prompting annotation repair and VC regeneration. Cross-language changes to memory models and tools confound this interaction.

"GT Verified" means complete machine-checked references for all 140 tasks; AlgoVeri reports expert curation and selected specification checks.

## knrA (Score 6)

Thank you for recognizing our verified corpus's value.

Q1. Count corrections preserve conclusions; efficiency gains hold on matched tasks and all-attempt costs (wFZw).

Q2. Contracts are judged automatically without human adjudication. GPT-5.5 xhigh receives the task description, C code, contract and Rocq definitions. All eight checks must pass: legal inputs, C safety, results, code consistency, input/output relations, memory effects, branches and full behavior. They screen for overly restrictive preconditions and weak postconditions. Separate manual inspection found every clearly weak contract in the sample was rejected. We will release the rubric, prompt and judge configuration. Proofs require VCG, Rocq kernel checks and deterministic auditing.

Q3. High costs limited each task/configuration to one trajectory; repeat-run variance was not measured (CWud).

Q4. The three settings need not follow a strict difficulty order: annotations affect VC difficulty. In p050 (decode_shift), one of eight reversals, generated invariants retain nonzero input/output-character facts for use at return; reference invariants require deriving them. End-to-end permits easier-to-prove contracts, subject to adequacy checks.

Q5. Instructions prohibit reference answers, prior results and other task workspaces. Current-task artifacts, supplied definitions, documentation and listed examples are allowed, including reference annotations in proof-only. Transcripts are audited for compliance.

## CWud (Score 6)

Thank you for valuing our evaluation.

Q1. QCP/Rocq supports repository-level verification; model limits and costs motivate function-level tasks. Transfer to real repositories is untested. SWE-bench tests repository repairs; we require functional/memory proofs. Long-horizon means iterative annotation/proof repair: GPT-5.5 xhigh/Codex successes average 42.8 min, 119.7 tool calls, 55.8 turns and 9.1M input/34.7K output tokens. Mean API costs: CAV $7.41/success, SWE-Pro $1.93/attempt (same setup); AlgoVeri $2.78 per shared success (P3, arXiv:2608.09277; effort unspecified).

Q2. RQ1 compares model–harness pairs: official integrations when available, otherwise Claude Code for its GLM/DeepSeek integration. For RQ2, we fix Codex and effort; efficiency gains hold on matched tasks and all attempts (wFZw).

Q3. RQ5 tests success retention. We fixed 30 GLM-5.2 successes under Claude Code before testing alternatives: Codex CLI retained 23, OpenCode 13. Only the harness changes. Whether alternatives solve CC failures requires separate testing.

Q4. High costs limited each task/configuration to one trajectory; repeat-run variability is unmeasured.

Q5. GPT-5.5 xhigh/Codex wrote annotations and proofs. Experts reviewed specs and intermediate artifacts, guided semantics and barred proof bypasses. Spec writing/review took six person-months; construction took 30 min–20 h/task. Inclusion required expert consensus, regenerated VCs and Rocq acceptance. We will use vector figures.

## 6RZa (Score 6)

Thank you for recognizing our benchmark’s value.

Q1. p117 (select_words) returns exactly the words with n consonants in order, preserving input and owning allocated output strings. Its reference has 99 lemmas and 1,937 nonblank proof lines. Scan induction and recursive heap reasoning preserve ownership of earlier strings when appending a word. GPT-5.4 xhigh completed 28 ITP obligations in 90 min, leaving 18; no configuration passed the audit. The 140 references contain 5,562 VCs and 62,812 nongenerated proof lines.

Q2. CBMC can complement QCP on suitable obligations. Our p052 pilot verified its encoding for 0<=n<=64 in 0.29 s; loop-contract attempts for 0<=n<INT_MAX timed out at 180 s or hit conversion errors. CBMC's memory-predicate interface excludes mutual recursion. It does not natively accept QCP assertions or Rocq predicates; translation must preserve their semantics. Its standard workflow has no direct ITP handoff for unresolved obligations.

Q3. QCP/Rocq (arXiv:2505.12878) integrates SMT and ITP: SMT handles routine VCs; Rocq handles residual VCs through lemmas and induction over separation-logic resources. Proof feedback guides annotation repair and VC regeneration. Separation logic tracks disjoint ownership; inductive predicates describe heaps of arbitrary size. Our benchmark measures this interaction and provides machine-checked references for all tasks. Table 3 separates success, failure and timeout counts, and success-only from non-timeout means.

## AI Review

Thank you. Our response to wFZw details reporting corrections and controlled RQ2 analyses. The strongest result remains 80/140; all 140 references are machine-checked. The corrected 744/841 proof-stage failures support the reported verification bottleneck.

Lemur (arXiv:2310.04870) uses verifier feedback to generate and repair C invariants. We will cite it. CAV-Bench covers broader auxiliary annotations coupled with explicit Rocq proofs: annotations determine VCs, while ITP feedback guides annotation repair and VC regeneration. Our contribution is this verified corpus and coupled evaluation workflow.

In p050, generated invariants retain character-nonzero facts for the return proof, whereas the reference invariant requires deriving them. knrA discusses this example, the complementary task settings and the cost-constrained single-trajectory design.

End-to-end contract assessment is automated with a fixed LLM rubric; proof acceptance separately requires VCG and Rocq checks. Methods can reuse the judge protocol. The rubric screens for vacuous or weak contracts. Audited success combines proof acceptance with compliance with the stated access and input-preservation rules.

CWud details repository interaction, construction effort and costs; 6RZa explains p117 and the combined SMT and ITP workflow. We will clarify task inputs, generated artifacts and acceptance paths, show the omitted i declaration, and label proof size as "nongenerated Rocq proof LOC."

## Letter to the Area Chair

Dear Area Chair,

Thank you for coordinating the reviews. We respectfully ask that wFZw’s score of 3 be reconsidered in light of the corrected results and additional analyses in our response.

The discrepancies arose from aggregation and transcription errors. We appreciate the reviewer’s careful checks. All 140 machine-checked references remain valid, and the central findings of substantial verification headroom and predominantly proof-stage failures remain unchanged.

To address the RQ2 concerns, we compared results while controlling task composition, harness and reasoning effort. Token and tool savings are larger on matched tasks, and budgeted time per success decreases when all attempts, including timeouts, are counted.

We appreciate that wFZw recognizes the motivation, clear task design and verification artifacts. knrA raises related concerns about counts and efficiency while recommending acceptance and recognizing the verified corpus and fixed-contract task. These reviews provide complementary perspectives on the paper’s contribution.

We respectfully ask the AC to weigh the corrected evidence and additional analyses alongside the verified corpus, task design and evaluation methodology, and consider whether the remaining concerns warrant a clear-rejection recommendation. Thank you for your consideration.
