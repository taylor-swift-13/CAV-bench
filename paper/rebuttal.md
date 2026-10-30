# AAAI Rebuttal

Updated: 2026-10-30

## wFZw (Score 3)

Thank you for checking statistics and RQ2.

Q1 (statistics). The discrepancies arose from errors in result aggregation and transcription, not different underlying runs.

Table 3 (140 tasks each; W/F/T=success/non-timeout failure/timeout):

|Model/effort/harness|W/F/T|
|---|---|
|GPT-5.5/xhigh/Codex|80/31/29|
|GPT-5.5/medium/Codex|59/61/20|
|GPT-5.4/xhigh/Codex|53/48/39|
|GPT-5.4/high/Codex|40/96/4|
|GPT-5.4/medium/Codex|20/120/0|
|GPT-5.4/low/Codex|16/124/0|
|GPT-5.4-mini/medium/Codex|8/130/2|
|GLM-5.2/thinking/Claude Code|30/77/33|
|DeepSeek-V4-Pro/thinking/Claude Code|5/55/80|
|kimi-2.7-code/thinking/Kimi Code|18/99/23|

Non-timeout failures total 841: 744 proof-stage (88.5%) and 97 VCG-stage (11.5%), matching RQ4. GPT-5.4 xhigh's 37.9% matches Fig. 2(c) at 90 min. Affected costs, plots and text will be synchronized; other data and our core contributions and conclusions remain unchanged.

Q2 (efficiency). Efficiency gains are larger on matched tasks, controlling for differences in task composition. Fixing Codex and effort, GPT-5.5 versus GPT-5.4 reduces paired-success input/output tokens and tool calls by 66.1%/53.6%/33.3% at medium and 62.8%/57.0%/32.4% at xhigh. Input falls on 14/15 medium and 35/39 xhigh pairs. Across 140 attempts, budgeted minutes/success fall 165.8→105.0 (medium) and 153.4→95.1 (xhigh). We divide total attempt time by successes, charging timeouts 90 min and capping other durations at 90. Official harnesses are preferred (CWud).

## Cmct (Score 5)

Thank you for questions on scope and novelty.

Q1. Long-horizon interaction extends beyond end-to-end to the fixed-contract primary task. GPT-5.5 xhigh/Codex primary successes average 42.8 min, 55.8 turns, 119.7 tool calls (3.01 VCG/12.60 Rocq checks), and 9.1M/34.7K input/output tokens. Evaluation costs are high (CWud).

Q2. End-to-end evaluation is automated: an LLM judge applies a fixed rubric to generated contracts, without human adjudication of submissions. We will release the rubric, prompt, judge model and configuration for reuse. Fixed-contract primary acceptance is deterministic. Proof acceptance separately requires VCG, Rocq kernel checks and deterministic auditing. End-to-end need not be harder or longer than primary; adequacy criteria apply (knrA).

Q3. AlgoVeri (arXiv:2602.09464) compares SMT-based Dafny/Verus with Lean ITP across distinct memory abstractions. Its Lean setting has no C annotation-to-VC stage. Dafny's managed heap abstracts away C pointer arithmetic and manual memory management; p117 requires preserving input memory and owning newly allocated output strings. Primary and proof-only fix C code, contracts and toolchain, varying annotations to isolate annotation-proof interaction. Proof failures can trigger annotation repair and VC regeneration; cross-language comparisons cannot isolate this effect.

"GT Verified" means complete machine-checked references for all 140 tasks; AlgoVeri reports expert curation and selected specification checks.

## knrA (Score 6)

Thank you for examining evaluation rigor.

Q1. Corrected counts preserve conclusions; paired/all-attempt efficiency gains hold (wFZw). Official harnesses are preferred (CWud).

Q2. Generated contracts are judged automatically, without human adjudication. GPT-5.5 xhigh receives the task description, C code, contract and Rocq definitions. All eight checks must pass: legal inputs, C safety, results, code consistency, input/output relations, memory effects, branches and full behavior. Checks screen for overly restrictive preconditions and weak postconditions. Manual inspection found all clearly weak contracts in the sample were rejected. We will release the rubric, prompt and judge configuration. Proof acceptance independently requires VCG, Rocq kernel checks and deterministic auditing.

Q3. High evaluation costs (CWud) allowed one trajectory per task/configuration; repeat-run variance was not measured.

Q4. For the eight reversals, consider p050 (decode_shift). Generated invariants retain input/output character-nonzero facts for direct use at return; reference invariants require deriving them. Fixed annotations need not make tasks easier. End-to-end also permits easier-to-prove contract formulations, subject to adequacy checks.

Q5. Instructions explicitly prohibit reference answers, prior results and other task workspaces. Current-task artifacts, supplied definitions, documentation and listed examples are allowed. Transcript auditing enforces this access policy.

## CWud (Score 6)

Thank you for scope and harness questions.

Q1. Our workflow supports modular verification via contracts and repository interaction. Targets average 29.1 C LOC. Corpus-wide specs/dependencies span 52K Rocq LOC; permitted references exceed 220K LOC. Agents coordinate definitions, annotations, VCs and proofs. SWE-bench (arXiv:2310.06770) tests issue repairs; we require functional/memory proofs. GPT-5.5 xhigh/Codex successes average 42.8 min; recorded API costs: $7.41, versus $1.93/attempt on SWE-bench Pro with matched model/effort/harness. P3 reports $2.78/13.9 min on AlgoVeri's shared successes (arXiv:2608.09277; effort unspecified). Interaction is iterative (Cmct).

Q2. We evaluate model/harness systems, using official integrations when available and Claude Code otherwise. RQ2 fixes harness and effort (wFZw).

Q3. RQ5 tests retention on 30 Claude Code successes selected before alternative-harness runs. Costs limited the model-by-harness matrix. Whether alternatives solve CC failures requires separate testing.

Q4. Costs limited each task/configuration to one trajectory; repeat-run variability is unmeasured. Paired/all-attempt efficiency gains hold (wFZw); Table 3's gray means include non-timeout failures.

Q5. Experts guided GPT-5.5 xhigh/Codex while agents wrote annotations/proofs. Spec writing/review took six person-months, with 30 min-20 h construction per task. Inclusion required expert consensus, regenerated VCs and Rocq acceptance. We will use vector figures.

## 6RZa (Score 6)

Thank you for questions on proofs and tool choice.

Q1. Tasks require functional and memory proofs. p117 (select_words) must return all and only words with n consonants, in order, preserve the input and own the allocated output strings. Its reference uses 99 lemmas/1,937 nonblank proof lines. Induction establishes that appending a word preserves ownership of earlier strings. GPT-5.4 xhigh completed 28 ITP obligations in 90 min, leaving 18; no configuration achieved audited success. 140 references contain 5,562 VCs and 62,812 nongenerated proof lines.

Q2. CBMC can complement QCP on suitable obligations. Our p052 pilot verified its encoding for 0<=n<=64 in 0.29 s; loop-contract attempts for 0<=n<INT_MAX timed out at 180 s or encountered conversion errors. CBMC's memory-predicate interface excludes mutual recursion. It does not natively accept QCP assertions/Rocq predicates, so translation must preserve their semantics. Its standard workflow has no direct ITP handoff for unresolved obligations.

Q3. QCP/Rocq (arXiv:2505.12878) combines SMT automation with explicit inductive proofs over separation-logic memory resources. Agents can introduce lemmas, repair proofs, revise annotations and regenerate VCs when automation stalls. This enables the annotation-proof interaction our benchmark measures, with machine-checked references for every task. Proof work spans the repository (CWud). Table 3 distinguishes successes/failures/timeouts and success means from non-timeout means.

## AI Review

Thank you. The reporting corrections and controlled RQ2 analyses are detailed in wFZw. The strongest result remains 80/140; all 140 references are machine-checked. The corrected 744/841 proof-stage failures support the reported verification bottleneck.

Lemur (arXiv:2310.04870) uses verifier feedback to repair C invariants. We will cite this work. CAV-Bench contributes a verified C corpus and an evaluation setting coupling auxiliary annotations with explicit Rocq proofs: annotations determine VCs, and proof feedback guides annotation repair and VC regeneration.

The p050 trajectory makes this interaction concrete: generated invariants retain character-nonzero facts for the return proof, whereas the reference invariant requires deriving them. See knrA for this example, the complementary task settings and the cost-constrained single-trajectory design.

End-to-end contract assessment is automated with a fixed LLM rubric; proof acceptance separately requires VCG/Rocq checks. The same judge protocol can be reused across methods. The rubric screens for vacuous or weak contracts. Audited success combines proof acceptance with compliance with the stated access and input-preservation rules.

CWud details repository interaction, construction effort and costs; 6RZa gives p117's proof example and the SMT/ITP rationale. We will clarify task inputs, generated artifacts and acceptance paths, show the omitted i declaration, and label proof size as "nongenerated Rocq proof LOC."

## Letter to the Area Chair

Dear Area Chair,

Thank you for coordinating the reviews. We respectfully request that the final assessment weigh the corrected evidence and the benchmark's core contributions when reconsidering wFZw's score of 3, alongside the other scores of 5, 6, 6 and 6.

The reporting discrepancies arose from aggregation and transcription errors. The corrected tables preserve the strongest result, 80/140 (57.1%), and the finding that 744/841 non-timeout failures reach the proof stage. All 140 machine-checked references remain valid. These corrections leave the verified corpus, task design and evaluation methodology unchanged.

The additional RQ2 analyses address task composition and harness effects directly. With harness and effort fixed, token and tool savings persist on jointly solved tasks. Including all 140 attempts, budgeted minutes per success decrease from 165.8 to 105.0 at medium and from 153.4 to 95.1 at xhigh.

knrA raises closely related questions about counts and efficiency, while recommending acceptance and explicitly recognizing the verified corpus and fixed-contract task. The other reviews also recognize the work's methodological and empirical value.

We ask that the corrected reporting and additional analyses be considered together with these contributions. The benchmark provides verified targets while exposing substantial headroom for current agents. We appreciate reconsideration of whether the score of 3 reflects the paper in light of this evidence.
