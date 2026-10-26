# AAAI Rebuttal

Prepared: 2026-10-27

The AI Review response and AC letter remain drafts for approval. Nothing has been submitted or sent.

## wFZw (Score 3)

We apologize for reporting oversights: Table 4 transcription errors and inconsistent application of Fig. 2(c)'s 5,400s cutoff in early Table 3 results. Correct non-timeout failures: 841, comprising 744 reaching proof and 97 failing at VCG (88.5%/11.5%). GLM-5.2: W/F/T=30/77/33. After consistent truncation, GPT-5.5 xhigh, GPT-5.4 xhigh and high yield 78/31/31, 53/48/39 and 39/96/5 (55.7%, 37.9%, 27.9%). Across 1,400 attempts: 326/841/233. Counts, costs, figures and text are corrected; rankings, substantial verification headroom and predominantly proof-stage failures persist. The strongest result changes by two tasks (57.1%→55.7%); all 140 machine-checked references are unaffected.

RQ2 now controls task composition, harness and effort. On jointly solved tasks with the same Codex/effort, GPT-5.5 versus GPT-5.4 reduces input/output tokens and tool calls by 66.1%/53.6%/33.3% at medium and 62.8%/57.0%/32.4% at xhigh. Input falls on 14/15 medium and 35/39 xhigh pairs. Including all 140 attempts, assigning timeouts 90 min and capping other durations at 90, amortized minutes/success fall 165.8→105.0 (medium) and 153.4→97.6 (xhigh). Amortization divides total budgeted attempt time by audited successes, including unsuccessful effort. Thus, matched-task token/tool savings and all-attempt budgeted time savings both hold. CWud explains harness selection.

## Cmct (Score 5)

"Long-horizon" denotes sustained agent interaction; we will clarify this. With C code/contracts supplied, GPT-5.5 xhigh/Codex solves 78/140 within 90 min, with 31 timeouts. Successes average 55.3 turns, 119.2 tool calls (2.95 VCG/12.55 Rocq checks), 9.1M input/34.7K output tokens and 41.5 min. CWud details costs/construction.

AlgoVeri (arXiv:2602.09464) compares SMT-based Dafny/Verus with Lean ITP. Different memory-modeling granularity and cross-language comparisons cannot isolate annotation-proof coupling within one C workflow. We fix C code/contracts: inadequate auxiliary annotations can yield unprovable VCs discovered during Rocq proof construction, prompting annotation repair and VC regeneration. This couples source annotations with ITP feedback under C memory-validity, aliasing and resource-preservation obligations. Dafny/Verus lack this explicit ITP stage; AlgoVeri's Lean setting lacks source-annotation-to-VC translation and C-style raw-memory operations.

"GT Verified" means complete machine-checked references for all tasks. AlgoVeri reports expert-reviewed specs and selected formal checks, not full verified-reference coverage across all three languages. References establish task solvability. It supplies contracts; we additionally evaluate generation. For why end-to-end need not be harder or longer than primary, the reusable contract rubric and kernel-checked proof acceptance, see knrA. The fixed-contract primary task has deterministic acceptance.

## knrA (Score 6)

wFZw addresses counts and RQ2's paired/all-attempt analyses; CWud explains harness selection.

Inputs: description, C, contract and Rocq definitions. The end-to-end LLM judge checks legal inputs, C safety, results, code consistency, input/output relations, memory effects, branches and full behavior; all eight must pass. It screens for over-restrictive preconditions and weak postconditions. Manual inspection found all clearly weak contracts in the inspected sample were rejected. Experts reviewed reference contracts; generated contracts use the judge without manual adjudication. The rubric/prompt are reusable. Final verification separately requires VCG, Rocq kernel proof checking and deterministic auditing; LLM judgments cannot bypass these checks.

The settings need not have a strict difficulty ordering. In p050 (decode_shift), the agent-generated invariant explicitly retains input/output character-nonzero facts for direct use at return; the reference invariant requires deriving them at return. This shows annotation choice changes subsequent proof work. End-to-end agents can also choose contract formulations, subject to adequacy checks. High costs (CWud) limited each task/configuration to one trajectory; run-to-run variance is unmeasured.

Instructions explicitly forbid reference answers, prior results and other task workspaces; current-task artifacts, supplied definitions, documentation and listed examples are allowed. Transcript auditing enforces this distinction.

## CWud (Score 6)

SWE-bench (arXiv:2310.06770) evaluates issue-driven repository repairs via tests; we require functional/memory proofs. Corpus-wide specs/transitive dependencies span 52K Rocq LOC; permitted references exceed 220K LOC. Agents coordinate cross-file definitions, annotations, VCs and proof libraries; function calls are supported. Coupling also applies to modular verification; long-horizon evidence: Cmct.

Targets average 29.1 C LOC. With GPT-5.5 xhigh/Codex, 78 successes average 41.5 min/$7.41 estimated API cost after cache discounts. This exceeds $1.93/attempt on SWE-bench Pro with the same model/effort/harness (Journal, June 17; includes failures). P3 (arXiv:2608.09277, Table 7) reports $2.78/13.9 min for plain Codex-GPT-5.5 on AlgoVeri's jointly solved subset, also below ours; effort is unspecified.

We evaluate model/harness jointly, using official integrations, else Claude Code. RQ5 tests a model without official integration on 30 CC successes fixed before alternatives: success retention. High costs precluded full model × harness testing or repeats; variance is unmeasured. Matched RQ2/all-attempt costs: wFZw. Gray means include non-timeout failures.

Experts guided GPT-5.5 xhigh/Codex; agents wrote annotations/proofs. Spec writing/review took six person-months; construction 30 min-20 h/task. Inclusion required expert consensus, regenerated VCs and Rocq acceptance. We will use vector figures.

## 6RZa (Score 6)

p117 (select_words) must return all words with exactly n consonants in order, preserve input and own allocated output strings. Its reference has 99 lemmas/1,937 nonblank proof lines, including scan-state induction and recursive heap reasoning. Its inductive proof shows that each newly allocated word can be added to the output while preserving ownership of all previously allocated strings. GPT-5.4 xhigh used 90 min, completing 28 ITP obligations with 18 unfinished; no evaluated configuration achieved audited success. HumanEval tests do not establish these guarantees. Across all 140 references, there are 5,562 VCs and 62,812 nongenerated Rocq proof lines.

QCP (arXiv:2505.12878) combines SMT automation, Rocq ITP and separation-logic C memory reasoning. Agents revise annotations/regenerate VCs and use lemmas, induction and proof repair when automation fails. This combined workflow motivates our choice.

CBMC does not natively accept QCP separation-logic assertions or Rocq inductive predicates. Re-encoding requires semantic preservation; otherwise the target changes. When automated solving times out/fails, its standard workflow offers no direct ITP handoff to continue difficult obligations. It cannot directly replace our proof-stage baseline. CBMC could complement QCP by automating suitable simpler obligations.

CWud details repository context/costs. Table 3's caption will define W/F/T and distinguish success means from non-timeout means including failures.

## AI Review — Draft for approval

Thank you. See wFZw for corrected counts, RQ2's same-harness/effort paired comparisons and all-attempt budgeted time analysis. The strongest result is 78/140 within 90 minutes; all 140 machine-checked references remain unaffected.

See knrA for p050: generated invariants retain character-nonzero facts that the reference invariant requires deriving at return. The settings need not form a strict difficulty ordering. Single trajectories cannot isolate annotation effects from run-to-run variation. The contract rubric, manual inspection and access policy are explained there. Audited success requires proof acceptance and protocol compliance.

Lemur (arXiv:2310.04870) studies verifier-guided C invariant generation and repair. CAV-Bench covers broader auxiliary annotations and explicit Rocq proofs: annotations determine VCs, while ITP feedback guides annotation revision and VC regeneration. Lemur does not evaluate this coupled workflow. We will clarify this distinction and cite it.

See CWud for construction effort, costs and harness selection, and 6RZa for p117's proof complexity and QCP's SMT/ITP design. "Long-horizon" means sustained agent interaction.

We will clarify task inputs, outputs and acceptance paths, show the omitted i declaration, and use "nongenerated Rocq proof LOC" to distinguish agent-written proofs from generated files.

## Letter to the Area Chair — Draft for approval

Dear Area Chair,

We respectfully request reassessment of wFZw's score of 3, which is an outlier against the other scores of 5, 6, 6 and 6. We believe the review places disproportionate weight on reporting discrepancies and potentially overstated claims, while giving insufficient weight to the verified corpus, task design and evaluation methodology.

The discrepancies arose from oversights in statistical reporting. Correcting them changes the strongest result from 80/140 to 78/140 (57.1% to 55.7%), without affecting the 140 machine-checked references or the benchmark's core contribution. The central findings of substantial verification headroom and predominantly proof-stage failures remain unchanged.

For RQ2, additional comparisons control task composition, harness and reasoning effort. Token/tool savings persist on matched tasks, and budgeted time per success decreases when all attempts, including timeouts, are included.

Notably, knrA raises substantially overlapping concerns about counts and efficiency comparisons, yet recommends acceptance and explicitly recognizes the verified corpus and fixed-contract task as valuable contributions. Other reviews also recognize the work's methodological and empirical value.

We ask the AC to weigh the corrected evidence and enduring contribution, and assess whether a clear-rejection recommendation remains proportionate to the unresolved concerns.
