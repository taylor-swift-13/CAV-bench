# CAV-Bench paper

This directory contains the AAAI-27 manuscript, supplementary material, reproducibility checklist, author response, figures, and the frozen statistics used by the paper.

## Documents

| Document | Source | PDF |
| --- | --- | --- |
| Main paper | [main.tex](main.tex) | [main.pdf](main.pdf) |
| Supplementary material | [appendix.tex](appendix.tex) | [appendix.pdf](appendix.pdf) |
| Reproducibility checklist | [ReproducibilityChecklist.tex](ReproducibilityChecklist.tex) | [ReproducibilityChecklist.pdf](ReproducibilityChecklist.pdf) |

[rebuttal.md](rebuttal.md) contains the English author responses. It also includes the AI-review response and AC letter. Publication in this repository is not submission to the review system.

## Source layout

- `sections/`: manuscript and supplementary TeX sections.
- `tables/`: generated LaTeX table bodies.
- `figures/`: figure assets and frozen experiment snapshots.
- `scripts/`: statistics collection and figure/table generation.
- `references.bib`: bibliography.
- `paper_preamble.tex`, `math_commands.tex`: shared definitions.
- `aaai2027.sty`, `aaai2027.bst`: AAAI author-kit files.

## Build

Run from this directory:

```bash
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex

pdflatex -interaction=nonstopmode -halt-on-error appendix.tex
bibtex appendix
pdflatex -interaction=nonstopmode -halt-on-error appendix.tex
pdflatex -interaction=nonstopmode -halt-on-error appendix.tex

pdflatex -interaction=nonstopmode -halt-on-error ReproducibilityChecklist.tex
```

The main paper and appendix have separate bibliographies and must be compiled separately. The checked-in PDFs accompany the source package; compilation intermediates such as `.aux`, `.log`, `.blg`, and Python caches are excluded from this publication update.

## Audited data

The paper uses a consolidated **140-task** cohort: 102 core tasks, 30 extension tasks, and 8 additional tasks drawn from the corresponding experiment branches. The principal frozen artifacts are:

- `figures/publication_results.json`: author-confirmed publication counts, cost means, checkpoint aggregates, and revision provenance. This is the source for current Tables 3-4 and Figure 2.
- `figures/main_table_140_audit.json`: preserved historical selected workspaces and log-derived audit results; superseded by the publication aggregates for the corrected paper.
- `figures/error_table_140_audit.json`: preserved historical failure-stage and audit summaries; current outcome totals are in `publication_results.json`.
- `figures/branch_140_audit.json`: the three task settings.
- `figures/harness_glm52_30_audit.json`: the fixed 30-task harness-retention cohort.
- `figures/stats_snapshot.json`: supporting statistics used by the plotting scripts; interpret together with the audited overrides above.

Audited success requires a successful check and recorded total time at most **5,400 seconds**. Missing runs are counted as timeouts in the reported outcome totals. Table 3 distinguishes successful-run means from non-timeout means including failures. Run selection and protocol rejection rules are recorded in the audit snapshots and collector implementation; they must not be replaced by simply taking the latest successful run.

The generation scripts refer to the original experiment layout. Rebuilding figures from these frozen snapshots is distinct from collecting a new run cohort. Check the path assumptions and selection policy before recollecting statistics; the supplied data and source figures are preserved in this update.

## Author-confirmed reporting correction (2026-10-30)

The correction follows the author's supplied Q1 response: GLM-5.2 has 77 non-timeout failures and 33 timeouts; the non-timeout failure total is 841, including 744 proof-stage and 97 VCG-stage failures; GPT-5.4 xhigh has 53 successes (37.9%). Other pre-cutoff publication results are retained, including GPT-5.5 xhigh with 80 successes and GPT-5.4 high with 40. Total outcomes are 329 successes, 841 failures and 230 timeouts.

`publication_results.json` records the source of every restored aggregate. The 90-minute plot endpoints use the author-confirmed publication counts; earlier checkpoints retain the existing timing observations. This is an author-supplied aggregate correction, not an independent re-audit of corrected per-run times. Historical audit snapshots and raw experiment logs have not been changed.

Regenerate Tables 3-4 with `python3 scripts/make_publication_tables.py`; the existing main/error table entry points delegate to it when the publication revision is present. Figure 2 uses the same publication data. Do not overwrite this revision by recollecting the unchanged historical logs.
