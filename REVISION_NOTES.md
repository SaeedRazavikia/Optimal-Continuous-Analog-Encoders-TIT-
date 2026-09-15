# Submission-length revision — September 15, 2026

The submission version is **50 pages including references**, reduced from 59 pages. The extended arXiv version is 56 pages. Font size, margins, line spacing, and figure scale are unchanged.

## Content changes

- Removed the former assumptions table (Table I) and stated the R/S assumptions concisely in Section II-D. Each theorem retains its own hypotheses.
- Excluded the Lean-verification appendix from the submission build, retaining its complete source for arXiv.
- Retained the ancillary “Scope of the Criterion” and “Approximate Rigidity” appendices in the arXiv build. The submission keeps all main results and their proofs in Appendices A–F.
- Condensed repeated explanations in the introduction, model, decoding, implementation, enclosing-ellipse discussion, certification, numerical results, and conclusions.
- Preserved the digital-modulation motivation, moment examples and interactions, every formal statement, all main proofs, numerical values, table entries and figure data. Statements excluded from submission remain unchanged in the extended source.
- Updated references to the removed table and made mentions of the arXiv-only appendices conditional.

## Build either version

```sh
latexmk -pdf manuscript.tex
latexmk -pdf manuscript_arxiv.tex
```

The first command builds the submission version by default. The second enables the arXiv appendices through the shared source switch. No manual commenting or uncommenting is required.

## Verification

Both PDFs compile without unresolved references or layout warnings; revised pages were rendered and inspected. All 17 theorem/lemma/proposition/corollary environments in the complete source are unchanged. The submission includes 15 of these statements; the ancillary criterion-transfer corollary and approximate-rigidity proposition are arXiv-only.

The Lean proof sources and all 55 audited source/configuration hashes are unchanged from audited proof commit 6783e9c68823213e2f4bc31259ab6a1ad6072d89. Its audit covers 673 declarations in 47 modules, with the remaining formalization gaps documented in the artifact. This editorial revision does not claim new formalization progress.

The source archive includes both build files, all omitted appendices, the numerical reproduction package, the Lean project and a SHA256SUMS.txt manifest. Updates are published on the existing draft PR without merging main.
