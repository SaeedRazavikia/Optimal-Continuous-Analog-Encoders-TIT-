# Manuscript formats

Both PDFs use the same mathematical text, figures, appendices, and bibliography.

| Format | Entry point | Output |
| --- | --- | --- |
| Two-column IEEE journal layout | `manuscript.tex` | `TIT_Paper_Revised.pdf` |
| Single-column, double-spaced layout | `manuscript_submission.tex` | `TIT_Paper_Submission.pdf` |

Run `python3 build.py` to build both formats. Use `--format paper` or
`--format submission` to build only one. The script runs three LaTeX passes
for each selected format so cross-references and plot legends resolve.

The single-column version uses US letter paper, 1-inch text margins, and
12-point text on a 24-point baseline. The abstract, keywords, narrative,
theorems, proofs, appendices, figure captions, and references use this text
size and spacing. Tables retain their compact source typography; labels
inside figures retain their original typography. All figures remain native
TikZ/PGFPlots vectors and shrink proportionally only when needed to fit the
text width. Equation and theorem numbering is shared across the formats.

This is the requested review layout, not an assertion that a particular
journal's current submission requirements have been checked.
