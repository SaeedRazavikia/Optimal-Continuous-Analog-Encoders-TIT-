# It Takes Two Moments — Lean formalization

Machine-checked proofs accompanying Saeed Razavikia's paper:

**[It Takes Two Moments: Rigidity and Limits of Continuous Encoders for
Over-the-Air Computation](https://arxiv.org/abs/2610.21536v1)**  
[Read on arXiv](https://arxiv.org/html/2610.21536v1) · [PDF](https://arxiv.org/pdf/2610.21536v1)

This repository is the formalization companion. It contains the Lean proofs,
a readable correspondence guide, and the files needed to verify them.
The correspondence is pinned to **arXiv:2610.21536v1**.

## Read and compare

| Start with… | What it provides |
|---|---|
| [Statements and proof guide](docs/STATEMENTS.md) | The ten paper results, key assumptions, proof outlines, and links to both the paper and Lean |
| [Coverage](formalization/COVERAGE.md) | Exact scope of the formalized results and exclusions |
| [Theorem map](formalization/THEOREM_MAP.md) | Detailed declaration names and supporting proof chains |
| [Lean sources](formalization/Analog/) | The definitions and proofs checked by Lean |

All ten numbered results have formal counterparts under their stated
hypotheses: **Theorems 1–5, Propositions 1–4, and Lemma 1**. This includes
the explicit minimum decoder, its Gaussian limit, and globally optimal
quadratic/quartic encoders. Unnumbered gradient claims, numerical examples,
and experiments are outside this coverage; see the inventory for details.

## Verify

Install Python 3, Git, and Lean's `elan` toolchain manager. From the repository
root, run:

```sh
cd formalization
lake exe cache get
python3 verify.py
```

The project pins Lean **4.24.0** and its mathlib dependencies. Verification
checks the statement-to-declaration catalog, builds all modules with warnings
rejected, and runs a kernel audit with `--trust=0`. No paper source files or
LaTeX installation are needed.

The recorded successful audit covers **1,268 public declarations in 107
modules**, using only `propext`, `Classical.choice`, and `Quot.sound`.
See the [verification report](formalization/verification/report.json) for
source hashes and [GitHub Actions](https://github.com/SaeedRazavikia/Rigidity-and-Limits-of-Continuous-Encoders/actions/workflows/verify-lean.yml)
for repository-run status.

Lean verifies the formal statements. The correspondence checks validate the
local catalog and its links to audited declarations; they do not automatically
prove that a natural-language paper statement and a Lean statement are equivalent.
Use the guide to compare their hypotheses and conclusions.

## Files

- `formalization/` — Lean sources, pinned dependencies, coverage, and audit evidence.
- `docs/STATEMENTS.md` — readable paper-to-proof correspondence.
- `CITATION.cff` — citation metadata for the artifact and paper.

For proof-maintenance instructions, see [formalization/README.md](formalization/README.md).
Adapted topology proofs retain their [provenance](formalization/notes/completion-topology.md)
and [third-party license](formalization/THIRD_PARTY_LICENSES/ClassificationOfSurfaces-LICENSE).
