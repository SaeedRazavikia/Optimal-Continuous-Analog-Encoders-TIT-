# It Takes Two Moments

**Rigidity and Limits of Continuous Encoders for Over-the-Air Computation**  
Saeed Razavikia

This repository contains the research manuscript, its Lean 4 formalization,
and code to reproduce the numerical results. The paper studies which continuous
encoders support exact moment-based computation and how to optimize their
robustness to channel noise.

## Start here

| To… | Open… |
|---|---|
| Read the paper | [Main.tex](Main.tex), or build the PDF below |
| Understand exactly what is proved | [Formalization coverage](formalization/COVERAGE.md) |
| Find a theorem in Lean | [Theorem map](formalization/THEOREM_MAP.md) |
| Verify the proofs | [Instructions below](#verify-the-proofs) or [GitHub Actions](https://github.com/SaeedRazavikia/Optimal-Continuous-Analog-Encoders-TIT-/actions/workflows/verify-lean.yml) |
| Reproduce the experiments | [Reproduction guide](docs/REPRODUCING.md) |

## Verify the proofs

With Lean's `elan` toolchain manager installed, run from the repository root:

```sh
cd formalization
lake exe cache get
python3 verify.py
```

The project pins Lean **4.24.0** and its mathlib dependencies. Verification
builds all modules, rejects warnings and admitted proofs, checks the manuscript
and theorem inventories, and runs a kernel audit with `--trust=0`.

The recorded successful audit covers **1,198 public declarations in 100
modules**. The only allowed axioms are Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. See the [audit report](formalization/verification/report.json)
for exact source hashes, and [GitHub Actions](https://github.com/SaeedRazavikia/Optimal-Continuous-Analog-Encoders-TIT-/actions/workflows/verify-lean.yml)
for the status of repository runs.

The completed proof areas include heterogeneous rigidity, general SDP
attainment, Gaussian converse and minimax results, and general grid
certification. **This is not a claim that every statement in the paper is
formalized.** Remaining formula wrappers and examples are listed in the
[coverage inventory](formalization/COVERAGE.md).

## Build the paper

Install a LaTeX distribution with `latexmk`, IEEEtran, and PGFPlots, then run
from the repository root:

```sh
python3 build.py
```

The output is `build/Main.pdf`. The manuscript's bibliography and editable
TikZ/PGFPlots figures are included; the numerical experiments do not need to
be rerun to build the paper.

## Repository layout

| Path | Purpose |
|---|---|
| `Main.tex`, `bibliography.bib` | Current manuscript and references |
| `figures/` | Figure sources used by the manuscript |
| `formalization/` | Lean proofs, pinned dependencies, coverage, and audit evidence |
| `code/`, `results/` | Numerical scripts and recorded JSON results |
| `docs/` | Reproduction instructions and experiment details |

The Lean artifact has [citation metadata](formalization/CITATION.cff).
Adapted topology proofs retain their [provenance](formalization/notes/completion-topology.md)
and [third-party license](formalization/THIRD_PARTY_LICENSES/ClassificationOfSurfaces-LICENSE).
Superseded drafts and historical audit snapshots remain available in
[Git history](https://github.com/SaeedRazavikia/Optimal-Continuous-Analog-Encoders-TIT-/tree/54d1083238b5e3e9a009138c3bb69c09d37f58e9).
