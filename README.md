# It Takes Two Moments — Lean formalization

Machine-checked proofs accompanying Saeed Razavikia's paper,
**[It Takes Two Moments: Rigidity and Limits of Continuous Encoders for
Over-the-Air Computation](https://arxiv.org/abs/2610.21536v1)**.

The formalization covers **Theorems 1–5, Propositions 1–4, and Lemma 1**, under
their stated hypotheses in **arXiv:2610.21536v1**. The paper is available on
[arXiv](https://arxiv.org/html/2610.21536v1); this repository contains its Lean
companion and verification materials.

## Read the proofs

Start with the **[statement and proof guide](docs/STATEMENTS.md)**. Find the
paper's theorem number, read its summary, and follow the link to the Lean
statement and proof. No installation is needed to browse these files.

- [Coverage](formalization/COVERAGE.md) records the exact scope and exclusions.
- [Theorem map](formalization/THEOREM_MAP.md) lists supporting declarations and proof dependencies.
- [Lean sources](formalization/Analog/) contain the definitions and proofs.

Unnumbered gradient claims, numerical examples, and experiments are outside
the recorded coverage.

## Verify locally

Install **Git, Python 3, and Elan** (Lean's toolchain manager). Follow the
[official Lean installation instructions](https://lean-lang.org/install/manual/)
for your operating system. Ensure `git`, `python3`, and `lake` are available
in your terminal, then run:

```sh
git clone https://github.com/SaeedRazavikia/Rigidity-and-Limits-of-Continuous-Encoders.git
cd Rigidity-and-Limits-of-Continuous-Encoders/formalization
lake exe cache get
python3 verify.py
```

The project selects Lean **4.24.0** and the pinned mathlib dependencies.
The first run downloads the toolchain and dependency cache. No LaTeX
installation or paper source files are required.

A successful run ends with:

```text
PASS: 1268 declarations; compilation and kernel audit complete.
```

The kernel audit can run for several minutes without printing progress.
If verification fails, the terminal names the relevant log in `verification/`,
and `verification/report.json` records the failure.

## What is checked

Verification checks the paper-to-Lean catalog, builds all modules with warnings
rejected, and rechecks imported proofs with `lean --trust=0`. The recorded
successful audit covers **1,268 public declarations in 107 modules**, using only
`propext`, `Classical.choice`, and `Quot.sound`.

See the [audit report](formalization/verification/report.json) for source hashes
and the [GitHub Actions runs](https://github.com/SaeedRazavikia/Rigidity-and-Limits-of-Continuous-Encoders/actions/workflows/verify-lean.yml)
for CI status. A recorded local audit and a GitHub run have separate results.
Lean checks the formal statements; the correspondence guide explains how their
hypotheses and conclusions match the paper.

For changes to the project, use the [maintainer guide](formalization/README.md).
[CITATION.cff](CITATION.cff) supplies citation metadata. Adapted topology proofs
retain their [provenance](formalization/notes/completion-topology.md) and
[third-party license](formalization/THIRD_PARTY_LICENSES/ClassificationOfSurfaces-LICENSE).
