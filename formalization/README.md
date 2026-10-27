# Lean proof project

This project formalizes results from
[It Takes Two Moments, arXiv:2610.21536v1](https://arxiv.org/abs/2610.21536v1).
Start with the [statement and proof guide](../docs/STATEMENTS.md), then use
[COVERAGE.md](COVERAGE.md) for exact scope and [THEOREM_MAP.md](THEOREM_MAP.md)
to locate supporting declarations.

## Verify

Install Python 3, Git, and Lean through Elan. The checked-in `lean-toolchain`
selects **Lean 4.24.0**; `lake-manifest.json` pins mathlib and its dependencies.
From the repository root:

```sh
cd formalization
lake exe cache get
python3 verify.py
```

The script checks the paper-correspondence catalog and theorem inventory,
builds every module with warnings rejected, and runs `lean --trust=0 Audit.lean`.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed axioms.
The recorded audit covers **1,268 public declarations in 107 modules**.

Results and source hashes are written to [verification/report.json](verification/report.json).
A failed run records a failure. Each [GitHub Actions run](https://github.com/SaeedRazavikia/Rigidity-and-Limits-of-Continuous-Encoders/actions/workflows/verify-lean.yml)
has its own status. The paper is read on arXiv; verification needs no LaTeX source.

## Paper correspondence

[paper_targets.json](paper_targets.json) retains the ten reviewed statement
excerpts, their fingerprints, versioned paper links, and Lean declaration names.
[check_correspondence.py](check_correspondence.py) checks this local catalog,
the reader guide, and the declaration references without downloading the paper.
The source-snapshot fingerprint is historical provenance, not a requirement to
keep the full manuscript here.

These checks detect stale or inconsistent correspondence records. They do not
establish semantic equivalence between prose and Lean. Compare the paper's
assumptions with the actual Lean declarations and the scope notes.

## Updating the project

After changing proofs, run `python3 update_audit.py`, then `python3 verify.py`.
When updating the paper version or correspondence guide, review the mathematical
statements and coverage first, edit the catalog and guide together, and run:

```sh
python3 check_correspondence.py --update
python3 -m unittest discover -s tests -v
python3 verify.py
```

Updating fingerprints records the reviewed correspondence; it does not add proofs.
The explanatory [notes](notes/) describe the longer proof chains.
Adapted topology sources retain their [provenance](notes/completion-topology.md)
and [third-party license](THIRD_PARTY_LICENSES/ClassificationOfSurfaces-LICENSE).
[runtime/](runtime/) documents the local audit environment; its adapter is
unnecessary on an ordinary Linux installation.
