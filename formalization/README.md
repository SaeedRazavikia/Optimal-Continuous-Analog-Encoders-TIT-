# Lean formalization

Proofs accompanying [Main.tex](../Main.tex), *It Takes Two Moments: Rigidity and
Limits of Continuous Encoders for Over-the-Air Computation*.

The saved local audit passed **1,198 public declarations in 100 modules**.
The development covers heterogeneous rigidity, general SDP attainment,
Gaussian statistical limits, and grid certification. Some formula and example
wrappers remain incomplete; [COVERAGE.md](COVERAGE.md) gives the precise scope.

## Start here

| Purpose | File or folder |
|---|---|
| See what is proved and what remains | [COVERAGE.md](COVERAGE.md) |
| Find the theorem for a manuscript result | [THEOREM_MAP.md](THEOREM_MAP.md) |
| Read the Lean proofs | [Analog/](Analog/) |
| Inspect verification results and source hashes | [verification/report.json](verification/report.json) |
| Read the proof explanations | [notes/](notes/) |

## Verify

Install Python 3, Git, and Lean through Elan. The checked-in `lean-toolchain`
selects **Lean 4.24.0**; `lake-manifest.json` pins mathlib and its dependencies.
From the repository root, run:

```sh
cd formalization
lake exe cache get
python3 verify.py
```

The script checks manuscript correspondence and the declaration inventory,
builds every module with warnings rejected, and runs `lean --trust=0 Audit.lean`.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed axioms. Results
are written to `verification/`; a failed run records a failure.

The saved audit applies to the source hashes in its report. Each
[GitHub Actions run](https://github.com/SaeedRazavikia/Optimal-Continuous-Analog-Encoders-TIT-/actions/workflows/verify-lean.yml)
has its own status. A passing audit certifies the Lean statements with their
hypotheses, not every claim in the paper.

## Updating proofs

After proof changes, run `python3 update_audit.py`, then `python3 verify.py`.
After manuscript changes, review the mathematics and coverage before running
`python3 check_manuscript.py --update`; this updates correspondence, not proofs.

The adapted topology proofs retain their
[provenance](notes/completion-topology.md) and
[third-party license](THIRD_PARTY_LICENSES/ClassificationOfSurfaces-LICENSE).
[runtime/](runtime/) documents the saved audit's environment; its adapter is
unnecessary on an ordinary Linux installation.
