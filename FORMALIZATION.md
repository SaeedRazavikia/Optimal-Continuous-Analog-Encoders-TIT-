# Formal verification scope

Version 0.4.0 of [formalization/](formalization/) accompanies the current supplied
[Main.tex](Main.tex), *Geometric Optimization of Continuous Encoders for
Moment-Based Computation*. Its ten numbered statements and exact source hash are
recorded in [manuscript_targets.json](formalization/manuscript_targets.json).
The existing `manuscript.tex`, `sections/`, and compiled manuscript files belong
to the earlier repository revision; they are not the correspondence target of
this audit.

The four requested proof developments are complete:

- Full heterogeneous rigidity under the original assumptions, including proved
  planar topology, automatic regularity, common nonsingular columns and
  individual node offsets.
- General SDP attainment, including dependent features, singular Gram blocks,
  zero optimum and comparison with arbitrary continuous encoders.
- Gaussian fixed-prior, fixed-encoder minimax and optimized minimax limits over
  all Borel decoders, with changing-design and singular-limit converses and
  a fixed encoder and decoder attaining the optimum.
- General grid certification, including attained sampled and continuum optima,
  C2 remainder bounds, quadratic mesh gaps and finite PSD dual witnesses.

The local warning-free build and `lean --trust=0 Audit.lean` passed for
**1,198 public declarations in 100 modules**, using only `propext`,
`Classical.choice` and `Quot.sound`. The [verification report](formalization/verification/report.json)
records the source hashes and declaration dependencies. Repository CI runs the
same verification; its status is reported separately by GitHub Actions.

[THEOREM_MAP.md](formalization/THEOREM_MAP.md) identifies the principal Lean
declarations. [COVERAGE.md](formalization/COVERAGE.md) states the exact hypotheses
and remaining scope: the displayed minimum-decoder representation, specialized
score/parabola wrappers, general gradient sandwich, and individual examples and
numerical claims are not all formalized. The passed audit is not an assertion
that every manuscript statement is fully covered.

For pinned dependencies and reproduction commands, see
[formalization/README.md](formalization/README.md) and
[PUBLISH.md](formalization/PUBLISH.md).
