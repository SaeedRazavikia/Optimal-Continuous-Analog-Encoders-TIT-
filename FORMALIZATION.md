# Formal verification scope

The accompanying `formalization/` project contains the checked sources, `THEOREM_MAP.md`, the complete 18-statement inventory in `COVERAGE.md`, and the verification report with source hashes.

This revision adds the complete general operational score and shrinking-pair theorem, actual two-input moment paths, general operational reconstruction from PSD constraints, maximum-separation attainment, native local moment geometry and the fiber-to-affine rigidity chain, the dominated-convergence MSE limit and variance-decoder specialization, and substantial convex-frontier results.

The original variance optimization, quadratic/quartic certificates, sharp decoders, and implementation results are preserved. The main general score proof in the paper now follows the verified two-input path argument.

The remaining unrestricted continuous-encoder proof needs topological local factorization and automatic differentiability. The full general decoder-to-trace formula, complete inverse-form probabilistic frontier, certified-grid proof, and remaining appendix results also remain incomplete. The Lean-verification appendix and the acknowledgment accurately identify selected verified results.
