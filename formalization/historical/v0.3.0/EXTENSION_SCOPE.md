# Scope of the current two-statistic model

The current manuscript has incorporated and broadened the former extension.
There is no current numbered `thm:extension`. Its main results use a separate
curve γ_k at every node and a shared pair of encoder columns with separate
offsets c_k. Current synthesis admits singular Gram blocks, dependent feature
families, and a zero optimal score.

`HeterogeneousScore` models this finite-input setup directly and proves the
actual attained-pair score characterization, including singular encoders.
`SingularGram` supplies generalized planar rank reduction, and
`HeterogeneousSynthesis` assembles every feasible SDP point into actual
continuous peak-feasible encoders with the guaranteed operational score. The old
`TwoStatisticDesign`, `TwoStatisticAttainment`, and `TwoStatisticPositivity`
modules retain stronger shared-curve assumptions. Their positive-attainment
results remain special cases, not the general current SDP theorem.

Current synthesis still needs the reduced coefficient compactness argument
for dependent features, attainment at zero as well as positive optimum, the
positive-optimum/Lipschitz equivalence, and the attained-optimum assembly.
The unrestricted continuous-class interpretation additionally needs rigidity.

Current statistical results are new in another respect: they optimize over
arbitrary Borel decoders. The old `GeneralSmallNoise` and `GaussianNoise`
modules establish decoder achievability for a restricted target family.
They do not contain the weighted van Trees converse or singular-limit argument.

See `COVERAGE.md` and `notes/current-*-audit.md` for precise current scope.
The old extension inventory is preserved only under `historical/v0.2.0/`.
