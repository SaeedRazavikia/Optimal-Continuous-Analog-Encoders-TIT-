# Compact outer-risk optimization

`Analog/CompactRiskOptimization.lean` proves the compactness step converting
sequential local risk converses into convergence of an actual infimum over
designs. It contains both unrestricted and admissible-subset forms. The
admissible-subset form is the one intended for identifiable Gaussian designs
inside a compact coefficient closure.

The principal theorem is
`admissible_outer_infimum_tendsto_of_eventual_upper`. Its conclusion is

```text
Tendsto (fun n => sInf ((fun p => r p n) '' {p | good p})) atTop (nhds m).
```

Its hypotheses are a compact metric ambient design space; real-valued,
nonnegative risk on the admissible class; a lower bound `m ≤ J p` for every
admissible design; one admissible design whose risks are eventually below
every `b > m`; and two sequential converse statements. For any sequence of
admissible designs converging in the ambient compact space, along any
strictly increasing noise-index subsequence, an admissible limit has the
local lower bounds below `J` of that limit, while an inadmissible limit has
risk diverging to positive infinity.

The admissible class need not be closed, compact, or open. Singular designs
are allowed only as limits in this theorem: neither local lower bounds nor
nonnegativity are demanded for singular designs at finite stages. The
admissible reference design guarantees that every risk image is nonempty.
The companion `admissible_outer_infimum_tendsto` accepts convergence of the
reference design's risk to `m`, which implies the needed upper estimates.

The proof does not assume a uniform local converse. If an eventual lower
bound for the outer infimum fails, it extracts infinitely many violating
indices. The conditional-infimum property supplies an actual admissible
design below the same threshold at each such index; exact finite-noise
minimizers are unnecessary. Compactness gives a convergent subsequence of
these designs, and composition preserves strict monotonicity of the noise
indices. The regular-limit converse or singular-limit divergence contradicts
the chosen threshold. This establishes the required uniform lower bound as
a conclusion. The reference design supplies the upper bound.

This module is an abstract assembly theorem. It does not itself prove the
Gaussian sequential risk converses, identify the coefficient objective, or
construct its minimizing design; those are separate, explicitly supplied
model-specific inputs. No continuity of finite-noise risk in the design and
no finite-noise optimizer are required.

Validation uses the pinned Lean toolchain and `--trust=0`. No admitted proofs,
added axioms, or native decision procedures are used.
