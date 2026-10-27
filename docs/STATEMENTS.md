# Paper statements and Lean proofs

A reading guide to [*It Takes Two Moments: Rigidity and Limits of Continuous
Encoders for Over-the-Air Computation*, arXiv:2610.21536v1](https://arxiv.org/abs/2610.21536v1)
by Saeed Razavikia. Each entry links the paper's statement and proof to the
corresponding checked Lean declarations.

These are concise mathematical summaries. The linked paper supplies the full
hypotheses and notation; the Lean declaration supplies the exact formal
statement. **Complete** means the correspondence described in
[COVERAGE.md](../formalization/COVERAGE.md) is complete. **Partial** identifies
a remaining translation or specialization step, rather than an admitted Lean
proof. All listed Lean declarations are included in the kernel audit.

| Paper result | Topic | Correspondence |
|---|---|---|
| [Theorem 1](#thm-rigidity) | Heterogeneous encoder rigidity | Complete |
| [Theorem 2](#thm-sdp) | Optimal SDP design and attainment | Complete |
| [Proposition 1](#prop-amplification) | Sharp uniform noise amplification | Complete |
| [Theorem 3](#thm-decoder) | Minimum-formula decoder | Partial |
| [Proposition 2](#prop-radius-minimax) | Bounded-noise minimax error | Complete |
| [Theorem 4](#thm-identifiable-minimax) | Gaussian minimax limits | Complete |
| [Proposition 3](#prop-general-small-noise) | Fixed-prior Gaussian limit | Statistical limit complete; decoder formula partial |
| [Lemma 1](#prop-score) | Endpoint formula for the score | Partial |
| [Proposition 4](#thm-parabola) | Quadratic and quartic designs | Partial |
| [Theorem 5](#thm-certifiedgrid) | Certified discretization | Complete |

## Notation used below

Inputs satisfy $s_k\in I=[-1,1]$. The two moments are
$m_j=K^{-1}\sum_k\phi_{j,k}(s_k)$, and the target is
$f(m)=\psi_1(m_1)+\psi_2(m_2)$. Write $\mathcal M_K$ for the attainable moment
set, $r_{\mathcal E}(s)=\sum_k\mathcal E_k(s_k)$ for the noiseless aggregate,
and $\Lambda(\mathcal E;f)$ for the infimum of squared received separation
divided by squared target separation over pairs with unequal target values.
For a common-column encoder, $U$ is its real two-by-two coefficient matrix,
$G=U^{\mathsf T}U$, and $w(m)=\nabla f(m)$.

<a id="thm-rigidity"></a>
## Theorem 1 — Heterogeneous rigidity

[Paper statement](https://arxiv.org/html/2610.21536v1#Thmtheorem1)
· [Paper proof: Appendix A-A](https://arxiv.org/html/2610.21536v1#A1.SS1)

For $K\ge4$, assume each local feature is continuous on $I$ and $C^1$ in its
interior, and each family $1,\phi_{1,k},\phi_{2,k}$ is linearly independent.
Each receiver function is continuous on its closed moment interval, $C^1$ in
the interior, and either affine everywhere or nonaffine on every open
subinterval. If both receiver functions are nonconstant and at least one is
nonaffine, continuous encoders permit exact identifiable computation iff

$$
\mathcal E_k(s)=c_k+u\phi_{1,k}(s)+v\phi_{2,k}(s),
$$

where the common columns $u,v\in\mathbb C$ are real-linearly independent.
No decoder regularity is assumed.

**Lean:** [`Analog.HeterogeneousFullRigidity.heterogeneous_rigidity`](../formalization/Analog/HeterogeneousFullRigidity.lean#L266).

**Proof route:** completion readouts recover both local moments; planar
invariance of domain gives local factorization; averaging proves encoder
regularity; derivative relations and endpoint integration produce common
columns and separate offsets. Exact recovery forces the columns to be
nonsingular. **Correspondence: complete.**

<a id="thm-sdp"></a>
## Theorem 2 — Exact SDP design and attainment

[Paper statement](https://arxiv.org/html/2610.21536v1#Thmtheorem2)
· [Paper proof: Appendix A-B](https://arxiv.org/html/2610.21536v1#A1.SS2)

For $K\ge2$, $P>0$, continuous local/receiver functions, and nonconstant $f$,
the maximum robustness over peak-feasible common-column encoders is
$K^2\lambda_\star$. The optimum $\lambda_\star$ is attained by the paper's
PSD program: node matrices $H_k\succeq0$ share a lower block $G$, satisfy every
continuum peak constraint, and obey

$$
(m-m')^{\mathsf T}G(m-m')\ge\lambda\,|f(m)-f(m')|^2
\quad(m,m'\in\mathcal M_K).
$$

The optimum is positive iff $f$ is Lipschitz on $\mathcal M_K$. Under Theorem 1's
assumptions, it also optimizes over all continuous peak-feasible encoders.

**Lean:** [`Analog.HeterogeneousAttainment.heterogeneous_sdp_attained`](../formalization/Analog/HeterogeneousAttainment.lean#L350),
[`Analog.HeterogeneousAttainment.optimal_positive_iff_euclidean_lipschitz`](../formalization/Analog/HeterogeneousAttainment.lean#L566),
and [`Analog.HeterogeneousGlobalOptimum.unrestricted_sdp_attained`](../formalization/Analog/HeterogeneousGlobalOptimum.lean#L102).

**Proof route:** reconstruct physical planar encoders from PSD blocks without
increasing peak power; identify their operational score with the secant
constraints; obtain attainment by compactness in the space of actual encoder
functions. Rigidity handles arbitrary positive-score competitors.
Singular blocks, dependent features, and zero optimum are included.
**Correspondence: complete.**

<a id="prop-amplification"></a>
## Proposition 1 — Sharp uniform noise amplification

[Paper statement](https://arxiv.org/html/2610.21536v1#Thmproposition1)
· [Paper proof: Appendix B-A](https://arxiv.org/html/2610.21536v1#A2.SS1)

For continuous encoders and a continuous nonconstant target, the least uniform
noise-amplification constant is

$$L_{\mathcal E}=\Lambda(\mathcal E;f)^{-1/2}.$$

A continuous decoder attains the bound when the score is positive. At zero
score, no decoder has a finite uniform constant.

**Lean:** [`Analog.Decoder.sharp_uniform_decoder`](../formalization/Analog/Amplification.lean#L124) and
[`Analog.Decoder.zero_score_no_finite_uniform_decoder`](../formalization/Analog/Amplification.lean#L146).

**Proof route:** any uniform guarantee bounds target differences by received
separation. Conversely, a Lipschitz extension of the noiseless readout achieves
the sharp bound. The zero-score result is expressed without treating infinity
as a real number. **Correspondence: complete.**

<a id="thm-decoder"></a>
## Theorem 3 — A decoder given by a minimum

[Paper statement](https://arxiv.org/html/2610.21536v1#Thmtheorem3)
· [Paper proof: Appendix B-B](https://arxiv.org/html/2610.21536v1#A2.SS2)

Under Theorem 2's assumptions, a positive-score common-column encoder has the
paper's decoder

$$
D(y)=\min_{m\in\mathcal M_K}\{f(m)+L_{\mathcal E}\|y-Kc-KUm\|_2\},
$$

where $c$ is the average node offset. It is exact without noise and satisfies
$|D(r_{\mathcal E}(s)+z)-f(s)|\le L_{\mathcal E}|z|$.

**Lean:** [`Analog.Decoder.pairwise_exists_lipschitz`](../formalization/Analog/Decoder.lean#L50),
[`Analog.Decoder.sharp_uniform_decoder`](../formalization/Analog/Amplification.lean#L124), and [`Analog.Decoder.clip_uniform`](../formalization/Analog/Decoder.lean#L111).

**Proof route:** extend the Lipschitz noiseless readout to all received values;
the extension gives the sharp uniform bound, which is preserved by output
clipping. **Correspondence: partial.** Existence and the bound are checked;
a dedicated theorem identifying this extension with the displayed minimum
over the current compact moment set remains to be assembled.

<a id="prop-radius-minimax"></a>
## Proposition 2 — Minimax error for bounded noise

[Paper statement](https://arxiv.org/html/2610.21536v1#Thmproposition2)
· [Paper proof: Appendix B-C](https://arxiv.org/html/2610.21536v1#A2.SS3)

For a fixed continuous encoder, continuous target, and noise bound $|z|\le r$,
define $\omega_{\mathcal E}(d)$ as the largest target difference between
admissible input pairs whose noiseless aggregates are at distance at most $d$.
Then

$$\inf_D\sup_{s,\,|z|\le r}|D(r_{\mathcal E}(s)+z)-f(s)|
=\tfrac12\omega_{\mathcal E}(2r).$$

The midpoint of the smallest and largest target values consistent with an
observation attains this error.

**Lean:** [`Analog.RadiusMinimax.borel_radius_minimax`](../formalization/Analog/RadiusMinimax.lean#L392).

**Proof route:** a maximizing input pair gives an indistinguishability lower
bound; compactness supplies consistent target extrema, and their midpoint
is a Borel decoder attaining it. Radius zero and nonidentifiable maps are
included. **Correspondence: complete.**

<a id="thm-identifiable-minimax"></a>
## Theorem 4 — Gaussian minimax limits

[Paper statement](https://arxiv.org/html/2610.21536v1#Thmtheorem4)
· [Paper proof: Appendix C-A](https://arxiv.org/html/2610.21536v1#A3.SS1)

Assume the paper's $C^1$ receiver conditions and
$\mathcal M_K=\overline{\operatorname{int}\mathcal M_K}$. For each fixed
peak-feasible encoder with nonsingular common columns, the best worst-case
Gaussian MSE over all Borel decoders satisfies

$$
\lim_{\sigma_z^2\downarrow0}\frac{\inf_D R_{\max}(\mathcal E,D;\sigma_z^2)}{\sigma_z^2}
=\frac{1}{2K^2}\max_{m\in\mathcal M_K}w(m)^{\mathsf T}G^{-1}w(m).
$$

If every local feature family is independent and the interior gradient vectors
span $\mathbb R^2$, optimizing over encoders gives the attained minimum of this
coefficient. A single encoder and decoder, independent of noise power, attain
it; allowing noise-dependent designs does not improve it.

**Lean:** [`Analog.GaussianFixedMinimax.fixed_encoder_minimax`](../formalization/Analog/GaussianFixedMinimax.lean#L185) and
[`Analog.GaussianOptimizedMinimax.heterogeneous_optimized_minimax_achieved`](../formalization/Analog/GaussianOptimizedMinimax.lean#L506).

**Proof route:** local-prior lower bounds and endpoint-decoder upper bounds
identify the fixed-design limit. Compactness, changing-Gram converses, and
singular-limit exclusion justify the outer optimization. The physical channel
factor $K$ and total complex-noise normalization are retained.
**Correspondence: complete.**

<a id="prop-general-small-noise"></a>
## Proposition 3 — Fixed-prior Gaussian limit

[Paper statement](https://arxiv.org/html/2610.21536v1#Thmproposition3)
· [Paper proof: Appendix C-B](https://arxiv.org/html/2610.21536v1#A3.SS2)

Under the same $C^1$ receiver assumptions, fix a nonsingular encoder and a
regular moment prior $\pi$—with a positive $C^1$ density on an open, full-mass interior region—the optimum average MSE over
all Borel decoders has leading coefficient

$$
\lim_{\sigma_z^2\downarrow0}\frac{\inf_D R_\pi(\mathcal E,D;\sigma_z^2)}{\sigma_z^2}
=\frac{1}{2K^2}\operatorname{tr}\!\left(G^{-1}\mathbb E_\pi[ww^{\mathsf T}]\right).
$$

**Lean:** [`Analog.FixedPriorGaussianLimit.fixed_prior_limit_inverse_trace`](../formalization/Analog/FixedPriorGaussianLimit.lean#L332)
and [`Analog.FixedPriorGaussianLimit.exact_decoder_prior_limit`](../formalization/Analog/FixedPriorGaussianLimit.lean#L349).

**Proof route:** Gaussian score identities, local information inequalities,
and smooth-test approximation prove the converse, including infinite-risk
Borel decoders. Every fixed exact globally Lipschitz decoder attains the same
coefficient. **The statistical limit is complete.** The paper names the
minimum-formula decoder of Theorem 3; identifying that precise representation
is the remaining correspondence step, so the full entry is marked **partial**.

<a id="prop-score"></a>
## Lemma 1 — Endpoint formula for the score

[Paper statement](https://arxiv.org/html/2610.21536v1#Thmlemma1)
· [Paper proof: Appendix D-A](https://arxiv.org/html/2610.21536v1#A4.SS1)

For $K\ge4$, shared features $(s,\phi(s))$, target $f(m)=m_2-\psi(m_1)$,
and the paper's strictly convex/concave shape and differentiability assumptions
on $\phi,\psi$, an
encoder $\mathcal E_k(s)=c_k+us+v\phi(s)$ with $G\succ0$ satisfies

$$
\Lambda(\mathcal E;f)=\frac{K^2}{\max_{j\in\{-,+\}}w_j^{\mathsf T}G^{-1}w_j},
\qquad w_\pm=(-\psi'(\pm1),1)^{\mathsf T}.
$$

Admissible pairs with received distance tending to zero approach the infimum.

**Lean:** [`Analog.GeneralScore.general_operational_score`](../formalization/Analog/GeneralScore.lean#L489) and
[`Analog.GeneralScore.general_score_small_distance_sharpness`](../formalization/Analog/GeneralScore.lean#L516).

**Proof route:** a dual-norm bound reduces the upper coefficient to endpoint
slopes; moving two actual transmitter inputs constructs the sharpness pairs.
**Correspondence: partial.** The shared-feature result is checked, but its
wrapper for the current finite-node model with arbitrary node offsets remains
unassembled.

<a id="thm-parabola"></a>
## Proposition 4 — Quadratic and quartic optimal encoders

[Paper statement](https://arxiv.org/html/2610.21536v1#Thmproposition4)
· [Paper proof: Appendix D-B](https://arxiv.org/html/2610.21536v1#A4.SS2)

For $K\ge4$, $P>0$, and an even $C^1$ strictly convex or strictly concave
receiver function $\psi$, put $M=|\psi'(1)|$ and $f(m)=m_2-\psi(m_1)$.
The paper gives explicit globally
robustness-optimal shared encoders for features $s^2$ and $s^4$:

$$
\mathcal E_2^\star(s)=\sqrt P\,[as+i(bs^2-1)],\qquad
\mathcal E_4^\star(s)=\sqrt P\,[a_\rho s+i(b_\rho s^4+c_\rho)].
$$

The quadratic parameters are explicit radicals. The quartic parameters are
explicit functions of the unique $\rho\in(0,1/3)$ satisfying
$8\rho^2(1+\rho)(1+3\rho)=M^2(1-3\rho)$; the linked paper gives all formulas.

**Lean:** [`Analog.quadratic_optimal_all_power`](../formalization/Analog/PowerScaling.lean#L75),
[`Analog.GeneralQuadratic.optimalParameter_manuscript`](../formalization/Analog/GeneralQuadratic.lean#L220), and
[`Analog.Quartic.quartic_optimal_all_power`](../formalization/Analog/QuarticPower.lean#L85).

**Proof route:** polynomial peak identities and convex optimality certificates
establish coefficient-Gram optima, then power scaling restores arbitrary $P$.
**Correspondence: partial.** These optima and parameter formulas are checked;
the complete wrapper for the paper's general even readout, offset averaging,
and comparison with every continuous encoder collection remains separate.

<a id="thm-certifiedgrid"></a>
## Theorem 5 — Certified discretization

[Paper statement](https://arxiv.org/html/2610.21536v1#Thmtheorem5)
· [Paper proof: Appendix D-C](https://arxiv.org/html/2610.21536v1#A4.SS3)

Assume $K\ge1$, $P>0$, $C^2$ node features with each family
$1,\phi_{1,k},\phi_{2,k}$ independent, and a continuous nonconstant target.
Each grid contains both endpoints and three fixed spanning feature samples.
Only the peak constraints are sampled; every moment-pair secant is retained.
For maximum mesh spacing $h$, the sampled optimum $\lambda_h$ is attained.
A proved second-derivative bound $M_h$ gives the common scaling

$$
\rho_h=\frac{P}{P+M_hh^2/8},\qquad
\rho_h\lambda_h\le\lambda_\star\le\lambda_h,\qquad
\lambda_h-\rho_h\lambda_h=O(h^2).
$$

The scaled matrices reconstruct peak-feasible encoders with score at least
$K^2\rho_h\lambda_h$. Under Theorem 1's assumptions the bracket also certifies
the optimum over all continuous peak-feasible encoders.

**Lean:** [`Analog.HeterogeneousGrid.certified_discretization`](../formalization/Analog/HeterogeneousGrid.lean#L257),
[`Analog.HeterogeneousGrid.scaling_gap_isBigO`](../formalization/Analog/HeterogeneousGrid.lean#L198), and
[`Analog.HeterogeneousGlobalOptimum.grid_maximum_global_bound`](../formalization/Analog/HeterogeneousGlobalOptimum.lean#L81).

**Proof route:** spanning samples bound the feasible matrices; compactness gives
attainment; the sharp $1/8$ interpolation bound controls between-grid peaks;
one common scaling preserves every secant constraint. Uniform bounds yield
the quadratic gap and operational reconstruction. **Correspondence: complete.**

## Checking a correspondence

Open a linked paper statement, then its Lean declaration and assumptions.
Use [THEOREM_MAP.md](../formalization/THEOREM_MAP.md) for intermediate lemmas
and [COVERAGE.md](../formalization/COVERAGE.md) for precise remaining scope.
The proof audit verifies Lean terms; it does not automatically prove that a
prose summary or paper statement is logically equivalent to those terms.
