# Complete manuscript proof coverage inventory

Status: **the manuscript is not fully formalized**. This inventory covers the 18 numbered mathematical results reachable from `paper/manuscript.tex`, including the unlabeled criterion-transfer corollary. The theorem statements below are exact extracts from the reorganized paper; the context column records assumptions and definitions stated outside their theorem environments. Numbering follows source order and is not a promise that numerical theorem numbers will remain unchanged after editing.

This is a coverage inventory, not a proof certificate. For newly integrated files, the final `Audit.lean`, `verify.py`, and saved verification report determine which declarations were actually checked. A checked specialization, algebraic certificate, or conditional lemma does not mark its broader manuscript theorem complete.

## Coverage at the level of complete manuscript statements

| Source order | Result | Current coverage |
|---|---|---|
| 1 | `thm:rigidity` | Full affine-family exactness equivalence and conditional necessity checked; unrestricted continuous theorem incomplete. |
| 2 | `thm:sdp` | General operational reconstruction and positive maximum attainment checked; full continuous-class equivalence incomplete. |
| 3 | `thm:parabola` | Full quadratic operational variance optimum checked for all P>0,K≥2; general-M Gram optimum checked; continuous-class theorem remains incomplete. |
| 4 | `thm:quartic` | Complete finite-dimensional quartic Gram optimum checked for every M>0,P>0; operational and continuous-class parts unverified. |
| 5 | `prop:amplification` | Full operational content checked via attained-minimum and zero-score statements. |
| 6 | `thm:decoder` | Complete explicit quadratic-variance decoder checked; full general-target decoder theorem remains unverified. |
| 7 | `prop:general-small-noise` | Actual dominated-convergence limit and variance-decoder specialization checked; complete general trace formula incomplete. |
| 8 | `thm:pareto` | Attained Gram frontier, convexity, monotonicity, uniqueness and qualitative branches checked; full original frontier theorem incomplete. |
| 9 | `cor:quadratic-pareto` | Quadratic optimizer and parameter facts checked; constrained stochastic frontier remains unverified. |
| 10 | `thm:certifiedgrid` | Unverified in full. |
| 11 | `lem:collision` | Complete general statement checked, under weaker regularity assumptions. |
| 12 | `lem:topology` | Conditional open-slice argument checked; original theorem unverified. |
| 13 | `lem:affine` | Local-fiber-to-affine representation and coefficient independence checked; unrestricted continuity-to-rigidity reduction incomplete. |
| 14 | `prop:score` | Complete general operational formula and shrinking-pair statement checked. |
| 15 | `cor:inverse-synthesis` | Unverified in full. |
| 16 | `thm:polynomial` | Unverified in full. |
| 17 | `cor:transfer-unlabeled` | Unverified in full. |
| 18 | `prop:approx-rigidity` | Unverified in full. |

## Exact statements, hypotheses, and dependencies

### 1. `thm:rigidity` — theorem

Source: `sections/rigidity.tex`. **Full affine-family exactness equivalence and conditional necessity checked; unrestricted continuous theorem incomplete.**

**Context and hypotheses.** K≥4; I=[−1,1]; φ continuous on I, C¹ in the interior, nonaffine; ψ continuous on I, C¹ in the interior, strictly convex/concave. E is a continuous planar encoder. Exact computation means equality of received sums implies equality of the target.

```latex
\begin{theorem}
\label{thm:rigidity}
Let $K\ge4$. Assume $\phi\in C(I)\cap C^1((-1,1))$ is nonaffine and $\psi\in C(I)\cap C^1((-1,1))$ is strictly convex or strictly concave. A continuous planar encoder exactly computes \eqref{eq:target} if and only if
\begin{equation}
 \enc(s)=c+u s+v\phi(s),
 \qquad c,u,v\in\R^2,
 \label{eq:affine}
\end{equation}
with $u,v$ linearly independent in the real plane.
\end{theorem}
```

**Dependencies.** Lemmas lem:collision and lem:affine for necessity. Invertibility of the coefficient map (S,T)↦uS+vT for sufficiency, followed by the prescribed scalar readout.

**Verified scope and remaining gap.** `Analog.RigidityCompletion.FeatureEncoder.exact_iff_det_ne_zero_of_nonaffine` proves exactness iff independent directions for affine-feature encoders under the manuscript feature/readout hypotheses. `Analog.RigidityAnalysis.rigid_representation_of_local_fibers` proves necessity for an actual continuous exact encoder once its interior differentiability and local moment-fiber constancy are supplied. Actual channel congruence on the full source interval is checked. No final theorem derives both remaining hypotheses from continuity and exactness alone.

### 2. `thm:sdp` — theorem

Source: `sections/synthesis.tex`. **General operational reconstruction and positive maximum attainment checked; full continuous-class equivalence incomplete.**

**Context and hypotheses.** K≥4, P>0; φ and ψ satisfy the stronger score assumptions in the Optimal Design subsection. The theorem now includes the score identity and shrinking-pair clause, supported by prop:score in the design-proof appendix. z(s)=(1,s,φ(s)); H is a symmetric 3×3 positive-semidefinite matrix; G is its lower-right 2×2 block. The objective is λ≥0, peak inequalities hold for every s∈I, and both rank-one score matrix inequalities hold.

```latex
\begin{theorem}
\label{thm:sdp}
Let $K\ge4$ and $P>0$, and impose the assumptions of this subsection. For every encoder \eqref{eq:affine} with independent $u,v$,
\begin{equation}
 \Lambda_{\sq}(\enc;f_{\phi,\psi})
 =\frac{K^2}{\max\{w_-^\T G^{-1}w_-,\;w_+^\T G^{-1}w_+\}}.
 \label{eq:exactscore}
\end{equation}
The infimum is approached at arbitrarily small received distance. The global optimum over all continuous peak-admissible encoders is $K^2\lambda_\star$, where $\lambda_\star$ is the optimum of
\begin{equation}
\begin{aligned}
 \text{maximize}\quad &\lambda\\
 \text{over}\quad &H\in\mathbb S^3,\quad\lambda\ge0,\\
 \text{subject to}\quad
 &H\suc0,\\
 &z(s)^\T H z(s)\le P\quad\text{for every }s\in[-1,1],\\
 &G-\lambda w_-w_-^\T\suc0,\\
 &G-\lambda w_+w_+^\T\suc0.
\end{aligned}
\label{eq:sdp}
\end{equation}
where $z(s)=(1,s,\phi(s))^\T$ and $G$ is the lower-right $2\times2$ block of $H$. This is a convex semidefinite problem with seven real variables and a continuum of scalar peak constraints. Its optimum is attained and yields an exact planar encoder.
\end{theorem}
```

**Dependencies.** Theorem thm:rigidity; Proposition prop:score; Schur complement equivalence; positivity of G from independent endpoint slopes; rank-two Gram reconstruction by reducing the translation diagonal; a positive feasible point; compactness from three spanning feature vectors; attainment.

**Verified scope and remaining gap.** `Analog.GeneralDesign.positive_sdp_operational_synthesis` combines genuine PSD/Schur reconstruction with the general operational score: every positive feasible SDP point yields a continuous, exact planar curve with the entire peak constraint and actual score at least K²λ. Independence of endpoint directions follows from strict curvature of the mean-dependent term. `Analog.SynthesisAttainment` derives spanning anchors from strict feature curvature and a positive feasible design from continuity and P>0. It derives coordinate bounds from actual anchor evaluations, proves the continuum feasible set closed and compact, and proves positive maximum-separation attainment with an operational realization. Its `operational_maximum_attained` compares the positive continuous exact optimizer against all affine-feature coefficient curves, including singular and constant curves; `positive_score_implies_positive_gram` handles those competitors without assuming their nondegeneracy. The general continuous-class upper bound still requires unrestricted rigidity; additional final interfaces and hypotheses are listed in THEOREM_MAP.md.

### 3. `thm:parabola` — theorem

Source: `sections/examples.tex`. **Full quadratic operational variance optimum checked for all P>0,K≥2; general-M Gram optimum checked; continuous-class theorem remains incomplete.**

**Context and hypotheses.** K≥4, P>0; φ(s)=s²; ψ∈C¹(I) is even and strictly convex or strictly concave; M=|ψ′(1)|>0, t=M/2, b=2/(1−t²+t√(t²+2)), a=√(b(2−b)). Competitors are all continuous shared peak-admissible encoders.

```latex
\begin{theorem}
\label{thm:parabola}
For every $K\ge4$, an optimal encoder for $f=Q/K-\psi(S/K)$ over all continuous peak-admissible maps is
\begin{equation}
\begin{aligned}
 \enc^\star(s)&=\sqrt P\,[a s+i(bs^2-1)],\\
 \Lambda_{\sq}^\star(f)&=K^2P\,b^2(b-1).
\end{aligned}
 \label{eq:parabola}
\end{equation}
Thus an infinite-dimensional class of nonlinear mean-dependent terms has an explicit optimal encoder determined by $M$ alone.
\end{theorem}
```

**Dependencies.** Theorem thm:rigidity; Proposition prop:score; reflection/translation projection or an equivalent direct algebraic converse; all-interval peak identity; minimization of M²/[b(2−b)]+1/b²; explicit root formula; P and K² scaling; exclusion of nonexact competitors.

**Verified scope and remaining gap.** `Analog.GeneralQuadratic` proves the complete finite-dimensional quadratic Gram optimum for every M>0, including root existence, uniqueness, the closed formula, and its identity with the manuscript parameter. `Analog.quadratic_optimal_all_power` extends that optimization to every P>0. For variance M=2, `Analog.quadratic_variance_operational_optimal` connects the actual all-pair score and proves continuum peak feasibility, the attained value 4K²P/(9+6√3), and the converse over every planar quadratic encoder, for all K≥2 and P>0. The remaining gaps are the reduction of every continuous encoder to that coefficient class and the operational score theorem for general ψ; neither follows merely from the full coefficient optimization.

### 4. `thm:quartic` — theorem

Source: `sections/examples.tex`. **Complete finite-dimensional quartic Gram optimum checked for every M>0,P>0; operational and continuous-class parts unverified.**

**Context and hypotheses.** K≥4, P>0; φ(s)=s⁴; ψ even and strictly convex/concave with finite continuous derivative, M=|ψ′(1)|>0. ρ is the unique root in (0,1/3) of 8ρ²(1+ρ)(1+3ρ)=M²(1−3ρ). dρ=1+2ρ+9ρ²; aρ²=8ρ/dρ; bρ=2/[(1+ρ)√dρ]; cρ=−(1+2ρ+3ρ²)/[(1+ρ)√dρ].

```latex
\begin{theorem}
\label{thm:quartic}
For every $K\ge4$, an optimal continuous encoder for $K^{-1}\sum_k s_k^4-\psi(S/K)$ is
\begin{equation}
 \boxed{\enc^\star(s)=\sqrt P\,[a_\rho s+i(b_\rho s^4+c_\rho)]}.
 \label{eq:quarticmap}
\end{equation}
Its optimal squared separation is
\begin{equation}
 \boxed{\Lambda_{\sq}^\star
 =\frac{K^2P}{M^2/a_\rho^2+1/b_\rho^2}
 =\frac{8K^2P\rho}
 {d_\rho\,[M^2+2\rho(1+\rho)^2]}}.
 \label{eq:quarticscore}
\end{equation}
\end{theorem}
```

**Dependencies.** Theorem thm:rigidity; Proposition prop:score; reflection/projection reduction; root existence and uniqueness; coefficient identities; factorized continuum peak gap; positive KKT multipliers; convex global supporting certificate; arbitrary-power and transmitter scaling.

**Verified scope and remaining gap.** `Analog.Quartic` in `Quartic.lean` and `QuarticPower.lean` proves root existence/uniqueness in (0,1/3), the coefficient relations, continuum peak feasibility, the KKT/supporting certificate, and the converse over every planar quartic coefficient curve, including arbitrary correlation. `quartic_optimal_all_power` covers every M>0,P>0 and the exact displayed normalized Gram value. Multiplying the Gram inequality by K² is checked separately and is explicitly not an identification with an operational score. The full theorem still requires unrestricted rigidity and the quartic/general-readout operational-score correspondence.

### 5. `prop:amplification` — proposition

Source: `sections/decoding.tex`. **Full operational content checked via attained-minimum and zero-score statements.**

**Context and hypotheses.** Any continuous encoder on the compact source cube; nonconstant continuous scalar target. A is the infimum over constants L≥0 for which one decoder obeys the uniform disturbance inequality at every input and every n∈ℝ². A=+∞ when no finite constant exists. Λ is operational squared separation, with 0^(−1/2)=+∞.

```latex
\begin{proposition}\label{prop:amplification}
For any continuous encoder and nonconstant continuous scalar target,
$$\mathcal A(\enc;f)=\Lambda_\sq(\enc;f)^{-1/2},$$
with $0^{-1/2}=+\infty$. A continuous decoder attains every finite value.
\end{proposition}
```

**Dependencies.** Uniform guarantee implies exactness and pairwise Lipschitz inequality; well-defined received-set readout; compactness; McShane extension preserving the optimal Lipschitz constant; infimum/supremum identity including Λ=0; continuity and attainment of finite constants; scalar output clipping.

**Verified scope and remaining gap.** `Analog.Decoder.sharp_uniform_decoder` proves existence of a globally Lipschitz continuous exact decoder whose uniform constant is 1/√Λ, and proves this constant no larger than any finite uniform constant for any other decoder. `finite_uniform_decoder_iff_positive_score` and `zero_score_no_finite_uniform_decoder` establish the zero-score/infinite-required-amplification case. The metric theorem covers arbitrary received maps and nonconstant real targets, a larger class than the manuscript. The extended-real symbol A itself is not introduced as a separate formal infimum: the source proves the equivalent attained-minimum statement when finite and impossibility of every finite constant when Λ=0. `Analog.Decoder.uniform_iff_additive_noise` gives the additive-disturbance formulation, and `Analog.ArbitraryEncoder.asComplex_squared_distance` verifies that the complex metric is precisely the manuscript Euclidean cost. Its variance bridge connects this metric score to the actual list-based multiple-access variance score. Scalar clipping is covered by `Analog.Decoder.clip_uniform`.

### 6. `thm:decoder` — theorem

Source: `sections/decoding.tex`. **Complete explicit quadratic-variance decoder checked; full general-target decoder theorem remains unverified.**

**Context and hypotheses.** Theorem uses the score assumptions of thm:sdp, an invertible coefficient matrix U=[u v], G=UᵀU, and the prescribed metric strip projection: transform received y to (m̃,t̃), clip m̃ to [−1,1], correct t̃ by G12/G22·(m̃−m̂), then output t̂−ψ(m̂).

```latex
\begin{theorem}\label{thm:decoder}
Under the assumptions of Theorem~\ref{thm:sdp}, \eqref{eq:stripdecoder} is exact and attains the smallest possible uniform constant
\begin{equation}
 L_\enc=\frac1K\sqrt{\max_{\sigma\in\{-,+\}}w_\sigma^\T G^{-1}w_\sigma}
 =\Lambda_\sq(\enc;f)^{-1/2}.
 \label{eq:decoderconstant}
\end{equation}
An additional scalar projection onto an interval containing the target range preserves this conclusion.
\end{theorem}
```

**Dependencies.** Closed-form minimizer of G-metric strip projection via the positive Schur complement; nonexpansiveness of Euclidean projection on its received image; endpoint gradient bound and line integration; noiseless exactness; Propositions prop:score and prop:amplification for optimality; optional scalar clipping.

**Verified scope and remaining gap.** `Analog.Strip.project_unique_minimizer` verifies the actual correlated clipping-and-correction formula as the unique minimizer over the unbounded moment strip; `project_squared_nonexpansive` proves nonexpansiveness in squared Gram distance. `variance_readout_squared_bound`, `projected_variance_squared_bound`, and `projected_variance_error` prove the variance readout bound on the entire strip and after projection. `Analog.Curve.explicitVarianceDecoder_optimal` now proves the assembled received-coordinate variance decoder: the actual complex-plane inverse, corrected projection, exactness for every valid tuple, global Lipschitz continuity, all-complex-disturbance guarantee, and minimality among all decoders, for every nondegenerate quadratic curve and K≥2. These variance results do not yet cover general ψ, its endpoint-gradient bound, or the full theorem under arbitrary feature/readout assumptions. The generic sharp amplification and clipping results are already checked as recorded under Proposition prop:amplification.

### 7. `prop:general-small-noise` — proposition

Source: `sections/pareto.tex`. **Actual dominated-convergence limit and variance-decoder specialization checked; complete general trace formula incomplete.**

**Context and hypotheses.** The synthesis assumptions hold. The input prior satisfies |m|<1 almost surely; Qπ=E[w(m)w(m)ᵀ] is positive definite. Noise is independent circular complex Gaussian CN(0,N0). The decoder is the prescribed strip projection/readout, with optional clipping locally inactive at the true target almost surely. G is the feature Gram matrix of any continuous exact peak-admissible encoder.

```latex
\begin{proposition}\label{prop:general-small-noise}
For every continuous exact peak-admissible encoder, let $G$ be its feature Gram matrix. If $N\sim\mathcal{CN}(0,N_0)$, then the specified decoder satisfies
\begin{equation}
 \mathcal J_\pi(G):=\lim_{N_0\downarrow0}
 \frac{\mathbb E_{\pi,N}|\widehat f(Y)-f(\mathbf s)|^2}{N_0}
 =\frac{\operatorname{tr}(Q_\pi G^{-1})}{2K^2}.
 \label{eq:general-small-noise}
\end{equation}
\end{proposition}
```

**Dependencies.** Theorem thm:rigidity; local inactivity of projection and permitted clipping; differentiability of the received readout; coupling N=√N0 Z; Gaussian covariance I2/2; pointwise small-noise limit; integrable uniform domination from Theorem thm:decoder; dominated convergence and trace/expectation identities.

**Verified scope and remaining gap.** `Analog.SmallNoise.leading_mse_power_exact` proves the actual MSE/noise-power limit for a measurable nominal signal and disturbance with finite second moment, a globally Lipschitz decoder, exactness, and its almost-sure Fréchet derivative. The limiting squared derivative is proved integrable. `variance_leading_mse` derives differentiability of the actual complex variance decoder at interior recovered means rather than assuming it. Independent product-measure covariance evaluation and the isotropic one-half factor are verified, as is the inverse-Gram gradient-energy identity. The complete general strip/clipping gradient and trace-formula specialization, Gaussian-law moment derivation, and continuous-encoder reduction remain unassembled. The variance specialization still states exactness of the random nominal signal explicitly; the deterministic exactness theorem supplies it for valid input lists.

### 8. `thm:pareto` — theorem

Source: `sections/pareto.tex`. **Attained Gram frontier, convexity, monotonicity, uniqueness and qualitative branches checked; full original frontier theorem incomplete.**

**Context and hypotheses.** The preceding prior and synthesis hypotheses hold, Qπ positive definite; 0≤γ≤λ⋆. At γ>0, minimize tr(Qπ X)/(2K²) over the five ellipse variables with endpoint budgets w±ᵀXw±≤1/γ; omit those budgets at γ=0. γ_c is the reciprocal of the maximum endpoint budget at the unconstrained minimizer X0.

```latex
\begin{theorem}[Exact frontier]\label{thm:pareto}
Using the enclosing-ellipse class $\mathcal C_P$ in \eqref{eq:ellipse-class}, for $\gamma>0$ we obtain $\mathcal V_\pi(\gamma)$ from the five-variable convex program
\begin{equation}
\begin{aligned}
 \text{minimize}\quad &\frac{\operatorname{tr}(Q_\pi X)}{2K^2}\\
 \text{over}\quad &X\in\mathbb S^2,\quad a\in\R^2,\\
 \text{subject to}\quad
 &(X,a)\in\mathcal C_P,\\
 &w_\sigma^\T Xw_\sigma\le\gamma^{-1}
       \quad(\sigma\in\{-,+\}).
\end{aligned}
 \label{eq:pareto-sdp}
\end{equation}
At $\gamma=0$, we omit the last two inequalities. An optimum exists, has a unique inverse feature Gram matrix $X$, and yields an exact planar encoder through
$$
 \mathsf U^\T\mathsf U=X^{-1},\qquad
 \enc(s)=\mathsf U(g(s)-a).
$$
The value is finite, continuous, convex, and nondecreasing on $[0,\lambda_\star]$.

Let $X_0$ minimize \eqref{eq:pareto-sdp} at zero floor, and set
$$
 \gamma_c=\left(\max_{\sigma\in\{-,+\}}
 w_\sigma^\T X_0w_\sigma\right)^{-1}.
$$
The frontier is constant on $[0,\gamma_c]$. The encoder minimizing average small-noise error already meets every separation requirement in this interval. If $\gamma_c<\lambda_\star$, it is strictly increasing thereafter, and every optimal encoder on that branch satisfies $\Lambda_\sq=K^2\gamma$.
\end{theorem}
```

**Dependencies.** Corollary cor:inverse-synthesis; Propositions prop:score and prop:general-small-noise; positive-definite compact objective sublevels; attained optimum; strict convexity of tr(QG^(−1)); uniqueness of optimal Gram matrix; Gram-form convexity in floor γ; nested feasible sets; endpoint continuity via compactness; active-floor mixing argument; strict growth above the constant portion.

**Verified scope and remaining gap.** `Analog.Frontier` proves genuine PSD and continuum-peak feasibility convexity, inverse-Gram risk strict convexity, and convexity/monotonicity of the actual feasible-design infimum. It proves uniqueness, the exact plateau threshold, floor activity, and strict increase with explicit optimizer witnesses where required. It also reconstructs planar feasible curves. Its risk parameters correspond to μ=E[-ψ′(m)] and v=Var(ψ′(m)), so Q=[[v+μ²,μ],[μ,1]], and endpoint directions use -ψ′(±1). These signs matter for asymmetric input distributions. `Analog.FrontierAttainment.frontier_attained_on_maximal_interval` now supplies actual optimizer existence at every feasible floor including zero from the original strict feature shape, continuity, positive power/variance and distinct endpoint directions; it proves the determinant barrier det G≥v/R² on risk sublevels and derives compactness. Thus the optimizer witnesses required by the qualitative branches are available. Endpoint continuity, the five-variable inverse-form equivalence, the general probabilistic trace connection, and unrestricted continuous-encoder equivalence remain separate obligations.

### 9. `cor:quadratic-pareto` — corollary

Source: `sections/pareto.tex`. **Quadratic optimizer and parameter facts checked; constrained stochastic frontier remains unverified.**

**Context and hypotheses.** φ(s)=s²; ψ even; distribution of m symmetric; 0<M_eff=√E[ψ′(m)²]<M=|ψ′(1)|. b(x) is the stated positive-slope quadratic optimizer; R_M(b)=[M²/(b(2−b))+1/b²]^(−1). b_+(r) is the unique root on the decreasing branch [b_M,2), with b_+(0)=2. b_γ=min(b_eff,b_+(γ/P)).

```latex
\begin{corollary}\label{cor:quadratic-pareto}
For every $0\le\gamma\le\lambda_\star$, define
$$b_\gamma=\min\{b_{\rm eff},b_+(\gamma/P)\}.$$
An encoder attaining the global frontier over the continuous exact class is
\begin{equation}
 \enc_\gamma(s)=\sqrt P\left[\sqrt{b_\gamma(2-b_\gamma)}\,s
       +i(b_\gamma s^2-1)\right],
 \label{eq:quadratic-pareto-map}
\end{equation}
and its optimal small-noise coefficient is
\begin{equation}
 \mathcal V_\pi(\gamma)=\frac1{2K^2P}
 \left[\frac{M_{\rm eff}^2}{b_\gamma(2-b_\gamma)}
       +\frac1{b_\gamma^2}\right].
 \label{eq:quadratic-pareto-value}
\end{equation}
The constant portion ends at $\gamma_c=P R_M(b_{\rm eff})$.
\end{corollary}
```

**Dependencies.** Theorem thm:pareto; reflection/translation-projection dominance for both prior objective and separation; quadratic feasible-boundary characterization; root existence/uniqueness and monotonicity of b(x),R_M; interval form of the feasible floor set; constrained scalar minimization; P,K scaling.

**Verified scope and remaining gap.** `Analog.GeneralQuadratic` and `Analog.PowerScaling` verify the unconstrained finite-dimensional optimizer, closed parameter formula, uniqueness of its stationarity root, and arbitrary-power scaling. They do not yet formalize the prior expectation, M_eff bounds, constrained floor branch, b_+ existence/uniqueness, the clipped minimizer, or the full continuous-class frontier.

### 10. `thm:certifiedgrid` — theorem

Source: `sections/certified_synthesis.tex`. **Unverified in full.**

**Context and hypotheses.** Theorem thm:sdp hypotheses plus φ∈C²(I), P>0. The finite grid contains endpoints and three fixed spanning feature anchors; h is the maximum spacing. H_h,U_h optimize the grid relaxation. Z_j=max_I ‖z^(j)‖ for j=0,1,2; M_h=2‖H_h‖(Z_1²+Z_0Z_2); ρ_h=P/(P+M_h h²/8).

```latex
\begin{theorem}\label{thm:certifiedgrid}
Assume the hypotheses of Theorem~\ref{thm:sdp} and $\phi\in C^2(I)$. Let $\mathcal T_h$ contain both endpoints, have maximum adjacent spacing $h$, and include three fixed points whose feature vectors span $\R^3$. Let $U_h$ denote the optimum obtained by imposing the peak constraints only on $\mathcal T_h$, and let $(H_h,U_h)$ be an optimizer. Set
$$
 Z_j=\max_{s\in I}\|z^{(j)}(s)\|_2,\qquad j=0,1,2,
$$
where $z^{(0)}=z$, and define
$$
 M_h=2\|H_h\|_2(Z_1^2+Z_0Z_2),\qquad
 \rho_h=\frac{P}{P+M_hh^2/8}.
$$
Then $(\rho_h H_h,\rho_h U_h)$ satisfies every constraint of \eqref{eq:sdp}, and
\begin{equation}
 \rho_h U_h\le\lambda_\star\le U_h,
 \qquad U_h-\rho_h U_h=O(h^2).
 \label{eq:certifiedgrid}
\end{equation}
\end{theorem}
```

**Dependencies.** Second derivative of the peak quadratic form; operator-norm derivative bound; scalar interpolation remainder Mh²/8; scaling of semidefinite constraints; relaxation upper bound; uniform matrix bound from fixed anchors; existence of grid optimizer; uniform O(h²) estimate.

**Verified scope and remaining gap.** No complete grid certificate theorem has been formalized. The rational exponential witness verification implemented in Python is also separate from Lean verification.

### 11. `lem:collision` — lemma

Source: `sections/rigidity_proof.tex`. **Complete general statement checked, under weaker regularity assumptions.**

**Context and hypotheses.** K≥4; φ defines T=Σφ(s); ψ is C¹ on the interval interior and strictly convex or strictly concave. The encoder exactly computes T/K−ψ(S/K). Both colliding triples lie in the source interior. No encoder continuity is needed for this lemma.

```latex
\begin{lemma}
\label{lem:collision}
Suppose $K\ge4$, $\psi$ is $C^1$ in the interval interior and strictly convex or strictly concave, and $\enc$ exactly computes \eqref{eq:target}. If two interior triples have the same encoded sum, then they have the same $S$ and $T$.
\end{lemma}
```

**Dependencies.** Common completions at fourth inputs 0 and 1/2, with K−4 zeros; strict monotonicity of fixed-length increments from strict convexity/concavity; equality of the two moments. The revised proof does not use the stated differentiability hypothesis.

**Verified scope and remaining gap.** `Analog.GeneralCollision.triple_collision_preserves_moments` proves the general feature/readout statement for every K≥4 and arbitrary planar E, with actual strict convexity or strict concavity of ψ on the interval interior. It requires no differentiability of ψ or regularity of φ,E, and permits endpoint entries in both triples. The proof uses two common completions and strict secant inequalities. `positive_separation_triple_collision` derives the same conclusion from a positive operational lower bound. The variance-specific declarations remain valid specializations.

### 12. `lem:topology` — lemma

Source: `sections/rigidity_proof.tex`. **Conditional open-slice argument checked; original theorem unverified.**

**Context and hypotheses.** B is an open subset of ℝ²; J is a real interval. R is jointly continuous. A recovery map q, without continuity assumptions, recovers p from R(p,t).

```latex
\begin{lemma}
\label{lem:topology}
Let $B\subset\R^2$ be open, let $J\subset\R$ be an interval, and let $R:B\times J\to\R^2$ be continuous. Suppose there is a map $q$ on its image such that $q(R(p,t))=p$. Then $R(p,t)$ is independent of $t$ for each fixed $p$.
\end{lemma}
```

**Dependencies.** Planar invariance of domain makes every injective fixed-t slice an open map; local constancy; connectedness of J.

**Verified scope and remaining gap.** `Analog.open_slice_fiber_constancy` proves constancy under an explicit `IsOpenMap` hypothesis on every slice and preconnectedness of its parameter space. Continuity and injectivity alone have not been connected to openness; see `CONTINUOUS_SCOPE.md`.

### 13. `lem:affine` — lemma

Source: `sections/rigidity_proof.tex`. **Local-fiber-to-affine representation and coefficient independence checked; unrestricted continuity-to-rigidity reduction incomplete.**

**Context and hypotheses.** I=[−1,1]; φ is continuous on I, C¹ on (−1,1), and nonaffine. E is continuous. Encoded triple collisions imply equality of both moments.

```latex
\begin{lemma}
\label{lem:affine}
Let $\phi\in C(I)\cap C^1((-1,1))$ be nonaffine, and let $\enc:I\to\R^2$ be continuous. Suppose equality of encoded sums for any two interior triples implies equality of their $S$ and $T$ statistics. Then $\enc$ has form \eqref{eq:affine} with linearly independent $u,v$.
\end{lemma}
```

**Dependencies.** Lemma lem:topology; distinct derivative anchors from nonaffineness; C¹ inverse-function charts; local moment factorization; compactly supported smoothing and cutoff construction; differentiation along fibers via implicit-function theorem; affine derivative integration; endpoint continuity; independence of u,v using open moment image.

**Verified scope and remaining gap.** `Analog.RigidityAnalysis.rigid_representation_of_local_fibers` derives an independent affine-feature representation on the entire closed interval from the original feature/target assumptions, actual exact computation, encoder continuity, interior encoder differentiability, and local moment-fiber constancy. The native inverse-function theorem constructs the local sections; chain rules derive the tangent-kernel relations; integration and endpoint extension then yield the representation. `Analog.RigidityCompletion` derives genuine open moment neighborhoods and proves coefficient independence from exactness. The remaining obligations are exactness-to-local-factorization via planar topology and automatic differentiability via localized smoothing.

### 14. `prop:score` — proposition

Source: `sections/design_proof.tex`. **Complete general operational formula and shrinking-pair statement checked.**

**Context and hypotheses.** K≥4; φ is continuous on I and C¹ in the interior, strictly convex or strictly concave; ψ∈C¹(I) is strictly convex or strictly concave. E=c+us+vφ(s), with independent u,v. G is their 2×2 Gram matrix; w±=(−ψ′(±1),1). Λ is the all-pair infimum of squared received distance divided by squared nonzero target gap.

```latex
\begin{proposition}
\label{prop:score}
For an encoder \eqref{eq:affine} with independent $u,v$, the operational score is given by \eqref{eq:exactscore}.
The infimum is approached by pairs with received distance tending to zero.
\end{proposition}
```

**Dependencies.** Metric Cauchy–Schwarz; endpoint extrema of the dual-gradient norm; secant/mean-value bounds on the moment strip; explicit two-input paths realizing every first-order moment direction at a prescribed interior mean; one-sided endpoint slope continuity; local separation bounds and a contradiction argument yielding the epsilon/delta shrinking-pair witnesses.

**Verified scope and remaining gap.** `Analog.GeneralScore.general_operational_score` proves the actual all-pair operational identity for every nondegenerate planar two-feature curve and K>=2. The feature is strictly convex or concave on the closed source interval and differentiable in its interior; the mean-dependent term is convex or concave, differentiable within the closed interval, with continuous within-interval derivative. Thus endpoint derivatives are genuinely one-sided and the theorem covers the manuscript assumptions. `general_score_small_distance_sharpness` proves unequal-target admissible pairs at every positive received-distance radius and every positive score tolerance. `Analog.MomentPaths.exists_source_path_at_mean` constructs the two-input paths rather than assuming moment realizability. The separate variance identity also covers degenerate curves.

### 15. `cor:inverse-synthesis` — corollary

Source: `sections/design_proof.tex`. **Unverified in full.**

**Context and hypotheses.** Same hypotheses as Theorem thm:sdp. g(s)=(s,φ(s)). C_P comprises symmetric X and a∈ℝ² with the 3×3 block matrix [[P,(g(s)−a)ᵀ],[g(s)−a,X]] positive semidefinite for every s. Nonaffineness implies X positive definite. Endpoint budgets are w±ᵀXw±≤t.

```latex
\begin{corollary}\label{cor:inverse-synthesis}
Under the hypotheses of Theorem~\ref{thm:sdp}, program~\eqref{eq:inverse-synthesis} attains a positive optimum $t_\star$ and gives $\Lambda_\sq^\star=K^2/t_\star$. An optimal encoder follows from the enclosing-ellipse reconstruction in Section~\ref{sec:inverse-synthesis}.
\end{corollary}
```

**Dependencies.** Theorem thm:sdp; Proposition prop:score; Schur complements; encoder/containing-ellipse bijection; positive definiteness from a nonaffine graph; compact objective sublevels and attainment.

**Verified scope and remaining gap.** The complete convex formulation, positive attained optimum, and reconstruction have no final Lean counterpart.

### 16. `thm:polynomial` — theorem

Source: `sections/polynomial_appendix.tex`. **Unverified in full.**

**Context and hypotheses.** K≥4; P>0. F(m,q)=Σ a_ij m^i q^j has finitely many nonnegative coefficients, nonnegative integer exponents, one common parity for all present mean exponents i, and strictly positive endpoint partials α=Σi a_ij, β=Σj a_ij. t=α/(2β), b=2/(1−t²+t√(t²+2)), a0=√(b(2−b)).

```latex
\begin{theorem}
\label{thm:polynomial}
Let $K\ge4$ and let \eqref{eq:polyclass} satisfy the stated conditions. Define
$$
 t=\frac{\alpha}{2\beta},\qquad
 b=\frac{2}{1-t^2+t\sqrt{t^2+2}},\qquad a_0=\sqrt{b(2-b)}.
$$
An optimal encoder over every continuous shared peak-admissible map is
\begin{equation}
\begin{aligned}
 \enc^\star(s)&=\sqrt P\,[a_0s+i(bs^2-1)],\\
 \Lambda_{\sq}^\star(f)&=\frac{K^2P}{\beta^2}b^2(b-1).
\end{aligned}
 \label{eq:polyopt}
\end{equation}
\end{theorem}
```

**Dependencies.** Polynomial completion identity and coefficient comparison, split by the top weighted-degree term; strict monotonicity from coefficient/parity assumptions; Lemma lem:affine for quadratic rigidity; rectangle gradient bounds; local attainable sharpness at consensus endpoints; reflection and continuum peak reduction; weighted scalar optimum; nonexact competitors have zero score.

**Verified scope and remaining gap.** Neither the general moment-minus-mean collision lemma nor a quadratic algebraic optimizer proves this polynomial-class collision and operational-gradient theorem. The same all-continuous rigidity dependency remains.

### 17. `cor:transfer-unlabeled` — corollary

Source: `sections/transfer.tex`. **Unverified in full.**

**Context and hypotheses.** Targets satisfy Proposition prop:score hypotheses. D:[0,∞)→[0,∞) is continuous, D(0)=0, D(d)>0 for d>0; D(d)≥c_D d² throughout the attainable peak distance range [0,2K√P], and D(d)/d²→c_D>0 as d↓0.

```latex
\begin{corollary}
Suppose $D:[0,\infty)\to[0,\infty)$ is continuous, $D(0)=0$, positive away from zero, and
$$
 D(d)\ge c_Dd^2\quad(0\le d\le2K\sqrt P),\qquad
 \lim_{d\downarrow0}\frac{D(d)}{d^2}=c_D>0.
$$
For the targets of Proposition~\ref{prop:score}, every exact continuous encoder satisfies $\Lambda_D=c_D\Lambda_{\sq}$. Therefore every optimal encoder for the targets of Proposition~\ref{prop:score} remains optimal, and its optimum is multiplied by $c_D$.
\end{corollary}
```

**Dependencies.** Proposition prop:score including shrinking-pair attainment; lower-envelope inequality; product limit for the quotient; zero score for nonexact encoders from D(0)=0; maximization across all continuous competitors.

**Verified scope and remaining gap.** The original manuscript gives this numbered corollary no LaTeX label. It must still count toward any “all proofs” claim. A squared-score theorem without the shrinking-pair clause is insufficient.

### 18. `prop:approx-rigidity` — proposition

Source: `sections/approximate_rigidity.tex`. **Unverified in full.**

**Context and hypotheses.** Fix K,φ,ψ satisfying Theorem thm:rigidity and P>0. E has uniform norm ≤√P and a prescribed common modulus ω with ω(h)→0. D is globally L-Lipschitz, L>0, and its uniform target error is ≤ε. A_φ is the family c+us+vφ(s) with independent directions; distance is in the uniform norm.

```latex
\begin{proposition}
\label{prop:approx-rigidity}
For fixed $P$, $\omega$, and $L>0$, there is a nondecreasing function $\eta(\epsilon)$ tending to zero as $\epsilon\downarrow0$ with the following property. If $E\in\mathcal E_{P,\omega}$ and an $L$-Lipschitz decoder $D:\R^2\to\R$ satisfy
$$
 \sup_{\mathbf s\in I^K}
 |D(r_E(\mathbf s))-f_{\phi,\psi}(\mathbf s)|\le\epsilon,
$$
then $\operatorname{dist}_\infty(E,\mathcal A_\phi)\le\eta(\epsilon)$. The function $\eta$ may also depend on the fixed $K$, $\phi$, and $\psi$.
\end{proposition}
```

**Dependencies.** Approximate collision inequality; Arzelà–Ascoli compactness and closedness of the encoder class; continuity/Lipschitz dependence of the scalar defect d_L; continuity of distance to A_φ even though A_φ is nonclosed; compact subsequence argument; exactness of the limit; Theorem thm:rigidity; construction, finiteness and monotonicity of η and its zero limit.

**Verified scope and remaining gap.** An implementation-error bound is not approximate rigidity. The quantitative modulus assumed here is input regularity, whereas the conclusion supplies only qualitative convergence; neither an explicit rate nor coefficient identification is claimed.

## Additional proved claims outside numbered theorem environments

The phrase “all proofs” also includes proofs written in prose and numerical certificate arguments. The following list makes the main additional obligations explicit. Numerical simulation outcomes are empirical observations rather than universal theorems, but their reproduction remains a separate evidence requirement.

| Location | Claim requiring separate coverage |
|---|---|
| `sections/model.tex` | Positive squared separation implies exactness; received-set and peak-distance facts used to define the objective. |
| `sections/assumptions.tex` | Endpoint-derivative counterexample and explanation that rigidity assumptions alone do not guarantee positive separation. |
| `sections/certified_synthesis.tex`, equations `eq:dualwitness`, `eq:expcertificate` | Soundness of finite primal/dual witnesses; matrix positivity and rational exponential enclosures; the displayed global upper/lower bounds and certified relative gap. Python exact rational checks are not Lean proofs. |
| `sections/examples.tex` | Root existence, uniqueness and closed form where not included in a formal theorem; exact displayed baselines and relative improvements; four active quartic peak contacts. |
| `sections/decoding.tex` | K=4 attainable variance moment-region boundary and intermediate attainment; Jensen containment for even features; explicit moment-interaction decoder; finite-disturbance-radius minimax error ω_E(2τ)/2 and Borel decoder construction; expected-error bound for arbitrary finite-second-moment noise. |
| `sections/implementation.tex` | The normed additive-noise formulation, termwise received perturbation bound, decoded implementation bound, uniform-gain specialization and peak-safe quantization are checked in `Analog.Implementation`; remaining prose specializations must map to these hypotheses, including calibration assumptions. |
| `sections/pareto.tex` | Qπ positive definiteness equivalent to nonzero variance of ψ′(m); symmetry giving diagonal Qπ; M_eff bounds; independent uniform-source moment formula. |
| `sections/criterion_appendix.tex` | Exactness with arbitrarily poor conditioning; collision example at zero coefficient; positive uncentered-exponential score without exactness; binary-source optimum 64P/9 and strict loss from restricting the continuous optimum. |
| Numerical experiment sections and source scripts | Stated experimental configurations, coefficients, baselines and data processing must remain reproducible; kernel proof of the deterministic theorem cannot certify measured Monte Carlo outcomes. |

## Minimum chain for the unrestricted variance optimum

1. The arbitrary-encoder general collision lemma is now checked, including its variance specialization.
2. Complete planar invariance of domain or an equally strong checked substitute, then the original fiber-constancy lemma.
3. Derive local moment-fiber constancy from exactness via topology and prove automatic differentiability by localized smoothing. Native local moment charts, the fiber-to-kernel step, integration through endpoints, and coefficient independence are now checked. The final conditional representation theorem assembles those completed pieces.
4. The operational all-pair score and admissible shrinking-pair sharpness are now checked for general strictly curved features and regular convex/concave mean-dependent terms at K≥2; variance additionally includes degenerate curves.
5. Arbitrary peak power and transmitter count are connected to the checked variance optimizer over all quadratic competitors, including degenerate/zero-score curves. The final theorem over every continuous peak-feasible encoder still needs the rigidity reduction and the resulting competitor-class argument.

Completing this chain would justify a claim about the unrestricted variance optimum. It would **not** justify “all proofs in the paper”: every other statement and additional claim above must also have its own complete checked coverage. Importing an unproved manuscript claim as a hypothesis or an axiom does not complete that coverage.

## Verification acceptance criteria

- Formal theorem types must retain the manuscript quantifiers and hypotheses, and definitions must model the stated operational channel, source interval, peak constraint, target and score.
- Every declaration advertised as verified must compile under the pinned Lean/mathlib versions, with no `sorry`, `admit`, `sorryAx`, invented axioms, or unproved manuscript theorem imported as a premise.
- The axiom audit and kernel recheck must cover the final dependency graph. The source hash report must match the packaged files.
- The manuscript acknowledgment and formalization appendix must list the achieved scope. Until every result above is covered, use “selected results have Lean-checked proofs,” not “all proofs are formalized.”
