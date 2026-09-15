# Manuscript proof coverage inventory

Status: **the manuscript is not fully formalized**. This inventory covers the 17 theorem, lemma, proposition, and corollary statements reachable from the revised `manuscript.tex`, including the unlabeled criterion-transfer corollary. The quadratic and quartic cases are now one theorem; the general extension is in the main text as Theorem 4. Source-order numbers below are inventory positions, not printed theorem numbers. Statements are exact extracts from the accompanying revision titled *Geometric Optimization of Continuous Encoders for Moment-Based Computation*.

This inventory records scope; `Audit.lean`, `verify.py`, and the saved verification report determine the declarations actually checked. Checked specializations or conditional lemmas do not certify a broader manuscript theorem. `EXTENSION_SCOPE.md` gives the additional obligations for the new proof.

## Coverage of complete manuscript statements

| Source order | Result | Current coverage |
|---|---|---|
| 1 | `thm:rigidity` | Affine-family exactness and affine representation from local charts checked; producing those charts from exactness remains unverified. |
| 2 | `thm:sdp` | General operational score, reconstruction, compactness and positive maximum attainment checked within the coefficient class; unrestricted reduction remains unverified. |
| 3 | `thm:parabola` | Quadratic/quartic coefficient optima and general operational score checked; unrestricted continuous-class conclusion remains unverified. |
| 4 | `thm:extension` | General attained-pair SDP, positive-definite operational realization and coefficient-class optimum checked; smoothing/dense propagation checked from local charts. Topological production of charts, analytic and endpoint specializations remain unverified. |
| 5 | `prop:amplification` | Full operational content checked via attained-minimum and zero-score statements. |
| 6 | `thm:decoder` | General strip decoder, exactness, sharp all-input/all-disturbance amplification and clipping guarantee checked. |
| 7 | `prop:general-small-noise` | General Gaussian strip-decoder leading-MSE formula and permitted output clipping checked within the coefficient class; unrestricted classification remains separate. |
| 8 | `thm:pareto` | Attained continuous Gram frontier, uniqueness, qualitative branches and ellipse/Gram correspondences checked; unrestricted continuous-class frontier remains unverified. |
| 9 | `cor:quadratic-pareto` | Complete constrained quadratic coefficient frontier, upper root, clipped parameter and power scaling checked; prior specializations and unrestricted reduction remain separate. |
| 10 | `thm:certifiedgrid` | Continuum SDP grid certificate, spectral-norm remainder, optimizer attainment and uniform O(h²) loss checked; displayed numerical witnesses remain separate. |
| 11 | `lem:collision` | Complete general collision statement checked, including endpoint triple inputs and without differentiability assumptions. |
| 12 | `lem:topology` | Conditional open-slice constancy and compact-range recovery checked; planar invariance of domain remains unverified. |
| 13 | `lem:affine` | Local-chart smoothing, dense propagation, derivative integration and coefficient independence checked; collision-to-chart topology remains unverified. |
| 14 | `prop:score` | Complete general operational formula and shrinking-pair statement checked. |
| 15 | `cor:inverse-synthesis` | Ellipse/Gram equivalence and positive reciprocal inverse optimum checked; unrestricted operational conclusion still depends on rigidity. |
| 16 | `cor:transfer-unlabeled` | Actual peak-constrained moment-score transfer and zero-collision case checked; unrestricted competitor-class conclusion still depends on rigidity. |
| 17 | `prop:approx-rigidity` | Actual encoder-class compactness, pair defect and constructed stability modulus checked; identification of the exact class with affine moment curves remains a premise. |

## Exact statements, hypotheses, and dependencies

### 1. `thm:rigidity` — theorem

Source: `sections/rigidity.tex`. **Affine-family exactness and affine representation from local charts checked; producing those charts from exactness remains unverified.**

**Context and hypotheses.** K≥4; I=[−1,1]; φ continuous on I, C¹ in the interior, nonaffine; ψ continuous on I, C¹ in the interior, strictly convex/concave. E is a continuous planar encoder. Exact computation means equality of received sums implies equality of the target.

```latex
\begin{theorem}
\label{thm:rigidity}
Let $K\ge4$. Assume $\phi\in C(I)\cap C^1((-1,1))$ is nonaffine and $\psi\in C(I)\cap C^1((-1,1))$ is strictly convex or strictly concave. A continuous encoder $\enc:I\to\R^2\cong\C$ exactly computes $f_{\phi,\psi}:I^K\to\R$ in \eqref{eq:target}, in the sense of \eqref{eq:exactness}, if and only if
\begin{equation}
 \enc(s)=c+u s+v\phi(s),
 \qquad s\in I,\quad c,u,v\in\R^2,
 \label{eq:affine}
\end{equation}
with $u,v$ linearly independent, equivalently $\det[\,u\ v\,]\ne0$.
\end{theorem}
```

**Dependencies.** Lemmas lem:collision and lem:affine for necessity. Invertibility of the coefficient map (S,T)↦uS+vT for sufficiency, followed by the prescribed scalar readout.

**Verified scope and remaining gap.** `Analog.RigidityCompletion.FeatureEncoder.exact_iff_det_ne_zero_of_nonaffine` proves the exactness equivalence within the affine moment family. `Analog.GeneralRigidity` constructs actual local inverse sections, derives independent tangent anchors from functional independence, and integrates derivative relations through the source endpoints. `Analog.EncoderRegularity.planar_affine_of_local_charts` derives encoder differentiability and the affine representation from continuous local triple factorizations; its dense-chart version also derives regularity and propagation from the actual regular triple-statistic image. `Analog.PlanarTopology` proves encoder injectivity, a closed source-curve embedding and continuous recovery of both triple statistics directly from exactness. None of these statements produces the reverse local factorization from continuity and exactness alone: that remaining step uses planar invariance of domain. The established coefficient-independence argument then applies once the affine representation is available.

### 2. `thm:sdp` — theorem

Source: `sections/synthesis.tex`. **General operational score, reconstruction, compactness and positive maximum attainment checked within the coefficient class; unrestricted reduction remains unverified.**

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
where $z(s)=(1,s,\phi(s))^\T\in\R^3$ and $G$ is the lower-right $2\times2$ block of $H$. This is a convex semidefinite problem with seven real variables and a continuum of scalar peak constraints. Its optimum is attained and yields an exact planar encoder.
\end{theorem}
```

**Dependencies.** Theorem thm:rigidity; Proposition prop:score; Schur complement equivalence; positivity of G from independent endpoint slopes; rank-two Gram reconstruction by reducing the translation diagonal; a positive feasible point; compactness from three spanning feature vectors; attainment.

**Verified scope and remaining gap.** `Analog.GeneralDesign.positive_sdp_operational_synthesis` combines genuine PSD/Schur reconstruction with the general operational score: every positive feasible SDP point yields a continuous, exact planar curve with the entire peak constraint and actual score at least K²λ. Independence of endpoint directions follows from strict curvature of the mean-dependent term. `Analog.SynthesisAttainment` derives spanning anchors from strict feature curvature and a positive feasible design from continuity and P>0. It derives coordinate bounds from actual anchor evaluations, proves the continuum feasible set closed and compact, and proves positive maximum-separation attainment with an operational realization. Its `operational_maximum_attained` compares the positive continuous exact optimizer against all affine-feature coefficient curves, including singular and constant curves; `positive_score_implies_positive_gram` handles those competitors without assuming their nondegeneracy. The general continuous-class upper bound still requires unrestricted rigidity; additional final interfaces and hypotheses are listed in THEOREM_MAP.md.

### 3. `thm:parabola` — theorem

Source: `sections/examples.tex`. **Quadratic/quartic coefficient optima and general operational score checked; unrestricted continuous-class conclusion remains unverified.**

**Context and hypotheses.** K≥4, P>0; φ(s)=s²; ψ∈C¹(I) is even and strictly convex or strictly concave; M=|ψ′(1)|>0, t=M/2, b=2/(1−t²+t√(t²+2)), a=√(b(2−b)). Competitors are all continuous shared peak-admissible encoders.

```latex
\begin{theorem}[Quadratic and quartic encoders]
\label{thm:parabola}\label{thm:quartic}
Let $K\ge4$ be an integer and let $P>0$. Under the preceding assumptions on $\psi$, the desired functions $f_{\phi,\psi}:I^K\to\R$ in \eqref{eq:target} admit the following globally optimal encoders among all continuous maps $\enc:I\to\C$ satisfying $|\enc(s)|^2\le P$ for every $s\in I$:
for $\phi(s)=s^2$,
\begin{equation}
\begin{aligned}
 \enc_2^\star(s)&=\sqrt P\,[a s+i(bs^2-1)],\qquad s\in I,\\
 \Lambda_{\sq}^\star(f_{\phi_2,\psi})&=K^2P\lambda_2;
\end{aligned}
 \label{eq:parabola}
\end{equation}
for $\phi(s)=s^4$,
\begin{equation}
\begin{aligned}
 \enc_4^\star(s)&=\sqrt P\,[a_\rho s+i(b_\rho s^4+c_\rho)],\qquad s\in I,\\
 \Lambda_{\sq}^\star(f_{\phi_4,\psi})&=K^2P\lambda_4.
\end{aligned}
 \label{eq:quarticscore}
\end{equation}
\end{theorem}
```

**Dependencies.** Theorem thm:rigidity; Proposition prop:score; reflection/translation projection or an equivalent direct algebraic converse; all-interval peak identity; minimization of M²/[b(2−b)]+1/b²; explicit root formula; P and K² scaling; exclusion of nonexact competitors.

**Verified scope and remaining gap.** `Analog.GeneralQuadratic.quadratic_optimal_closed_form` and `Analog.quadratic_optimal_all_power` prove the complete quadratic Gram optimum, its root characterization and displayed parameter, for every M>0 and P>0. `Analog.quadratic_variance_operational_optimal` assembles the actual all-pair score, continuum peak feasibility and optimum 4K²P/(9+6√3) over every planar quadratic curve, including degenerate curves, for K≥2. The general operational score and shrinking-pair theorem are checked in `Analog.GeneralScore`; they are no longer an unverified ingredient for general ψ.

**Quartic part of the combined theorem.** `Analog.Quartic.quartic_optimal_all_power` checks the complete quartic coefficient-Gram optimization for every positive slope parameter and power, including the continuum peak certificate and coefficient-class converse. The operational interpretation uses the checked general score theorem. The unresolved common step is enlarging the coefficient competitors to all continuous encoders through unrestricted rigidity. The label `thm:quartic` aliases this combined theorem.

### 4. `thm:extension` — theorem

Source: `sections/examples.tex`; proof in `sections/polynomial_appendix.tex`. **General attained-pair SDP, positive-definite operational realization and coefficient-class optimum checked; smoothing/dense propagation checked from local charts. Topological production of charts, analytic and endpoint specializations remain unverified.**

**Context and hypotheses.** K≥4; I=[−1,1]; γ=(φ₁,φ₂) continuous on I and C¹ in its interior; 1,φ₁,φ₂ functionally independent. M is the actual image of valid K-input configurations under μγ. F is continuous on M. The common-completion identification hypothesis holds locally on a dense open subset of the regular triple-statistic image. The design conclusion additionally assumes P>0 and F nonconstant and Lipschitz on M.

```latex
\begin{theorem}[Extension to two additive statistics]
\label{thm:extension}\label{thm:polynomial}
Let $K\ge4$, $P>0$, and let \eqref{eq:general-function} satisfy the regularity, independence, and common-completion condition stated above.
\begin{enumerate}
\item A continuous encoder $\enc:I\to\R^2\cong\C$ exactly computes $f$ if and only if
$$
 \enc(s)=c+\mathsf U\gamma(s),\qquad s\in I,\quad
 c\in\R^2,\quad\mathsf U\in\R^{2\times2},\quad\det\mathsf U\ne0.
$$
\item If $F$ is additionally nonconstant and Lipschitz on $\mathcal M$ in the Euclidean norm, then $\Lambda_\sq^\star(f)=K^2\lambda_\gamma^\star$, where $\lambda_\gamma^\star>0$ is the attained optimum of
\begin{equation}
\begin{aligned}
 \text{maximize}\quad &\lambda\\
 \text{over}\quad &H\in\mathbb S^3,\quad\lambda\ge0,\\
 \text{subject to}\quad &H\succeq0,\\
 &z_\gamma(s)^\T H z_\gamma(s)\le P\qquad(s\in I),\\
 &(\mu-\nu)^\T G(\mu-\nu)\ge\lambda|F(\mu)-F(\nu)|^2
       \qquad(\mu,\nu\in\mathcal M).
\end{aligned}
 \label{eq:general-sdp}
\end{equation}
Here $z_\gamma(s)=(1,\gamma(s)^\T)^\T\in\R^3$ and $G$ is the lower-right $2\times2$ block of $H$. Every optimizer yields an exact planar encoder satisfying the peak constraint.
\end{enumerate}
\end{theorem}
```

**Dependencies and remaining scope.** `Analog.CompletionIdentification` proves the common-completion collision implication. `Analog.AdditiveStatistics`, `Analog.AttainableScore` and `Analog.TwoStatisticDesign` model actual admissible tuples, affine encoding, exactness and the attained-pair score. `Analog.TwoStatisticAttainment` derives spanning anchors from functional independence, compactness of the full seven-variable feasible set and a positive attained maximum. `Analog.TwoStatisticPositivity.general_sdp_operational_attainment` derives positive definiteness from the actual dense common-completion condition and jointly realizes the SDP optimum as a continuous exact peak-feasible encoder with score K²λ; `general_operational_maximum_attained` compares it with every coefficient curve, including singular competitors. No optimizer or positive-definite block is assumed in these final theorems.

`Analog.EncoderRegularity.planar_affine_of_dense_charts` proves automatic C¹ regularity, dense propagation and the endpoint-inclusive affine representation from continuous local factorizations on an identifying set O with the actual inclusion `regularTripleImage ⊆ closure O`. Only production of those charts from exactness and common-completion identification remains missing in this rigidity chain; it is not disguised as a proved topological result. Analytic identification and endpoint-gradient/explicit polynomial specializations remain unverified. Formal F is total on the plane but evaluated only on M; regularity outside M is not assumed. A finite Lipschitz constant in the Lean product metric is equivalent to one in the Euclidean metric. See `EXTENSION_SCOPE.md`. The label `thm:polynomial` remains an alias.

### 5. `prop:amplification` — proposition

Source: `sections/decoding.tex`. **Full operational content checked via attained-minimum and zero-score statements.**

**Context and hypotheses.** Any continuous encoder on the compact source cube; nonconstant continuous scalar target. A is the infimum over constants L≥0 for which one decoder obeys the uniform disturbance inequality at every input and every n∈ℝ². A=+∞ when no finite constant exists. Λ is operational squared separation, with 0^(−1/2)=+∞.

```latex
\begin{proposition}\label{prop:amplification}
Let $I=[-1,1]$, $K\in\mathbb N$ with $K\ge1$, $\enc:I\to\R^2$ be continuous, and $f:I^K\to\R$ be continuous and nonconstant. Then
$$\mathcal A(\enc;f)=\Lambda_\sq(\enc;f)^{-1/2},$$
with $0^{-1/2}=+\infty$. A continuous decoder attains every finite value.
\end{proposition}
```

**Dependencies.** Uniform guarantee implies exactness and pairwise Lipschitz inequality; well-defined received-set readout; compactness; McShane extension preserving the optimal Lipschitz constant; infimum/supremum identity including Λ=0; continuity and attainment of finite constants; scalar output clipping.

**Verified scope and remaining gap.** `Analog.Decoder.sharp_uniform_decoder` proves existence of a globally Lipschitz continuous exact decoder whose uniform constant is 1/√Λ, and proves this constant no larger than any finite uniform constant for any other decoder. `finite_uniform_decoder_iff_positive_score` and `zero_score_no_finite_uniform_decoder` establish the zero-score/infinite-required-amplification case. The metric theorem covers arbitrary received maps and nonconstant real targets, a larger class than the manuscript. The extended-real symbol A itself is not introduced as a separate formal infimum: the source proves the equivalent attained-minimum statement when finite and impossibility of every finite constant when Λ=0. `Analog.Decoder.uniform_iff_additive_noise` gives the additive-disturbance formulation, and `Analog.ArbitraryEncoder.asComplex_squared_distance` verifies that the complex metric is precisely the manuscript Euclidean cost. Its variance bridge connects this metric score to the actual list-based multiple-access variance score. Scalar clipping is covered by `Analog.Decoder.clip_uniform`.

### 6. `thm:decoder` — theorem

Source: `sections/decoding.tex`. **General strip decoder, exactness, sharp all-input/all-disturbance amplification and clipping guarantee checked.**

**Context and hypotheses.** Theorem uses the score assumptions of thm:sdp, an invertible coefficient matrix U=[u v], G=UᵀU, and the prescribed metric strip projection: transform received y to (m̃,t̃), clip m̃ to [−1,1], correct t̃ by G12/G22·(m̃−m̂), then output t̂−ψ(m̂).

```latex
\begin{theorem}\label{thm:decoder}
Under the assumptions of Theorem~\ref{thm:sdp}, let $\enc(s)=c+us+v\phi(s)$ with $c,u,v\in\R^2$ and linearly independent $u,v$. The receiver function $\widehat f:\R^2\to\R$ in \eqref{eq:stripdecoder} exactly computes $f_{\phi,\psi}:I^K\to\R$ and attains the smallest possible uniform constant for this encoder
\begin{equation}
 L_\enc=\frac1K\sqrt{\max_{\sigma\in\{-,+\}}w_\sigma^\T G^{-1}w_\sigma}
 =\Lambda_\sq(\enc;f)^{-1/2}.
 \label{eq:decoderconstant}
\end{equation}
An additional scalar projection onto an interval containing $f(I^K)$ preserves this conclusion.
\end{theorem}
```

**Dependencies.** Closed-form minimizer of G-metric strip projection via the positive Schur complement; nonexpansiveness of Euclidean projection on its received image; endpoint gradient bound and line integration; noiseless exactness; Propositions prop:score and prop:amplification for optimality; optional scalar clipping.

**Verified scope and remaining gap.** `Analog.GeneralDecoder.decode_optimal` proves the assembled general received-coordinate decoder: actual inverse moment recovery, corrected strip projection, exactness for every admissible input list, global Lipschitz continuity, the uniform guarantee for every complex disturbance, and minimality among all decoders. `amplification_reciprocal_score` identifies its constant with the reciprocal square root of the actual score. Endpoint regularity is modeled by differentiability within the closed interval and continuous `derivWithin`; this permits finite one-sided endpoint derivatives and does not require differentiability of an arbitrary extension outside I. `Analog.Strip.project_unique_minimizer` and `project_squared_nonexpansive` verify the correction and metric nonexpansiveness. `Analog.Decoder.clip_uniform` preserves the guarantee under the permitted scalar output projection. The earlier explicit variance theorem remains a specialization.

### 7. `prop:general-small-noise` — proposition

Source: `sections/pareto.tex`. **General Gaussian strip-decoder leading-MSE formula and permitted output clipping checked within the coefficient class; unrestricted classification remains separate.**

**Context and hypotheses.** The synthesis assumptions hold. The input prior satisfies |m|<1 almost surely; Qπ=E[w(m)w(m)ᵀ] is positive definite. Noise is independent circular complex Gaussian CN(0,N0). The decoder is the prescribed strip projection/readout, with optional clipping locally inactive at the true target almost surely. G is the feature Gram matrix of any continuous exact peak-admissible encoder.

```latex
\begin{proposition}\label{prop:general-small-noise}
For every continuous encoder $\enc:I\to\R^2$ that exactly computes $f_{\phi,\psi}:I^K\to\R$ and satisfies \eqref{eq:peak-model}, let $G=\mathsf U^\T\mathsf U\in\mathbb S_{++}^2$ be the Gram matrix of its coefficient vectors $u,v$. If $N\sim\mathcal{CN}(0,N_0)$, then the strip decoder $\widehat f:\R^2\to\R$ satisfies
\begin{equation}
 \mathcal J_\pi(G):=\lim_{N_0\downarrow0}
 \frac{\mathbb E_{\pi,N}|\widehat f(Y)-f(\mathbf s)|^2}{N_0}
 =\frac{\operatorname{tr}(Q_\pi G^{-1})}{2K^2}.
 \label{eq:general-small-noise}
\end{equation}
\end{proposition}
```

**Dependencies.** Theorem thm:rigidity; local inactivity of projection and permitted clipping; differentiability of the received readout; coupling N=√N0 Z; Gaussian covariance I2/2; pointwise small-noise limit; integrable uniform domination from Theorem thm:decoder; dominated convergence and trace/expectation identities.

**Verified scope and remaining gap.** `Analog.GeneralSmallNoise.source_leading_mse_inverseGram` proves the actual general strip-decoder limit for admissible input lists and independent normalized isotropic noise. It derives exactness, inverse moment recovery, local differentiability, measurable bounded slope moments, dominated convergence and the inverse-Gram trace expression. The scalar risk parameters are μ=−E[ψ′(m)] and v=E[ψ′(m)²]−E[ψ′(m)]², giving Q=[[v+μ²,μ],[μ,1]] and the normalization 1/(2K²).

`Analog.GaussianNoise.gaussian_source_leading_mse` instantiates the genuine circular Gaussian law from two independent real N(0,1/2) coordinates and derives its moments and integrability. `clipped_leading_mse_inverseGram` and `gaussian_clipped_leading_mse` cover optional scalar output clipping when the true value lies strictly inside the clipping interval almost surely; no uniform distance from the boundary is assumed. These are complete coefficient-family decoder limits, with no derivative or Lipschitz conclusion assumed. Passing from every continuous exact encoder to that coefficient family still requires unrestricted rigidity.

### 8. `thm:pareto` — theorem

Source: `sections/pareto.tex`. **Attained continuous Gram frontier, uniqueness, qualitative branches and ellipse/Gram correspondences checked; unrestricted continuous-class frontier remains unverified.**

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
At $\gamma=0$, we omit the last two inequalities. An optimum exists, has a unique inverse Gram matrix $X=G^{-1}\in\mathbb S_{++}^2$, and yields an exact planar encoder through
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

**Verified scope and remaining gap.** `Analog.Frontier` proves convexity of the actual continuum Gram constraints, strict convexity of inverse-Gram risk, the infimum frontier's convexity and monotonicity, uniqueness, the plateau, active separation floor and strict increase after the plateau. `Analog.FrontierAttainment.frontier_attained_on_maximal_interval` supplies optimizer witnesses at every floor, including zero, using a derived determinant barrier det G≥v/R². `Analog.FrontierContinuity.attained_continuous_frontier_of_strict_shape` proves continuity on the whole closed feasible interval, including the maximal floor; it derives anchors, maximum separation and optimizer existence from the stated shape, power and variance assumptions.

`Analog.InverseSynthesis` checks positive definiteness, both directions of the ellipse/Gram feasibility correspondence, inverse round trips, endpoint costs and attainment of the reciprocal inverse optimum. The general probabilistic trace formula, including Gaussian noise and permitted output clipping, is now checked as described under Proposition `prop:general-small-noise`. The sign convention is μ=−E[ψ′(m)], v=Var(ψ′(m)), with endpoint directions −ψ′(±1). The full manuscript theorem still quantifies over unrestricted continuous encoders; its final identification with the assembled coefficient/Gram/ellipse results requires the missing rigidity reduction. The map does not advertise a single checked declaration for that unrestricted frontier.

### 9. `cor:quadratic-pareto` — corollary

Source: `sections/pareto.tex`. **Complete constrained quadratic coefficient frontier, upper root, clipped parameter and power scaling checked; prior specializations and unrestricted reduction remain separate.**

**Context and hypotheses.** φ(s)=s²; ψ even; distribution of m symmetric; 0<M_eff=√E[ψ′(m)²]<M=|ψ′(1)|. b(x) is the stated positive-slope quadratic optimizer; R_M(b)=[M²/(b(2−b))+1/b²]^(−1). b_+(r) is the unique root on the decreasing branch [b_M,2), with b_+(0)=2. b_γ=min(b_eff,b_+(γ/P)).

```latex
\begin{corollary}\label{cor:quadratic-pareto}
For every $0\le\gamma\le\lambda_\star$, define
$b_\gamma=\min\{b_{\rm eff},b_+(\gamma/P)\}.$
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

**Verified scope and remaining gap.** `Analog.QuadraticFrontier` proves existence and uniqueness of the upper-branch root, the cubic identity, monotonicity of the stationary parameter, the exact plateau test, and global constrained optimality of the clipped parameter. `clipped_curve_optimal_all_power` gives the displayed risk and peak/separation constraints at every P>0, against all nondegenerate quadratic coefficient curves; it includes the maximal-floor case rather than assuming an interior optimum. `Analog.GeneralQuadratic` supplies the explicit stationary parameter. The new Gaussian limit identifies the inverse-Gram objective for the implemented decoder. The hypotheses 0<M_eff<M are explicit scalar premises in the quadratic optimizer theorem; deriving them and diagonal Q from the stated source symmetry is part of the additional prior-specialization inventory below. Enlarging competitors to all continuous exact encoders still requires rigidity.

### 10. `thm:certifiedgrid` — theorem

Source: `sections/certified_synthesis.tex`. **Continuum SDP grid certificate, spectral-norm remainder, optimizer attainment and uniform O(h²) loss checked; displayed numerical witnesses remain separate.**

**Context and hypotheses.** Theorem thm:sdp hypotheses plus φ∈C²(I), P>0. The finite grid contains endpoints and three fixed spanning feature anchors; h is the maximum spacing. H_h,U_h optimize the grid relaxation. Z_j=max_I ‖z^(j)‖ for j=0,1,2; M_h=2‖H_h‖(Z_1²+Z_0Z_2); ρ_h=P/(P+M_h h²/8).

```latex
\begin{theorem}\label{thm:certifiedgrid}
Assume the hypotheses of Theorem~\ref{thm:sdp} and $\phi\in C^2(I;\R)$. Let $\mathcal T_h\subset I$ be a finite grid containing both endpoints, with maximum adjacent spacing $h>0$, and containing three fixed inputs whose vectors $z(s)=(1,s,\phi(s))^\T$ span $\R^3$. Let $U_h$ denote the optimum obtained by imposing the peak constraints only on $\mathcal T_h$, and let $(H_h,U_h)\in\mathbb S_+^3\times[0,\infty)$ be an optimizer. Set
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
 \qquad U_h-\rho_h U_h=O(h^2)\quad(h\downarrow0).
 \label{eq:certifiedgrid}
\end{equation}
\end{theorem}
```

**Dependencies.** Second derivative of the peak quadratic form; operator-norm derivative bound; scalar interpolation remainder Mh²/8; scaling of semidefinite constraints; relaxation upper bound; uniform matrix bound from fixed anchors; existence of grid optimizer; uniform O(h²) estimate.

**Verified scope and remaining gap.** `Analog.CertifiedGrid.c2_grid_certificate` derives the sampled and continuum SDP optima and the scaled feasible design with the manuscript spectral constant 2‖H‖(Z₁²+Z₀Z₂). The file proves the scalar Mh²/8 interpolation bound, finite-grid bracketing, actual Euclidean Gram-operator identity, C² derivative data and attainment of the norm maxima. `certified_grid_bracket` also applies to a supplied grid optimum. Fixed anchors give uniform coefficient and operator bounds; `grid_scaling_gap_isBigO` proves the actual O(h²) scaling gap without assuming bounded sampled optimizers or operator norms. These statements certify the continuum Gram program. Individual rational/exponential witness values and numerical solver outputs remain separate evidence obligations; Python rational checks are not Lean proofs.

### 11. `lem:collision` — lemma

Source: `sections/rigidity_proof.tex`. **Complete general collision statement checked, including endpoint triple inputs and without differentiability assumptions.**

**Context and hypotheses.** K≥4; φ defines T=Σφ(s); ψ is strictly convex or strictly concave; no differentiability is assumed. The encoder exactly computes T/K−ψ(S/K). Both colliding triples lie in the source interior. No encoder continuity is needed for this lemma.

```latex
\begin{lemma}
\label{lem:collision}
Let $K\ge4$, $I=[-1,1]$, $\phi:I\to\R$, and $\psi:I\to\R$, where $\psi$ is strictly convex or strictly concave. Suppose $\enc:I\to\R^2$ exactly computes $f_{\phi,\psi}:I^K\to\R$ in \eqref{eq:target}. Then, for every $\mathbf a,\mathbf b\in(-1,1)^3$,
\begin{align*}
 &\sum_{j=1}^3\enc(a_j)=\sum_{j=1}^3\enc(b_j)\\
 &\quad\Longrightarrow\quad
 \begin{pmatrix}\sum_{j=1}^3 a_j\\\sum_{j=1}^3\phi(a_j)\end{pmatrix}
 =\begin{pmatrix}\sum_{j=1}^3 b_j\\\sum_{j=1}^3\phi(b_j)\end{pmatrix}.
\end{align*}
\end{lemma}
```

**Dependencies.** Common completions at fourth inputs 0 and 1/2, with K−4 zeros; strict monotonicity of fixed-length increments from strict convexity/concavity; equality of the two moments. No differentiability hypothesis is present in the revised lemma or needed by its proof.

**Verified scope and remaining gap.** `Analog.GeneralCollision.triple_collision_preserves_moments` proves the general feature/readout statement for every K≥4 and arbitrary planar E, with actual strict convexity or strict concavity of ψ on the interval interior. It requires no differentiability of ψ or regularity of φ,E, and permits endpoint entries in both triples. The proof uses two common completions and strict secant inequalities. `positive_separation_triple_collision` derives the same conclusion from a positive operational lower bound. The variance-specific declarations remain valid specializations.

### 12. `lem:topology` — lemma

Source: `sections/rigidity_proof.tex`. **Conditional open-slice constancy and compact-range recovery checked; planar invariance of domain remains unverified.**

**Context and hypotheses.** B is an open subset of ℝ²; J is a real interval. R is jointly continuous. A recovery map q, without continuity assumptions, recovers p from R(p,t).

```latex
\begin{lemma}
\label{lem:topology}
Let $B\subset\R^2$ be open, let $J\subset\R$ be an interval, and let $R:B\times J\to\R^2$ be continuous. Suppose there is a map $q:R(B\times J)\to B$ such that $q(R(p,t))=p$ for every $(p,t)\in B\times J$. Then $R(p,t)$ is independent of $t$ for each fixed $p$.
\end{lemma}
```

**Dependencies.** Planar invariance of domain makes every injective fixed-t slice an open map; local constancy; connectedness of J.

**Verified scope and remaining gap.** `Analog.open_slice_fiber_constancy` proves constancy under an explicit `IsOpenMap` hypothesis on every slice and preconnectedness of its parameter space. `Analog.PlanarTopology.continuous_recovery_of_compact` supplies a continuous recovery map on an actual compact received range from collision preservation, and `continuous_triple_moment_recovery` applies it to exact computation. This is the recovery direction, not local constancy on moment fibers. Continuity and injectivity have not been connected to planar slice openness; `CONTINUOUS_SCOPE.md` records the remaining invariance-of-domain dependency.

### 13. `lem:affine` — lemma

Source: `sections/rigidity_proof.tex`. **Local-chart smoothing, dense propagation, derivative integration and coefficient independence checked; collision-to-chart topology remains unverified.**

**Context and hypotheses.** I=[−1,1]; φ is continuous on I, C¹ on (−1,1), and nonaffine. E is continuous. Encoded triple collisions imply equality of both moments.

```latex
\begin{lemma}
\label{lem:affine}
Let $\phi:I\to\R$ be nonaffine and belong to $C(I)\cap C^1((-1,1))$, and let $\enc:I\to\R^2$ be continuous. Suppose equality of encoded sums for any two interior triples implies equality of their $S$ and $T$ statistics. Then $\enc$ has form \eqref{eq:affine} with $c,u,v\in\R^2$ and linearly independent $u,v$.
\end{lemma}
```

**Dependencies.** Lemma lem:topology; distinct derivative anchors from nonaffineness; C¹ inverse-function charts; local moment factorization; compactly supported smoothing and cutoff construction; differentiation along fibers via implicit-function theorem; affine derivative integration; endpoint continuity; independence of u,v using open moment image.

**Verified scope and remaining gap.** `Analog.EncoderRegularity.contDiffAt_of_triple_factorization` derives automatic C¹ regularity from an actual continuous source-box factorization. It constructs the pair-coordinate inverse, localizes the receiver by a Tietze extension on a smaller closed ball and uses a genuinely normalized smooth convolution kernel. `planar_affine_of_local_charts` assembles the affine representation through both endpoints without assuming encoder differentiability. The stronger `planar_affine_of_dense_charts` needs charts only over a set dense in the actual regular triple image and proves the required regularity and derivative propagation itself. `Analog.GeneralRigidity` provides independent tangent anchors, local sections, kernel calculations and integration; `Analog.RigidityCompletion` supplies the original-family coefficient-independence consequence of exactness. The remaining obligation is deriving the local charts from the collision implication through planar topology, not smoothing or dense propagation.

### 14. `prop:score` — proposition

Source: `sections/design_proof.tex`. **Complete general operational formula and shrinking-pair statement checked.**

**Context and hypotheses.** K≥4; φ is continuous on I and C¹ in the interior, strictly convex or strictly concave; ψ∈C¹(I) is strictly convex or strictly concave. E=c+us+vφ(s), with independent u,v. G is their 2×2 Gram matrix; w±=(−ψ′(±1),1). Λ is the all-pair infimum of squared received distance divided by squared nonzero target gap.

```latex
\begin{proposition}
\label{prop:score}
Under the hypotheses of Section~\ref{sec:synthesis}, let $\enc:I\to\R^2$ have the form \eqref{eq:affine} with $c,u,v\in\R^2$ and linearly independent $u,v$. Its operational score for $f_{\phi,\psi}:I^K\to\R$ is given by \eqref{eq:exactscore}.
The infimum is approached by pairs with received distance tending to zero.
\end{proposition}
```

**Dependencies.** Metric Cauchy–Schwarz; endpoint extrema of the dual-gradient norm; secant/mean-value bounds on the moment strip; explicit two-input paths realizing every first-order moment direction at a prescribed interior mean; one-sided endpoint slope continuity; local separation bounds and a contradiction argument yielding the epsilon/delta shrinking-pair witnesses.

**Verified scope and remaining gap.** `Analog.GeneralScore.general_operational_score` proves the actual all-pair operational identity for every nondegenerate planar two-feature curve and K>=2. The feature is strictly convex or concave on the closed source interval and differentiable in its interior; the mean-dependent term is convex or concave, differentiable within the closed interval, with continuous within-interval derivative. Thus endpoint derivatives are genuinely one-sided and the theorem covers the manuscript assumptions. `general_score_small_distance_sharpness` proves unequal-target admissible pairs at every positive received-distance radius and every positive score tolerance. `Analog.MomentPaths.exists_source_path_at_mean` constructs the two-input paths rather than assuming moment realizability. The separate variance identity also covers degenerate curves.

### 15. `cor:inverse-synthesis` — corollary

Source: `sections/design_proof.tex`. **Ellipse/Gram equivalence and positive reciprocal inverse optimum checked; unrestricted operational conclusion still depends on rigidity.**

**Context and hypotheses.** Same hypotheses as Theorem thm:sdp. g(s)=(s,φ(s)). C_P comprises symmetric X and a∈ℝ² with the 3×3 block matrix [[P,(g(s)−a)ᵀ],[g(s)−a,X]] positive semidefinite for every s. Nonaffineness implies X positive definite. Endpoint budgets are w±ᵀXw±≤t.

```latex
\begin{corollary}\label{cor:inverse-synthesis}
Under the hypotheses of Theorem~\ref{thm:sdp}, program~\eqref{eq:inverse-synthesis} attains a positive optimum $t_\star$ and gives $\Lambda_\sq^\star=K^2/t_\star$. An optimal encoder follows from the enclosing-ellipse reconstruction in Section~\ref{sec:inverse-synthesis}.
\end{corollary}
```

**Dependencies.** Theorem thm:sdp; Proposition prop:score; Schur complements; encoder/containing-ellipse bijection; positive definiteness from a nonaffine graph; compact objective sublevels and attainment.

**Verified scope and remaining gap.** `Analog.InverseSynthesis.positive_of_feasible` derives a positive-definite inverse Gram block from the nonaffine preprocessing graph. `feasible_iff_ellipse`, `ellipse_to_gram`, `gram_to_ellipse`, `roundtrip_gram` and `endpoint_cost_preserved` check the containing-ellipse and Gram correspondences. `inverse_optimum_attained_of_strict_shape` proves a positive attained inverse optimum equal to the reciprocal of the attained maximal Gram floor, without assuming an optimizer. The already verified score and planar synthesis provide the coefficient-family operational interpretation. The corollary's unrestricted continuous optimum still relies on the missing rigidity reduction.

### 16. `cor:transfer-unlabeled` — corollary

Source: `sections/transfer.tex`. **Actual peak-constrained moment-score transfer and zero-collision case checked; unrestricted competitor-class conclusion still depends on rigidity.**

**Context and hypotheses.** Desired functions satisfy Proposition prop:score hypotheses. 𝒟:[0,∞)→[0,∞) is continuous, 𝒟(0)=0, 𝒟(d)>0 for d>0; 𝒟(d)≥c_𝒟 d² throughout the attainable peak distance range [0,2K√P], and 𝒟(d)/d²→c_𝒟>0 as d↓0.

```latex
\begin{corollary}
Suppose $\mathscr D:[0,\infty)\to[0,\infty)$ is continuous, $\mathscr D(0)=0$, positive away from zero, and
$$
 \mathscr D(d)\ge c_{\mathscr D}d^2\quad(0\le d\le2K\sqrt P),\qquad
 \lim_{d\downarrow0}\frac{\mathscr D(d)}{d^2}=c_{\mathscr D}>0.
$$
Under the hypotheses of Proposition~\ref{prop:score}, every continuous encoder $\enc:I\to\R^2$ that satisfies the peak constraint and exactly computes $f_{\phi,\psi}:I^K\to\R$ satisfies $\Lambda_{\mathscr D}(\enc;f_{\phi,\psi})=c_{\mathscr D}\Lambda_{\sq}(\enc;f_{\phi,\psi})$. Consequently, every optimal encoder for this desired function remains optimal, and the optimal score is multiplied by $c_{\mathscr D}$.
\end{corollary}
```

**Dependencies.** Proposition prop:score including shrinking-pair attainment; lower-envelope inequality; product limit for the quotient; zero score for nonexact encoders from 𝒟(0)=0; maximization across all continuous competitors.

**Verified scope and remaining gap.** `Analog.CriterionTransfer.score_transfer` proves the exact operational infimum identity from the global lower envelope, the actual local quadratic limit and actual arbitrarily short sharp pairs. `peak_constrained_moment_transfer` derives the received-distance range from the physical peak constraint and applies the checked general shrinking-pair theorem to moment encoders. `collision_score_zero` covers nonexact collisions when the dissimilarity vanishes at zero. Thus the transfer step is checked on the coefficient class; extending the comparison to every continuous competitor still uses unrestricted rigidity. The manuscript corollary has no LaTeX label and remains part of this coverage inventory.

### 17. `prop:approx-rigidity` — proposition

Source: `sections/approximate_rigidity.tex`. **Actual encoder-class compactness, pair defect and constructed stability modulus checked; identification of the exact class with affine moment curves remains a premise.**

**Context and hypotheses.** Fix K,φ,ψ satisfying Theorem thm:rigidity and P>0. E has uniform norm ≤√P and a prescribed common modulus ω with ω(h)→0. D is globally L-Lipschitz, L>0, and its uniform target error is ≤ε. A_φ is the family c+us+vφ(s) with independent directions; distance is in the uniform norm.

```latex
\begin{proposition}
\label{prop:approx-rigidity}
For fixed $P$, $\omega$, and $L>0$, there is a nondecreasing function $\eta:[0,\infty)\to[0,\infty)$ with $\lim_{\epsilon\downarrow0}\eta(\epsilon)=0$ and the following property. For every $\epsilon\ge0$, if $E\in\mathcal E_{P,\omega}$ and an $L$-Lipschitz decoder $D:\R^2\to\R$ satisfy
$$
 \sup_{\mathbf s\in I^K}
 |D(r_E(\mathbf s))-f_{\phi,\psi}(\mathbf s)|\le\epsilon,
$$
then $\operatorname{dist}_\infty(E,\mathcal A_\phi)\le\eta(\epsilon)$. The function $\eta$ may also depend on the fixed $K$, $\phi$, and $\psi$.
\end{proposition}
```

**Dependencies.** Approximate collision inequality; Arzelà–Ascoli compactness and closedness of the encoder class; continuity/Lipschitz dependence of the scalar defect d_L; continuity of distance to A_φ even though A_φ is nonclosed; compact subsequence argument; exactness of the limit; Theorem thm:rigidity; construction, finiteness and monotonicity of η and its zero limit.

**Verified scope and remaining gap.** `Analog.ApproximateRigidity` constructs the modulus as a supremum of distances over actual defect sublevels with zero inserted for the empty case. It proves nonnegativity, monotonicity, η(0)=0 and the zero limit by minimizing the defect on compact sets at positive distance from the exact class. No closedness of that class is required. The file also proves the K-term complex-channel perturbation estimate, Lipschitz continuity of the actual pair defect with constant KL, zero-defect exactness and the defect bound from an L-Lipschitz approximate decoder.

`encoderClass_isCompact` derives closedness and Arzelà–Ascoli compactness for complex continuous encoders on the full interval with the actual peak and common-modulus bounds. It requires only the one-sided limit ω(h)→0 for h>0; no condition ω(0)=0 is added. `continuous_encoder_stability` assembles these steps and constructs η for any class containing all exact encoders. Its remaining structural premise is precisely exact-class identification. Taking that class to be the independent affine moment family still needs the unfinished unrestricted rigidity theorem; no independent proof of that premise is claimed.


## Additional proved claims outside numbered theorem environments

The phrase “all proofs” also includes proofs written in prose and numerical certificate arguments. The following list makes the main additional obligations explicit. Numerical simulation outcomes are empirical observations rather than universal theorems, but their reproduction remains a separate evidence requirement.

| Location | Claim requiring separate coverage |
|---|---|
| `sections/model.tex` | Positive squared separation implies exactness; checked compact-range recovery in `Analog.PlanarTopology` supplies receiver continuity, and `Analog.CriterionTransfer` derives the physical peak-distance bound. Remaining examples and prose specializations need their own matching declarations. |
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
3. Produce local triple factorizations from exactness via topology. Given continuous local charts, normalized convolution/Tietze regularization now derives encoder differentiability; the checked dense-chart argument derives propagation, and derivative integration reaches both endpoints. Native inverse sections and coefficient independence are also checked. The missing topological production of charts is the remaining step in this rigidity chain.
4. The operational all-pair score and admissible shrinking-pair sharpness are now checked for general strictly curved features and regular convex/concave mean-dependent terms at K≥2; variance additionally includes degenerate curves.
5. Arbitrary peak power and transmitter count are connected to the checked variance optimizer over all quadratic competitors, including degenerate/zero-score curves. The final theorem over every continuous peak-feasible encoder still needs the rigidity reduction and the resulting competitor-class argument.

Completing this chain would justify a claim about the unrestricted variance optimum. It would **not** justify “all proofs in the paper”: every other statement and additional claim above must also have its own complete checked coverage. Importing an unproved manuscript claim as a hypothesis or an axiom does not complete that coverage.

## Verification acceptance criteria

- Formal theorem types must retain the manuscript quantifiers and hypotheses, and definitions must model the stated operational channel, source interval, peak constraint, desired function and score.
- Every declaration advertised as verified must compile under the pinned Lean/mathlib versions, with no `sorry`, `admit`, `sorryAx`, invented axioms, or unproved manuscript theorem imported as a premise.
- The axiom audit and kernel recheck must cover the final dependency graph. The source hash report must match the packaged files.
- The manuscript acknowledgment and formalization appendix must list the achieved scope. Until every result above is covered, use “selected results have Lean-checked proofs,” not “all proofs are formalized.”

