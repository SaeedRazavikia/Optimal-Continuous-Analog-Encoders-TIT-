# TIT research roadmap

## 1. Scientific thesis

For a prescribed class of nonlinear distributed functions, the requirement of exact computation forces every shared continuous planar encoder into a specific feature-curve family. This structure converts global analog encoder design into a tractable geometric optimization, and selected subclasses admit explicit optimal curves.

This is the intended thesis to test and substantiate. Its strongest new foundation is the proposed continuous-rigidity theorem; its correctness and novelty remain subject to review.

The main question is the optimal analog counterpart of the squared-separation ChannelComp design problem. Keep the source function fixed, use one complex channel use, and impose a per-transmitter pointwise peak constraint. The curve includes its input parameterization, centering, scale, and orientation; its geometric image alone does not specify the encoder.

## 2. Core results and intended hierarchy

### A. Necessary encoder structure

Start from

$$
f_{\phi,\psi}(\mathbf s)=\frac1K\sum_k\phi(s_k)
-\psi\left(\frac1K\sum_k s_k\right).
$$

The proposed theorem assumes $K\ge4$, $\phi\in C([-1,1])\cap C^1((-1,1))$ nonaffine, and $\psi$ continuous and $C^1$ in the interior, strictly convex or strictly concave. It asserts that every continuous exact planar encoder, and only such encoders, has the form

$$
\mathscr E(s)=c+us+v\phi(s)
$$

with $u,v$ real-linearly independent.

The conceptual issue is why a scalar target forces two additive statistics. The proof first shows that equal received sums for triples must preserve both moments, using a common fourth variable. It then rules out continuous variation within moment fibers and derives automatic differentiability before proving affine dependence on the features.

This necessity theorem is more important than the observation that two features can be sent through I/Q coordinates. Treat the removal of encoder differentiability as a major claim requiring a careful proof, not a technical footnote. If it fails, retain the earlier $C^1$ theorem with an explicit narrower competitor class.

### B. Exact optimization over the forced curve

For the stronger assumptions $\phi,\psi\in C^1([-1,1])$, each strictly convex or strictly concave, define the Gram matrix

$$
G=\begin{pmatrix}|u|^2&\operatorname{Re}(u\bar v)\\
\operatorname{Re}(u\bar v)&|v|^2\end{pmatrix},\qquad
w_\pm=(-\psi'(\pm1),1)^{\mathsf T}.
$$

The proposed exact score is

$$
\Lambda_{\rm sq}(\mathscr E;f)
=\frac{K^2}{\max\{w_-^{\mathsf T}G^{-1}w_-,\ w_+^{\mathsf T}G^{-1}w_+\}}.
$$

Audit both directions: the all-pair inequality and the realizable shrinking pairs that make it sharp. An arbitrary direction in a formal moment plane is not automatically a realizable input perturbation; the local rank argument is essential.

The synthesis theorem uses a $3\times3$ positive semidefinite Gram matrix $H$, its lower $2\times2$ block $G$, and $z(s)=(1,s,\phi(s))^{\mathsf T}$. It maximizes $\lambda$ subject to

$$
z(s)^{\mathsf T}Hz(s)\le P\quad\text{for every }s\in[-1,1],\qquad
G-\lambda w_\pm w_\pm^{\mathsf T}\succeq0,
$$

with global score $K^2\lambda$. The seven real variables comprise six independent entries of $H$ and $\lambda$. The continuum of peak inequalities remains part of the problem. The proposed rank-two reconstruction eliminates a relaxation gap by reducing the translation norm while preserving the metric.

An exact design reduction is valuable even where no elementary formula exists. Present explicit solutions only for classes actually solved.

### C. Explicit geometry

Use three complete examples:

| Example | Purpose | Scope to retain |
| --- | --- | --- |
| Variance and the quadratic-feature nonlinear-mean class | Familiar target, closed-form peak-optimal parabola, explicit decoder | Global continuous result for $K\ge4$ depends on rigidity. The variance separation improvement over the centered parabola is about 3.13%, not an MSE gain. |
| Fourth-order Jensen gap $\operatorname{mean}(s^4)-m^4$ | Demonstrates a nonquadratic local feature and nonparabolic optimal curve | Do not call it the fourth central moment. Audit the algebraic root, peak factorization, and global optimality certificate. |
| A moment interaction such as $mq$ | Demonstrates a different readout and useful criterion comparison | Polynomial theorem requires nonnegative coefficients and a common parity of mean exponents; it does not cover arbitrary polynomials. |

For $f=q-\psi(m)$ with even strictly convex or concave $\psi$, let $M=|\psi'(1)|$, $t=M/2$, and

$$
b=\frac{2}{1-t^2+t\sqrt{t^2+2}},\qquad
\mathscr E^\star(s)=\sqrt P[\sqrt{b(2-b)}s+i(bs^2-1)].
$$

The claimed optimum is $K^2P b^2(b-1)$. For variance, $b=2/\sqrt3$ and the value is $4K^2P/(9+6\sqrt3)$.

For the quartic Jensen gap, the stored coefficients give a score approximately $0.058533506998K^2P$. The full formula and proof are in the continuous extension. Re-derive the normalizations before using these numbers.

### D. Operational meaning and usable decoding

Retain the exact uniform-amplification interpretation: one scalar decoder can attain disturbance constant $1/\sqrt{\Lambda_{\rm sq}}$. Credit the classical extension argument. Explain how the newly optimized encoder makes that interpretation computation-specific.

Develop an implementable decoder for the explicit examples. A promising task is to project the noisy received point onto a convex received region containing all attainable sums, then apply a readout with the proved Lipschitz constant on that region. Check the region, metric, projection property, and full readout bound. This is a proposed development task, not a newly certified theorem in this package.

The raw algebraic inverse may grow too fast outside the attainable set. Keep fixed-radius minimax error and Gaussian MSE as separate objectives. A short counterexample or discussion can establish the operational boundary; the full long-arc proof need not dominate the article.

## 3. Research sequence

| Stage | Work | Required output before advancing |
| --- | --- | --- |
| T1 | Freeze the exact model, target assumptions, and objective | A one-page theorem-scope table and notation sheet |
| T2 | Audit collision completion, topology, convolution, and affine rigidity | A line-by-line proof assessment, repairs or counterexamples, and a corrected theorem statement |
| T3 | Audit the score, continuous peak constraint, attainment, and planar reconstruction | A complete global synthesis proof and precise classification of what is solved |
| T4 | Verify and organize quadratic, quartic, and polynomial cases | Complete encoder/decoder/value/converse examples with exact normalizations |
| T5 | Certify a usable decoder and selected numerical designs | Reproducible implementation and a clearly scoped operational guarantee |
| T6 | Complete the novelty and companion-overlap comparison | A theorem-level matrix supported by primary sources |
| T7 | Write the manuscript from the validated result hierarchy | A coherent draft with full essential proofs and restrained examples |

Stages T2 and T3 are foundational. A polished introduction should not precede a decision on their validity. Literature review can proceed alongside proof assessment when the working environment permits.

## 4. Manuscript architecture

1. **Problem and contribution.** Explain the unresolved global curve-design question and distinguish exact representation from optimal conditioning.
2. **Analog ChannelComp model.** Define the continuous encoder class, peak constraint, fixed target, score, and operational interpretation.
3. **Necessary curve geometry.** Present the continuous-rigidity theorem and its main proof ideas.
4. **Global encoder synthesis.** Derive the exact score and convex formulation, including attainment and planar reconstruction.
5. **Explicit optimal curves.** Develop the three selected examples as complete solutions, not a catalog.
6. **Decoding and evidence.** Give practical decoding, relevant numerical checks, and carefully separated stochastic-error comparisons.
7. **Boundaries and extensions.** State the $K=3$ gap, dimensional limits, criterion dependence, and restricted function class.

Put essential reasoning in the manuscript. Move repetitive algebra and secondary cases to appendices. Do not append the entire coherence article to the new paper. Use a brief circular example only if it strengthens the explanation of function-dependent geometry.

## 5. Evidence that would make the result useful

The reader should be able to supply a target from the stated class, obtain an encoder and decoder, and inspect a global optimality certificate. Compare against a centered moment curve, sensible power-allocation baselines, and finite-dimensional numerical searches under exactly the same constraints. Numerical agreement is supportive; the continuum converse supplies global optimality.

For any numerically synthesized nonpolynomial feature, certify the peak inequality between sample points. For polynomial features, investigate exact interval nonnegativity or validated root/interval methods. Reuse archived experiments only with their actual settings and dates. The packaging step did not generate new scientific evidence.

Do not make the paper depend on a large percentage gain for variance. Its stronger contribution is the classification and exact solution of a global infinite-dimensional design problem.

## 6. Scope control

The following are valuable future questions but not prerequisites for a coherent $K\ge4$ planar paper: a full $K=3$ classification, arbitrary signal dimension, arbitrary symmetric functions, arbitrary user-specific encoders, average-power optimization, and globally minimum Gaussian MSE. Explore them only when they resolve a concrete weakness or provide a short decisive extension.

Local-quadratic metric transfer can be a concise corollary. The general-radial-criterion quadratic reduction can be included if its role is clear; it is not an all-noise closed-form solution. Keep the Gaussian exponential certificates primarily in TCOM.

## 7. Content decision

A strong main paper requires a correct and meaningfully new necessity theorem, a complete global synthesis argument, and explicit examples or certified computations demonstrating use. If the continuous extension is invalid, report whether the earlier smooth theorem still supports a sufficiently substantial paper. If novelty substantially overlaps known functional equations, revise the contribution around the genuinely new optimization and operational results. Do not compensate by adding more coherence lemmas or synthetic target examples.
