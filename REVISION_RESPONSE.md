# Revision response

This revision addresses the six weaknesses identified in the preceding assessment. It preserves the prescribed one-use, shared continuous planar encoder model.

| Issue | Revision | Evidence and remaining limits |
|---|---|---|
| Novelty not sufficiently established | Added the substantially closer restricted Cauchy–Pexider precedent and narrowed the first contribution to classification from scalar exactness. Credited integration/regularization as an established method. | Primary theorem-level comparison in `notes/novelty_review.md`; no historical-firstness claim or exhaustive-priority certificate. |
| Semi-infinite formulation without a general certified procedure | Added a finite-grid approximation theorem, continuous-feasibility scaling, dual upper witnesses, and an explicit stopping rule; implemented an exponential Jensen-gap example. | Rational interval verification and stored primal/dual witnesses certify the global score bracket. C2 features require verified evaluation and derivative bounds. |
| Different assumptions obscured theorem dependencies | Added an assumption/dependency table and a proved zero-score endpoint example. Removed the unnecessary finite endpoint derivative requirement on the local feature. | Rigidity, exact score, numerical synthesis, and decoding now state separate hypotheses. Proof review found no invalidating defect within that scope. |
| Operational benefit not established under finite noise | Added paired Gaussian-noise experiments with equal peak power and the same decoder architecture; included a prior-tuned high-SNR comparator and an analytic MSE limit. | Results concern the stated priors, encoders, and decoder. They demonstrate why the worst-case optimum need not minimize finite-noise MSE. |
| Examples suggested excessive target breadth | Separated feature changes from readout changes; moved the restricted polynomial theorem and proof to an appendix. | Quadratic, quartic, and exponential features have distinct roles. The quartic target is correctly identified as a Jensen gap. |
| Evidence and manuscript hierarchy needed improvement | Added exact rational certificates and statistical comparisons, moved secondary criterion/alphabet results to an appendix, and removed reconstruction language from the article. | All code/data and detailed audit records remain in the source package. Numerical checks support implementation, not topology or historical originality. |

The new literature comparison resolves the previous overstatement risk, but it does not prove historical priority. The proof review is independent within this writing workflow; no external researcher has reviewed or endorsed the theorem. The paper remains a research manuscript requiring the author's final technical and bibliographic review.

Further development is recorded in `DEVELOPMENT_RECORD.md`, including the global constrained small-noise frontier, inverse-metric synthesis, operational error bounds, qualitative stability, and the second numerical implementation.
