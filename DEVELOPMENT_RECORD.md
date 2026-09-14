## Submission-format release

The author confirmed that the bivariate draft is not planned for submission. We removed its bibliography entry and introductory comparison paragraph, and revised the cover letter and active submission notes. The source delivery omits the draft enclosure. Both manuscript layouts use the same mathematical section sources; the Lean proof files retain their audited hashes. The proof package is prepared for a new GitHub repository, pending a destination supplied by the author. No repository URL or public-availability claim has been added to the paper before upload.

# Development record (preceding technical revision)

This historical record documents the preceding technical strengthening. The current requested priorities and completed presentation work appear in `PRESENTATION_REVISION.md` and `SUBMISSION_PREPARATION.md`; the outside-review and fresh-environment suggestions below are not active tasks in this revision.

This record documents the work following agreement on the remaining strengthening steps. It distinguishes completed development from external actions that have not occurred.

| Agreed step | Concrete result supplied | Remaining limit |
|---|---|---|
| Challenge originality | Adversarial primary-source comparison, contribution matrix, and explicit attribution | No exhaustive priority certificate or specialist opinion |
| Independently inspect proofs | Additional internal review of rigidity, score, inverse synthesis, Pareto, stability, and implementation arguments | Same agent workflow; outside mathematical reconstruction remains pending |
| Develop a deeper bounded result | Exact small-noise frontier; unique optimal Gram matrix; continuous convex value with plateau and active branch; explicit full-class quadratic solution | Specified decoder and leading coefficient, not unrestricted finite-noise Bayesian optimization |
| Clarify synthesis geometry | Six-variable inverse-metric separation and five-variable frontier programs | Classical convex tools; continuum constraints still require certification |
| Strengthen operational motivation | Synchronized sensing example; implementation/gain-error bound; shrink-before-quantization construction | Calibration and synchronization are assumed resources |
| Investigate approximate rigidity | Qualitative proximity under common encoder continuity and decoder Lipschitz bounds | No rate and no implication from small average MSE alone |
| Independently reproduce evidence | Second exact verifier, analytic moments/coefficients, independent projection checks, high-precision frontier spots | Same environment; different-machine full regeneration remains pending |
| Prepare external review and positioning | `EXTERNAL_REVIEW_PACKET.md` and updated novelty, assessment, and overlap records | No researcher contacted or manuscript submitted |

## Evidence anchors

- `notes/structural_review.md` records the proof review. No invalidating defect was found in the reviewed chain. The uniform scalar quantization example requires integer B>=2 for its stated shrink factor.
- `results/independent_reproduction.json` records a second implementation: exact exponential certificate gap approximately 0.00598911%, 16 analytic design cells, 256 decoder comparisons, and two active-frontier points.
- `results/pareto_frontier.json`, its CSV companion, and `notes/pareto_reproduction.md` document 32 empirical rows and 12 convex numerical comparisons. They complement the analytic proof.
- Retaining 90% of optimal squared separation permits at most 5.41% larger uniform disturbance amplification and gives 17.68% or 29.07% lower limiting MSE coefficient for independent uniform sources at K=4 or K=16. These are asymptotic reductions, not universal finite-SNR gains.
- Reproduction found some K=4 endpoint-concentrated cells measurably nonasymptotic at 30 dB. The interpretation should retain this qualification.

## Outstanding actions and completion conditions

1. **External theorem and significance review:** obtain an assessment addressing the prepared questions, match novelty objections to specific prior theorems, and resolve mathematical objections. Internal reviews must not be relabeled as external review.
2. **Different-machine reproduction:** run the prepared commands in a fresh environment and retain logs. Exact certificate checks should pass; numerical differences should be explained using tolerances and statistical uncertainty.
3. **Final author and overlap review:** compare the actual companion against the updated allocation, including the new TIT small-noise frontier, then finalize author information, disclosure, and claims.

The development adds substantive results. It does not certify historical originality, external peer review, or acceptance.


## Communications and formalization revision

The final strict audit passes for 405 public declarations in 29 Lean modules. This revision adds general operational score and encoder-design attainment, an attained Gram-risk frontier, the small-noise DCT argument and variance specialization, and native local moment geometry with a conditional independent affine representation. See REVISION_NOTES.md for the presentation and proof-exposition changes, and formalization/COVERAGE.md for the precise remaining obligations. The unrestricted continuous theorem and complete manuscript remain unformalized.


## Proof organization revision

Merged encoder rigidity and encoder design. Moved supporting lemmas/proposition and the long quartic, frontier, and grid proofs to ordered appendices; retained four explanatory proofs in the main text. Refreshed stable-label correspondence and source locations without changing the Lean proof sources. See PROOF_ORGANIZATION.md.
