# Formalization revision

The new modules develop the three requested areas: continuous-encoder rigidity, general operational score and encoder design, and the probabilistic frontier. Their exact quantifiers and hypotheses are recorded in `formalization/COVERAGE.md`; successful strict verification is recorded in `formalization/verification/report.json`.

The general score now uses actual admissible source pairs and one-sided endpoint derivatives. Its sharpness witnesses come from two moving transmitter inputs. The design proof converts genuine continuum-feasible PSD matrices into continuous exact encoders with an actual operational guarantee. The rigidity chain now derives local moment geometry, differential kernels, endpoint representation, and coefficient independence, while explicitly retaining its remaining topology and regularization obligations.

The small-noise development proves the limiting argument through dominated convergence and treats the actual variance decoder. The frontier development proves properties of an actual feasible-design infimum, with conditional and attained statements distinguished in the theorem map.

These additions do not justify saying every manuscript proof is formalized. No missing mathematical theorem has been inserted as an axiom. The presentation revision and corrected proof organization are described in `REVISION_NOTES.md`.
