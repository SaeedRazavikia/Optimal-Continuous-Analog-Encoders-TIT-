# Communications presentation and proof revision

This revision makes the manuscript easier to enter from communications theory while retaining its information-theoretic converse and precise computation model.

## Presentation and organization

- Uses **transmitter**, **input distribution**, and **encoder design** consistently in the active paper and figure labels. Nonorthogonal feature directions are distinguished from statistical correlation.
- Rewrites the abstract around the channel, computation task, transmit curve, receiver, and robustness–accuracy tradeoff. The classification preview explicitly retains its target assumptions.
- Defines both normalized moments in the system model, explains the physical meaning of the separation score, and introduces `E(s)=c+us+vφ(s)` and the receiver's moment recovery before the rigidity proof.
- Explains the Gram entries as coefficient energies and an inner product, and the small-noise coefficient through `MSE=N₀J+o(N₀)`.
- Orders the main sections as system model, rigidity, encoder design, explicit curves, decoding and implementation, small-noise design, certified design, and numerical results.
- Places the finite-noise table after the experimental setup and keeps the performance figure before the conclusions. All six scientific figures remain native TikZ/PGFPlots.
- Removes the repeated sensing/calibration introduction from Implementation Errors and balances the reference columns.

## Proof exposition

The quadratic-frontier reduction now proves the feasible boundary directly. Convexity of `At+(bt+c)²` on `[0,1]` reduces the peak constraint to two endpoint inequalities. This replaces a reference to the quartic proof that did not establish the needed quadratic fact.

The general score's sharpness proof now varies two actual transmitter inputs. Their unequal feature derivatives allow any first-order moment direction. Endpoint limits give the exact score, and arbitrarily small path steps give the shrinking-pair clause. This avoids requiring an attainable-neighborhood theorem in the score proof and matches the new Lean development.

## Formal verification

The final verified declaration list and exact source hashes are in `formalization/verification/report.json`. `formalization/THEOREM_MAP.md` gives the main interfaces; `formalization/COVERAGE.md` records every numbered manuscript statement and distinguishes complete results, specializations, and conditional steps.

The unrestricted continuous-encoder theorem still requires the topological local-factorization and automatic-differentiability arguments. Successful verification of the new finite-dimensional, operational, and probabilistic components does not by itself complete that theorem or every proof in the paper. The acknowledgment therefore identifies selected verified results rather than claiming complete formalization.
