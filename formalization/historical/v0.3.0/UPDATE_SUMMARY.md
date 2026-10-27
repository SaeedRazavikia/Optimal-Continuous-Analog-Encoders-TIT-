# Formalization update — 27 October 2026

This update follows the current supplied `Main.tex` (10 numbered mathematical
statements). It does not claim a complete formalization of the paper.

## New formal results

The development adds **49 public declarations in six modules**:

| Module | Declarations | Main result |
|---|---:|---|
| `HeterogeneousScore` | 10 | Actual node-dependent aggregate and operational score identities, with distinct local features/offsets and possibly singular common columns. |
| `SingularGram` | 3 | All-rank planar PSD Gram reconstruction, power reduction, and common feature columns across nodes. |
| `HeterogeneousSynthesis` | 2 | Actual continuous encoders from every feasible common-Gram SDP point, all continuum peak bounds, operational score guarantee, and exactness at positive score. |
| `HeterogeneousRigidity` | 4 | Common derivative coefficients from explicit distinct-node determinant/anchor assumptions, and closed-interval integration with separate offsets. |
| `RadiusMinimax` | 23 | Full bounded-noise minimax result: attained pair modulus, explicit Borel midpoint decoder, and lower bound against every decoder, including zero radius. |
| `FiniteCertificates` | 7 | PSD trace-product nonnegativity, finite weighted weak-duality arithmetic, scaling, and certificate gaps. |

The radius-minimax result now has a complete general compact-input proof.
The SDP additions close the constructive feasible-point part of the current
proof, including singular Gram matrices and zero separation. They do not yet
prove optimizer attainment under all current assumptions.

## Changes to the verification record

- The previous audit covered 673 declarations in 47 modules. All 55 source and
  configuration hashes matched before editing, and all 47 original proof
  modules are unchanged.
- The updated inventory contains **722 declarations in 53 modules**. The full build and `--trust=0` kernel/axiom audit **passed**, with no warnings
  and no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`. The exact
  result and source hashes are in `verification/report.json`.
- `check_manuscript.py` binds the inventory to the full current manuscript and
  exact statements. `update_audit.py --check` rejects stale imports and theorem
  inventories. Both guards were tested on intentionally stale copies.
- Historical coverage and audit files are retained in `historical/v0.2.0/`.
  Their obsolete 17-statement inventory is not used for current coverage.
- The exact rational exponential certificate was rerun successfully. Its
  reported bounds are approximately 0.41964508992808314 and
  0.4196702244375766. This numerical check is separate from the Lean audit.

## Substantive unfinished work

1. Full heterogeneous continuous-encoder rigidity: dense completion separation,
   planar topology, heterogeneous regularization, and final necessity assembly.
2. General heterogeneous SDP attainment: reduced compactness for dependent
   features, zero-optimum attainment, and positive optimum iff Lipschitz readout.
3. New Gaussian minimax and Bayes converses: weighted van Trees, variational
   density, uniform/sequential limits, and exclusion of singular designs.
4. Full node-dependent grid/dual-certificate assembly and the general gradient
   sandwich, beyond the retained special cases and added arithmetic lemmas.

The proof review did not identify a mathematical counterexample in the current
arguments. It did identify substantial stale coverage claims, which have been
corrected. The manuscript itself and files outside `formalization/` are unchanged.
Start with `COVERAGE.md` for statement-level scope and `THEOREM_MAP.md` for the
principal Lean declarations. Detailed mathematical reviews are in `notes/`.
