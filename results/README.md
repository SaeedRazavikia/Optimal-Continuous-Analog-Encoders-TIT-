# Recorded numerical results

These JSON files are the retained numerical records. They are separate from
the Lean proof audit in `formalization/verification/report.json`.

| Record | Producing script |
|---|---|
| `certified_synthesis.json` | `code/certified_synthesis.py` — rational optimization witnesses |
| `finite_noise.json` | `code/finite_noise.py` — finite-noise simulations |
| `pareto_frontier.json` | `code/pareto_frontier.py` — robustness/MSE tradeoff |
| `independent_reproduction.json` | `code/independent_reproduce.py` — second implementation checks |
| `decoder_checks.json` | `code/verify_decoders.py` — decoder implementation checks |
| `extension_rerun.json` | `code/verify_extension.py` — analytic and numerical extension checks |

Paths in the table are relative to the repository root. See the
[reproduction guide](../docs/REPRODUCING.md) for commands and scope.
Regeneration may also create CSV exports, sample diagnostics, and rendered
figures; these duplicate outputs are ignored by Git. The manuscript uses
embedded data in its figure sources, so rerunning a simulation does not
automatically revise the paper.
