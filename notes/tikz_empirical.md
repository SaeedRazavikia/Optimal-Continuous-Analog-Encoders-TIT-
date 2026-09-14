# Native TikZ empirical and tradeoff figures

## Source and export

- `figures/tikz/finite_noise.tex`: four panels, matching the archived 72 Monte Carlo cells; common vertical scales within each target row; filled/solid separation-optimal curves and open/dashed prior-aware curves; color and circle/square markers identify terminal count.
- `figures/tikz/pareto_frontier.tex`: exact analytic small-noise frontier and the three containing ellipses in feature coordinates. The frontier includes each exact transition and a denser endpoint mesh. The ellipse panel uses `axis equal image` to preserve the feature-plane geometry.
- `code/export_tikz_empirical.py` uses only the Python standard library. It exports the existing results and evaluates the analytic formulas without running Monte Carlo. It checks all 32 archived Pareto designs to absolute coefficient tolerance `1e-12`, and verifies the archived paired 95% intervals before export.
- Shared dependencies: TikZ, PGFPlots with `compat=1.18`, `groupplots`, and colors `figBlue`, `figOrange`, `figGray`. No raster or external-PDF images appear in either figure.
- Panel axes use 8-point text and native vector marks. Figure inputs are intended directly inside `figure*` without `resizebox` so that fonts retain their size. An isolated two-pass build measured widths of 514.224 pt (finite noise) and 514.937 pt (Pareto), both below the intended 7.167-inch full text width. Both panels were rendered and visually inspected at 150 dpi; legends, tick labels, and plotted data were unclipped, with no overfull-box warnings.

## Recommended captions

### Finite noise

Empirical MSE reduction relative to the specified baseline, $100(1-\mathrm{MSE}_{\rm design}/\mathrm{MSE}_{\rm base})$. Solid curves maximize worst-case squared separation; dashed curves use the prior-aware small-noise coefficients. All designs satisfy the same pointwise peak constraint and use the same projection/readout and target-clipping architecture. Error bars show pointwise paired 95% confidence intervals and are often smaller than the markers. Endpoint Beta denotes $2X-1$ with $X\sim\operatorname{Beta}(0.3,0.3)$. Each source-law/terminal-count scenario uses 200,000 archived paired draws; no new Monte Carlo samples were generated for this rendering.

The final sentence on archival rendering belongs in reproducibility notes rather than necessarily in the manuscript caption. Existing numerical values and limitations remain valid.

### Pareto frontier

Variance design with a prescribed separation floor. (a) Reduction of the optimal small-noise MSE coefficient relative to the separation-optimal encoder; markers identify the transition from an inactive to an active separation constraint. (b) The feature curve $(s,s^2)$ and containing ellipses for full robustness, $90\%$ retention, and the uniform-$K=16$ prior optimum. The ellipses express the peak constraint in feature coordinates; they are not noise confidence regions. The curves in (a) are analytic, whereas the finite-noise gains in the adjacent table are empirical.

## Scope checks

The small-noise gain decreases after each marked transition because the plotted ordinate is reduction relative to the robust reference; the theorem's unnormalized minimum loss increases there. The clipping-dependent finite-noise results should not be labeled asymptotic or interpreted as proof of finite-noise MSE optimality. The ellipse panel shows feature coordinates, not the complex encoder plane. Its ellipses satisfy $(g-a)^\top G(g-a)=P$ for the associated encoders, with center $(0,1/b)$ and horizontal/vertical semiaxes $1/\sqrt{b(2-b)}$ and $1/b$ when $P=1$.

## Export verification

The exporter reproduced all 72 finite-noise cells and checked all 32 saved Pareto designs. The maximum absolute difference between its standard-library bisection implementation and the archived Pareto coefficient was `2.220446049250313e-16`. The final inputs are compiled natively at 8-point figure text.
