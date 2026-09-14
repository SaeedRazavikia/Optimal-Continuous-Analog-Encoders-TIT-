# Native TikZ system and decoder geometry

## System model

`figures/tikz/system_model.tex` is a full-width schematic with a 17.75 cm by 5.72 cm bounding box. It depicts the same encoder at every terminal, a single complex additive sum, additive disturbance, and the explicit projection/readout decoder. Unit effective gains and synchronization are model assumptions, not a proposed synchronization protocol. The per-terminal constraint is pointwise: `sup_s |E(s)|^2 <= P`.

Suggested placement: directly after the system-model definition and target equation, as a top-position `figure*`.

Suggested caption:

> Shared continuous encoding over one synchronized complex multiple-access channel use. Each terminal obeys the same pointwise peak constraint. The receiver estimates the prescribed moment-minus-mean target from the noisy aggregate; the projection decoder in Section VI gives a sharp uniform disturbance guarantee.

Prefer a section reference instead of a hard-coded section number.

## Decoder geometry

`figures/tikz/decoder_geometry.tex` is a single-column figure with an 8.533 cm by 6.141 cm bounding box. Both axes have the same scale so horizontal projection is genuinely Euclidean. The representative map is the globally robust variance encoder

`E(s)/sqrt(P) = a s + i (b s^2 - 1)`,
`b=2/sqrt(3)` and `a=sqrt(b(2-b))`.

Normalized received coordinates are `(x,z)=(a m,b q-1)`. For K=4 the exact finite-K moment region has lower boundary `q_min(m)=m^2` and upper boundary

`q_max(m) = [3 + (4m-j)^2]/4`,

where `j` is one of `-3,-1,1,3` and `|4m-j|<=1`. Adjacent formulas agree at their shared endpoints. Jensen's inequality gives the lower boundary, attained by four identical inputs. The maximum of the convex function `sum_k s_k^2` on the compact slice `sum_k s_k=4m`, `s_k in [-1,1]`, occurs at a vertex. At such a vertex at most one coordinate lies strictly inside the interval, so three endpoint coordinates sum to `j` and the fourth equals `4m-j`. The slice is convex, hence connected, and its continuous scalar image under the second moment is an interval; every value between the minimum and maximum is attained. The teal region is therefore the exact K=4 received region, not only the convex hull.

The noiseless marked point uses `(m,q)=(0.65,0.61)`. It is feasible because `q_min=0.4225` and `q_max=0.79`. The observation has normalized coordinates `(1.49,0.61)` and its strip projection is `(a,0.61)`. The projected point lies outside the exact received region, intentionally: the decoder only needs a containing strip and the Lipschitz readout. The arrow from the noiseless point to the observation is exactly the normalized additive disturbance.

Suggested placement: immediately after the projection decoder theorem/proof, before the discussion of the tighter convex hull.

Suggested caption:

> Projection decoding for the optimal variance curve, shown in normalized received coordinates for K=4. The exact attained region (teal) lies inside the received strip `S_r={|x|<=a}`. The decoder projects an observation `y` onto this strip and evaluates `hat q-hat m^2`. The projected point need not be attainable. The same scale on both axes preserves Euclidean geometry.

The caption should mention `a=sqrt(b(2-b))`, `b=2/sqrt(3)` or reference the equation defining the optimal variance map. All paths, fills, labels, and plotted curves are native TikZ; there is no image inclusion.

Both figures compiled successfully in an isolated LaTeX preview. I rendered and inspected the preview, then corrected a left-edge label overflow and a projection/noise annotation collision. The main manuscript was not compiled or edited by this task.
