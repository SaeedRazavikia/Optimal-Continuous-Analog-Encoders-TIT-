import Analog.ExplicitVarianceDecoder
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Leading mean-square error under vanishing additive noise

The random noiseless observation and disturbance can have any joint law.
A globally Lipschitz scalar decoder, differentiable almost surely at the
noiseless observation, has the expected squared directional derivative as
its leading small-noise MSE coefficient.  The theorem proves the pointwise
limit from a Fréchet derivative and justifies its integration by dominated
convergence.  It does not assume Gaussianity or independence.
-/

namespace Analog.SmallNoise

open Filter MeasureTheory
open scoped Topology NNReal

section Deterministic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Squared error normalized by the squared amplitude of the disturbance. -/
noncomputable def normalizedError (D : E → ℝ) (r z : E) (t : ℝ) : ℝ :=
  ((D (r + t • z) - D r) / t) ^ 2

/-- Differentiability gives the actual directional small-noise limit. -/
theorem normalizedError_tendsto {D : E → ℝ} {r : E} {J : E →L[ℝ] ℝ}
    (hD : HasFDerivAt D J r) (z : E) :
    Tendsto (normalizedError D r z) (𝓝[>] (0 : ℝ)) (𝓝 ((J z) ^ 2)) := by
  have h := (hD.lim_real z).comp tendsto_inv_nhdsGT_zero
  simpa only [Function.comp_def, inv_inv, smul_eq_mul, normalizedError,
    div_eq_mul_inv, mul_comm] using h.pow 2

/-- A uniform Lipschitz estimate supplies an amplitude-independent bound. -/
theorem normalizedError_le {D : E → ℝ} {L : ℝ≥0}
    (hD : LipschitzWith L D) (r z : E) (t : ℝ) :
    normalizedError D r z t ≤ (L : ℝ) ^ 2 * ‖z‖ ^ 2 := by
  by_cases ht : t = 0
  · simp only [normalizedError, ht, zero_smul, add_zero, sub_self, zero_div, zero_pow (by decide : 2 ≠ 0)]
    positivity
  have habs : 0 < |t| := abs_pos.mpr ht
  have h := hD.dist_le_mul (r + t • z) r
  have he : |D (r + t • z) - D r| ≤ (L : ℝ) * (|t| * ‖z‖) := by
    simpa only [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs] using h
  have hq : |(D (r + t • z) - D r) / t| ≤ (L : ℝ) * ‖z‖ := by
    rw [abs_div, div_le_iff₀ habs]
    nlinarith [he]
  calc
    normalizedError D r z t = |(D (r + t • z) - D r) / t| ^ 2 := by
      simp [normalizedError]
    _ ≤ ((L : ℝ) * ‖z‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hq 2
    _ = (L : ℝ) ^ 2 * ‖z‖ ^ 2 := by ring

/-- The squared received-coordinate gradient equals the inverse-Gram
quadratic form, including the channel-sum normalization by `K²`. -/
theorem gram_gradient_energy (ux uy vx vy K p q : ℝ) :
    ((vy * p - uy * q) / (K * (ux * vy - uy * vx))) ^ 2 +
      ((-vx * p + ux * q) / (K * (ux * vy - uy * vx))) ^ 2 =
    ((vx ^ 2 + vy ^ 2) * p ^ 2 - 2 * (ux * vx + uy * vy) * p * q +
      (ux ^ 2 + uy ^ 2) * q ^ 2) /
      (K ^ 2 * ((ux ^ 2 + uy ^ 2) * (vx ^ 2 + vy ^ 2) -
        (ux * vx + uy * vy) ^ 2)) := by
  have hGram : (ux ^ 2 + uy ^ 2) * (vx ^ 2 + vy ^ 2) -
      (ux * vx + uy * vy) ^ 2 = (ux * vy - uy * vx) ^ 2 := by ring
  rw [hGram]
  field_simp
  ring

end Deterministic

/-- An interior strip point has a neighborhood on which projection is inactive. -/
theorem projected_readout_eventuallyEq {X : Type*} [TopologicalSpace X]
    {p : X → ℝ × ℝ} {x : X} (hp : ContinuousAt p x)
    (hx : -1 < (p x).1 ∧ (p x).1 < 1) (B C : ℝ) (R : ℝ × ℝ → ℝ) :
    (fun y => R (Strip.project B C (p y))) =ᶠ[𝓝 x] (fun y => R (p y)) := by
  have hn : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 ((p x).1) := isOpen_Ioo.mem_nhds hx
  filter_upwards [hp.fst.preimage_mem_nhds hn] with y hy
  rw [Strip.project_fixes_strip B C ⟨hy.1.le, hy.2.le⟩]

/-- The explicit variance decoder is differentiable wherever the recovered
mean is strictly between the strip endpoints. -/
theorem variance_decoder_differentiableAt (e : Curve) (K : ℕ) (y : ℂ)
    (hy : -1 < (e.inverseMoments K (complexCoordinates y)).1 ∧
      (e.inverseMoments K (complexCoordinates y)).1 < 1) :
    DifferentiableAt ℝ (e.explicitVarianceDecoder K) y := by
  have hp : ContinuousAt (fun z => e.inverseMoments K (complexCoordinates z)) y := by
    unfold Curve.inverseMoments complexCoordinates
    fun_prop
  have hre : Differentiable ℝ (fun z : ℂ => z.re) := Complex.reCLM.differentiable
  have him : Differentiable ℝ (fun z : ℂ => z.im) := Complex.imCLM.differentiable
  have hraw : DifferentiableAt ℝ
      (fun z => Strip.varianceReadout (e.inverseMoments K (complexCoordinates z))) y := by
    unfold Curve.inverseMoments complexCoordinates Strip.varianceReadout
    simp only [div_eq_mul_inv]
    fun_prop
  exact hraw.congr_of_eventuallyEq
    (projected_readout_eventuallyEq hp hy e.B e.C Strip.varianceReadout)


section Integration

variable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure Ω}

/-- The normalized error is measurable under measurable observations and noise. -/
theorem normalizedError_measurable {D : E → ℝ} (hD : Continuous D)
    {r z : Ω → E} (hr : Measurable r) (hz : Measurable z) (t : ℝ) :
    Measurable (fun ω => normalizedError D (r ω) (z ω) t) := by
  exact (((hD.measurable.comp (hr.add (hz.const_smul t))).sub
    (hD.measurable.comp hr)).div_const t).pow_const 2

/-- The limiting squared derivative is itself integrable, even without a
separate measurability assumption on the derivative field. -/
theorem directional_second_moment_integrable {D : E → ℝ} {L : ℝ≥0}
    (hD : LipschitzWith L D) {r z : Ω → E}
    (hr : Measurable r) (hz : Measurable z)
    (hz2 : Integrable (fun ω => ‖z ω‖ ^ 2) μ)
    {J : Ω → E →L[ℝ] ℝ}
    (hJ : ∀ᵐ ω ∂μ, HasFDerivAt D (J ω) (r ω)) :
    Integrable (fun ω => (J ω (z ω)) ^ 2) μ := by
  have hlim : ∀ᵐ ω ∂μ, Tendsto (normalizedError D (r ω) (z ω))
      (𝓝[>] (0 : ℝ)) (𝓝 ((J ω (z ω)) ^ 2)) :=
    hJ.mono fun ω hω => normalizedError_tendsto hω (z ω)
  have hmeas := aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0 : ℝ))
    (fun t => (normalizedError_measurable hD.continuous hr hz t).aestronglyMeasurable) hlim
  apply (hz2.const_mul ((L : ℝ) ^ 2)).mono' hmeas
  filter_upwards [hlim] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact le_of_tendsto' hω (fun t => normalizedError_le hD (r ω) (z ω) t)

/-- A finite noise second moment justifies the integrated derivative limit.
No probability density, noise distribution, or independence is required. -/
theorem leading_mse_amplitude {D : E → ℝ} {L : ℝ≥0}
    (hD : LipschitzWith L D) {r z : Ω → E}
    (hr : Measurable r) (hz : Measurable z)
    (hz2 : Integrable (fun ω => ‖z ω‖ ^ 2) μ)
    {J : Ω → E →L[ℝ] ℝ}
    (hJ : ∀ᵐ ω ∂μ, HasFDerivAt D (J ω) (r ω)) :
    Tendsto (fun t : ℝ => ∫ ω, normalizedError D (r ω) (z ω) t ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ ω, (J ω (z ω)) ^ 2 ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun ω => (L : ℝ) ^ 2 * ‖z ω‖ ^ 2)
  · apply Filter.Eventually.of_forall
    intro t
    exact (normalizedError_measurable hD.continuous hr hz t).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro t
    apply Filter.Eventually.of_forall
    intro ω
    change ‖((D (r ω + t • z ω) - D (r ω)) / t) ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact normalizedError_le hD (r ω) (z ω) t
  · exact hz2.const_mul _
  · filter_upwards [hJ] with ω hω
    exact normalizedError_tendsto hω (z ω)

/-- The same limit in noise-power coordinates: the perturbation has amplitude
`sqrt N`, and the mean-square error is divided by `N`. -/
theorem leading_mse_power {D : E → ℝ} {L : ℝ≥0}
    (hD : LipschitzWith L D) {r z : Ω → E}
    (hr : Measurable r) (hz : Measurable z)
    (hz2 : Integrable (fun ω => ‖z ω‖ ^ 2) μ)
    {J : Ω → E →L[ℝ] ℝ}
    (hJ : ∀ᵐ ω ∂μ, HasFDerivAt D (J ω) (r ω)) :
    Tendsto (fun N : ℝ =>
      (∫ ω, (D (r ω + Real.sqrt N • z ω) - D (r ω)) ^ 2 ∂μ) / N)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ ω, (J ω (z ω)) ^ 2 ∂μ)) := by
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with N hN
      exact Real.sqrt_pos.mpr hN
  have h := (leading_mse_amplitude hD hr hz hz2 hJ).comp hsqrt
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with N hN
  change (∫ ω, normalizedError D (r ω) (z ω) (Real.sqrt N) ∂μ) = _
  simp only [normalizedError, div_pow, Real.sq_sqrt (le_of_lt hN), integral_div]

/-- Exact noiseless decoding identifies the centered decoder value with the
actual computation target in the leading MSE theorem. -/
theorem leading_mse_power_exact {D : E → ℝ} {L : ℝ≥0}
    (hD : LipschitzWith L D) {r z : Ω → E} {f : Ω → ℝ}
    (hr : Measurable r) (hz : Measurable z)
    (hz2 : Integrable (fun ω => ‖z ω‖ ^ 2) μ)
    (hexact : ∀ᵐ ω ∂μ, D (r ω) = f ω)
    {J : Ω → E →L[ℝ] ℝ}
    (hJ : ∀ᵐ ω ∂μ, HasFDerivAt D (J ω) (r ω)) :
    Tendsto (fun N : ℝ =>
      (∫ ω, (D (r ω + Real.sqrt N • z ω) - f ω) ^ 2 ∂μ) / N)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ ω, (J ω (z ω)) ^ 2 ∂μ)) := by
  refine (leading_mse_power hD hr hz hz2 hJ).congr fun N => ?_
  congr 1
  apply integral_congr_ae
  filter_upwards [hexact] with ω hω
  rw [hω]

end Integration

section VarianceApplication

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The actual inverse-map and strip-projection variance decoder satisfies
the leading MSE limit whenever the noiseless empirical mean is interior
almost surely. Its differentiability is proved above from local inactivity,
rather than supplied as a hypothesis of this specialization. -/
theorem variance_leading_mse (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (hdet : 0 < e.A * e.B - e.C ^ 2) {r z : Ω → ℂ} {f : Ω → ℝ}
    (hr : Measurable r) (hz : Measurable z)
    (hz2 : Integrable (fun ω => ‖z ω‖ ^ 2) μ)
    (hexact : ∀ᵐ ω ∂μ, e.explicitVarianceDecoder K (r ω) = f ω)
    (hmean : ∀ᵐ ω ∂μ,
      -1 < (e.inverseMoments K (complexCoordinates (r ω))).1 ∧
      (e.inverseMoments K (complexCoordinates (r ω))).1 < 1) :
    Tendsto (fun N : ℝ =>
      (∫ ω, (e.explicitVarianceDecoder K (r ω + Real.sqrt N • z ω) - f ω) ^ 2 ∂μ) / N)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ ω, (fderiv ℝ (e.explicitVarianceDecoder K) (r ω) (z ω)) ^ 2 ∂μ)) := by
  apply leading_mse_power_exact (e.explicitVarianceDecoder_lipschitz hK hdet)
    hr hz hz2 hexact
  filter_upwards [hmean] with ω hω
  exact (variance_decoder_differentiableAt e K (r ω) hω).hasFDerivAt

end VarianceApplication

section Covariance

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [SFinite ν]

/-- Square-integrable real functions have an integrable product. -/
theorem integrable_mul_of_squares {a b : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b)
    (ha2 : Integrable (fun ω => a ω ^ 2) μ)
    (hb2 : Integrable (fun ω => b ω ^ 2) μ) :
    Integrable (fun ω => a ω * b ω) μ := by
  apply (ha2.add hb2).mono' (ha.mul hb).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_mul]
  change |a ω| * |b ω| ≤ a ω ^ 2 + b ω ^ 2
  nlinarith [sq_nonneg (|a ω| - |b ω|), sq_abs (a ω), sq_abs (b ω),
    sq_nonneg (a ω), sq_nonneg (b ω)]

/-- Independence is represented by the product measure.  The entire second
moment of a two-coordinate directional derivative is evaluated, including
its covariance term. -/
theorem independent_directional_second_moment [SFinite μ]
    {a b : Ω → ℝ} {x y : Ξ → ℝ}
    (ha : Measurable a) (hb : Measurable b)
    (hx : Measurable x) (hy : Measurable y)
    (ha2 : Integrable (fun ω => a ω ^ 2) μ)
    (hb2 : Integrable (fun ω => b ω ^ 2) μ)
    (hx2 : Integrable (fun ξ => x ξ ^ 2) ν)
    (hy2 : Integrable (fun ξ => y ξ ^ 2) ν) :
    (∫ p : Ω × Ξ, (a p.1 * x p.2 + b p.1 * y p.2) ^ 2 ∂μ.prod ν) =
      (∫ ω, a ω ^ 2 ∂μ) * (∫ ξ, x ξ ^ 2 ∂ν) +
      2 * (∫ ω, a ω * b ω ∂μ) * (∫ ξ, x ξ * y ξ ∂ν) +
      (∫ ω, b ω ^ 2 ∂μ) * (∫ ξ, y ξ ^ 2 ∂ν) := by
  have hcross := (integrable_mul_of_squares ha hb ha2 hb2).mul_prod
    (integrable_mul_of_squares hx hy hx2 hy2)
  have hfun : (fun p : Ω × Ξ => (a p.1 * x p.2 + b p.1 * y p.2) ^ 2) =
      (fun p : Ω × Ξ => a p.1 ^ 2 * x p.2 ^ 2 +
        2 * ((a p.1 * b p.1) * (x p.2 * y p.2)) + b p.1 ^ 2 * y p.2 ^ 2) := by
    funext p
    ring
  have h1 := integral_add ((ha2.mul_prod hx2).add (hcross.const_mul 2))
    (hb2.mul_prod hy2)
  have h2 := integral_add (ha2.mul_prod hx2) (hcross.const_mul 2)
  simp only [Pi.add_apply] at h1 h2
  rw [hfun, h1, h2, integral_const_mul]
  rw [integral_prod_mul (fun ω => a ω ^ 2) (fun ξ => x ξ ^ 2),
    integral_prod_mul (fun ω => a ω * b ω) (fun ξ => x ξ * y ξ),
    integral_prod_mul (fun ω => b ω ^ 2) (fun ξ => y ξ ^ 2)]
  ring

/-- Isotropic noise with coordinate second moments one half yields the
one-half factor in the complex-channel leading MSE formula. -/
theorem isotropic_directional_second_moment [SFinite μ]
    {a b : Ω → ℝ} {x y : Ξ → ℝ}
    (ha : Measurable a) (hb : Measurable b)
    (hx : Measurable x) (hy : Measurable y)
    (ha2 : Integrable (fun ω => a ω ^ 2) μ)
    (hb2 : Integrable (fun ω => b ω ^ 2) μ)
    (hx2 : Integrable (fun ξ => x ξ ^ 2) ν)
    (hy2 : Integrable (fun ξ => y ξ ^ 2) ν)
    (hxx : (∫ ξ, x ξ ^ 2 ∂ν) = 1 / 2)
    (hyy : (∫ ξ, y ξ ^ 2 ∂ν) = 1 / 2)
    (hxy : (∫ ξ, x ξ * y ξ ∂ν) = 0) :
    (∫ p : Ω × Ξ, (a p.1 * x p.2 + b p.1 * y p.2) ^ 2 ∂μ.prod ν) =
      ((∫ ω, a ω ^ 2 ∂μ) + (∫ ω, b ω ^ 2 ∂μ)) / 2 := by
  rw [independent_directional_second_moment ha hb hx hy ha2 hb2 hx2 hy2,
    hxx, hyy, hxy]
  ring

end Covariance

end Analog.SmallNoise
