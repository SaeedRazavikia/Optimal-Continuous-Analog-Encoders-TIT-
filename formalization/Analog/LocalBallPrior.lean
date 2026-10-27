import Analog.GaussianScoreIdentity

/-!
# Actual local probability priors on the product plane

Uniform densities on positive-radius balls supply the regular local priors
used to convert the fixed-prior Gaussian converse into a pointwise worst-case
bound. The density is defined using the actual product Lebesgue volume;
normalization, local regularity, positivity, full mass, and local averaging
are proved rather than supplied as assumptions.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace Analog.LocalBallPrior
open GaussianScoreIdentity

/-- The normalized indicator of an ordinary product-norm ball. -/
def density (x : Plane) (r : ℝ) : Plane → ℝ :=
  (Metric.ball x r).indicator (fun _ => (volume.real (Metric.ball x r))⁻¹)

/-- Every positive-radius planar ball has finite positive real volume. -/
theorem ball_volume_pos (x : Plane) {r : ℝ} (hr : 0 < r) :
    0 < volume.real (Metric.ball x r) :=
  ENNReal.toReal_pos (Metric.measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne

/-- Ball-prior densities are measurable. -/
theorem measurable_density (x : Plane) (r : ℝ) : Measurable (density x r) :=
  measurable_const.indicator measurableSet_ball

/-- Ball-prior densities are everywhere nonnegative. -/
theorem density_nonneg (x : Plane) (r : ℝ) (m : Plane) : 0 ≤ density x r m := by
  by_cases hm : m ∈ Metric.ball x r
  · simp only [density, indicator_of_mem hm]
    positivity
  · simp [density, hm]

/-- The normalized ball density is Lebesgue integrable. -/
theorem integrable_density (x : Plane) (r : ℝ) : Integrable (density x r) := by
  apply (integrable_indicator_iff measurableSet_ball).mpr
  exact integrableOn_const (C := (volume.real (Metric.ball x r))⁻¹) measure_ball_lt_top.ne

/-- The actual Lebesgue integral of the density is one. -/
theorem integral_density (x : Plane) {r : ℝ} (hr : 0 < r) :
    (∫ m, density x r m) = 1 := by
  rw [density, integral_indicator_const _ measurableSet_ball]
  simp only [smul_eq_mul, mul_inv_cancel₀ (ball_volume_pos x hr).ne']

/-- The density is C¹ on the open ball, regardless of its boundary jump. -/
theorem contDiffOn_density (x : Plane) (r : ℝ) :
    ContDiffOn ℝ 1 (density x r) (Metric.ball x r) := by
  apply (contDiffOn_const (c := (volume.real (Metric.ball x r))⁻¹)).congr
  intro m hm
  simp [density, hm]

/-- The actual density is strictly positive at every point of its open ball. -/
theorem density_pos (x : Plane) {r : ℝ} (hr : 0 < r) {m : Plane}
    (hm : m ∈ Metric.ball x r) : 0 < density x r m := by
  simp only [density, indicator_of_mem hm]
  exact inv_pos.mpr (ball_volume_pos x hr)

/-- The constructed probability prior gives full mass to the open ball. -/
theorem priorLaw_ae_ball (x : Plane) (r : ℝ) :
    ∀ᵐ m ∂priorLaw (density x r), m ∈ Metric.ball x r := by
  apply (ae_withDensity_iff (measurable_density x r).ennreal_ofReal).mpr
  filter_upwards with m hm
  by_contra hnot
  simp [density, hnot] at hm

/-- Continuous functions are integrable for the actual normalized ball law. -/
theorem integrable_continuous (x : Plane) (r : ℝ) (g : Plane → ℝ)
    (hg : Continuous g) : Integrable g (priorLaw (density x r)) := by
  have hball : IntegrableOn g (Metric.ball x r) :=
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall x r)).mono_set
      Metric.ball_subset_closedBall
  have hprod : Integrable (fun m => density x r m * g m) := by
    have hi := (integrable_indicator_iff (s := Metric.ball x r) measurableSet_ball).mpr
      (hball.const_mul (volume.real (Metric.ball x r))⁻¹)
    convert hi using 1
    funext m
    by_cases hm : m ∈ Metric.ball x r <;> simp [density, hm]
  apply (integrable_withDensity_iff_integrable_smul'
    (measurable_density x r).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  simpa only [ENNReal.toReal_ofReal (density_nonneg x r _), smul_eq_mul] using hprod

/-- A pointwise lower bound on a ball gives the same lower bound for its
normalized prior expectation. -/
theorem integral_ge_of_on_ball (x : Plane) {r c : ℝ} (hr : 0 < r)
    (g : Plane → ℝ) (hg : Continuous g)
    (hbound : ∀ m ∈ Metric.ball x r, c ≤ g m) :
    c ≤ ∫ m, g m ∂priorLaw (density x r) := by
  letI := priorLaw_isProbability (density x r) (density_nonneg x r)
    (integrable_density x r) (integral_density x hr)
  have hh := integral_mono_ae (integrable_const c) (integrable_continuous x r g hg)
    ((priorLaw_ae_ball x r).mono (fun m hm => hbound m hm))
  simpa using hh

/-- Every neighborhood of a point with `a < g x` supports an actual regular
probability prior whose expectation of g is strictly larger than a. -/
theorem exists_regular_prior_above {U : Set Plane} (hU : IsOpen U) {x : Plane}
    (hx : x ∈ U) (g : Plane → ℝ) (hg : Continuous g) {a : ℝ} (ha : a < g x) :
    ∃ Ω : Set Plane, ∃ p : Plane → ℝ,
      IsOpen Ω ∧ Ω ⊆ U ∧ Measurable p ∧ (∀ m, 0 ≤ p m) ∧ Integrable p ∧
      (∫ m, p m) = 1 ∧ ContDiffOn ℝ 1 p Ω ∧ (∀ m ∈ Ω, 0 < p m) ∧
      (∀ᵐ m ∂priorLaw p, m ∈ Ω) ∧ a < ∫ m, g m ∂priorLaw p := by
  obtain ⟨b, hab, hbx⟩ := exists_between ha
  have hnear : U ∩ {m | b < g m} ∈ 𝓝 x :=
    inter_mem (hU.mem_nhds hx) (hg.continuousAt (Ioi_mem_nhds hbx))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨Metric.ball x r, density x r, Metric.isOpen_ball,
    (fun m hm => (hball hm).1), measurable_density x r, density_nonneg x r,
    integrable_density x r, integral_density x hr, contDiffOn_density x r,
    (fun _ hm => density_pos x hr hm), priorLaw_ae_ball x r, ?_⟩
  exact hab.trans_le (integral_ge_of_on_ball x hr g hg (fun m hm => (hball hm).2.le))

/-- Uniform pointwise proximity on the ball controls the error of the
actual prior average, with no limit or prior-concentration hypothesis. -/
theorem integral_close_of_on_ball (x : Plane) {r ε c : ℝ} (hr : 0 < r)
    (g : Plane → ℝ) (hg : Continuous g)
    (hclose : ∀ m ∈ Metric.ball x r, |g m - c| ≤ ε) :
    |(∫ m, g m ∂priorLaw (density x r)) - c| ≤ ε := by
  letI := priorLaw_isProbability (density x r) (density_nonneg x r)
    (integrable_density x r) (integral_density x hr)
  have hh := norm_integral_le_of_norm_le_const
    ((priorLaw_ae_ball x r).mono (fun m hm =>
      show ‖g m - c‖ ≤ ε by simpa only [Real.norm_eq_abs] using hclose m hm))
  rw [integral_sub (integrable_continuous x r g hg) (integrable_const c)] at hh
  simpa only [integral_const, measureReal_univ_eq_one, one_smul, mul_one,
    Real.norm_eq_abs] using hh

/-- Continuity supplies actual arbitrarily accurate local-ball priors
inside any prescribed open neighborhood of the center. -/
theorem exists_ball_prior_close {U : Set Plane} (hU : IsOpen U) {x : Plane}
    (hx : x ∈ U) (g : Plane → ℝ) (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, Metric.ball x r ⊆ U ∧
      (∀ m ∈ Metric.ball x r, |g m - g x| < ε) ∧
      |(∫ m, g m ∂priorLaw (density x r)) - g x| ≤ ε := by
  have hnear : U ∩ {m | |g m - g x| < ε} ∈ 𝓝 x := by
    apply inter_mem (hU.mem_nhds hx)
    have hc : ContinuousAt (fun m => |g m - g x|) x := by fun_prop
    exact hc (Iio_mem_nhds (show |g x - g x| < ε by simpa using hε))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r, hr, fun m hm => (hball hm).1, fun m hm => (hball hm).2, ?_⟩
  exact integral_close_of_on_ball x hr g hg (fun m hm => (hball hm).2.le)

end Analog.LocalBallPrior
