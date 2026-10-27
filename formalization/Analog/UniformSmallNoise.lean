import Analog.GeneralTargetSmallNoise
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Uniform small-noise Gaussian achievability

Uniform continuity of the actual derivative yields a uniform Taylor bound.
Gaussian tail control then yields uniform convergence of actual normalized
risks, and compactness identifies the attained worst-case coefficient.
-/
noncomputable section
namespace Analog.UniformSmallNoise
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Uniform continuity of the derivative supplies a uniform first-order
remainder estimate by the mean-value theorem, rather than as an assumption. -/
theorem uniform_taylor_bound (F : ℂ → ℝ) (J : ℂ → ℂ →L[ℝ] ℝ)
    (hF : ∀ x, HasFDerivAt F (J x) x) (hJ : UniformContinuous J)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x v : ℂ, ‖v‖ < δ →
      |F (x+v) - F x - J x v| ≤ ε * ‖v‖ := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp hJ ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x v hv
  let g : ℂ → ℝ := fun y => F y - J x y
  have hd : ∀ y ∈ Metric.ball x δ,
      HasFDerivWithinAt g (J y - J x) (Metric.ball x δ) y := by
    intro y _
    exact ((hF y).sub (J x).hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ y ∈ Metric.ball x δ, ‖J y-J x‖ ≤ ε := by
    intro y hy
    exact (show ‖J y-J x‖ < ε from by
      simpa only [dist_eq_norm] using hclose hy).le
  have hx : x ∈ Metric.ball x δ := by simpa using hδ
  have hxv : x+v ∈ Metric.ball x δ := by simpa [dist_eq_norm] using hv
  have hm := (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb hx hxv
  simp only [g, map_add, Real.norm_eq_abs, add_sub_cancel_left] at hm
  have heq : F (x+v) - (J x x + J x v) - (F x - J x x) = F (x+v) - F x - J x v := by ring
  rwa [heq] at hm

/-- A global derivative bound supplies the global Lipschitz constant. -/
theorem lipschitz_of_derivative_bound (F : ℂ → ℝ) (J : ℂ → ℂ →L[ℝ] ℝ)
    (hF : ∀ x, HasFDerivAt F (J x) x) {L : ℝ≥0}
    (hL : ∀ x, ‖J x‖ ≤ L) : LipschitzWith L F := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hb := (convex_univ : Convex ℝ (Set.univ : Set ℂ)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hF x).hasFDerivWithinAt) (fun x _ => hL x)
    (Set.mem_univ y) (Set.mem_univ x)
  simpa only [dist_eq_norm] using hb

/-- A useful squared-error comparison for two bounded real directional slopes. -/
theorem square_difference_bound (a b C e : ℝ)
    (ha : |a| ≤ C) (hb : |b| ≤ C) (he : |a-b| ≤ e) :
    |a^2-b^2| ≤ 2*C*e := by
  have hC : 0 ≤ C := (abs_nonneg a).trans ha
  have he0 : 0 ≤ e := (abs_nonneg (a-b)).trans he
  have hp : |a+b| ≤ 2*C := (abs_add_le a b).trans (by linarith)
  have hid : a^2-b^2 = (a-b)*(a+b) := by ring
  rw [hid, abs_mul]
  nlinarith [mul_le_mul he hp (abs_nonneg (a+b)) he0]

/-- Squared Gaussian norm has mean one for the constructed circular law. -/
theorem gaussian_norm_second_moment :
    (∫ z : ℂ, ‖z‖^2 ∂GaussianNoise.standardComplexGaussian) = 1 := by
  have hx : Integrable (fun z : ℂ => z.re^2) GaussianNoise.standardComplexGaussian := by
    exact (GaussianNoise.complex_norm_square_integrable).mono'
      (by fun_prop) (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [Complex.normSq_apply z, Complex.normSq_eq_norm_sq z, sq_nonneg z.im])
  have hy : Integrable (fun z : ℂ => z.im^2) GaussianNoise.standardComplexGaussian := by
    exact (GaussianNoise.complex_norm_square_integrable).mono'
      (by fun_prop) (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [Complex.normSq_apply z, Complex.normSq_eq_norm_sq z, sq_nonneg z.re])
  have heq : (fun z : ℂ => ‖z‖^2) = (fun z => z.re^2+z.im^2) := by
    funext z
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [heq, integral_add hx hy, GaussianNoise.complex_real_second_moment,
    GaussianNoise.complex_imag_second_moment]
  norm_num

/-- A measurable tail envelope, independent of the noiseless observation. -/
def tailEnvelope (δ t : ℝ) (z : ℂ) : ℝ :=
  if δ ≤ |t| *‖z‖ then ‖z‖^2 else 0

theorem tailEnvelope_measurable (δ t : ℝ) : Measurable (tailEnvelope δ t) := by
  unfold tailEnvelope
  exact Measurable.ite (isClosed_le continuous_const (continuous_const.mul continuous_norm)).measurableSet
    (by fun_prop) measurable_const

theorem tailEnvelope_bounds (δ t : ℝ) (z : ℂ) :
    0 ≤ tailEnvelope δ t z ∧ tailEnvelope δ t z ≤ ‖z‖^2 := by
  unfold tailEnvelope
  split_ifs <;> simp

theorem tailEnvelope_integrable (δ t : ℝ) :
    Integrable (tailEnvelope δ t) GaussianNoise.standardComplexGaussian := by
  apply GaussianNoise.complex_norm_square_integrable.mono'
    (tailEnvelope_measurable δ t).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (tailEnvelope_bounds δ t z).1]
    exact (tailEnvelope_bounds δ t z).2

/-- The second-moment tail vanishes as the noise amplitude tends to zero. -/
theorem tail_integral_tendsto {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t : ℝ => ∫ z : ℂ, tailEnvelope δ t z ∂GaussianNoise.standardComplexGaussian)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
  have hpoint (z : ℂ) : Tendsto (fun t : ℝ => tailEnvelope δ t z) (𝓝 (0 : ℝ)) (𝓝 0) := by
    have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| *‖z‖ < δ := by
      have hc : Continuous (fun t : ℝ => |t| *‖z‖) := continuous_abs.mul continuous_const
      have hm : |(0 : ℝ)| * ‖z‖ ∈ Set.Iio δ := by simpa using hδ
      have ht := (hc.continuousAt : ContinuousAt _ (0 : ℝ)).preimage_mem_nhds (isOpen_Iio.mem_nhds hm)
      simpa only [abs_zero, zero_mul] using ht
    apply tendsto_const_nhds.congr'
    filter_upwards [hsmall] with t ht
    simp [tailEnvelope, not_le.mpr ht]
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := GaussianNoise.standardComplexGaussian) (bound := fun z : ℂ => ‖z‖^2)
    (F := fun t : ℝ => tailEnvelope δ t) (f := fun _ : ℂ => (0 : ℝ))
    (Filter.Eventually.of_forall fun t => (tailEnvelope_measurable δ t).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tailEnvelope_bounds δ t z).1]
      exact (tailEnvelope_bounds δ t z).2)
    GaussianNoise.complex_norm_square_integrable (Filter.Eventually.of_forall hpoint)
  simpa using h

/-- A uniform Taylor bound controls squared normalized error using one
noise-only tail envelope, uniformly over all noiseless observations. -/
theorem normalized_error_difference_bound (F : ℂ → ℝ) (J : ℂ → ℂ →L[ℝ] ℝ)
    {L : ℝ≥0} (hLip : LipschitzWith L F) (hL : ∀ x, ‖J x‖ ≤ L)
    {ε δ : ℝ} (hε : 0 ≤ ε)
    (hTaylor : ∀ x v : ℂ, ‖v‖ < δ → |F (x+v)-F x-J x v| ≤ ε*‖v‖)
    (x z : ℂ) {t : ℝ} (ht : 0 < t) :
    |SmallNoise.normalizedError F x z t - (J x z)^2| ≤
      (2*(L : ℝ)*ε)*‖z‖^2 + (4*(L : ℝ)^2)*tailEnvelope δ t z := by
  let a := (F (x+t • z)-F x)/t
  let b := J x z
  have ha : |a| ≤ (L : ℝ)*‖z‖ := by
    have hd := hLip.dist_le_mul (x+t • z) x
    have hd' : |F (x+t • z)-F x| ≤ (L : ℝ)*(t*‖z‖) := by
      simpa only [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht] using hd
    dsimp [a]
    rw [abs_div, abs_of_pos ht, div_le_iff₀ ht]
    change |F (x+t • z)-F x| ≤ (L : ℝ)*‖z‖*t
    nlinarith
  have hb : |b| ≤ (L : ℝ)*‖z‖ := by
    have h := (J x).le_opNorm z
    have hh : |J x z| ≤ ‖J x‖*‖z‖ := by simpa only [Real.norm_eq_abs] using h
    exact hh.trans (mul_le_mul_of_nonneg_right (hL x) (norm_nonneg z))
  change |a^2-b^2| ≤ _
  by_cases hlarge : δ ≤ |t| * ‖z‖
  · have he : |a-b| ≤ 2*(L : ℝ)*‖z‖ := by
      have h := abs_sub a b
      linarith
    have hsq := square_difference_bound a b ((L : ℝ)*‖z‖) (2*(L : ℝ)*‖z‖) ha hb he
    rw [tailEnvelope, if_pos hlarge]
    have hn : 0 ≤ (2*(L : ℝ)*ε)*‖z‖^2 := by positivity
    nlinarith
  · have hv : ‖t • z‖ < δ := by
      simpa only [norm_smul, Real.norm_eq_abs] using lt_of_not_ge hlarge
    have hsmall := hTaylor x (t • z) hv
    have he : |a-b| ≤ ε*‖z‖ := by
      have hid : a-b = (F (x+t • z)-F x-J x (t • z))/t := by
        simp only [map_smul, smul_eq_mul]
        dsimp [a, b]
        field_simp
      rw [hid, abs_div, abs_of_pos ht, div_le_iff₀ ht]
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_assoc,
        mul_comm t, mul_left_comm ε] using hsmall
    have hsq := square_difference_bound a b ((L : ℝ)*‖z‖) (ε*‖z‖) ha hb he
    rw [tailEnvelope, if_neg hlarge]
    nlinarith

/-- Normalized actual Gaussian MSE at amplitude t and noiseless observation x. -/
def risk (F : ℂ → ℝ) (t : ℝ) (x : ℂ) : ℝ :=
  ∫ z : ℂ, SmallNoise.normalizedError F x z t ∂GaussianNoise.standardComplexGaussian

def energy (J : ℂ → ℂ →L[ℝ] ℝ) (x : ℂ) : ℝ :=
  ((J x 1)^2+(J x Complex.I)^2)/2

theorem normalizedError_integrable (F : ℂ → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L F) (x : ℂ) (t : ℝ) :
    Integrable (fun z : ℂ => SmallNoise.normalizedError F x z t)
      GaussianNoise.standardComplexGaussian := by
  apply (GaussianNoise.complex_norm_square_integrable.const_mul ((L : ℝ)^2)).mono'
    (SmallNoise.normalizedError_measurable hLip.continuous measurable_const measurable_id t).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact SmallNoise.normalizedError_le hLip x z t

/-- Actual Gaussian risks differ uniformly from their derivative energies by
a vanishing-tail bound derived from the genuine Taylor estimate. -/
theorem risk_difference_bound (F : ℂ → ℝ) (J : ℂ → ℂ →L[ℝ] ℝ)
    (hF : ∀ x, HasFDerivAt F (J x) x) {L : ℝ≥0}
    (hLip : LipschitzWith L F) (hL : ∀ x, ‖J x‖ ≤ L)
    {ε δ : ℝ} (hε : 0 ≤ ε)
    (hTaylor : ∀ x v : ℂ, ‖v‖ < δ → |F (x+v)-F x-J x v| ≤ ε*‖v‖)
    (x : ℂ) {t : ℝ} (ht : 0 < t) :
    |risk F t x - energy J x| ≤ 2*(L : ℝ)*ε + (4*(L : ℝ)^2) *
      ∫ z : ℂ, tailEnvelope δ t z ∂GaussianNoise.standardComplexGaussian := by
  have hri := normalizedError_integrable F hLip x t
  have hdi := SmallNoise.directional_second_moment_integrable hLip
    (measurable_const : Measurable (fun _ : ℂ => x)) measurable_id
    GaussianNoise.complex_norm_square_integrable (Filter.Eventually.of_forall fun _ => hF x)
  change Integrable (fun z : ℂ => (J x z)^2) GaussianNoise.standardComplexGaussian at hdi
  have hbound := (GaussianNoise.complex_norm_square_integrable.const_mul (2*(L : ℝ)*ε)).add
    ((tailEnvelope_integrable δ t).const_mul (4*(L : ℝ)^2))
  have hdiff : |risk F t x - energy J x| ≤ ∫ z : ℂ,
      (2*(L : ℝ)*ε)*‖z‖^2 + (4*(L : ℝ)^2)*tailEnvelope δ t z
      ∂GaussianNoise.standardComplexGaussian := by
    rw [risk, energy, ← GeneralTargetSmallNoise.gaussian_clm_second_moment (J x),
      ← integral_sub hri hdi, ← Real.norm_eq_abs]
    exact (norm_integral_le_integral_norm _).trans (integral_mono (hri.sub hdi).norm hbound
      (fun z => by
        rw [Real.norm_eq_abs]
        exact normalized_error_difference_bound F J hLip hL hε hTaylor x z ht))
  have hsum := integral_add
    (GaussianNoise.complex_norm_square_integrable.const_mul (2*(L : ℝ)*ε))
    ((tailEnvelope_integrable δ t).const_mul (4*(L : ℝ)^2))
  rw [hsum, integral_const_mul, integral_const_mul, gaussian_norm_second_moment, mul_one] at hdiff
  exact hdiff

/-- The normalized actual Gaussian risks converge uniformly on the entire
observation plane under a bounded uniformly continuous derivative. -/
theorem risk_tendstoUniformly (F : ℂ → ℝ) (J : ℂ → ℂ →L[ℝ] ℝ)
    (hF : ∀ x, HasFDerivAt F (J x) x) (hJ : UniformContinuous J)
    {L : ℝ≥0} (hLpos : 0 < L) (hL : ∀ x, ‖J x‖ ≤ L) :
    TendstoUniformly (risk F) (energy J) (𝓝[>] (0 : ℝ)) := by
  have hl : (0 : ℝ) < L := hLpos
  have hLip := lipschitz_of_derivative_bound F J hF hL
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he : 0 < ε/(4*(L : ℝ)) := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hTaylor⟩ := uniform_taylor_bound F J hF hJ he
  have htail : Tendsto (fun t : ℝ => (4*(L : ℝ)^2) *
      ∫ z : ℂ, tailEnvelope δ t z ∂GaussianNoise.standardComplexGaussian)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tail_integral_tendsto hδ)).mono_left
      nhdsWithin_le_nhds
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, (4*(L : ℝ)^2) *
      ∫ z : ℂ, tailEnvelope δ t z ∂GaussianNoise.standardComplexGaussian < ε/2 :=
    htail.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε/2))
  filter_upwards [hsmall, self_mem_nhdsWithin] with t ht htpos
  intro x
  have hb := risk_difference_bound F J hF hLip hL he.le hTaylor x htpos
  have hid : 2*(L : ℝ)*(ε/(4*(L : ℝ))) = ε/2 := by field_simp; ring
  rw [hid] at hb
  rw [Real.dist_eq, abs_sub_comm]
  linarith

/-- The derivative-energy coefficient is continuous whenever the derivative is. -/
theorem energy_continuous (J : ℂ → ℂ →L[ℝ] ℝ) (hJ : Continuous J) :
    Continuous (energy J) := by
  exact (((hJ.clm_apply continuous_const).pow 2).add
    ((hJ.clm_apply continuous_const).pow 2)).div_const 2

/-- All normalized risks have a global bound derived from the Lipschitz
constant and the actual unit-power circular Gaussian law. -/
theorem risk_bound (F : ℂ → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L F) (t : ℝ) (x : ℂ) :
    risk F t x ≤ (L : ℝ)^2 := by
  have hb := integral_mono (normalizedError_integrable F hLip x t)
    (GaussianNoise.complex_norm_square_integrable.const_mul ((L : ℝ)^2))
    (fun z => SmallNoise.normalizedError_le hLip x z t)
  simpa only [integral_const_mul, gaussian_norm_second_moment, mul_one] using hb

/-- The actual worst-case normalized Gaussian risk over a compact moment
image converges to the attained maximum derivative energy. This is an upper
achievability result for the displayed fixed decoder, not an estimator converse. -/
theorem worst_case_amplitude_limit (F : ℂ → ℝ) (J : ℂ → ℂ →L[ℝ] ℝ)
    (hF : ∀ x, HasFDerivAt F (J x) x) (hJ : UniformContinuous J)
    {L : ℝ≥0} (hLpos : 0 < L) (hL : ∀ x, ‖J x‖ ≤ L)
    (M : Set ℂ) (hM : IsCompact M) (hne : M.Nonempty) :
    ∃ xstar ∈ M, (∀ x ∈ M, energy J x ≤ energy J xstar) ∧
      Tendsto (fun t : ℝ => sSup ((risk F t) '' M))
        (𝓝[>] (0 : ℝ)) (𝓝 (energy J xstar)) := by
  have hLip := lipschitz_of_derivative_bound F J hF hL
  obtain ⟨xstar, hxstar, hmax⟩ := hM.exists_isMaxOn hne (energy_continuous J hJ.continuous).continuousOn
  refine ⟨xstar, hxstar, hmax, ?_⟩
  have hunif := Metric.tendstoUniformly_iff.mp (risk_tendstoUniformly F J hF hJ hLpos hL)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hunif (ε/2) (by linarith)] with t ht
  have hbounded : BddAbove ((risk F t) '' M) := by
    refine ⟨(L : ℝ)^2, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    exact risk_bound F hLip t x
  have hupper : sSup ((risk F t) '' M) ≤ energy J xstar + ε/2 := by
    apply csSup_le (hne.image _)
    rintro _ ⟨x, hx, rfl⟩
    have hxclose := ht x
    rw [Real.dist_eq] at hxclose
    have hb := (abs_lt.mp hxclose).1
    have hxm : energy J x ≤ energy J xstar := hmax hx
    linarith only [hb, hxm]
  have hlower : energy J xstar - ε/2 ≤ sSup ((risk F t) '' M) := by
    have hs := le_csSup hbounded (Set.mem_image_of_mem (risk F t) hxstar)
    have hxclose := ht xstar
    rw [Real.dist_eq] at hxclose
    have hb := (abs_lt.mp hxclose).2
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Noise-power form of the actual normalized risk used by the manuscript. -/
def powerRisk (F : ℂ → ℝ) (N : ℝ) (x : ℂ) : ℝ :=
  (∫ z : ℂ, (F (x+Real.sqrt N • z)-F x)^2 ∂GaussianNoise.standardComplexGaussian)/N

theorem risk_sqrt_eq_powerRisk (F : ℂ → ℝ) {N : ℝ} (hN : 0 ≤ N) (x : ℂ) :
    risk F (Real.sqrt N) x = powerRisk F N x := by
  simp only [risk, SmallNoise.normalizedError, div_pow, Real.sq_sqrt hN, integral_div, powerRisk]

/-- Full fixed-decoder worst-case achievability in noise-power coordinates,
with the maximum coefficient attained on the actual compact noiseless set. -/
theorem worst_case_power_limit (F : ℂ → ℝ) (J : ℂ → ℂ →L[ℝ] ℝ)
    (hF : ∀ x, HasFDerivAt F (J x) x) (hJ : UniformContinuous J)
    {L : ℝ≥0} (hLpos : 0 < L) (hL : ∀ x, ‖J x‖ ≤ L)
    (M : Set ℂ) (hM : IsCompact M) (hne : M.Nonempty) :
    ∃ xstar ∈ M, (∀ x ∈ M, energy J x ≤ energy J xstar) ∧
      Tendsto (fun N : ℝ => sSup ((powerRisk F N) '' M))
        (𝓝[>] (0 : ℝ)) (𝓝 (energy J xstar)) := by
  obtain ⟨xstar, hxstar, hmax, hlim⟩ := worst_case_amplitude_limit F J hF hJ hLpos hL M hM hne
  refine ⟨xstar, hxstar, hmax, ?_⟩
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with N hN
      exact Real.sqrt_pos.mpr hN
  apply (hlim.comp hsqrt).congr'
  filter_upwards [self_mem_nhdsWithin] with N hN
  change sSup ((risk F (Real.sqrt N)) '' M) = sSup ((powerRisk F N) '' M)
  have hf : risk F (Real.sqrt N) = powerRisk F N := funext (fun x => risk_sqrt_eq_powerRisk F hN.le x)
  rw [hf]

end Analog.UniformSmallNoise
