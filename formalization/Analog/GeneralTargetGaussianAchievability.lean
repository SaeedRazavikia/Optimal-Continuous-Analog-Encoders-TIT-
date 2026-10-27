import Analog.EndpointExtension
import Analog.UniformSmallNoise

/-!
# Constructed Gaussian achievability for the two-statistic readout

The decoder in the manuscript is constructed from the prescribed closed-interval
readouts. Its global C¹ regularity, bounded and uniformly continuous derivative,
and exactness are proved from those interval data. Uniform Gaussian asymptotics
then apply to every moment in a compact attainable set, including its boundary.
-/

noncomputable section
namespace Analog.GeneralTargetGaussianAchievability
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- The closed-interval data actually used by the endpoint extension. -/
structure IntervalReadout where
  lower : ℝ
  upper : ℝ
  ordered : lower ≤ upper
  value : ℝ → ℝ
  slope : ℝ → ℝ
  value_continuous : ContinuousOn value (Icc lower upper)
  slope_continuous : ContinuousOn slope (Icc lower upper)
  derivative : ∀ x ∈ Ioo lower upper, HasDerivAt value (slope x) x

/-- The original additive readout. -/
def target (r₁ r₂ : IntervalReadout) (m : ℂ) : ℝ :=
  r₁.value m.re + r₂.value m.im

/-- Its prescribed derivative, including the one-sided endpoint data. -/
def targetDerivative (r₁ r₂ : IntervalReadout) (m : ℂ) : ℂ →L[ℝ] ℝ :=
  r₁.slope m.re • Complex.reCLM + r₂.slope m.im • Complex.imCLM

/-- The rectangle on which the closed-interval data are prescribed. -/
def rectangle (r₁ r₂ : IntervalReadout) : Set ℂ :=
  {m | m.re ∈ Icc r₁.lower r₁.upper ∧ m.im ∈ Icc r₂.lower r₂.upper}

def extendedValue (r : IntervalReadout) : ℝ → ℝ :=
  EndpointExtension.extension r.lower r.upper r.value r.slope

def extendedSlope (r : IntervalReadout) : ℝ → ℝ :=
  EndpointExtension.clippedDerivative r.lower r.upper r.slope

def extendedTarget (r₁ r₂ : IntervalReadout) (m : ℂ) : ℝ :=
  extendedValue r₁ m.re + extendedValue r₂ m.im

def extendedDerivative (r₁ r₂ : IntervalReadout) (m : ℂ) : ℂ →L[ℝ] ℝ :=
  extendedSlope r₁ m.re • Complex.reCLM + extendedSlope r₂ m.im • Complex.imCLM

/-- The actual decoder, with the inverse affine channel applied before readout. -/
def decoder (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : ℂ) (y : ℂ) : ℝ :=
  extendedTarget r₁ r₂ (T.symm (y-c))

def decoderDerivative (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : ℂ)
    (y : ℂ) : ℂ →L[ℝ] ℝ :=
  (extendedDerivative r₁ r₂ (T.symm (y-c))).comp T.symm.toContinuousLinearMap

/-- Both the value and derivative extensions agree on the original rectangle. -/
theorem extension_agrees (r₁ r₂ : IntervalReadout) {m : ℂ} (hm : m ∈ rectangle r₁ r₂) :
    extendedTarget r₁ r₂ m = target r₁ r₂ m ∧
      extendedDerivative r₁ r₂ m = targetDerivative r₁ r₂ m := by
  constructor
  · unfold extendedTarget target extendedValue
    rw [EndpointExtension.extension_eq_on r₁.ordered r₁.value_continuous
      r₁.slope_continuous r₁.derivative hm.1,
      EndpointExtension.extension_eq_on r₂.ordered r₂.value_continuous
      r₂.slope_continuous r₂.derivative hm.2]
  · unfold extendedDerivative targetDerivative extendedSlope
    rw [EndpointExtension.clippedDerivative_eq _ hm.1,
      EndpointExtension.clippedDerivative_eq _ hm.2]

/-- Differentiability of the additive extension is derived from the interval
fundamental theorem, including at the original endpoints. -/
theorem extendedTarget_hasFDerivAt (r₁ r₂ : IntervalReadout) (m : ℂ) :
    HasFDerivAt (extendedTarget r₁ r₂) (extendedDerivative r₁ r₂ m) m := by
  exact ((EndpointExtension.extension_hasDerivAt r₁.ordered r₁.value
    r₁.slope_continuous m.re).comp_hasFDerivAt m Complex.reCLM.hasFDerivAt).add
    ((EndpointExtension.extension_hasDerivAt r₂.ordered r₂.value
    r₂.slope_continuous m.im).comp_hasFDerivAt m Complex.imCLM.hasFDerivAt)

/-- The constructed derivative is globally uniformly continuous. -/
theorem extendedDerivative_uniformContinuous (r₁ r₂ : IntervalReadout) :
    UniformContinuous (extendedDerivative r₁ r₂) := by
  have h₁ := (EndpointExtension.clippedDerivative_uniformContinuous r₁.ordered
    r₁.slope_continuous).comp Complex.reCLM.uniformContinuous
  have h₂ := (EndpointExtension.clippedDerivative_uniformContinuous r₂.ordered
    r₂.slope_continuous).comp Complex.imCLM.uniformContinuous
  exact (((ContinuousLinearMap.id ℝ ℝ).smulRight Complex.reCLM).uniformContinuous.comp h₁).add
    (((ContinuousLinearMap.id ℝ ℝ).smulRight Complex.imCLM).uniformContinuous.comp h₂)

/-- Compact closed-interval derivatives give a global operator-norm bound. -/
theorem extendedDerivative_bounded (r₁ r₂ : IntervalReadout) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m, ‖extendedDerivative r₁ r₂ m‖ ≤ B := by
  obtain ⟨B₁, hB₁, hb₁⟩ := EndpointExtension.clippedDerivative_bounded
    r₁.ordered r₁.slope_continuous
  obtain ⟨B₂, hB₂, hb₂⟩ := EndpointExtension.clippedDerivative_bounded
    r₂.ordered r₂.slope_continuous
  refine ⟨B₁*‖Complex.reCLM‖ + B₂*‖Complex.imCLM‖,
    add_nonneg (mul_nonneg hB₁ (norm_nonneg _)) (mul_nonneg hB₂ (norm_nonneg _)), ?_⟩
  intro m
  exact (norm_add_le _ _).trans (by
    simpa only [norm_smul, Real.norm_eq_abs, extendedSlope] using
      add_le_add (mul_le_mul_of_nonneg_right (hb₁ m.re) (norm_nonneg Complex.reCLM))
        (mul_le_mul_of_nonneg_right (hb₂ m.im) (norm_nonneg Complex.imCLM)))

/-- The inverse-affine decoder has the claimed global derivative. -/
theorem decoder_hasFDerivAt (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ)
    (c y : ℂ) : HasFDerivAt (decoder r₁ r₂ T c) (decoderDerivative r₁ r₂ T c y) y := by
  have hi : HasFDerivAt (fun y : ℂ => T.symm (y-c)) T.symm.toContinuousLinearMap y := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      T.symm.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const c)
  exact (extendedTarget_hasFDerivAt r₁ r₂ (T.symm (y-c))).comp y hi

/-- Uniform continuity survives the fixed inverse affine change of coordinates. -/
theorem decoderDerivative_uniformContinuous (r₁ r₂ : IntervalReadout)
    (T : ℂ ≃L[ℝ] ℂ) (c : ℂ) : UniformContinuous (decoderDerivative r₁ r₂ T c) := by
  have hi : UniformContinuous (fun y : ℂ => T.symm (y-c)) :=
    T.symm.toContinuousLinearMap.uniformContinuous.comp
      (uniformContinuous_id.sub uniformContinuous_const)
  exact ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).flip T.symm.toContinuousLinearMap).uniformContinuous.comp
    ((extendedDerivative_uniformContinuous r₁ r₂).comp hi)

/-- All global regularity needed for uniform risk convergence is derived from
the original closed-interval readouts and the invertible channel. -/
theorem decoder_regularity (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : ℂ) :
    ContDiff ℝ 1 (decoder r₁ r₂ T c) ∧
    UniformContinuous (decoderDerivative r₁ r₂ T c) ∧
    ∃ L : ℝ≥0, 0 < L ∧ (∀ y, ‖decoderDerivative r₁ r₂ T c y‖ ≤ L) ∧
      LipschitzWith L (decoder r₁ r₂ T c) := by
  have hJ := decoderDerivative_uniformContinuous r₁ r₂ T c
  have hD := decoder_hasFDerivAt r₁ r₂ T c
  have hcd : ContDiff ℝ 1 (decoder r₁ r₂ T c) := by
    apply contDiff_one_iff_fderiv.mpr
    refine ⟨fun y => (hD y).differentiableAt, ?_⟩
    have he : fderiv ℝ (decoder r₁ r₂ T c) = decoderDerivative r₁ r₂ T c :=
      funext (fun y => (hD y).fderiv)
    rw [he]
    exact hJ.continuous
  obtain ⟨B, hB, hb⟩ := extendedDerivative_bounded r₁ r₂
  let L : ℝ≥0 := ⟨B*‖T.symm.toContinuousLinearMap‖ + 1,
    by positivity⟩
  have hL : 0 < L := by change 0 < B*‖T.symm.toContinuousLinearMap‖+1; positivity
  have hbound : ∀ y, ‖decoderDerivative r₁ r₂ T c y‖ ≤ L := by
    intro y
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)).trans (by change _ ≤ _+1; linarith))
  exact ⟨hcd, hJ, L, hL, hbound,
    UniformSmallNoise.lipschitz_of_derivative_bound _ _ hD hbound⟩

/-- Exactness on the entire closed attainable rectangle. -/
theorem decoder_exact (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : ℂ)
    {m : ℂ} (hm : m ∈ rectangle r₁ r₂) :
    decoder r₁ r₂ T c (c+T m) = target r₁ r₂ m := by
  simpa only [decoder, add_sub_cancel_left, T.symm_apply_apply] using
    (extension_agrees r₁ r₂ hm).1

/-- The inverse-channel derivative energy in the prescribed coordinates. -/
def coefficient (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (m : ℂ) : ℝ :=
  ((targetDerivative r₁ r₂ m (T.symm 1))^2 +
    (targetDerivative r₁ r₂ m (T.symm Complex.I))^2)/2

theorem decoder_energy_eq (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : ℂ)
    {m : ℂ} (hm : m ∈ rectangle r₁ r₂) :
    UniformSmallNoise.energy (decoderDerivative r₁ r₂ T c) (c+T m) =
      coefficient r₁ r₂ T m := by
  simp only [UniformSmallNoise.energy, decoderDerivative, add_sub_cancel_left,
    T.symm_apply_apply, (extension_agrees r₁ r₂ hm).2,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, coefficient]

/-- Actual normalized Gaussian MSE for the constructed decoder. -/
def normalizedRisk (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : ℂ)
    (N : ℝ) (m : ℂ) : ℝ :=
  (∫ z : ℂ, (decoder r₁ r₂ T c (c+T m+Real.sqrt N • z) - target r₁ r₂ m)^2
    ∂GaussianNoise.standardComplexGaussian)/N

theorem normalizedRisk_eq (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : ℂ)
    {m : ℂ} (hm : m ∈ rectangle r₁ r₂) (t : ℝ) :
    normalizedRisk r₁ r₂ T c t m =
      UniformSmallNoise.powerRisk (decoder r₁ r₂ T c) t (c+T m) := by
  simp only [normalizedRisk, UniformSmallNoise.powerRisk, decoder_exact r₁ r₂ T c hm]

/-- The prescribed endpoint extension achieves the attained worst-case leading
coefficient on every nonempty compact moment set in the attainable rectangle.
This is an actual Gaussian supremum limit; no uniform Taylor estimate or risk
asymptotics are assumed. -/
theorem worst_case_limit (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : ℂ)
    (M : Set ℂ) (hM : IsCompact M) (hne : M.Nonempty)
    (hrect : M ⊆ rectangle r₁ r₂) :
    ∃ mstar ∈ M, (∀ m ∈ M, coefficient r₁ r₂ T m ≤ coefficient r₁ r₂ T mstar) ∧
      Tendsto (fun N : ℝ => sSup (normalizedRisk r₁ r₂ T c N '' M))
        (𝓝[>] (0 : ℝ)) (𝓝 (coefficient r₁ r₂ T mstar)) := by
  obtain ⟨_, hJ, L, hL, hb, _⟩ := decoder_regularity r₁ r₂ T c
  have hc : Continuous (fun m : ℂ => c+T m) := continuous_const.add T.continuous
  obtain ⟨ystar, ⟨mstar, hmstar, rfl⟩, hmax, hlim⟩ :=
    UniformSmallNoise.worst_case_power_limit (decoder r₁ r₂ T c)
      (decoderDerivative r₁ r₂ T c) (decoder_hasFDerivAt r₁ r₂ T c)
      hJ hL hb ((fun m => c+T m) '' M) (hM.image hc) (hne.image _)
  refine ⟨mstar, hmstar, ?_, ?_⟩
  · intro m hm
    simpa only [decoder_energy_eq r₁ r₂ T c (hrect hm),
      decoder_energy_eq r₁ r₂ T c (hrect hmstar)] using
      hmax (c+T m) (Set.mem_image_of_mem _ hm)
  · have himage : ∀ N : ℝ, normalizedRisk r₁ r₂ T c N '' M =
        UniformSmallNoise.powerRisk (decoder r₁ r₂ T c) N '' ((fun m => c+T m) '' M) := by
      intro N
      rw [Set.image_image]
      apply Set.image_congr
      intro m hm
      exact normalizedRisk_eq r₁ r₂ T c (hrect hm) N
    simpa only [himage, decoder_energy_eq r₁ r₂ T c (hrect hmstar)] using hlim

/-- Fixed-prior achievability for the same noise-independent constructed decoder.
The prior may give mass to the boundary: endpoint extension supplies the
required derivative there. No derivative-moment integrability is assumed. -/
theorem prior_limit {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : ℂ)
    (m : Ω → ℂ) (hm : Measurable m)
    (hrect : ∀ᵐ ω ∂μ, m ω ∈ rectangle r₁ r₂) :
    Tendsto (fun N : ℝ =>
      (∫ p : Ω × ℂ, (decoder r₁ r₂ T c (c+T (m p.1)+Real.sqrt N • p.2) -
        target r₁ r₂ (m p.1))^2 ∂μ.prod GaussianNoise.standardComplexGaussian)/N)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ ω, coefficient r₁ r₂ T (m ω) ∂μ)) := by
  obtain ⟨_, _, L, _, _, hLip⟩ := decoder_regularity r₁ r₂ T c
  have hexact : ∀ m ∈ (Set.univ : Set ℂ),
      decoder r₁ r₂ T c (c+T m) = extendedTarget r₁ r₂ m := by
    intro m _
    simp only [decoder, add_sub_cancel_left, T.symm_apply_apply]
  have hlim := GeneralTargetSmallNoise.gaussian_general_target_leading_mse (μ := μ)
    (Set.univ : Set ℂ) T c (extendedTarget r₁ r₂) (decoder r₁ r₂ T c)
    (L := L) hLip hexact m hm
    (Filter.Eventually.of_forall (fun _ => by simp))
    (fun ω => extendedDerivative r₁ r₂ (m ω))
    (Filter.Eventually.of_forall (fun ω => extendedTarget_hasFDerivAt r₁ r₂ (m ω)))
  have hint : (∫ ω, (extendedDerivative r₁ r₂ (m ω) (T.symm 1))^2 +
        (extendedDerivative r₁ r₂ (m ω) (T.symm Complex.I))^2 ∂μ) =
      ∫ ω, (targetDerivative r₁ r₂ (m ω) (T.symm 1))^2 +
        (targetDerivative r₁ r₂ (m ω) (T.symm Complex.I))^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hrect] with ω hω
    rw [(extension_agrees r₁ r₂ hω).2]
  have hcoef : (1/2 : ℝ) * (∫ ω, (extendedDerivative r₁ r₂ (m ω) (T.symm 1))^2 +
        (extendedDerivative r₁ r₂ (m ω) (T.symm Complex.I))^2 ∂μ) =
      ∫ ω, coefficient r₁ r₂ T (m ω) ∂μ := by
    rw [hint]
    simp only [coefficient, integral_div]
    ring
  rw [hcoef] at hlim
  convert hlim using 1
  ext N
  congr 1
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hrect] with p hp
  rw [(extension_agrees r₁ r₂ hp).1]

end Analog.GeneralTargetGaussianAchievability
