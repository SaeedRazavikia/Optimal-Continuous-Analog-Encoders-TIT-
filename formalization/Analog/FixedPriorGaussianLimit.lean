import Analog.GeneralTargetGaussianAchievability
import Analog.GaussianBayesConverse
import Analog.GaussianGramCoefficient
import Analog.GaussianLawBridge

/-!
# Sharp fixed-prior Gaussian risk for the prescribed two-statistic readout

This module assembles the genuine all-Borel-decoder converse and the
constructed endpoint-extension decoder in the same likelihood model.
-/
noncomputable section
namespace Analog.FixedPriorGaussianLimit
open Set Filter MeasureTheory
open GeneralTargetGaussianAchievability GaussianScoreIdentity GaussianBayesConverse
open scoped Topology NNReal ENNReal

abbrev Plane := ℝ × ℝ

/-- The moment-coordinate target appearing in the statistical model. -/
def planeTarget (r₁ r₂ : IntervalReadout) (m : Plane) : ℝ :=
  target r₁ r₂ (Complex.equivRealProdCLM.symm m)

/-- The global C¹ extension agrees with the prescribed target on prior support. -/
def planeExtension (r₁ r₂ : IntervalReadout) (m : Plane) : ℝ :=
  extendedTarget r₁ r₂ (Complex.equivRealProdCLM.symm m)

/-- The same explicit decoder in the likelihood's real-pair observation coordinates. -/
def planeDecoder (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : Plane) (y : Plane) : ℝ :=
  decoder r₁ r₂ T (Complex.equivRealProdCLM.symm c) (Complex.equivRealProdCLM.symm y)

def planeCoefficient (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (m : Plane) : ℝ :=
  coefficient r₁ r₂ T (Complex.equivRealProdCLM.symm m)

theorem planeExtension_contDiff (r₁ r₂ : IntervalReadout) :
    ContDiff ℝ 1 (planeExtension r₁ r₂) := by
  exact ((EndpointExtension.extension_contDiff r₁.ordered r₁.value r₁.slope_continuous).comp
    (contDiff_fst : ContDiff ℝ 1 (Prod.fst : Plane → ℝ))).add
      ((EndpointExtension.extension_contDiff r₂.ordered r₂.value r₂.slope_continuous).comp
        (contDiff_snd : ContDiff ℝ 1 (Prod.snd : Plane → ℝ)))

/-- The actual gradient of the extension is the clamped prescribed slope pair. -/
theorem planeExtension_gradient (r₁ r₂ : IntervalReadout) (m : Plane) :
    gradient (planeExtension r₁ r₂) m =
      (⟨extendedSlope r₁ m.1, extendedSlope r₂ m.2⟩ : ℂ) := by
  have hd := (extendedTarget_hasFDerivAt r₁ r₂ (Complex.equivRealProdCLM.symm m)).comp m
    Complex.equivRealProdCLM.symm.hasFDerivAt
  have hfd : fderiv ℝ (planeExtension r₁ r₂) m =
      (extendedDerivative r₁ r₂ (Complex.equivRealProdCLM.symm m)).comp
        Complex.equivRealProdCLM.symm.toContinuousLinearMap := hd.fderiv
  simp [gradient, hfd, extendedDerivative, firstDirection, secondDirection]

/-- Global gradient boundedness follows from the prescribed closed intervals. -/
theorem planeExtension_gradient_bounded (r₁ r₂ : IntervalReadout) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ‖gradient (planeExtension r₁ r₂) m‖ ≤ C := by
  obtain ⟨B₁, hB₁, hb₁⟩ := EndpointExtension.clippedDerivative_bounded
    r₁.ordered r₁.slope_continuous
  obtain ⟨B₂, hB₂, hb₂⟩ := EndpointExtension.clippedDerivative_bounded
    r₂.ordered r₂.slope_continuous
  refine ⟨B₁+B₂, add_nonneg hB₁ hB₂, fun m => ?_⟩
  rw [planeExtension_gradient]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add (hb₁ m.1) (hb₂ m.2))

/-- Both prescribed readout values are bounded on their closed rectangle. -/
theorem target_bounded (r₁ r₂ : IntervalReadout) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m ∈ rectangle r₁ r₂, |target r₁ r₂ m| ≤ B := by
  obtain ⟨B₁, hb₁⟩ := isCompact_Icc.bddAbove_image r₁.value_continuous.abs
  obtain ⟨B₂, hb₂⟩ := isCompact_Icc.bddAbove_image r₂.value_continuous.abs
  refine ⟨max B₁ 0 + max B₂ 0,
    add_nonneg (le_max_right _ _) (le_max_right _ _), ?_⟩
  intro m hm
  exact (abs_add_le _ _).trans (add_le_add
    ((hb₁ (Set.mem_image_of_mem _ hm.1)).trans (le_max_left _ _))
    ((hb₂ (Set.mem_image_of_mem _ hm.2)).trans (le_max_left _ _)))

/-- Achievability and converse coefficients coincide on the closed rectangle. -/
theorem coefficient_eq_inverse_energy (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ)
    {m : Plane} (hm : Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂) :
    planeCoefficient r₁ r₂ T m =
      ‖T.symm.toContinuousLinearMap.adjoint (gradient (planeExtension r₁ r₂) m)‖^2/2 := by
  unfold planeCoefficient coefficient
  rw [GaussianGramCoefficient.inverse_derivative_energy]
  rw [planeExtension_gradient]
  have hm₁ : m.1 ∈ Icc r₁.lower r₁.upper := hm.1
  have hm₂ : m.2 ∈ Icc r₂.lower r₂.upper := hm.2
  simp [targetDerivative, extendedSlope, EndpointExtension.clippedDerivative_eq _ hm₁,
    EndpointExtension.clippedDerivative_eq _ hm₂]

/-- The constructed decoder's squared error is integrable under independent
Gaussian noise. Its Lipschitz bound dominates the error by the noise energy. -/
theorem decoder_error_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : ℂ)
    (m : Ω → ℂ) (hm : Measurable m) (N : ℝ) :
    Integrable (fun p : Ω × ℂ =>
      (decoder r₁ r₂ T c (c+T (m p.1)+Real.sqrt N • p.2) - extendedTarget r₁ r₂ (m p.1))^2)
      (μ.prod GaussianNoise.standardComplexGaussian) := by
  obtain ⟨hC, _, L, _, _, hLip⟩ := decoder_regularity r₁ r₂ T c
  have hF : Continuous (extendedTarget r₁ r₂) :=
    (EndpointExtension.extension_contDiff r₁.ordered r₁.value r₁.slope_continuous).continuous.comp
      Complex.reCLM.continuous |>.add
    ((EndpointExtension.extension_contDiff r₂.ordered r₂.value r₂.slope_continuous).continuous.comp
      Complex.imCLM.continuous)
  have hz : Integrable (fun p : Ω × ℂ => ‖p.2‖^2) (μ.prod GaussianNoise.standardComplexGaussian) :=
    GaussianNoise.complex_norm_square_integrable.comp_snd μ
  apply (hz.const_mul (((L : ℝ)*|Real.sqrt N|)^2)).mono'
  · exact (((hC.continuous.measurable.comp
      (measurable_const.add (T.continuous.measurable.comp (hm.comp measurable_fst)) |>.add
        (measurable_snd.const_smul (Real.sqrt N)))).sub
      (hF.measurable.comp (hm.comp measurable_fst))).pow_const 2).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hexact : decoder r₁ r₂ T c (c+T (m p.1)) = extendedTarget r₁ r₂ (m p.1) := by
        simp [decoder]
      have h := hLip.dist_le_mul (c+T (m p.1)+Real.sqrt N • p.2) (c+T (m p.1))
      rw [Real.dist_eq, hexact] at h
      simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h
      have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
      simpa only [sq_abs, mul_pow, mul_assoc] using hs

/-- Equal prior-a.e. targets have exactly the same unrestricted Borel risk. -/
theorem optimalRisk_congr_target (p : Plane → ℝ) (hp : Measurable p)
    (hp0 : ∀ m, 0 ≤ p m) (f g : Plane → ℝ) (T : ℂ ≃L[ℝ] ℂ) (c : Plane) (v : ℝ≥0)
    (hfg : f =ᵐ[priorLaw p] g) : optimalRisk p f T c v = optimalRisk p g T c v := by
  unfold optimalRisk
  congr 1
  apply iInf_congr
  intro D
  unfold BorelRisk.bayesRisk BorelRisk.squareRisk
  apply lintegral_congr_ae
  filter_upwards [jointLaw_ae_of_priorLaw p hp hp0 (receiverFirst T) (receiverSecond T) c v hfg]
    with q hq
  rw [hq]

/-- Actual unnormalized risk of the constructed decoder in the additive model. -/
def additiveRisk (p : Plane → ℝ) (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ)
    (c : Plane) (N : ℝ) : ℝ :=
  ∫ q : Plane × ℂ,
    (decoder r₁ r₂ T (Complex.equivRealProdCLM.symm c)
      (Complex.equivRealProdCLM.symm c + T (Complex.equivRealProdCLM.symm q.1) +
        Real.sqrt N • q.2) - planeExtension r₁ r₂ q.1)^2
    ∂(priorLaw p).prod GaussianNoise.standardComplexGaussian

/-- The infimum over every Borel decoder is at most the finite actual risk of
our constructed endpoint-extension decoder, in the identical density model. -/
theorem optimalRisk_extension_le (p : Plane → ℝ) (hp : Measurable p)
    (hp0 : ∀ m, 0 ≤ p m) (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : Plane)
    {v : ℝ≥0} (hv : v ≠ 0) :
    optimalRisk p (planeExtension r₁ r₂) T c v ≤ additiveRisk p r₁ r₂ T c (2*(v : ℝ)) := by
  letI := priorLaw_isProbability p hp0 hpi hpn
  have hf := (planeExtension_contDiff r₁ r₂).continuous.measurable
  have hd : Measurable (planeDecoder r₁ r₂ T c) :=
    (decoder_regularity r₁ r₂ T (Complex.equivRealProdCLM.symm c)).1.continuous.measurable.comp
      Complex.equivRealProdCLM.symm.continuous.measurable
  let D : BorelRisk.BorelDecoder Plane := ⟨planeDecoder r₁ r₂ T c, hd⟩
  have hobs (m : Plane) (z : ℂ) :
      Complex.equivRealProdCLM.symm (GaussianLawBridge.additiveObservation
        (receiverFirst T) (receiverSecond T) c v m z) =
      Complex.equivRealProdCLM.symm c + T (Complex.equivRealProdCLM.symm m) +
        Real.sqrt (2*(v : ℝ)) • z := by
    simpa [ArbitraryEncoder.asComplex] using
      GaussianLawBridge.additiveObservation_asComplex T (Complex.equivRealProdCLM.symm c) v m z
  have hi := decoder_error_integrable (μ := priorLaw p) r₁ r₂ T
    (Complex.equivRealProdCLM.symm c) (fun m : Plane => Complex.equivRealProdCLM.symm m)
    Complex.equivRealProdCLM.symm.continuous.measurable (2*(v : ℝ))
  have heq : BorelRisk.bayesRisk (jointLaw p (receiverFirst T) (receiverSecond T) c v)
      (fun q => planeExtension r₁ r₂ q.1) (fun q => q.2) D =
      ENNReal.ofReal (additiveRisk p r₁ r₂ T c (2*(v : ℝ))) := by
    dsimp only [BorelRisk.bayesRisk, Function.comp_def, D]
    rw [GaussianLawBridge.squareRisk_eq_additive p hp hp0
      (receiverFirst T) (receiverSecond T) c hv _ _ hf hd]
    simp_rw [planeDecoder, hobs]
    exact (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm
  have hle := iInf_le (fun D : BorelRisk.BorelDecoder Plane =>
    BorelRisk.bayesRisk (jointLaw p (receiverFirst T) (receiverSecond T) c v)
      (fun q => planeExtension r₁ r₂ q.1) (fun q => q.2) D) D
  rw [heq] at hle
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  have hnonneg : 0 ≤ additiveRisk p r₁ r₂ T c (2*(v : ℝ)) :=
    integral_nonneg (fun _ => sq_nonneg _)
  rw [ENNReal.toReal_ofReal hnonneg] at hreal
  exact hreal

/-- Fixed-prior leading risk of the actual constructed decoder, in the same
prior coordinates as the lower bound. -/
theorem additiveRisk_limit (p : Plane → ℝ) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : Plane)
    (hrect : ∀ᵐ m ∂priorLaw p, Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂) :
    Tendsto (fun N : ℝ => additiveRisk p r₁ r₂ T c N / N) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ m, planeCoefficient r₁ r₂ T m ∂priorLaw p)) := by
  letI := priorLaw_isProbability p hp0 hpi hpn
  have hlim := prior_limit (μ := priorLaw p) r₁ r₂ T (Complex.equivRealProdCLM.symm c)
    (fun m : Plane => Complex.equivRealProdCLM.symm m)
    Complex.equivRealProdCLM.symm.continuous.measurable hrect
  convert hlim using 1
  ext N
  congr 1
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hrect] with q hq
  rw [planeExtension, (extension_agrees r₁ r₂ hq).1]

/-- Full fixed-prior equality along every positive vanishing noise sequence.
The risk is the genuine nonnegative-risk infimum over all Borel decoders,
with the original prescribed readout, not a risk surrogate. -/
theorem fixed_prior_sequential_limit {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (hfull : ∀ᵐ m ∂priorLaw p, m ∈ Ω)
    (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : Plane)
    (hrect : ∀ᵐ m ∂priorLaw p, Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂)
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => optimalRisk p (planeTarget r₁ r₂) T c (v n) / (2*(v n : ℝ)))
      atTop (𝓝 (∫ m, planeCoefficient r₁ r₂ T m ∂priorLaw p)) := by
  obtain ⟨C, hC, hgrad⟩ := planeExtension_gradient_bounded r₁ r₂
  obtain ⟨B, hB, hb⟩ := target_bounded r₁ r₂
  have htarget : ∀ᵐ m ∂priorLaw p, -B ≤ planeExtension r₁ r₂ m ∧
      planeExtension r₁ r₂ m ≤ B := by
    filter_upwards [hrect] with m hm
    change -B ≤ extendedTarget r₁ r₂ (Complex.equivRealProdCLM.symm m) ∧
      extendedTarget r₁ r₂ (Complex.equivRealProdCLM.symm m) ≤ B
    rw [(extension_agrees r₁ r₂ hm).1]
    exact abs_le.mp (hb _ hm)
  have hlo := regular_prior_bayes_converse_total_noise hΩ p hp hp0 hpi hpn hpC hpPos hfull
    (planeExtension r₁ r₂) (planeExtension_contDiff r₁ r₂) T c hC hgrad v hv hlim
    (-B) B (by linarith) htarget
  have heq : (∫ m, ‖T.symm.toContinuousLinearMap.adjoint
        (gradient (planeExtension r₁ r₂) m)‖^2 ∂priorLaw p)/2 =
      ∫ m, planeCoefficient r₁ r₂ T m ∂priorLaw p := by
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards [hrect] with m hm
    exact (coefficient_eq_inverse_energy r₁ r₂ T hm).symm
  rw [heq] at hlo
  have hvlim : Tendsto (fun n => 2*(v n : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using hlim.const_mul 2, Filter.Eventually.of_forall (fun n => ?_)⟩
    change 0 < 2*(v n : ℝ)
    exact mul_pos (by norm_num) (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (hv n)))
  have hu := (additiveRisk_limit p hp0 hpi hpn r₁ r₂ T c hrect).comp hvlim
  have hresult := GaussianConverseLimits.tendsto_of_lowerAsymptotic_upper hlo
    (fun n => div_le_div_of_nonneg_right
      (optimalRisk_extension_le p hp hp0 hpi hpn r₁ r₂ T c (hv n)) (by positivity)) hu
  have hfg : planeTarget r₁ r₂ =ᵐ[priorLaw p] planeExtension r₁ r₂ := by
    filter_upwards [hrect] with m hm
    exact (extension_agrees r₁ r₂ hm).1.symm
  convert hresult using 1
  ext n
  rw [optimalRisk_congr_target p hp hp0 _ _ T c (v n) hfg]

/-- The full one-sided small-noise limit, normalized by total complex power
`2v`, follows from the verified converse and the single constructed decoder.
Only local C¹ positivity of the prior on its open full-mass region is needed. -/
theorem fixed_prior_limit {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (hfull : ∀ᵐ m ∂priorLaw p, m ∈ Ω)
    (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : Plane)
    (hrect : ∀ᵐ m ∂priorLaw p, Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂) :
    Tendsto (fun v : ℝ≥0 => optimalRisk p (planeTarget r₁ r₂) T c v / (2*(v : ℝ)))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (∫ m, planeCoefficient r₁ r₂ T m ∂priorLaw p)) := by
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro v hv
  have hvpos : ∀ᶠ n in atTop, 0 < v n := hv.eventually self_mem_nhdsWithin
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hvpos
  apply (Filter.tendsto_add_atTop_iff_nat n₀).mp
  have hv' : ∀ n, v (n+n₀) ≠ 0 := fun n => ne_of_gt (hn₀ _ (Nat.le_add_left _ _))
  have hvl : Tendsto (fun n => (v (n+n₀) : ℝ)) atTop (𝓝 0) :=
    NNReal.tendsto_coe.mpr ((tendsto_nhds_of_tendsto_nhdsWithin hv).comp
      (Filter.tendsto_add_atTop_nat n₀))
  exact fixed_prior_sequential_limit hΩ p hp hp0 hpi hpn hpC hpPos hfull
    r₁ r₂ T c hrect (fun n => v (n+n₀)) hv' hvl

/-- The original pair of prescribed receiver slopes in real moment coordinates. -/
def prescribedGradient (r₁ r₂ : IntervalReadout) (m : Plane) : ℂ :=
  ⟨r₁.slope m.1, r₂.slope m.2⟩

/-- The coefficient is exactly one half the manuscript's inverse-Gram trace,
with second moments of the original prescribed slopes. -/
theorem coefficient_integral_eq_trace (p : Plane → ℝ) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ)
    (hrect : ∀ᵐ m ∂priorLaw p, Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂) :
    (∫ m, planeCoefficient r₁ r₂ T m ∂priorLaw p) =
      Matrix.trace (GaussianGramCoefficient.gradientSecondMoment (priorLaw p)
        (prescribedGradient r₁ r₂) * (GaussianGramCoefficient.gramMatrix T)⁻¹)/2 := by
  letI := priorLaw_isProbability p hp0 hpi hpn
  let w : Plane → ℂ := gradient (planeExtension r₁ r₂)
  have hw : Measurable w := (gradient_continuous (planeExtension_contDiff r₁ r₂)).measurable
  obtain ⟨C, hC, hb⟩ := planeExtension_gradient_bounded r₁ r₂
  have hr : Integrable (fun m => (w m).re^2) (priorLaw p) := by
    apply (integrable_const (C^2)).mono' ((Complex.measurable_re.comp hw).pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun m => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (abs_nonneg _) hC).mpr ((Complex.abs_re_le_norm _).trans (hb m)) |>
        (by simpa only [sq_abs] using ·)
  have hi : Integrable (fun m => (w m).im^2) (priorLaw p) := by
    apply (integrable_const (C^2)).mono' ((Complex.measurable_im.comp hw).pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun m => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (abs_nonneg _) hC).mpr ((Complex.abs_im_le_norm _).trans (hb m)) |>
        (by simpa only [sq_abs] using ·)
  have hweq : w =ᵐ[priorLaw p] prescribedGradient r₁ r₂ := by
    filter_upwards [hrect] with m hm
    rw [show w m = gradient (planeExtension r₁ r₂) m from rfl, planeExtension_gradient]
    have hm₁ : m.1 ∈ Icc r₁.lower r₁.upper := hm.1
    have hm₂ : m.2 ∈ Icc r₂.lower r₂.upper := hm.2
    simp [extendedSlope, prescribedGradient, EndpointExtension.clippedDerivative_eq _ hm₁,
      EndpointExtension.clippedDerivative_eq _ hm₂]
  have hMoment : GaussianGramCoefficient.gradientSecondMoment (priorLaw p) w =
      GaussianGramCoefficient.gradientSecondMoment (priorLaw p) (prescribedGradient r₁ r₂) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [GaussianGramCoefficient.gradientSecondMoment, Matrix.of_apply]
    all_goals
      apply integral_congr_ae
      filter_upwards [hweq] with m hm
      rw [hm]
  have hint : (∫ m, planeCoefficient r₁ r₂ T m ∂priorLaw p) =
      (∫ m, ‖T.symm.toContinuousLinearMap.adjoint (w m)‖^2 ∂priorLaw p)/2 := by
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards [hrect] with m hm
    exact coefficient_eq_inverse_energy r₁ r₂ T hm
  rw [hint, GaussianGramCoefficient.integrated_inverse_trace _ T w hw hr hi, hMoment]

/-- Fixed-prior Gaussian optimal risk in the explicit inverse-Gram trace form. -/
theorem fixed_prior_limit_inverse_trace {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (hfull : ∀ᵐ m ∂priorLaw p, m ∈ Ω)
    (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : Plane)
    (hrect : ∀ᵐ m ∂priorLaw p, Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂) :
    Tendsto (fun v : ℝ≥0 => optimalRisk p (planeTarget r₁ r₂) T c v / (2*(v : ℝ)))
      (𝓝[>] (0 : ℝ≥0))
      (𝓝 (Matrix.trace (GaussianGramCoefficient.gradientSecondMoment (priorLaw p)
        (prescribedGradient r₁ r₂) * (GaussianGramCoefficient.gramMatrix T)⁻¹)/2)) := by
  rw [← coefficient_integral_eq_trace p hp0 hpi hpn r₁ r₂ T hrect]
  exact fixed_prior_limit hΩ p hp hp0 hpi hpn hpC hpPos hfull r₁ r₂ T c hrect

/-- Every fixed globally Lipschitz decoder exact on the attainable set has
this same prior-averaged coefficient whenever the prior is interior-supported.
The decoder derivative is forced by exactness and is not assumed. -/
theorem exact_decoder_prior_limit {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : ℂ)
    (M : Set ℂ) (hrect : M ⊆ rectangle r₁ r₂) (D : ℂ → ℝ) {L : ℝ≥0}
    (hD : LipschitzWith L D) (hexact : ∀ m ∈ M, D (c+T m) = target r₁ r₂ m)
    (m : Ω → ℂ) (hm : Measurable m) (hinterior : ∀ᵐ ω ∂μ, m ω ∈ interior M) :
    Tendsto (fun N : ℝ =>
      (∫ p : Ω × ℂ, (D (c+T (m p.1)+Real.sqrt N • p.2) - target r₁ r₂ (m p.1))^2
        ∂μ.prod GaussianNoise.standardComplexGaussian)/N)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ ω, coefficient r₁ r₂ T (m ω) ∂μ)) := by
  have hex : ∀ m ∈ M, D (c+T m) = extendedTarget r₁ r₂ m := by
    intro m hm
    rw [hexact m hm, (extension_agrees r₁ r₂ (hrect hm)).1]
  have hlim := GeneralTargetSmallNoise.gaussian_general_target_leading_mse (μ := μ)
    M T c (extendedTarget r₁ r₂) D hD hex m hm hinterior
    (fun ω => extendedDerivative r₁ r₂ (m ω))
    (Filter.Eventually.of_forall (fun ω => extendedTarget_hasFDerivAt r₁ r₂ (m ω)))
  have hsupport : ∀ᵐ ω ∂μ, m ω ∈ rectangle r₁ r₂ :=
    hinterior.mono (fun _ hω => hrect (interior_subset hω))
  have hcoef : (1/2 : ℝ)*(∫ ω, (extendedDerivative r₁ r₂ (m ω) (T.symm 1))^2 +
      (extendedDerivative r₁ r₂ (m ω) (T.symm Complex.I))^2 ∂μ) =
      ∫ ω, coefficient r₁ r₂ T (m ω) ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hsupport] with ω hω
    rw [(extension_agrees r₁ r₂ hω).2]
    unfold coefficient
    ring
  rw [hcoef] at hlim
  convert hlim using 1
  ext N
  congr 1
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsupport] with q hq
  rw [(extension_agrees r₁ r₂ hq).1]

end Analog.FixedPriorGaussianLimit
