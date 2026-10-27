import Analog.GaussianVanTrees
import Analog.WeightedVariational
import Analog.GaussianConverseLimits
import Mathlib.Analysis.Complex.Basic

/-!
# Fixed-prior Gaussian Bayes converse

This module combines the actual regular-prior Gaussian score inequality with
constructed smooth-test density. The risk is the infimum over all Borel
decoders of the nonnegative squared-error integral.
-/

noncomputable section
namespace Analog.GaussianBayesConverse
open MeasureTheory Set Filter GaussianScoreIdentity GaussianVanTrees
open scoped Topology ENNReal NNReal ContDiff

abbrev Plane := ℝ × ℝ

def firstDirection : Plane := (1, 0)
def secondDirection : Plane := (0, 1)

/-- The real moment gradient, represented isometrically by a complex number. -/
def gradient (f : Plane → ℝ) (m : Plane) : ℂ :=
  ⟨fderiv ℝ f m firstDirection, fderiv ℝ f m secondDirection⟩

/-- The receiver's first real row, for an invertible real-linear complex map. -/
def receiverFirst (S : ℂ ≃L[ℝ] ℂ) : Plane →L[ℝ] ℝ :=
  Complex.reCLM.comp (S.toContinuousLinearMap.comp
    Complex.equivRealProdCLM.symm.toContinuousLinearMap)

/-- The receiver's second real row. -/
def receiverSecond (S : ℂ ≃L[ℝ] ℂ) : Plane →L[ℝ] ℝ :=
  Complex.imCLM.comp (S.toContinuousLinearMap.comp
    Complex.equivRealProdCLM.symm.toContinuousLinearMap)

theorem gradient_continuous {f : Plane → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradient f) := by
  have h₁ := (hf.continuous_fderiv_apply le_rfl).comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : Plane => firstDirection)))
  have h₂ := (hf.continuous_fderiv_apply le_rfl).comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : Plane => secondDirection)))
  convert (Complex.continuous_ofReal.comp h₁).add
    ((Complex.continuous_ofReal.comp h₂).mul (continuous_const :
      Continuous (fun _ : Plane => Complex.I))) using 1
  ext m
  simp [gradient, Complex.ext_iff]

theorem complex_inner_coordinates (u v : ℂ) :
    inner ℝ u v = u.re * v.re + u.im * v.im := by
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
  change (v * star u).re = _
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem receiver_energy_coordinates (S : ℂ ≃L[ℝ] ℂ) (u : ℂ) :
    receiverFirst S (u.re • firstDirection + u.im • secondDirection) ^ 2 +
      receiverSecond S (u.re • firstDirection + u.im • secondDirection) ^ 2 =
        ‖S u‖ ^ 2 := by
  have he : Complex.equivRealProdCLM.symm
      (u.re • firstDirection + u.im • secondDirection) = u := by
    apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply, firstDirection, secondDirection]
  simp only [receiverFirst, receiverSecond, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, he, Complex.reCLM_apply, Complex.imCLM_apply]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem test_components {η : Plane → ℂ} {Ω : Set Plane}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ Ω) :
    ContDiff ℝ 1 (fun m => (η m).re) ∧ ContDiff ℝ 1 (fun m => (η m).im) ∧
    HasCompactSupport (fun m => (η m).re) ∧ HasCompactSupport (fun m => (η m).im) ∧
    tsupport (fun m => (η m).re) ⊆ Ω ∧ tsupport (fun m => (η m).im) ⊆ Ω := by
  have hsre : tsupport (fun m => (η m).re) ⊆ tsupport η := by
    apply closure_mono
    intro m hm hz
    exact hm (by simp [hz])
  have hsim : tsupport (fun m => (η m).im) ⊆ tsupport η := by
    apply closure_mono
    intro m hm hz
    exact hm (by simp [hz])
  exact ⟨(Complex.reCLM.contDiff.comp hη).of_le (by norm_num),
    (Complex.imCLM.contDiff.comp hη).of_le (by norm_num),
    hc.comp_left (g := Complex.re) rfl, hc.comp_left (g := Complex.im) rfl,
    hsre.trans hs, hsim.trans hs⟩

theorem sensitivity_eq_inner {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpC : ContDiffOn ℝ 1 p Ω) (f : Plane → ℝ) (hf : ContDiff ℝ 1 f)
    {η : Plane → ℂ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ω) :
    sensitivity p f (fun m => (η m).re) (fun m => (η m).im)
      firstDirection secondDirection = ∫ m, inner ℝ (η m) (gradient f m) ∂priorLaw p := by
  obtain ⟨h₁, h₂, hc₁, hc₂, hs₁, hs₂⟩ := test_components hη hc hs
  have ha₁ := RegularPriorFlux.flux_contDiff hΩ hpC h₁ hs₁
  have ha₂ := RegularPriorFlux.flux_contDiff hΩ hpC h₂ hs₂
  have hd₁ := (hf.continuous_fderiv le_rfl).clm_apply (continuous_const :
    Continuous (fun _ : Plane => firstDirection))
  have hd₂ := (hf.continuous_fderiv le_rfl).clm_apply (continuous_const :
    Continuous (fun _ : Plane => secondDirection))
  have hi₁ := (hd₁.mul ha₁.continuous).integrable_of_hasCompactSupport (μ := volume)
    ((RegularPriorFlux.flux_hasCompactSupport (p := p) hc₁).mul_left)
  have hi₂ := (hd₂.mul ha₂.continuous).integrable_of_hasCompactSupport (μ := volume)
    ((RegularPriorFlux.flux_hasCompactSupport (p := p) hc₂).mul_left)
  rw [sensitivity, ← integral_add hi₁ hi₂, priorLaw_integral p hp hp0]
  apply integral_congr_ae
  exact Eventually.of_forall fun m => by
    dsimp only
    rw [complex_inner_coordinates]
    dsimp only [gradient]
    ring

theorem channelInformation_eq_energy (p : Plane → ℝ) (hp : Measurable p)
    (hp0 : ∀ m, 0 ≤ p m) (S : ℂ ≃L[ℝ] ℂ) (η : Plane → ℂ) :
    channelInformation p (fun m => (η m).re) (fun m => (η m).im)
      firstDirection secondDirection (receiverFirst S) (receiverSecond S) =
        ∫ m, ‖S (η m)‖ ^ 2 ∂priorLaw p := by
  rw [channelInformation, priorLaw_integral p hp hp0]
  apply integral_congr_ae
  refine Eventually.of_forall fun m => ?_
  dsimp only
  have he : (p m * (η m).re) • firstDirection + (p m * (η m).im) • secondDirection =
      p m • ((η m).re • firstDirection + (η m).im • secondDirection) := by
    simp only [smul_add, mul_smul]
  rw [he, map_smul, map_smul]
  simp only [smul_eq_mul]
  rw [← receiver_energy_coordinates S (η m)]
  by_cases hz : p m = 0
  · simp [hz]
  · field_simp

/-- The actual Bayes risk includes every measurable decoder and infinite-risk
decoders; the conversion to a real number is justified by clipping. -/
def optimalRisk (p f : Plane → ℝ) (S : ℂ ≃L[ℝ] ℂ) (c : Plane) (v : ℝ≥0) : ℝ :=
  (⨅ D : BorelRisk.BorelDecoder Plane,
    BorelRisk.bayesRisk (jointLaw p (receiverFirst S) (receiverSecond S) c v)
      (fun q => f q.1) (fun q => q.2) D).toReal

theorem optimalRisk_nonneg (p f : Plane → ℝ) (S : ℂ ≃L[ℝ] ℂ) (c : Plane) (v : ℝ≥0) :
    0 ≤ optimalRisk p f S c v := ENNReal.toReal_nonneg

/-- A compact test lower-bounds the normalized infimum over every Borel
decoder. All score and integration-by-parts hypotheses are derived from the
stated locally regular density. -/
theorem optimalRisk_test_bound {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (f : Plane → ℝ) (hf : ContDiff ℝ 1 f) (S : ℂ ≃L[ℝ] ℂ) (c : Plane)
    {η : Plane → ℂ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ω)
    (hB : 0 < ∫ m, ‖S (η m)‖ ^ 2 ∂priorLaw p)
    {v : ℝ≥0} (hv : v ≠ 0) (lo hi : ℝ) (hlohi : lo ≤ hi)
    (htarget : ∀ᵐ m ∂priorLaw p, lo ≤ f m ∧ f m ≤ hi) :
    (∫ m, inner ℝ (η m) (gradient f m) ∂priorLaw p) ^ 2 /
      ((v : ℝ) * priorInformation p (fun m => (η m).re) (fun m => (η m).im)
        firstDirection secondDirection + (∫ m, ‖S (η m)‖ ^ 2 ∂priorLaw p)) ≤
      optimalRisk p f S c v / (v : ℝ) := by
  letI := jointLaw_isProbability p hp0 hpi hpn (receiverFirst S) (receiverSecond S) c hv
  letI : Nonempty (BorelRisk.BorelDecoder Plane) := ⟨⟨fun _ => 0, measurable_const⟩⟩
  have hvR : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  obtain ⟨h₁, h₂, hc₁, hc₂, hs₁, hs₂⟩ := test_components hη hc hs
  have ht := jointLaw_ae_of_priorLaw p hp hp0 (receiverFirst S) (receiverSecond S) c v htarget
  have htm : Measurable (fun q : Plane × Plane => f q.1) :=
    hf.continuous.measurable.comp measurable_fst
  have hA := sensitivity_eq_inner hΩ p hp hp0 hpC f hf hη hc hs
  have hE := channelInformation_eq_energy p hp hp0 S η
  have hC : 0 ≤ priorInformation p (fun m => (η m).re) (fun m => (η m).im)
      firstDirection secondDirection := by
    apply integral_nonneg
    intro m
    exact div_nonneg (sq_nonneg _) (hp0 m)
  have hden : 0 < priorInformation p (fun m => (η m).re) (fun m => (η m).im)
      firstDirection secondDirection +
        channelInformation p (fun m => (η m).re) (fun m => (η m).im)
          firstDirection secondDirection (receiverFirst S) (receiverSecond S) / (v : ℝ) := by
    rw [hE]
    exact add_pos_of_nonneg_of_pos hC (div_pos hB hvR)
  have hbound : sensitivity p f (fun m => (η m).re) (fun m => (η m).im)
      firstDirection secondDirection ^ 2 /
      (priorInformation p (fun m => (η m).re) (fun m => (η m).im)
        firstDirection secondDirection +
        channelInformation p (fun m => (η m).re) (fun m => (η m).im)
          firstDirection secondDirection (receiverFirst S) (receiverSecond S) / (v : ℝ)) ≤
      optimalRisk p f S c v := by
    rw [optimalRisk, (BorelRisk.iInf_bayesRisk_toReal (fun q : Plane × Plane => f q.1)
      (fun q => q.2) htm measurable_snd hlohi ht).2]
    apply le_ciInf
    intro D
    exact regular_information_bound hΩ p hp hp0 hpC hpPos f _ _ hf h₁ h₂ hc₁ hc₂
      hs₁ hs₂ firstDirection secondDirection (receiverFirst S) (receiverSecond S) c hv
      (fun y => Decoder.clip lo hi (D.1 y))
      (BorelRisk.clipped_error_memLp htm (D.2.comp measurable_snd) hlohi ht) hden
  rw [hA, hE] at hbound
  have h := div_le_div_of_nonneg_right hbound hvR.le
  convert h using 1
  rw [div_div]
  congr 1
  field_simp

/-- The actual statistical bound passes to zero noise for each fixed compact
test; the decoder is already optimized over all Borel functions. -/
theorem test_lower_asymptotic {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (f : Plane → ℝ) (hf : ContDiff ℝ 1 f) (S : ℂ ≃L[ℝ] ℂ) (c : Plane)
    {η : Plane → ℂ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ω)
    (hB : 0 < ∫ m, ‖S (η m)‖ ^ 2 ∂priorLaw p)
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0))
    (lo hi : ℝ) (hlohi : lo ≤ hi)
    (htarget : ∀ᵐ m ∂priorLaw p, lo ≤ f m ∧ f m ≤ hi) :
    GaussianConverseLimits.LowerAsymptotic
      (fun n => optimalRisk p f S c (v n) / (v n : ℝ))
      ((∫ m, inner ℝ (η m) (gradient f m) ∂priorLaw p) ^ 2 /
        (∫ m, ‖S (η m)‖ ^ 2 ∂priorLaw p)) := by
  apply GaussianConverseLimits.lowerAsymptotic_of_ratio hB
    (denominator := fun n => (v n : ℝ) *
      priorInformation p (fun m => (η m).re) (fun m => (η m).im)
        firstDirection secondDirection + (∫ m, ‖S (η m)‖ ^ 2 ∂priorLaw p))
  · simpa only [zero_mul, zero_add] using
      (hlim.mul_const (priorInformation p (fun m => (η m).re) (fun m => (η m).im)
        firstDirection secondDirection)).add_const (∫ m, ‖S (η m)‖ ^ 2 ∂priorLaw p)
  · intro n
    exact optimalRisk_test_bound hΩ p hp hp0 hpi hpn hpC hpPos f hf S c
      hη hc hs hB (hv n) lo hi hlohi htarget

/-- Fixed-prior Gaussian converse under local C¹ positivity alone. The
coefficient is the true inverse-Gram gradient energy and the risk is the
infimum over all Borel decoders. Both the score bound and the smooth-test
variational completeness are proved, not supplied as hypotheses. -/
theorem regular_prior_bayes_converse {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (hfull : ∀ᵐ m ∂priorLaw p, m ∈ Ω)
    (f : Plane → ℝ) (hf : ContDiff ℝ 1 f) (S : ℂ ≃L[ℝ] ℂ) (c : Plane)
    {C : ℝ} (hC : 0 ≤ C) (hgrad : ∀ m, ‖gradient f m‖ ≤ C)
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0))
    (lo hi : ℝ) (hlohi : lo ≤ hi)
    (htarget : ∀ᵐ m ∂priorLaw p, lo ≤ f m ∧ f m ≤ hi) :
    GaussianConverseLimits.LowerAsymptotic
      (fun n => optimalRisk p f S c (v n) / (v n : ℝ))
      (∫ m, ‖S.symm.toContinuousLinearMap.adjoint (gradient f m)‖ ^ 2 ∂priorLaw p) := by
  letI := priorLaw_isProbability p hp0 hpi hpn
  have hsup := WeightedVariational.inverse_gram_variational_supremum S
    (gradient_continuous hf) hΩ hfull hC hgrad
  have hnonempty : (WeightedVariational.gramVariationalValues S (gradient f) Ω (priorLaw p)).Nonempty := by
    refine ⟨0, fun _ => 0, contDiff_const, HasCompactSupport.zero, ?_, ?_⟩
    · change tsupport (0 : Plane → ℂ) ⊆ Ω
      simp [tsupport]
    · simp
  intro a ha
  by_cases hnegative : a < 0
  · exact Eventually.of_forall fun n => hnegative.le.trans
      (div_nonneg (optimalRisk_nonneg p f S c (v n)) (v n).coe_nonneg)
  · have ha0 : 0 ≤ a := le_of_not_gt hnegative
    rw [← hsup] at ha
    obtain ⟨q, hqmem, haq⟩ := exists_lt_of_lt_csSup hnonempty ha
    obtain ⟨η, hη, hc, hs, rfl⟩ := hqmem
    have hB : 0 < ∫ m, ‖S (η m)‖ ^ 2 ∂priorLaw p := by
      have hnonneg : 0 ≤ ∫ m, ‖S (η m)‖ ^ 2 ∂priorLaw p :=
        integral_nonneg (fun _ => sq_nonneg _)
      have hne : (∫ m, ‖S (η m)‖ ^ 2 ∂priorLaw p) ≠ 0 := by
        intro hz
        rw [hz, div_zero] at haq
        exact (not_lt_of_ge ha0) haq
      exact lt_of_le_of_ne hnonneg (Ne.symm hne)
    exact test_lower_asymptotic hΩ p hp hp0 hpi hpn hpC hpPos f hf S c hη hc hs
      hB v hv hlim lo hi hlohi htarget a haq

/-- The manuscript normalizes by total complex noise power `N₀ = 2v`.
The real-coordinate Gaussian converse therefore has its required factor 1/2. -/
theorem regular_prior_bayes_converse_total_noise {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (hfull : ∀ᵐ m ∂priorLaw p, m ∈ Ω)
    (f : Plane → ℝ) (hf : ContDiff ℝ 1 f) (S : ℂ ≃L[ℝ] ℂ) (c : Plane)
    {C : ℝ} (hC : 0 ≤ C) (hgrad : ∀ m, ‖gradient f m‖ ≤ C)
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0))
    (lo hi : ℝ) (hlohi : lo ≤ hi)
    (htarget : ∀ᵐ m ∂priorLaw p, lo ≤ f m ∧ f m ≤ hi) :
    GaussianConverseLimits.LowerAsymptotic
      (fun n => optimalRisk p f S c (v n) / (2 * (v n : ℝ)))
      ((∫ m, ‖S.symm.toContinuousLinearMap.adjoint (gradient f m)‖ ^ 2 ∂priorLaw p) / 2) := by
  have h := regular_prior_bayes_converse hΩ p hp hp0 hpi hpn hpC hpPos hfull
    f hf S c hC hgrad v hv hlim lo hi hlohi htarget
  intro a ha
  have ha' : 2 * a < ∫ m, ‖S.symm.toContinuousLinearMap.adjoint (gradient f m)‖ ^ 2 ∂priorLaw p := by
    linarith
  filter_upwards [h (2 * a) ha'] with n hn
  have hd := div_le_div_of_nonneg_right hn (show (0 : ℝ) ≤ 2 by norm_num)
  simpa only [mul_div_cancel_left₀ _ (show (2 : ℝ) ≠ 0 by norm_num),
    div_div, mul_comm (v n : ℝ) 2] using hd

end Analog.GaussianBayesConverse
