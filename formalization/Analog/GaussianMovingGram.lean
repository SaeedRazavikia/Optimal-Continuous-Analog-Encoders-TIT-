import Analog.GaussianBayesConverse
import Analog.GaussianSequentialConverse
import Analog.GaussianGramCoefficient

/-!
# Full variational Gaussian converse along changing Gram matrices

Only the three receiver Gram entries must converge. Compact-test energy
convergence is derived from its actual quadratic expansion, and smooth-test
completeness supplies the limiting inverse-Gram coefficient.
-/

noncomputable section
namespace Analog.GaussianMovingGram
open MeasureTheory Set Filter GaussianScoreIdentity GaussianVanTrees GaussianBayesConverse
open GaussianGramCoefficient GaussianConverseLimits
open scoped Topology NNReal ContDiff

abbrev Plane := ℝ × ℝ

theorem receiver_energy_expansion (S : ℂ ≃L[ℝ] ℂ) (z : ℂ) :
    ‖S z‖ ^ 2 = gramA S * z.re ^ 2 + 2 * gramC S * (z.re * z.im) + gramB S * z.im ^ 2 := by
  have he : S z = z.re • S 1 + z.im • S Complex.I :=
    complex_linear_apply S.toContinuousLinearMap z
  rw [he, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul, gramA, gramB, gramC]
  ring

theorem test_energy_integrable (μ : Measure Plane) [IsFiniteMeasure μ]
    (S : ℂ ≃L[ℝ] ℂ) {η : Plane → ℂ} (hη : Continuous η) (hc : HasCompactSupport η) :
    Integrable (fun m => ‖S (η m)‖ ^ 2) μ :=
  ((S.continuous.comp hη).norm.pow 2).integrable_of_hasCompactSupport
    ((hc.comp_left (map_zero S)).comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))

theorem test_energy_moments (μ : Measure Plane) [IsFiniteMeasure μ]
    (S : ℂ ≃L[ℝ] ℂ) {η : Plane → ℂ} (hη : Continuous η) (hc : HasCompactSupport η) :
    (∫ m, ‖S (η m)‖ ^ 2 ∂μ) =
      gramA S * (∫ m, (η m).re ^ 2 ∂μ) +
      2 * gramC S * (∫ m, (η m).re * (η m).im ∂μ) +
      gramB S * (∫ m, (η m).im ^ 2 ∂μ) := by
  have hr : Integrable (fun m => (η m).re ^ 2) μ :=
    ((Complex.continuous_re.comp hη).pow 2).integrable_of_hasCompactSupport
      (hc.comp_left (g := fun z : ℂ => z.re ^ 2) (by simp))
  have hi : Integrable (fun m => (η m).im ^ 2) μ :=
    ((Complex.continuous_im.comp hη).pow 2).integrable_of_hasCompactSupport
      (hc.comp_left (g := fun z : ℂ => z.im ^ 2) (by simp))
  have hri : Integrable (fun m => (η m).re * (η m).im) μ :=
    ((Complex.continuous_re.comp hη).mul (Complex.continuous_im.comp hη)).integrable_of_hasCompactSupport
      (hc.comp_left (g := fun z : ℂ => z.re * z.im) (by simp))
  simp_rw [receiver_energy_expansion]
  have hsum := integral_add ((hr.const_mul (gramA S)).add (hri.const_mul (2 * gramC S)))
    (hi.const_mul (gramB S))
  simp only [Pi.add_apply] at hsum
  rw [hsum, integral_add (hr.const_mul (gramA S)) (hri.const_mul (2 * gramC S))]
  simp only [integral_const_mul]

/-- Receiver Gram convergence gives convergence of every actual compact-test
energy; no moment convergence is imposed as an additional hypothesis. -/
theorem test_energy_tendsto (μ : Measure Plane) [IsFiniteMeasure μ]
    (S : ℕ → ℂ ≃L[ℝ] ℂ) (S₀ : ℂ ≃L[ℝ] ℂ)
    (hA : Tendsto (fun n => gramA (S n)) atTop (𝓝 (gramA S₀)))
    (hB : Tendsto (fun n => gramB (S n)) atTop (𝓝 (gramB S₀)))
    (hC : Tendsto (fun n => gramC (S n)) atTop (𝓝 (gramC S₀)))
    {η : Plane → ℂ} (hη : Continuous η) (hc : HasCompactSupport η) :
    Tendsto (fun n => ∫ m, ‖S n (η m)‖ ^ 2 ∂μ) atTop
      (𝓝 (∫ m, ‖S₀ (η m)‖ ^ 2 ∂μ)) := by
  simp_rw [test_energy_moments μ _ hη hc]
  exact ((hA.mul_const _).add ((hC.const_mul 2).mul_const _)).add (hB.mul_const _)

/-- A nonzero prior test has positive energy for every invertible receiver,
so finite-noise information denominators are genuinely positive. -/
theorem test_energy_positive (μ : Measure Plane) [IsFiniteMeasure μ]
    (S T : ℂ ≃L[ℝ] ℂ) {η : Plane → ℂ} (hη : Continuous η) (hc : HasCompactSupport η)
    (hpos : 0 < ∫ m, ‖T (η m)‖ ^ 2 ∂μ) :
    0 < ∫ m, ‖S (η m)‖ ^ 2 ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun _ => sq_nonneg _) (test_energy_integrable μ S hη hc)]
  rw [integral_pos_iff_support_of_nonneg (fun _ => sq_nonneg _) (test_energy_integrable μ T hη hc)] at hpos
  have he : Function.support (fun m => ‖S (η m)‖ ^ 2) =
      Function.support (fun m => ‖T (η m)‖ ^ 2) := by
    ext m
    simp only [Function.mem_support, ne_eq, sq_eq_zero_iff, norm_eq_zero]
    rw [show S (η m) = 0 ↔ η m = 0 from
      ⟨fun h => S.injective (h.trans (map_zero S).symm), fun h => by simp [h]⟩]
    rw [show T (η m) = 0 ↔ η m = 0 from
      ⟨fun h => T.injective (h.trans (map_zero T).symm), fun h => by simp [h]⟩]
  rwa [he]

/-- The full all-Borel-decoder lower coefficient holds along changing
invertible receiver maps whenever their Gram entries tend to a nonsingular
Gram limit. The offsets and decoders may change freely with noise level. -/
theorem moving_gram_bayes_converse {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (hfull : ∀ᵐ m ∂priorLaw p, m ∈ Ω)
    (f : Plane → ℝ) (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hC : 0 ≤ C) (hgrad : ∀ m, ‖gradient f m‖ ≤ C)
    (S : ℕ → ℂ ≃L[ℝ] ℂ) (S₀ : ℂ ≃L[ℝ] ℂ)
    (hA : Tendsto (fun n => gramA (S n)) atTop (𝓝 (gramA S₀)))
    (hB : Tendsto (fun n => gramB (S n)) atTop (𝓝 (gramB S₀)))
    (hcross : Tendsto (fun n => gramC (S n)) atTop (𝓝 (gramC S₀)))
    (c : ℕ → Plane) (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0))
    (lo hi : ℝ) (hlohi : lo ≤ hi)
    (htarget : ∀ᵐ m ∂priorLaw p, lo ≤ f m ∧ f m ≤ hi) :
    LowerAsymptotic
      (fun n => optimalRisk p f (S n) (c n) (v n) / (2 * (v n : ℝ)))
      ((∫ m, ‖S₀.symm.toContinuousLinearMap.adjoint (gradient f m)‖ ^ 2 ∂priorLaw p) / 2) := by
  letI := priorLaw_isProbability p hp0 hpi hpn
  have hsup := WeightedVariational.inverse_gram_variational_supremum S₀
    (gradient_continuous hf) hΩ hfull hC hgrad
  have hnonempty : (WeightedVariational.gramVariationalValues S₀ (gradient f) Ω (priorLaw p)).Nonempty := by
    refine ⟨0, fun _ => 0, contDiff_const, HasCompactSupport.zero, ?_, ?_⟩
    · change tsupport (0 : Plane → ℂ) ⊆ Ω
      simp [tsupport]
    · simp
  intro a ha
  by_cases hnegative : a < 0
  · exact Eventually.of_forall fun n => hnegative.le.trans
      (div_nonneg (optimalRisk_nonneg p f (S n) (c n) (v n))
        (mul_nonneg (by norm_num) (v n).coe_nonneg))
  · have ha0 : 0 ≤ a := le_of_not_gt hnegative
    have ha' : 2 * a < sSup (WeightedVariational.gramVariationalValues S₀ (gradient f) Ω (priorLaw p)) := by
      rw [hsup]
      linarith
    obtain ⟨q, hqmem, haq⟩ := exists_lt_of_lt_csSup hnonempty ha'
    obtain ⟨η, hη, hc, hs, rfl⟩ := hqmem
    have henergy : 0 < ∫ m, ‖S₀ (η m)‖ ^ 2 ∂priorLaw p := by
      have hnonneg : 0 ≤ ∫ m, ‖S₀ (η m)‖ ^ 2 ∂priorLaw p :=
        integral_nonneg (fun _ => sq_nonneg _)
      have hne : (∫ m, ‖S₀ (η m)‖ ^ 2 ∂priorLaw p) ≠ 0 := by
        intro hz
        rw [hz, div_zero] at haq
        linarith
      exact lt_of_le_of_ne hnonneg (Ne.symm hne)
    obtain ⟨h₁, h₂, hc₁, hc₂, hs₁, hs₂⟩ := test_components hη hc hs
    have hEn : ∀ n, 0 < channelInformation p (fun m => (η m).re) (fun m => (η m).im)
        firstDirection secondDirection (receiverFirst (S n)) (receiverSecond (S n)) := by
      intro n
      rw [channelInformation_eq_energy p hp hp0]
      exact test_energy_positive (priorLaw p) (S n) S₀ hη.continuous hc henergy
    have hElim : Tendsto (fun n => channelInformation p (fun m => (η m).re) (fun m => (η m).im)
        firstDirection secondDirection (receiverFirst (S n)) (receiverSecond (S n))) atTop
        (𝓝 (∫ m, ‖S₀ (η m)‖ ^ 2 ∂priorLaw p)) := by
      simp only [channelInformation_eq_energy p hp hp0]
      exact test_energy_tendsto (priorLaw p) S S₀ hA hB hcross hη.continuous hc
    have hseq := GaussianSequentialConverse.nonsingular_row_sequence_lower hΩ p hp hp0 hpi hpn
      hpC hpPos f (fun m => (η m).re) (fun m => (η m).im) hf h₁ h₂ hc₁ hc₂ hs₁ hs₂
      firstDirection secondDirection (fun n => receiverFirst (S n)) (fun n => receiverSecond (S n))
      c v hv hlim lo hi hlohi htarget hEn _ henergy hElim
    rw [sensitivity_eq_inner hΩ p hp hp0 hpC f hf hη hc hs] at hseq
    apply hseq a
    have hquot : a < ((∫ m, inner ℝ (η m) (gradient f m) ∂priorLaw p) ^ 2 /
        (∫ m, ‖S₀ (η m)‖ ^ 2 ∂priorLaw p)) / 2 := by linarith
    simpa only [div_div, mul_comm _ (2 : ℝ)] using hquot

end Analog.GaussianMovingGram
