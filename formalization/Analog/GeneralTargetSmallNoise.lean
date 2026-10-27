import Analog.SmallNoise
import Analog.GaussianNoise
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Leading risk for a general exact decoder on an attainable moment set

At interior moments, exactness forces a decoder's local germ to equal the
prescribed differentiable target after the inverse affine channel. Thus no
separate differentiability assumption on the decoder is needed. This works
for an arbitrary two-statistic readout, not just m₂ - ψ(m₁). It establishes
achievability, not a statistical converse against arbitrary estimators.
-/

noncomputable section
namespace Analog.GeneralTargetSmallNoise

open Set Filter MeasureTheory
open scoped Topology NNReal

section Deterministic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exactness on an affine received set determines the decoder near every
interior moment. The received map is invertible; the set need not be convex. -/
theorem exact_decoder_eventuallyEq (M : Set E) (T : E ≃L[ℝ] E) (c : E)
    (F D : E → ℝ) (hexact : ∀ m ∈ M, D (c + T m) = F m)
    {m : E} (hm : m ∈ interior M) :
    D =ᶠ[𝓝 (c + T m)] (fun y => F (T.symm (y - c))) := by
  have hcont : Continuous (fun y : E => T.symm (y - c)) :=
    T.symm.continuous.comp (continuous_id.sub continuous_const)
  have he : T.symm (c + T m - c) = m := by simp
  have hmem : M ∈ 𝓝 m := mem_interior_iff_mem_nhds.mp hm
  have hmem' : M ∈ 𝓝 (T.symm (c + T m - c)) := by simpa only [he] using hmem
  have hcontAt : ContinuousAt (fun y : E => T.symm (y - c)) (c + T m) :=
    hcont.continuousAt
  have hnear : ∀ᶠ y in 𝓝 (c + T m), T.symm (y - c) ∈ M := by
    exact hcontAt.preimage_mem_nhds hmem'
  filter_upwards [hnear] with y hy
  have h := hexact (T.symm (y - c)) hy
  simpa using h

/-- The actual exact decoder has the inverse-channel derivative at interior
moments. Continuity or differentiability of the decoder is not assumed. -/
theorem exact_decoder_hasFDerivAt (M : Set E) (T : E ≃L[ℝ] E) (c : E)
    (F D : E → ℝ) (hexact : ∀ m ∈ M, D (c + T m) = F m)
    {m : E} (hm : m ∈ interior M) {J : E →L[ℝ] ℝ}
    (hF : HasFDerivAt F J m) :
    HasFDerivAt D (J.comp (T.symm : E →L[ℝ] E)) (c + T m) := by
  have hinv : HasFDerivAt (fun y : E => T.symm (y - c))
      (T.symm : E →L[ℝ] E) (c + T m) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      T.symm.hasFDerivAt.comp (c + T m)
      ((hasFDerivAt_id (c + T m)).sub_const c)
  have hf : HasFDerivAt F J (T.symm (c + T m - c)) := by simpa using hF
  exact (hf.comp (c + T m) hinv).congr_of_eventuallyEq
    (exact_decoder_eventuallyEq M T c F D hexact hm)

end Deterministic

section Integration
variable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure Ω}

/-- Actual leading MSE of any fixed Lipschitz decoder exact on the attainable
set. The target is arbitrary; interiority and target derivatives imply the
decoder derivative, and square-integrable noise supplies dominated convergence.
The probability law may couple moments and noise; no density is required. -/
theorem general_target_leading_mse (M : Set E) (T : E ≃L[ℝ] E) (c : E)
    (F D : E → ℝ) {L : ℝ≥0} (hD : LipschitzWith L D)
    (hexact : ∀ m ∈ M, D (c + T m) = F m)
    (m z : Ω → E) (hm : Measurable m) (hz : Measurable z)
    (hz2 : Integrable (fun ω => ‖z ω‖ ^ 2) μ)
    (hinterior : ∀ᵐ ω ∂μ, m ω ∈ interior M)
    (J : Ω → E →L[ℝ] ℝ) (hF : ∀ᵐ ω ∂μ, HasFDerivAt F (J ω) (m ω)) :
    Tendsto (fun N : ℝ =>
      (∫ ω, (D (c + T (m ω) + Real.sqrt N • z ω) - F (m ω)) ^ 2 ∂μ) / N)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ ω, (J ω (T.symm (z ω))) ^ 2 ∂μ)) := by
  have hr : Measurable (fun ω => c + T (m ω)) :=
    measurable_const.add (T.continuous.measurable.comp hm)
  apply SmallNoise.leading_mse_power_exact hD hr hz hz2
    (J := fun ω => (J ω).comp (T.symm : E →L[ℝ] E))
  · filter_upwards [hinterior] with ω hω
    exact hexact (m ω) (interior_subset hω)
  · filter_upwards [hinterior, hF] with ω hi hf
    exact exact_decoder_hasFDerivAt M T c F D hexact hi hf

end Integration
/-- Every real-linear scalar functional on the complex plane is determined
by its values on the two real coordinate directions. -/
theorem complex_clm_apply (J : ℂ →L[ℝ] ℝ) (z : ℂ) :
    J z = z.re * J 1 + z.im * J Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz, map_add, map_smul, map_smul]
  rfl

/-- The actual circular Gaussian law has the claimed directional covariance,
for every real continuous linear functional, with no assumed moment identities. -/
theorem gaussian_clm_second_moment (J : ℂ →L[ℝ] ℝ) :
    (∫ z : ℂ, (J z)^2 ∂GaussianNoise.standardComplexGaussian) =
      ((J 1)^2 + (J Complex.I)^2) / 2 := by
  have hz2 := GaussianNoise.complex_norm_square_integrable
  have hx2 : Integrable (fun z : ℂ => z.re^2) GaussianNoise.standardComplexGaussian := by
    apply hz2.mono' (Complex.continuous_re.measurable.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [Complex.normSq_apply z, Complex.normSq_eq_norm_sq z, sq_nonneg z.im]
  have hy2 : Integrable (fun z : ℂ => z.im^2) GaussianNoise.standardComplexGaussian := by
    apply hz2.mono' (Complex.continuous_im.measurable.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [Complex.normSq_apply z, Complex.normSq_eq_norm_sq z, sq_nonneg z.re]
  have hxy := SmallNoise.integrable_mul_of_squares
    Complex.continuous_re.measurable Complex.continuous_im.measurable hx2 hy2
  have heq : (fun z : ℂ => (J z)^2) =
      (fun z => (J 1)^2 * z.re^2 + (2 * J 1 * J Complex.I) * (z.re*z.im) +
        (J Complex.I)^2 * z.im^2) := by
    funext z
    rw [complex_clm_apply]
    ring
  have hsum := integral_add
    ((hx2.const_mul ((J 1)^2)).add (hxy.const_mul (2 * J 1 * J Complex.I)))
    (hy2.const_mul ((J Complex.I)^2))
  have hsum' := integral_add (hx2.const_mul ((J 1)^2))
    (hxy.const_mul (2 * J 1 * J Complex.I))
  simp only [Pi.add_apply] at hsum hsum'
  rw [heq, hsum, hsum']
  simp only [integral_const_mul, GaussianNoise.complex_real_second_moment,
    GaussianNoise.complex_imag_second_moment, GaussianNoise.complex_cross_moment]
  ring

section GaussianIntegration
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- General-target circular-Gaussian achievability with the coefficient
explicitly evaluated in the inverse channel's real and imaginary directions.
Interiority and target differentiability force the decoder derivative. The
limiting derivative square is proved integrable from decoder Lipschitzness;
no measurability or integrability assumption on the derivative field is added. -/
theorem gaussian_general_target_leading_mse (M : Set ℂ) (T : ℂ ≃L[ℝ] ℂ) (c : ℂ)
    (F D : ℂ → ℝ) {L : ℝ≥0} (hD : LipschitzWith L D)
    (hexact : ∀ m ∈ M, D (c + T m) = F m)
    (m : Ω → ℂ) (hm : Measurable m)
    (hinterior : ∀ᵐ ω ∂μ, m ω ∈ interior M)
    (J : Ω → ℂ →L[ℝ] ℝ) (hF : ∀ᵐ ω ∂μ, HasFDerivAt F (J ω) (m ω)) :
    Tendsto (fun N : ℝ =>
      (∫ p : Ω × ℂ, (D (c + T (m p.1) + Real.sqrt N • p.2) - F (m p.1))^2
        ∂μ.prod GaussianNoise.standardComplexGaussian) / N)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((1 / 2 : ℝ) * ∫ ω,
        (J ω (T.symm 1))^2 + (J ω (T.symm Complex.I))^2 ∂μ)) := by
  let ν := GaussianNoise.standardComplexGaussian
  have hr : Measurable (fun p : Ω × ℂ => c + T (m p.1)) :=
    measurable_const.add (T.continuous.measurable.comp (hm.comp measurable_fst))
  have hJ : ∀ᵐ p : Ω × ℂ ∂μ.prod ν,
      HasFDerivAt D ((J p.1).comp (T.symm : ℂ →L[ℝ] ℂ)) (c + T (m p.1)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hinterior,
      Measure.quasiMeasurePreserving_fst.ae hF] with p hi hf
    exact exact_decoder_hasFDerivAt M T c F D hexact hi hf
  have hi := SmallNoise.directional_second_moment_integrable hD hr measurable_snd
    (GaussianNoise.complex_norm_square_integrable.comp_snd μ) hJ
  change Integrable (fun p : Ω × ℂ => (J p.1 (T.symm p.2))^2) (μ.prod ν) at hi
  have hlim := general_target_leading_mse M T c F D hD hexact
    (fun p : Ω × ℂ => m p.1) (fun p : Ω × ℂ => p.2) (hm.comp measurable_fst) measurable_snd
    (GaussianNoise.complex_norm_square_integrable.comp_snd μ)
    (Measure.quasiMeasurePreserving_fst.ae hinterior)
    (fun p : Ω × ℂ => J p.1) (Measure.quasiMeasurePreserving_fst.ae hF)
  have heval : (∫ p : Ω × ℂ, (J p.1 (T.symm p.2))^2 ∂μ.prod ν) =
      (1 / 2 : ℝ) * ∫ ω, (J ω (T.symm 1))^2 + (J ω (T.symm Complex.I))^2 ∂μ := by
    rw [MeasureTheory.integral_prod _ hi]
    simp_rw [show ∀ ω, (∫ z : ℂ, (J ω (T.symm z))^2 ∂ν) =
      ((J ω (T.symm 1))^2 + (J ω (T.symm Complex.I))^2)/2 from
        fun ω => gaussian_clm_second_moment ((J ω).comp (T.symm : ℂ →L[ℝ] ℂ))]
    rw [integral_div]
    ring
  rw [heval] at hlim
  exact hlim

end GaussianIntegration
end Analog.GeneralTargetSmallNoise
