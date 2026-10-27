import Analog.GeneralSmallNoise
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Standard circular complex Gaussian noise

We construct the complex law from two independent N(0, 1/2) coordinates.
Its moment and integrability facts discharge the noise hypotheses in the
general decoder's leading-MSE theorem.
-/

noncomputable section

namespace Analog.GaussianNoise

open MeasureTheory ProbabilityTheory ArbitraryEncoder GeneralDecoder GeneralScore
open GeneralSmallNoise GramSynthesis Set Filter
open scoped Topology NNReal

def coordinateGaussian : Measure ℝ := gaussianReal 0 (1 / 2)

instance : IsProbabilityMeasure coordinateGaussian := by
  unfold coordinateGaussian
  infer_instance

lemma asComplex_measurable : Measurable asComplex :=
  Complex.equivRealProdCLM.symm.continuous.measurable

def standardComplexGaussian : Measure ℂ :=
  (coordinateGaussian.prod coordinateGaussian).map asComplex

instance : IsProbabilityMeasure standardComplexGaussian :=
  Measure.isProbabilityMeasure_map asComplex_measurable.aemeasurable

theorem coordinate_mean : (∫ x : ℝ, x ∂coordinateGaussian) = 0 := by
  exact integral_id_gaussianReal

theorem coordinate_second_moment : (∫ x : ℝ, x ^ 2 ∂coordinateGaussian) = 1 / 2 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0))
  rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id.aemeasurable] at h
  simpa only [integral_id_gaussianReal, sub_zero, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat] using h

theorem coordinate_square_integrable : Integrable (fun x : ℝ => x ^ 2) coordinateGaussian := by
  have h : MemLp id (2 : ENNReal) coordinateGaussian := memLp_id_gaussianReal 2
  simpa only [Real.norm_eq_abs, sq_abs, id_eq] using h.integrable_norm_pow (by decide : 2 ≠ 0)

theorem complex_norm_square_integrable :
    Integrable (fun z : ℂ => ‖z‖ ^ 2) standardComplexGaussian := by
  apply (integrable_map_measure (by fun_prop) asComplex_measurable.aemeasurable).mpr
  convert (coordinate_square_integrable.comp_fst coordinateGaussian).add
    (coordinate_square_integrable.comp_snd coordinateGaussian) using 1
  ext p
  simp only [Function.comp_apply, Pi.add_apply, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply, asComplex]
  ring

theorem complex_real_second_moment :
    (∫ z : ℂ, z.re ^ 2 ∂standardComplexGaussian) = 1 / 2 := by
  unfold standardComplexGaussian
  rw [integral_map asComplex_measurable.aemeasurable (by fun_prop)]
  change (∫ p : ℝ × ℝ, p.1 ^ 2 ∂coordinateGaussian.prod coordinateGaussian) = _
  have h := integral_prod_mul (μ := coordinateGaussian) (ν := coordinateGaussian)
    (fun x : ℝ => x ^ 2) (fun _ : ℝ => (1 : ℝ))
  simpa only [mul_one, integral_const, measureReal_univ_eq_one, one_smul,
    coordinate_second_moment] using h

theorem complex_imag_second_moment :
    (∫ z : ℂ, z.im ^ 2 ∂standardComplexGaussian) = 1 / 2 := by
  unfold standardComplexGaussian
  rw [integral_map asComplex_measurable.aemeasurable (by fun_prop)]
  change (∫ p : ℝ × ℝ, p.2 ^ 2 ∂coordinateGaussian.prod coordinateGaussian) = _
  have h := integral_prod_mul (μ := coordinateGaussian) (ν := coordinateGaussian)
    (fun _ : ℝ => (1 : ℝ)) (fun x : ℝ => x ^ 2)
  simpa only [one_mul, integral_const, measureReal_univ_eq_one, one_smul,
    coordinate_second_moment] using h

theorem complex_cross_moment :
    (∫ z : ℂ, z.re * z.im ∂standardComplexGaussian) = 0 := by
  unfold standardComplexGaussian
  rw [integral_map asComplex_measurable.aemeasurable (by fun_prop)]
  change (∫ p : ℝ × ℝ, p.1 * p.2 ∂coordinateGaussian.prod coordinateGaussian) = _
  have h := integral_prod_mul (μ := coordinateGaussian) (ν := coordinateGaussian)
    (fun x : ℝ => x) (fun x : ℝ => x)
  simpa only [coordinate_mean, zero_mul] using h

section SourceLaw

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The paper's actual source-list small-noise statement, now with the
Gaussian law instantiated rather than its moments assumed. -/
theorem gaussian_source_leading_mse (e : Curve) {K : ℕ} (hK : 0 < K) (φ ψ : ℝ → ℝ)
    (hD : 0 < det e.A e.B e.C)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hc : ContinuousOn (readoutSlope ψ) (Icc (-1 : ℝ) 1))
    (hshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (xs : Ω → List ℝ) (hvalid : ∀ᵐ ω ∂μ, ValidInput K (xs ω))
    (hr : Measurable (fun ω => asComplex (received (encoder e φ) (xs ω))))
    (hmean : ∀ᵐ ω ∂μ, -1 < firstMoment (xs ω) / (K : ℝ) ∧ firstMoment (xs ω) / (K : ℝ) < 1) :
    Tendsto (fun N : ℝ =>
      (∫ p : Ω × ℂ, (decode e K ψ (asComplex (received (encoder e φ) (xs p.1)) +
        Real.sqrt N • p.2) - GeneralCollision.target K φ ψ (xs p.1)) ^ 2
        ∂μ.prod standardComplexGaussian) / N)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Frontier.risk (-(∫ ω, readoutSlope ψ (firstMoment (xs ω) / (K : ℝ)) ∂μ))
        ((∫ ω, readoutSlope ψ (firstMoment (xs ω) / (K : ℝ)) ^ 2 ∂μ) -
          (∫ ω, readoutSlope ψ (firstMoment (xs ω) / (K : ℝ)) ∂μ) ^ 2)
        ⟨e.A, e.B, e.C⟩ / (2 * (K : ℝ) ^ 2))) :=
  source_leading_mse_inverseGram e hK φ ψ hD hd hc hshape xs hvalid hr hmean
    complex_norm_square_integrable complex_real_second_moment complex_imag_second_moment
    complex_cross_moment

/-- The permitted output-clipped decoder has the same coefficient under
the instantiated circular Gaussian law. -/
theorem gaussian_clipped_leading_mse (e : Curve) {K : ℕ} (hK : 0 < K) (ψ : ℝ → ℝ)
    (hD : 0 < det e.A e.B e.C)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hc : ContinuousOn (readoutSlope ψ) (Icc (-1 : ℝ) 1))
    (hshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    {r : Ω → ℂ} {f : Ω → ℝ} (hr : Measurable r)
    (hexact : ∀ᵐ ω ∂μ, decode e K ψ (r ω) = f ω)
    (hmean : ∀ᵐ ω ∂μ, -1 < (e.inverseMoments K (complexCoordinates (r ω))).1 ∧
      (e.inverseMoments K (complexCoordinates (r ω))).1 < 1)
    (a b : ℝ) (hclip : ∀ᵐ ω ∂μ, a < f ω ∧ f ω < b) :
    Tendsto (fun N : ℝ =>
      (∫ p : Ω × ℂ, (Decoder.clip a b
        (decode e K ψ (r p.1 + Real.sqrt N • p.2)) - f p.1) ^ 2
        ∂μ.prod standardComplexGaussian) / N)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Frontier.risk (-(∫ ω, slopeField e K ψ (r ω) ∂μ))
        ((∫ ω, slopeField e K ψ (r ω) ^ 2 ∂μ) -
          (∫ ω, slopeField e K ψ (r ω) ∂μ) ^ 2)
        ⟨e.A, e.B, e.C⟩ / (2 * (K : ℝ) ^ 2))) :=
  clipped_leading_mse_inverseGram e hK ψ hD hd hc hshape hr hexact hmean a b hclip
    complex_norm_square_integrable complex_real_second_moment complex_imag_second_moment
    complex_cross_moment

end SourceLaw

end Analog.GaussianNoise
