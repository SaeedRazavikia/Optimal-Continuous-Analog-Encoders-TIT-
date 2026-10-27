import Analog.GaussianScoreIdentity
import Analog.GaussianNoise
import Analog.GaussianBayesConverse

/-!
# Equality of the Gaussian density model and additive-noise model

The likelihood-based converse and the independent standard-complex-Gaussian
achievability calculation describe the same probability law. These results
identify the measures, including risks of arbitrary Borel decoders.
-/

noncomputable section
namespace Analog.GaussianLawBridge
open MeasureTheory ProbabilityTheory GaussianScoreIdentity GaussianNoise
open scoped Topology NNReal ENNReal

abbrev Plane := ℝ × ℝ

def additiveObservation (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0)
    (m : Plane) (z : ℂ) : Plane :=
  (c.1 + r₁ m + Real.sqrt (2 * (v : ℝ)) * z.re,
    c.2 + r₂ m + Real.sqrt (2 * (v : ℝ)) * z.im)

def sampleMap (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0)
    (q : Plane × ℂ) : Plane × Plane :=
  (q.1, additiveObservation r₁ r₂ c v q.1 q.2)

theorem additiveObservation_measurable (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0) :
    Measurable (fun q : Plane × ℂ => additiveObservation r₁ r₂ c v q.1 q.2) := by
  unfold additiveObservation
  fun_prop

theorem sampleMap_measurable (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0) :
    Measurable (sampleMap r₁ r₂ c v) :=
  measurable_fst.prodMk (additiveObservation_measurable r₁ r₂ c v)

/-- Scaling a standard real coordinate of variance 1/2 by sqrt(2v) gives
variance v, with the stated observation mean. -/
theorem coordinate_affine_law (u : ℝ) (v : ℝ≥0) :
    coordinateGaussian.map (fun x => u + Real.sqrt (2 * (v : ℝ)) * x) =
      gaussianReal u v := by
  have he : (⟨Real.sqrt (2 * (v : ℝ)) ^ 2, sq_nonneg _⟩ : ℝ≥0) * (1 / 2) = v := by
    apply NNReal.eq
    change Real.sqrt (2 * (v : ℝ)) ^ 2 * (1 / 2 : ℝ) = (v : ℝ)
    have hnon : 0 ≤ 2 * (v : ℝ) := by positivity
    rw [Real.sq_sqrt hnon]
    ring
  change (gaussianReal 0 (1 / 2)).map
    ((fun x : ℝ => u + x) ∘ (fun x : ℝ => Real.sqrt (2 * (v : ℝ)) * x)) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_add, he]
  simp

/-- Conditional on each moment, the additive circular Gaussian has precisely
the pair of independent real Gaussian laws used by the likelihood. -/
theorem conditional_additive_law (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0)
    (m : Plane) :
    standardComplexGaussian.map (additiveObservation r₁ r₂ c v m) =
      (gaussianReal (c.1 + r₁ m) v).prod (gaussianReal (c.2 + r₂ m) v) := by
  rw [standardComplexGaussian, Measure.map_map (by unfold additiveObservation; fun_prop)
    asComplex_measurable]
  change (coordinateGaussian.prod coordinateGaussian).map
    (Prod.map (fun x => c.1 + r₁ m + Real.sqrt (2 * (v : ℝ)) * x)
      (fun x => c.2 + r₂ m + Real.sqrt (2 * (v : ℝ)) * x)) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    coordinate_affine_law, coordinate_affine_law]

/-- The product conditional Gaussian law has the actual likelihood density. -/
theorem conditional_density_law (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane)
    {v : ℝ≥0} (hv : v ≠ 0) (m : Plane) :
    (gaussianReal (c.1 + r₁ m) v).prod (gaussianReal (c.2 + r₂ m) v) =
      volume.withDensity (fun y => ENNReal.ofReal (likelihood r₁ r₂ c v m y)) := by
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv,
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _)]
  congr 1
  funext y
  exact (ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)).symm

/-- Exact equality of the two observation models: a prior moment and an
independent standard circular Gaussian pushed through the additive channel
have the same joint law as the explicit Gaussian likelihood density. -/
theorem jointLaw_eq_additive_pushforward
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0) :
    ((priorLaw p).prod standardComplexGaussian).map (sampleMap r₁ r₂ c v) =
      jointLaw p r₁ r₂ c v := by
  apply Measure.ext_of_lintegral
  intro H hH
  have hsample := sampleMap_measurable r₁ r₂ c v
  have hl : Measurable (fun q : Plane × Plane =>
      ENNReal.ofReal (likelihood r₁ r₂ c v q.1 q.2)) :=
    (likelihood_joint_continuous r₁ r₂ c v).measurable.ennreal_ofReal
  have hcond : ∀ m : Plane,
      (∫⁻ z, H (m, additiveObservation r₁ r₂ c v m z) ∂standardComplexGaussian) =
        ∫⁻ y, ENNReal.ofReal (likelihood r₁ r₂ c v m y) * H (m, y) := by
    intro m
    have hpair : Measurable (fun y : Plane => (m, y)) :=
      measurable_const.prodMk measurable_id
    have hHm : Measurable (fun y : Plane => H (m, y)) :=
      hH.comp hpair
    have hTm : Measurable (additiveObservation r₁ r₂ c v m) := by
      unfold additiveObservation
      fun_prop
    have hlm : Measurable (fun y : Plane => ENNReal.ofReal (likelihood r₁ r₂ c v m y)) := by
      change Measurable (fun y : Plane => ENNReal.ofReal
        (gaussianPDFReal (c.1 + r₁ m) v y.1 * gaussianPDFReal (c.2 + r₂ m) v y.2))
      exact (((measurable_gaussianPDFReal _ _).comp measurable_fst).mul
        ((measurable_gaussianPDFReal _ _).comp measurable_snd)).ennreal_ofReal
    rw [← lintegral_map (μ := standardComplexGaussian) hHm hTm, conditional_additive_law,
      conditional_density_law r₁ r₂ c hv,
      lintegral_withDensity_eq_lintegral_mul volume hlm hHm]
    rfl
  rw [lintegral_map hH hsample,
    lintegral_prod (fun q => H (sampleMap r₁ r₂ c v q)) (hH.comp hsample).aemeasurable]
  change (∫⁻ m, ∫⁻ z, H (m, additiveObservation r₁ r₂ c v m z)
    ∂standardComplexGaussian ∂priorLaw p) = _
  simp_rw [hcond]
  have hout : Measurable (fun m : Plane =>
      ∫⁻ y : Plane, ENNReal.ofReal (likelihood r₁ r₂ c v m y) * H (m, y)) :=
    (hl.mul hH).lintegral_prod_right
  have hdensity : Measurable (fun q : Plane × Plane =>
      ENNReal.ofReal (p q.1 * likelihood r₁ r₂ c v q.1 q.2)) :=
    ((hp.comp measurable_fst).mul (likelihood_joint_continuous r₁ r₂ c v).measurable).ennreal_ofReal
  rw [priorLaw, lintegral_withDensity_eq_lintegral_mul volume hp.ennreal_ofReal hout,
    jointLaw, lintegral_withDensity_eq_lintegral_mul volume hdensity hH]
  change (∫⁻ m, ENNReal.ofReal (p m) *
      (∫⁻ y, ENNReal.ofReal (likelihood r₁ r₂ c v m y) * H (m, y))) =
    ∫⁻ q : Plane × Plane, ENNReal.ofReal (p q.1 * likelihood r₁ r₂ c v q.1 q.2) * H q
      ∂volume.prod volume
  rw [lintegral_prod _ (hdensity.mul hH).aemeasurable]
  apply lintegral_congr
  intro m
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro y
  rw [ENNReal.ofReal_mul (hp0 m), mul_assoc]

/-- Integrability transfers in both directions between the two identical
observation models. No boundedness of the integrand is required. -/
theorem integrable_jointLaw_iff_additive
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0)
    (H : Plane × Plane → ℝ) (hH : Measurable H) :
    Integrable H (jointLaw p r₁ r₂ c v) ↔
      Integrable (fun q => H (sampleMap r₁ r₂ c v q))
        ((priorLaw p).prod standardComplexGaussian) := by
  rw [← jointLaw_eq_additive_pushforward p hp hp0 r₁ r₂ c hv]
  exact integrable_map_measure hH.aestronglyMeasurable
    (sampleMap_measurable r₁ r₂ c v).aemeasurable

/-- Real integrals agree exactly under the density and additive-noise models. -/
theorem integral_jointLaw_eq_additive
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0)
    (H : Plane × Plane → ℝ) (hH : Measurable H) :
    (∫ q, H q ∂jointLaw p r₁ r₂ c v) =
      ∫ q, H (sampleMap r₁ r₂ c v q) ∂(priorLaw p).prod standardComplexGaussian := by
  rw [← jointLaw_eq_additive_pushforward p hp hp0 r₁ r₂ c hv]
  exact integral_map (sampleMap_measurable r₁ r₂ c v).aemeasurable hH.aestronglyMeasurable

/-- Nonnegative squared risks agree even for an unbounded Borel decoder with
infinite risk. -/
theorem squareRisk_eq_additive
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0)
    (f D : Plane → ℝ) (hf : Measurable f) (hD : Measurable D) :
    BorelRisk.squareRisk (jointLaw p r₁ r₂ c v) (fun q => f q.1) (fun q => D q.2) =
      ∫⁻ q, ENNReal.ofReal ((D (additiveObservation r₁ r₂ c v q.1 q.2) - f q.1)^2)
        ∂(priorLaw p).prod standardComplexGaussian := by
  unfold BorelRisk.squareRisk
  rw [← jointLaw_eq_additive_pushforward p hp hp0 r₁ r₂ c hv]
  exact lintegral_map (((hD.comp measurable_snd).sub (hf.comp measurable_fst)).pow_const 2).ennreal_ofReal
    (sampleMap_measurable r₁ r₂ c v)

/-- Complex coordinates identify the additive observation with the standard
affine receiver expression used by the explicit decoder. -/
theorem additiveObservation_asComplex (S : ℂ ≃L[ℝ] ℂ) (c : ℂ) (v : ℝ≥0)
    (m : Plane) (z : ℂ) :
    ArbitraryEncoder.asComplex (additiveObservation
      (GaussianBayesConverse.receiverFirst S) (GaussianBayesConverse.receiverSecond S)
      (Complex.equivRealProdCLM c) v m z) =
      c + S (ArbitraryEncoder.asComplex m) + Real.sqrt (2 * (v : ℝ)) • z := by
  apply Complex.ext <;>
    simp [ArbitraryEncoder.asComplex, additiveObservation,
      GaussianBayesConverse.receiverFirst, GaussianBayesConverse.receiverSecond,
      Complex.equivRealProdCLM_symm_apply, Complex.mk_eq_add_mul_I]

end Analog.GaussianLawBridge
