import Analog.GeneralDecoder
import Analog.SmallNoise
import Analog.Frontier

/-!
# Actual general-decoder derivatives and their small-noise limit

We differentiate the corrected strip decoder at interior means, identify its
two received-coordinate derivatives, and connect them to the inverse-Gram
quadratic form. The integrated limit applies to the implemented decoder.
-/

noncomputable section

namespace Analog.GeneralSmallNoise

open Set Filter MeasureTheory GeneralDecoder GeneralScore GramSynthesis
open scoped Topology NNReal

def meanDerivative (e : Curve) (K : ℕ) : ℂ →L[ℝ] ℝ :=
  ((K : ℝ) * e.basisDet)⁻¹ • (e.vy • Complex.reCLM - e.vx • Complex.imCLM)

def momentDerivative (e : Curve) (K : ℕ) : ℂ →L[ℝ] ℝ :=
  ((K : ℝ) * e.basisDet)⁻¹ • ((-e.uy) • Complex.reCLM + e.ux • Complex.imCLM)

def gradient (e : Curve) (K : ℕ) (slope : ℝ) : ℂ →L[ℝ] ℝ :=
  momentDerivative e K - slope • meanDerivative e K

def gradientReal (e : Curve) (K : ℕ) (slope : ℝ) : ℝ :=
  (-e.uy - slope * e.vy) / ((K : ℝ) * e.basisDet)

def gradientImag (e : Curve) (K : ℕ) (slope : ℝ) : ℝ :=
  (e.ux + slope * e.vx) / ((K : ℝ) * e.basisDet)

theorem inverse_mean_hasFDerivAt (e : Curve) (K : ℕ) (y : ℂ) :
    HasFDerivAt (fun z => (e.inverseMoments K (complexCoordinates z)).1)
      (meanDerivative e K) y := by
  have hr := ((Complex.reCLM.hasFDerivAt (x := y)).sub_const ((K : ℝ) * e.cx)).const_mul e.vy
  have hi := ((Complex.imCLM.hasFDerivAt (x := y)).sub_const ((K : ℝ) * e.cy)).const_mul e.vx
  convert (hr.sub hi).const_mul (((K : ℝ) * e.basisDet)⁻¹) using 1
  ext z
  simp only [Curve.inverseMoments, complexCoordinates, Pi.sub_apply, Complex.reCLM_apply,
    Complex.imCLM_apply]
  ring

theorem inverse_moment_hasFDerivAt (e : Curve) (K : ℕ) (y : ℂ) :
    HasFDerivAt (fun z => (e.inverseMoments K (complexCoordinates z)).2)
      (momentDerivative e K) y := by
  have hr := ((Complex.reCLM.hasFDerivAt (x := y)).sub_const ((K : ℝ) * e.cx)).const_mul (-e.uy)
  have hi := ((Complex.imCLM.hasFDerivAt (x := y)).sub_const ((K : ℝ) * e.cy)).const_mul e.ux
  convert (hr.add hi).const_mul (((K : ℝ) * e.basisDet)⁻¹) using 1
  ext z
  simp only [Curve.inverseMoments, complexCoordinates, Pi.add_apply, Complex.reCLM_apply,
    Complex.imCLM_apply]
  ring

theorem decode_hasFDerivAt (e : Curve) (K : ℕ) (ψ : ℝ → ℝ)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1)) (y : ℂ)
    (hy : -1 < (e.inverseMoments K (complexCoordinates y)).1 ∧
      (e.inverseMoments K (complexCoordinates y)).1 < 1) :
    HasFDerivAt (decode e K ψ)
      (gradient e K (readoutSlope ψ (e.inverseMoments K (complexCoordinates y)).1)) y := by
  have hp : ContinuousAt (fun z => e.inverseMoments K (complexCoordinates z)) y := by
    unfold Curve.inverseMoments complexCoordinates
    fun_prop
  have hs := readoutSlope_hasDerivAt ψ hd _ hy
  have hc := hs.comp_hasFDerivAt y (inverse_mean_hasFDerivAt e K y)
  have hraw := (inverse_moment_hasFDerivAt e K y).sub hc
  change HasFDerivAt (fun z => postprocess ψ (e.inverseMoments K (complexCoordinates z)))
    (gradient e K (readoutSlope ψ (e.inverseMoments K (complexCoordinates y)).1)) y at hraw
  exact hraw.congr_of_eventuallyEq
    (SmallNoise.projected_readout_eventuallyEq hp hy e.B e.C (postprocess ψ))

theorem gradient_apply (e : Curve) (K : ℕ) (slope : ℝ) (z : ℂ) :
    gradient e K slope z = gradientReal e K slope * z.re + gradientImag e K slope * z.im := by
  simp only [gradient, meanDerivative, momentDerivative, gradientReal, gradientImag,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  ring

/-- The exact received-coordinate gradient norm, including the channel
normalization, equals the inverse-Gram sensitivity. -/
theorem gradient_energy (e : Curve) (K : ℕ) (slope : ℝ) :
    gradientReal e K slope ^ 2 + gradientImag e K slope ^ 2 =
      (e.B * slope ^ 2 + 2 * e.C * slope + e.A) /
        ((K : ℝ) ^ 2 * det e.A e.B e.C) := by
  have h := SmallNoise.gram_gradient_energy e.ux e.uy e.vx e.vy K (-slope) 1
  convert h using 1 <;>
    dsimp [gradientReal, gradientImag, Curve.basisDet, Curve.A, Curve.B, Curve.C, det] <;> ring

section JointLaw

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The actual general decoder has the leading-MSE limit. Differentiability
is derived from the mean-interior condition, not assumed of the decoder. -/
theorem leading_mse (e : Curve) {K : ℕ} (hK : 0 < K) (ψ : ℝ → ℝ)
    (hD : 0 < det e.A e.B e.C)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    {r z : Ω → ℂ} {f : Ω → ℝ}
    (hr : Measurable r) (hz : Measurable z)
    (hz2 : Integrable (fun ω => ‖z ω‖ ^ 2) μ)
    (hexact : ∀ᵐ ω ∂μ, decode e K ψ (r ω) = f ω)
    (hmean : ∀ᵐ ω ∂μ, -1 < (e.inverseMoments K (complexCoordinates (r ω))).1 ∧
      (e.inverseMoments K (complexCoordinates (r ω))).1 < 1) :
    Tendsto (fun N : ℝ =>
      (∫ ω, (decode e K ψ (r ω + Real.sqrt N • z ω) - f ω) ^ 2 ∂μ) / N)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ ω, (gradient e K
        (readoutSlope ψ (e.inverseMoments K (complexCoordinates (r ω))).1) (z ω)) ^ 2 ∂μ)) := by
  apply SmallNoise.leading_mse_power_exact (decode_lipschitz e hK ψ hD hd hshape)
    hr hz hz2 hexact
  filter_upwards [hmean] with ω hω
  exact decode_hasFDerivAt e K ψ hd (r ω) hω

end JointLaw

/-- Endpoint-clipped extension makes the slope field measurable everywhere;
it agrees with the true derivative at every admissible interior mean. -/
def slopeField (e : Curve) (K : ℕ) (ψ : ℝ → ℝ) (y : ℂ) : ℝ :=
  readoutSlope ψ (Decoder.clip (-1) 1 (e.inverseMoments K (complexCoordinates y)).1)

theorem slopeField_continuous (e : Curve) (K : ℕ) (ψ : ℝ → ℝ)
    (hc : ContinuousOn (readoutSlope ψ) (Icc (-1 : ℝ) 1)) :
    Continuous (slopeField e K ψ) := by
  apply hc.comp_continuous
  · apply (Decoder.clip_lipschitz (-1) 1).continuous.comp
    unfold Curve.inverseMoments complexCoordinates
    fun_prop
  · intro y
    exact Strip.project_in_strip e.B e.C (e.inverseMoments K (complexCoordinates y))

section IndependentNoise

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem slopeField_square_integrable (e : Curve) (K : ℕ) (ψ : ℝ → ℝ)
    (hc : ContinuousOn (readoutSlope ψ) (Icc (-1 : ℝ) 1))
    {r : Ω → ℂ} (hr : Measurable r) :
    Integrable (fun ω => slopeField e K ψ (r ω) ^ 2) μ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hm := ((slopeField_continuous e K ψ hc).measurable.comp hr).pow_const 2
  apply (integrable_const (C ^ 2)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  have hb := hC (Decoder.clip (-1) 1 (e.inverseMoments K (complexCoordinates (r ω))).1)
    (Strip.project_in_strip e.B e.C (e.inverseMoments K (complexCoordinates (r ω))))
  have hb' : |slopeField e K ψ (r ω)| ≤ C := hb
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change slopeField e K ψ (r ω) ^ 2 ≤ C ^ 2
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hb')).mpr hb'

lemma affine_square_integrable {s : Ω → ℝ} (hs : Integrable s μ)
    (hs2 : Integrable (fun ω => s ω ^ 2) μ) (a b : ℝ) :
    Integrable (fun ω => (a + b * s ω) ^ 2) μ := by
  convert ((integrable_const (a ^ 2)).add (hs.const_mul (2 * a * b))).add
    (hs2.const_mul (b ^ 2)) using 1
  ext ω
  simp only [Pi.add_apply]
  ring

theorem gradient_second_moment (e : Curve) (K : ℕ) {s : Ω → ℝ}
    (hs : Measurable s) (hs2 : Integrable (fun ω => s ω ^ 2) μ)
    {ν : Measure ℂ} [IsProbabilityMeasure ν]
    (hz2 : Integrable (fun z : ℂ => ‖z‖ ^ 2) ν)
    (hxx : (∫ z : ℂ, z.re ^ 2 ∂ν) = 1 / 2)
    (hyy : (∫ z : ℂ, z.im ^ 2 ∂ν) = 1 / 2)
    (hxy : (∫ z : ℂ, z.re * z.im ∂ν) = 0) :
    (∫ p : Ω × ℂ, (gradient e K (s p.1) p.2) ^ 2 ∂μ.prod ν) =
      Frontier.risk (-(∫ ω, s ω ∂μ))
        ((∫ ω, s ω ^ 2 ∂μ) - (∫ ω, s ω ∂μ) ^ 2)
        ⟨e.A, e.B, e.C⟩ / (2 * (K : ℝ) ^ 2) := by
  have hs1 : Integrable s μ := by
    simpa using SmallNoise.integrable_mul_of_squares (b := fun _ => (1 : ℝ))
      hs measurable_const hs2 (by simp only [one_pow]; exact integrable_const (1 : ℝ))
  have ha : Measurable (fun ω => gradientReal e K (s ω)) := by
    unfold gradientReal
    fun_prop
  have hb : Measurable (fun ω => gradientImag e K (s ω)) := by
    unfold gradientImag
    fun_prop
  have ha2 : Integrable (fun ω => gradientReal e K (s ω) ^ 2) μ := by
    simpa [gradientReal, div_pow, mul_comm] using
      (affine_square_integrable hs1 hs2 (-e.uy) (-e.vy)).div_const (((K : ℝ) * e.basisDet) ^ 2)
  have hb2 : Integrable (fun ω => gradientImag e K (s ω) ^ 2) μ := by
    simpa [gradientImag, div_pow, mul_comm] using
      (affine_square_integrable hs1 hs2 e.ux e.vx).div_const (((K : ℝ) * e.basisDet) ^ 2)
  have hx2 : Integrable (fun z : ℂ => z.re ^ 2) ν := by
    apply hz2.mono' (Complex.continuous_re.measurable.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [Complex.normSq_apply z, Complex.normSq_eq_norm_sq z, sq_nonneg z.im]
  have hy2 : Integrable (fun z : ℂ => z.im ^ 2) ν := by
    apply hz2.mono' (Complex.continuous_im.measurable.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [Complex.normSq_apply z, Complex.normSq_eq_norm_sq z, sq_nonneg z.re]
  simp_rw [gradient_apply]
  rw [SmallNoise.isotropic_directional_second_moment ha hb
    Complex.continuous_re.measurable Complex.continuous_im.measurable ha2 hb2 hx2 hy2 hxx hyy hxy]
  rw [← integral_add ha2 hb2]
  simp_rw [gradient_energy]
  have hi1 := integral_add ((hs2.const_mul e.B).add (hs1.const_mul (2 * e.C))) (integrable_const e.A)
  have hi2 := integral_add (hs2.const_mul e.B) (hs1.const_mul (2 * e.C))
  simp only [Pi.add_apply] at hi1 hi2
  rw [integral_div, hi1, hi2, integral_const_mul, integral_const_mul]
  simp only [integral_const, measureReal_univ_eq_one, one_smul]
  rw [Frontier.risk_trace_formula]
  dsimp
  ring

/-- Full general-decoder small-noise specialization for an independent
isotropic complex disturbance. Gaussian noise is a special case. The
right side is tr(Q G⁻¹)/(2 K²), with Q's entries obtained from the actual
source-law slope moments. The prior need not have independent coordinates. -/
theorem leading_mse_inverseGram (e : Curve) {K : ℕ} (hK : 0 < K) (ψ : ℝ → ℝ)
    (hD : 0 < det e.A e.B e.C)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hc : ContinuousOn (readoutSlope ψ) (Icc (-1 : ℝ) 1))
    (hshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    {r : Ω → ℂ} {f : Ω → ℝ} (hr : Measurable r)
    (hexact : ∀ᵐ ω ∂μ, decode e K ψ (r ω) = f ω)
    (hmean : ∀ᵐ ω ∂μ, -1 < (e.inverseMoments K (complexCoordinates (r ω))).1 ∧
      (e.inverseMoments K (complexCoordinates (r ω))).1 < 1)
    {ν : Measure ℂ} [IsProbabilityMeasure ν]
    (hz2 : Integrable (fun z : ℂ => ‖z‖ ^ 2) ν)
    (hxx : (∫ z : ℂ, z.re ^ 2 ∂ν) = 1 / 2)
    (hyy : (∫ z : ℂ, z.im ^ 2 ∂ν) = 1 / 2)
    (hxy : (∫ z : ℂ, z.re * z.im ∂ν) = 0) :
    Tendsto (fun N : ℝ =>
      (∫ p : Ω × ℂ, (decode e K ψ (r p.1 + Real.sqrt N • p.2) - f p.1) ^ 2 ∂μ.prod ν) / N)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Frontier.risk (-(∫ ω, slopeField e K ψ (r ω) ∂μ))
        ((∫ ω, slopeField e K ψ (r ω) ^ 2 ∂μ) -
          (∫ ω, slopeField e K ψ (r ω) ∂μ) ^ 2)
        ⟨e.A, e.B, e.C⟩ / (2 * (K : ℝ) ^ 2))) := by
  have hJ : ∀ᵐ p : Ω × ℂ ∂μ.prod ν,
      HasFDerivAt (decode e K ψ) (gradient e K (slopeField e K ψ (r p.1))) (r p.1) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hmean] with p hp
    have he : slopeField e K ψ (r p.1) =
        readoutSlope ψ (e.inverseMoments K (complexCoordinates (r p.1))).1 := by
      unfold slopeField
      rw [Decoder.clip_fixed hp.1.le hp.2.le]
    rw [he]
    exact decode_hasFDerivAt e K ψ hd (r p.1) hp
  have hlim := SmallNoise.leading_mse_power_exact (decode_lipschitz e hK ψ hD hd hshape)
    (hr.comp measurable_fst) measurable_snd (hz2.comp_snd μ)
    (Measure.quasiMeasurePreserving_fst.ae hexact) hJ
  have hid := gradient_second_moment (μ := μ) e K ((slopeField_continuous e K ψ hc).measurable.comp hr)
    (slopeField_square_integrable e K ψ hc hr) hz2 hxx hyy hxy
  simp only [Function.comp_def] at hid hlim
  rw [hid] at hlim
  exact hlim

/-- Operational form on actual admissible source lists. Exactness and the
inverse-moment identity are proved, so the theorem's target is the desired
function itself, and its prior-gradient moments use the empirical mean. -/
theorem source_leading_mse_inverseGram (e : Curve) {K : ℕ} (hK : 0 < K) (φ ψ : ℝ → ℝ)
    (hD : 0 < det e.A e.B e.C)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hc : ContinuousOn (readoutSlope ψ) (Icc (-1 : ℝ) 1))
    (hshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (xs : Ω → List ℝ)
    (hvalid : ∀ᵐ ω ∂μ, ArbitraryEncoder.ValidInput K (xs ω))
    (hr : Measurable (fun ω => ArbitraryEncoder.asComplex
      (ArbitraryEncoder.received (encoder e φ) (xs ω))))
    (hmean : ∀ᵐ ω ∂μ, -1 < ArbitraryEncoder.firstMoment (xs ω) / (K : ℝ) ∧
      ArbitraryEncoder.firstMoment (xs ω) / (K : ℝ) < 1)
    {ν : Measure ℂ} [IsProbabilityMeasure ν]
    (hz2 : Integrable (fun z : ℂ => ‖z‖ ^ 2) ν)
    (hxx : (∫ z : ℂ, z.re ^ 2 ∂ν) = 1 / 2)
    (hyy : (∫ z : ℂ, z.im ^ 2 ∂ν) = 1 / 2)
    (hxy : (∫ z : ℂ, z.re * z.im ∂ν) = 0) :
    Tendsto (fun N : ℝ =>
      (∫ p : Ω × ℂ, (decode e K ψ
        (ArbitraryEncoder.asComplex (ArbitraryEncoder.received (encoder e φ) (xs p.1)) +
          Real.sqrt N • p.2) - GeneralCollision.target K φ ψ (xs p.1)) ^ 2 ∂μ.prod ν) / N)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Frontier.risk
        (-(∫ ω, readoutSlope ψ (ArbitraryEncoder.firstMoment (xs ω) / (K : ℝ)) ∂μ))
        ((∫ ω, readoutSlope ψ (ArbitraryEncoder.firstMoment (xs ω) / (K : ℝ)) ^ 2 ∂μ) -
          (∫ ω, readoutSlope ψ (ArbitraryEncoder.firstMoment (xs ω) / (K : ℝ)) ∂μ) ^ 2)
        ⟨e.A, e.B, e.C⟩ / (2 * (K : ℝ) ^ 2))) := by
  let r : Ω → ℂ := fun ω => ArbitraryEncoder.asComplex
    (ArbitraryEncoder.received (encoder e φ) (xs ω))
  have hinv : ∀ᵐ ω ∂μ, e.inverseMoments K (complexCoordinates (r ω)) = moments K φ (xs ω) := by
    filter_upwards [hvalid] with ω hω
    change e.inverseMoments K (ArbitraryEncoder.received (encoder e φ) (xs ω)) = _
    rw [← forward_moments e hK φ (xs ω) hω, e.inverse_forwardMoments hK hD]
  have hm : ∀ᵐ ω ∂μ, -1 < (e.inverseMoments K (complexCoordinates (r ω))).1 ∧
      (e.inverseMoments K (complexCoordinates (r ω))).1 < 1 := by
    filter_upwards [hinv, hmean] with ω hi hm
    rwa [hi]
  have hex : ∀ᵐ ω ∂μ, decode e K ψ (r ω) = GeneralCollision.target K φ ψ (xs ω) :=
    hvalid.mono fun ω hω => decode_exact e hK φ ψ hD (xs ω) hω
  have hlim := leading_mse_inverseGram e hK ψ hD hd hc hshape hr hex hm hz2 hxx hyy hxy
  have hs : (fun ω => slopeField e K ψ (r ω)) =ᵐ[μ]
      (fun ω => readoutSlope ψ (ArbitraryEncoder.firstMoment (xs ω) / (K : ℝ))) := by
    filter_upwards [hinv, hmean] with ω hi hm
    unfold slopeField
    rw [hi]
    change readoutSlope ψ (Decoder.clip (-1) 1 (ArbitraryEncoder.firstMoment (xs ω) / (K : ℝ))) = _
    rw [Decoder.clip_fixed hm.1.le hm.2.le]
  have hs2 := hs.mono fun ω hω => congrArg (fun t : ℝ => t ^ 2) hω
  rw [integral_congr_ae hs, integral_congr_ae hs2] at hlim
  exact hlim

theorem output_clip_hasFDerivAt {D : ℂ → ℝ} {J : ℂ →L[ℝ] ℝ}
    {a b : ℝ} {y : ℂ} (hD : HasFDerivAt D J y) (hy : a < D y ∧ D y < b) :
    HasFDerivAt (fun z => Decoder.clip a b (D z)) J y := by
  apply hD.congr_of_eventuallyEq
  have he := hD.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hy)
  filter_upwards [he] with z hz
  exact Decoder.clip_fixed hz.1.le hz.2.le

/-- Optional output clipping has the same full inverse-Gram coefficient
when the noiseless desired function lies inside its clipping interval
almost surely. No separation from the clipping endpoints is required. -/
theorem clipped_leading_mse_inverseGram (e : Curve) {K : ℕ} (hK : 0 < K) (ψ : ℝ → ℝ)
    (hD : 0 < det e.A e.B e.C)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hc : ContinuousOn (readoutSlope ψ) (Icc (-1 : ℝ) 1))
    (hshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    {r : Ω → ℂ} {f : Ω → ℝ} (hr : Measurable r)
    (hexact : ∀ᵐ ω ∂μ, decode e K ψ (r ω) = f ω)
    (hmean : ∀ᵐ ω ∂μ, -1 < (e.inverseMoments K (complexCoordinates (r ω))).1 ∧
      (e.inverseMoments K (complexCoordinates (r ω))).1 < 1)
    (a b : ℝ) (hclip : ∀ᵐ ω ∂μ, a < f ω ∧ f ω < b)
    {ν : Measure ℂ} [IsProbabilityMeasure ν]
    (hz2 : Integrable (fun z : ℂ => ‖z‖ ^ 2) ν)
    (hxx : (∫ z : ℂ, z.re ^ 2 ∂ν) = 1 / 2)
    (hyy : (∫ z : ℂ, z.im ^ 2 ∂ν) = 1 / 2)
    (hxy : (∫ z : ℂ, z.re * z.im ∂ν) = 0) :
    Tendsto (fun N : ℝ =>
      (∫ p : Ω × ℂ, (Decoder.clip a b
        (decode e K ψ (r p.1 + Real.sqrt N • p.2)) - f p.1) ^ 2 ∂μ.prod ν) / N)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Frontier.risk (-(∫ ω, slopeField e K ψ (r ω) ∂μ))
        ((∫ ω, slopeField e K ψ (r ω) ^ 2 ∂μ) -
          (∫ ω, slopeField e K ψ (r ω) ∂μ) ^ 2)
        ⟨e.A, e.B, e.C⟩ / (2 * (K : ℝ) ^ 2))) := by
  have hlip : LipschitzWith (amplification e K ψ)
      (fun y => Decoder.clip a b (decode e K ψ y)) := by
    simpa only [one_mul, Function.comp_def] using
      (Decoder.clip_lipschitz a b).comp (decode_lipschitz e hK ψ hD hd hshape)
  have hex : ∀ᵐ ω ∂μ, Decoder.clip a b (decode e K ψ (r ω)) = f ω := by
    filter_upwards [hexact, hclip] with ω he hc
    rw [he, Decoder.clip_fixed hc.1.le hc.2.le]
  have hJ : ∀ᵐ p : Ω × ℂ ∂μ.prod ν,
      HasFDerivAt (fun y => Decoder.clip a b (decode e K ψ y))
        (gradient e K (slopeField e K ψ (r p.1))) (r p.1) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hmean,
      Measure.quasiMeasurePreserving_fst.ae hexact,
      Measure.quasiMeasurePreserving_fst.ae hclip] with p hp he hc
    have hs : slopeField e K ψ (r p.1) =
        readoutSlope ψ (e.inverseMoments K (complexCoordinates (r p.1))).1 := by
      unfold slopeField
      rw [Decoder.clip_fixed hp.1.le hp.2.le]
    rw [hs]
    apply output_clip_hasFDerivAt (decode_hasFDerivAt e K ψ hd (r p.1) hp)
    rwa [he]
  have hlim := SmallNoise.leading_mse_power_exact hlip
    (hr.comp measurable_fst) measurable_snd (hz2.comp_snd μ)
    (Measure.quasiMeasurePreserving_fst.ae hex) hJ
  have hid := gradient_second_moment (μ := μ) e K ((slopeField_continuous e K ψ hc).measurable.comp hr)
    (slopeField_square_integrable e K ψ hc hr) hz2 hxx hyy hxy
  simp only [Function.comp_def] at hid hlim
  rw [hid] at hlim
  exact hlim

end IndependentNoise

end Analog.GeneralSmallNoise
