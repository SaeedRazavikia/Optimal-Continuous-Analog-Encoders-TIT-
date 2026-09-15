import Analog.ExplicitVarianceDecoder
import Analog.GeneralScore

/-!
# The general moment-minus-mean strip decoder

This file proves the endpoint-dual bound for the actual corrected strip
decoder, exactness on all admissible source lists, and optimal amplification
under the hypotheses of the operational score theorem. No decoder estimate
is assumed.
-/

noncomputable section

namespace Analog.GeneralDecoder

open Set ArbitraryEncoder GeneralCollision GeneralScore GramSynthesis
open scoped NNReal

def postprocess (ψ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := p.2 - ψ p.1

def moments (K : ℕ) (φ : ℝ → ℝ) (xs : List ℝ) : ℝ × ℝ :=
  (firstMoment xs / (K : ℝ), featureMoment φ xs / (K : ℝ))

def decode (e : Curve) (K : ℕ) (ψ : ℝ → ℝ) (y : ℂ) : ℝ :=
  postprocess ψ (Strip.project e.B e.C (e.inverseMoments K (complexCoordinates y)))

def amplification (e : Curve) (K : ℕ) (ψ : ℝ → ℝ) : ℝ≥0 :=
  ⟨Real.sqrt (endpointDual e ψ / (K : ℝ) ^ 2), Real.sqrt_nonneg _⟩

theorem postprocess_squared_bound (e : Curve) (ψ : ℝ → ℝ)
    (hD : 0 < det e.A e.B e.C)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (p q : ℝ × ℝ) (hp : Strip.InStrip p) (hq : Strip.InStrip q) :
    (postprocess ψ p - postprocess ψ q) ^ 2 ≤
      endpointDual e ψ * Strip.gramDistance e.A e.B e.C p q := by
  obtain ⟨a, ha, hb, heq⟩ := secant_slope_between_endpoints ψ hd hshape p.1 q.1 hp hq
  have hc := dual_cauchy e.A e.B e.C (-a) 1 (p.1 - q.1) (p.2 - q.2) hD
  have hdual := dual_endpoint_bound e hD (readoutSlope ψ (-1)) (readoutSlope ψ 1) a ⟨ha, hb⟩
  have hcost := form2_nonneg e.A e.B e.C (coefficient_A_pos e hD) hD
    (p.1 - q.1) (p.2 - q.2)
  have hm := mul_le_mul_of_nonneg_right hdual hcost
  have he : postprocess ψ p - postprocess ψ q = (p.2 - q.2) - a * (p.1 - q.1) := by
    dsimp [postprocess]
    linarith only [heq]
  rw [he]
  change _ ≤ endpointDual e ψ * form2 e.A e.B e.C (p.1 - q.1) (p.2 - q.2)
  dsimp [endpointDual]
  nlinarith only [hc, hm]

theorem projected_squared_bound (e : Curve) (ψ : ℝ → ℝ)
    (hD : 0 < det e.A e.B e.C)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (p q : ℝ × ℝ) :
    (postprocess ψ (Strip.project e.B e.C p) - postprocess ψ (Strip.project e.B e.C q)) ^ 2 ≤
      endpointDual e ψ * Strip.gramDistance e.A e.B e.C p q := by
  exact (postprocess_squared_bound e ψ hD hd hshape _ _
    (Strip.project_in_strip _ _ _) (Strip.project_in_strip _ _ _)).trans
      (mul_le_mul_of_nonneg_left
        (Strip.project_squared_nonexpansive (e.B_positive hD) hD p q)
        (endpointDual_pos e ψ hD).le)

theorem decode_squared_bound (e : Curve) {K : ℕ} (hK : 0 < K) (ψ : ℝ → ℝ)
    (hD : 0 < det e.A e.B e.C)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (y z : ℂ) :
    (decode e K ψ y - decode e K ψ z) ^ 2 ≤
      (endpointDual e ψ / (K : ℝ) ^ 2) * dist y z ^ 2 := by
  have h := projected_squared_bound e ψ hD hd hshape
    (e.inverseMoments K (complexCoordinates y)) (e.inverseMoments K (complexCoordinates z))
  rw [e.inverseMoments_distance hK hD, complexCoordinates_distance] at h
  change (decode e K ψ y - decode e K ψ z) ^ 2 ≤ _ at h
  convert h using 1
  ring

theorem decode_lipschitz (e : Curve) {K : ℕ} (hK : 0 < K) (ψ : ℝ → ℝ)
    (hD : 0 < det e.A e.B e.C)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ) :
    LipschitzWith (amplification e K ψ) (decode e K ψ) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [Real.dist_eq]
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (amplification e K ψ).coe_nonneg
    dist_nonneg)).mp
  rw [sq_abs, mul_pow]
  change _ ≤ Real.sqrt (endpointDual e ψ / (K : ℝ) ^ 2) ^ 2 * dist y z ^ 2
  rw [Real.sq_sqrt (div_nonneg (endpointDual_pos e ψ hD).le (sq_nonneg _))]
  exact decode_squared_bound e hK ψ hD hd hshape y z

theorem forward_moments (e : Curve) {K : ℕ} (hK : 0 < K) (φ : ℝ → ℝ)
    (xs : List ℝ) (hx : ValidInput K xs) :
    e.forwardMoments K (moments K φ xs) = received (encoder e φ) xs := by
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [received_encoder, hx.1]
  apply Prod.ext <;> dsimp [Curve.forwardMoments, moments] <;> field_simp <;> ring

theorem decode_exact (e : Curve) {K : ℕ} (hK : 0 < K) (φ ψ : ℝ → ℝ)
    (hD : 0 < det e.A e.B e.C) (xs : List ℝ) (hx : ValidInput K xs) :
    decode e K ψ (asComplex (received (encoder e φ) xs)) = target K φ ψ xs := by
  change postprocess ψ (Strip.project e.B e.C
    (e.inverseMoments K (received (encoder e φ) xs))) = _
  have hm : Strip.InStrip (moments K φ xs) := mean_in_source hK xs hx
  rw [← forward_moments e hK φ xs hx, e.inverse_forwardMoments hK hD,
    Strip.project_fixes_strip e.B e.C hm]
  rfl

theorem decode_uniform (e : Curve) {K : ℕ} (hK : 0 < K) (φ ψ : ℝ → ℝ)
    (hD : 0 < det e.A e.B e.C)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ) :
    ∀ xs, ValidInput K xs → ∀ N : ℂ,
      |decode e K ψ (asComplex (received (encoder e φ) xs) + N) - target K φ ψ xs| ≤
        (amplification e K ψ : ℝ) * ‖N‖ := by
  have hu := Decoder.lipschitz_exact_uniform
    (r := complexReceived K (encoder e φ)) (f := fun x : AdmissibleInput K => target K φ ψ x.val)
    (decode_lipschitz e hK ψ hD hd hshape)
    (fun x => decode_exact e hK φ ψ hD x.val x.property)
  intro xs hx N
  exact (Decoder.uniform_iff_additive_noise _ _ _ _).mp hu ⟨xs, hx⟩ N

theorem amplification_reciprocal_score (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (φ ψ : ℝ → ℝ) (hD : 0 < det e.A e.B e.C)
    (hφ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨ StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ)
    (hdφ : ∀ z ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ φ z)
    (hψ : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (hdψ : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hcψ : ContinuousOn (readoutSlope ψ) (Icc (-1 : ℝ) 1)) :
    (amplification e K ψ : ℝ) = 1 / Real.sqrt (score K φ ψ e) := by
  rw [general_operational_score e hK φ ψ hD hφ hdφ hψ hdψ hcψ]
  change Real.sqrt (endpointDual e ψ / (K : ℝ) ^ 2) = _
  rw [Real.sqrt_div (endpointDual_pos e ψ hD).le,
    Real.sqrt_div (sq_nonneg (K : ℝ))]
  simp only [one_div_div]

theorem metricScore_eq (e : Curve) (K : ℕ) (φ ψ : ℝ → ℝ) :
    Decoder.metricScore (complexReceived K (encoder e φ))
      (fun x : AdmissibleInput K => target K φ ψ x.val) = score K φ ψ e := by
  unfold Decoder.metricScore score Operational.score
  congr 1
  ext q
  constructor
  · rintro ⟨x, _, y, _, hne, hq⟩
    refine ⟨x.val, x.property, y.val, y.property, hne, ?_⟩
    simpa only [complexReceived, asComplex_squared_distance] using hq
  · rintro ⟨xs, hxs, ys, hys, hne, hq⟩
    refine ⟨⟨xs, hxs⟩, Set.mem_univ _, ⟨ys, hys⟩, Set.mem_univ _, hne, ?_⟩
    simpa only [complexReceived, asComplex_squared_distance] using hq

/-- No alternative decoder, even a discontinuous one, has a smaller
all-input and all-disturbance amplification constant. -/
theorem decode_optimal (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (φ ψ : ℝ → ℝ) (hD : 0 < det e.A e.B e.C)
    (hφ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨ StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ)
    (hdφ : ∀ z ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ φ z)
    (hψ : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (hdψ : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hcψ : ContinuousOn (readoutSlope ψ) (Icc (-1 : ℝ) 1)) :
    (∀ xs, ValidInput K xs → ∀ N : ℂ,
      |decode e K ψ (asComplex (received (encoder e φ) xs) + N) - target K φ ψ xs| ≤
        (amplification e K ψ : ℝ) * ‖N‖) ∧
    ∀ (L : ℝ≥0) (D : ℂ → ℝ),
      (∀ xs, ValidInput K xs → ∀ N : ℂ,
        |D (asComplex (received (encoder e φ) xs) + N) - target K φ ψ xs| ≤ (L : ℝ) * ‖N‖) →
      amplification e K ψ ≤ L := by
  refine ⟨decode_uniform e (by omega) φ ψ hD hdψ hψ, ?_⟩
  intro L D hu
  have hn : Operational.NonconstantOn Set.univ (fun x : AdmissibleInput K => target K φ ψ x.val) := by
    obtain ⟨xs, hxs, ys, hys, hne⟩ := target_nonconstant_of_strict_feature hK φ ψ hφ
    exact ⟨⟨xs, hxs⟩, Set.mem_univ _, ⟨ys, hys⟩, Set.mem_univ _, hne⟩
  have hs : 0 < Decoder.metricScore (complexReceived K (encoder e φ))
      (fun x : AdmissibleInput K => target K φ ψ x.val) := by
    rw [metricScore_eq, general_operational_score e hK φ ψ hD hφ hdφ hψ hdψ hcψ]
    have hk : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
    exact div_pos (sq_pos_of_pos hk) (endpointDual_pos e ψ hD)
  have hub : Decoder.UniformBound (complexReceived K (encoder e φ))
      (fun x : AdmissibleInput K => target K φ ψ x.val) L D := by
    apply (Decoder.uniform_iff_additive_noise _ _ _ _).mpr
    intro x N
    exact hu x.val x.property N
  have hl := Decoder.sharpConstant_le_uniform hn hs hub
  change (1 / Real.sqrt (Decoder.metricScore (complexReceived K (encoder e φ))
      (fun x : AdmissibleInput K => target K φ ψ x.val)) : ℝ) ≤ (L : ℝ) at hl
  rw [metricScore_eq, ← amplification_reciprocal_score e hK φ ψ hD hφ hdφ hψ hdψ hcψ] at hl
  exact hl

end Analog.GeneralDecoder
