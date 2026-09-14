import Analog.StripProjection
import Analog.EuclideanBridge

/-!
# The explicit variance decoder on the complex channel

We invert the actual affine received map, apply the correlated strip
projection, and evaluate the variance readout. The decoder is exact on every
valid source list and attains the smallest uniform additive-noise constant.
-/

noncomputable section

namespace Analog

open ArbitraryEncoder
open scoped NNReal

def Curve.basisDet (e : Curve) : ℝ := e.ux * e.vy - e.uy * e.vx

lemma Curve.basisDet_sq (e : Curve) : e.basisDet ^ 2 = e.A * e.B - e.C ^ 2 := by
  dsimp [Curve.basisDet, Curve.A, Curve.B, Curve.C]
  ring

lemma Curve.basisDet_ne_zero (e : Curve) (hdet : 0 < e.A * e.B - e.C ^ 2) :
    e.basisDet ≠ 0 := by
  have h := e.basisDet_sq
  intro hz
  rw [hz, zero_pow (by decide : 2 ≠ 0)] at h
  linarith

lemma Curve.B_positive (e : Curve) (hdet : 0 < e.A * e.B - e.C ^ 2) : 0 < e.B := by
  have hA : 0 ≤ e.A := by dsimp [Curve.A]; positivity
  nlinarith [sq_nonneg e.C]

def Curve.forwardMoments (e : Curve) (K : ℕ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((K : ℝ) * e.cx + K * (e.ux * p.1 + e.vx * p.2),
    (K : ℝ) * e.cy + K * (e.uy * p.1 + e.vy * p.2))

/-- The actual inverse linear transformation of the received plane. -/
def Curve.inverseMoments (e : Curve) (K : ℕ) (y : ℝ × ℝ) : ℝ × ℝ :=
  ((e.vy * (y.1 - K * e.cx) - e.vx * (y.2 - K * e.cy)) / ((K : ℝ) * e.basisDet),
    (-e.uy * (y.1 - K * e.cx) + e.ux * (y.2 - K * e.cy)) / ((K : ℝ) * e.basisDet))

lemma Curve.inverse_forwardMoments (e : Curve) {K : ℕ} (hK : 0 < K)
    (hdet : 0 < e.A * e.B - e.C ^ 2) (p : ℝ × ℝ) :
    e.inverseMoments K (e.forwardMoments K p) = p := by
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hd := e.basisDet_ne_zero hdet
  apply Prod.ext <;> dsimp [Curve.inverseMoments, Curve.forwardMoments]
  · apply (div_eq_iff (mul_ne_zero hk hd)).mpr
    dsimp [Curve.basisDet]
    ring
  · apply (div_eq_iff (mul_ne_zero hk hd)).mpr
    dsimp [Curve.basisDet]
    ring

lemma Curve.forward_inverseMoments (e : Curve) {K : ℕ} (hK : 0 < K)
    (hdet : 0 < e.A * e.B - e.C ^ 2) (y : ℝ × ℝ) :
    e.forwardMoments K (e.inverseMoments K y) = y := by
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hd := e.basisDet_ne_zero hdet
  apply Prod.ext <;> dsimp [Curve.inverseMoments, Curve.forwardMoments]
  · field_simp
    dsimp [Curve.basisDet]
    ring
  · field_simp
    dsimp [Curve.basisDet]
    ring

lemma Curve.forwardMoments_distance (e : Curve) (K : ℕ) (p q : ℝ × ℝ) :
    squaredDistance (e.forwardMoments K p) (e.forwardMoments K q) =
      (K : ℝ) ^ 2 * Strip.gramDistance e.A e.B e.C p q := by
  dsimp [Curve.forwardMoments, squaredDistance, Strip.gramDistance, Strip.energy,
    Curve.A, Curve.B, Curve.C]
  ring

lemma Curve.inverseMoments_distance (e : Curve) {K : ℕ} (hK : 0 < K)
    (hdet : 0 < e.A * e.B - e.C ^ 2) (p q : ℝ × ℝ) :
    Strip.gramDistance e.A e.B e.C (e.inverseMoments K p) (e.inverseMoments K q) =
      squaredDistance p q / (K : ℝ) ^ 2 := by
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  apply (eq_div_iff (pow_ne_zero 2 hk)).mpr
  have h := e.forwardMoments_distance K (e.inverseMoments K p) (e.inverseMoments K q)
  rw [e.forward_inverseMoments hK hdet, e.forward_inverseMoments hK hdet] at h
  simpa only [mul_comm] using h.symm

def empiricalMoments (K : ℕ) (xs : List ℝ) : ℝ × ℝ :=
  (firstMoment xs / (K : ℝ), secondMoment xs / (K : ℝ))

lemma empiricalMoments_in_strip {K : ℕ} (hK : 0 < K) (xs : List ℝ)
    (hx : ValidInput K xs) : Strip.InStrip (empiricalMoments K xs) := by
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hb := firstMoment_bounds xs hx.2
  rw [hx.1] at hb
  constructor
  · apply (le_div_iff₀ hk).mpr
    simpa using hb.1
  · apply (div_le_iff₀ hk).mpr
    simpa using hb.2

lemma Curve.forward_empiricalMoments (e : Curve) {K : ℕ} (hK : 0 < K)
    (xs : List ℝ) (hx : ValidInput K xs) :
    e.forwardMoments K (empiricalMoments K xs) = received e.encoder xs := by
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [e.received_encoder, hx.1]
  apply Prod.ext <;> dsimp [Curve.forwardMoments, empiricalMoments] <;> field_simp <;> ring

def complexCoordinates (y : ℂ) : ℝ × ℝ := (y.re, y.im)

lemma complexCoordinates_distance (y z : ℂ) :
    squaredDistance (complexCoordinates y) (complexCoordinates z) = dist y z ^ 2 := by
  rw [← asComplex_squared_distance]
  rfl

/-- Explicit inverse, correlated clipping, then variance readout. -/
def Curve.explicitVarianceDecoder (e : Curve) (K : ℕ) (y : ℂ) : ℝ :=
  Strip.varianceReadout (Strip.project e.B e.C (e.inverseMoments K (complexCoordinates y)))

lemma Curve.score_positive (e : Curve) (hdet : 0 < e.A * e.B - e.C ^ 2) : 0 < e.score :=
  div_pos hdet (e.denominator_pos hdet)

lemma Curve.actual_varianceScore_positive (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (hdet : 0 < e.A * e.B - e.C ^ 2) : 0 < varianceScore K e.encoder := by
  rw [e.variance_operational_score hK]
  have hk : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  exact mul_pos (sq_pos_of_pos hk) (e.score_positive hdet)

lemma Curve.decoder_factor_identity (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (hdet : 0 < e.A * e.B - e.C ^ 2) :
    ((e.A + 4 * e.B + 4 * |e.C|) / (e.A * e.B - e.C ^ 2)) / (K : ℝ) ^ 2 =
      1 / varianceScore K e.encoder := by
  rw [e.variance_operational_score hK]
  dsimp [Curve.score]
  field_simp

/-- Global squared Lipschitz bound for the actual implementable decoder. -/
theorem Curve.explicitVarianceDecoder_squared_bound (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (hdet : 0 < e.A * e.B - e.C ^ 2) (y z : ℂ) :
    (e.explicitVarianceDecoder K y - e.explicitVarianceDecoder K z) ^ 2 ≤
      (1 / varianceScore K e.encoder) * dist y z ^ 2 := by
  have h := Strip.projected_variance_squared_bound (e.B_positive hdet) hdet
    (e.inverseMoments K (complexCoordinates y)) (e.inverseMoments K (complexCoordinates z))
  rw [e.inverseMoments_distance (by omega) hdet, complexCoordinates_distance] at h
  change (e.explicitVarianceDecoder K y - e.explicitVarianceDecoder K z) ^ 2 ≤ _ at h
  have hid := e.decoder_factor_identity hK hdet
  have heq : ((e.A + 4 * e.B + 4 * |e.C|) / (e.A * e.B - e.C ^ 2)) *
      (dist y z ^ 2 / (K : ℝ) ^ 2) = (1 / varianceScore K e.encoder) * dist y z ^ 2 := by
    rw [← hid]
    ring
  rwa [heq] at h

theorem Curve.explicitVarianceDecoder_lipschitz (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (hdet : 0 < e.A * e.B - e.C ^ 2) :
    LipschitzWith (varianceAmplification K e.encoder) (e.explicitVarianceDecoder K) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [Real.dist_eq]
  have hs := e.actual_varianceScore_positive hK hdet
  have h := e.explicitVarianceDecoder_squared_bound hK hdet y z
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (varianceAmplification K e.encoder).coe_nonneg
    dist_nonneg)).mp
  rw [sq_abs, mul_pow]
  change _ ≤ (1 / Real.sqrt (varianceScore K e.encoder)) ^ 2 * dist y z ^ 2
  simpa only [div_pow, one_pow, Real.sq_sqrt hs.le] using h

theorem Curve.explicitVarianceDecoder_exact (e : Curve) {K : ℕ} (hK : 0 < K)
    (hdet : 0 < e.A * e.B - e.C ^ 2) (xs : List ℝ) (hx : ValidInput K xs) :
    e.explicitVarianceDecoder K (asComplex (received e.encoder xs)) = variance K xs := by
  change Strip.varianceReadout (Strip.project e.B e.C
    (e.inverseMoments K (received e.encoder xs))) = _
  rw [← e.forward_empiricalMoments hK xs hx, e.inverse_forwardMoments hK hdet,
    Strip.project_fixes_strip e.B e.C (empiricalMoments_in_strip hK xs hx)]
  rfl

/-- The specified decoder attains the all-input, all-complex-disturbance
guarantee at the exact operational reciprocal-root constant. -/
theorem Curve.explicitVarianceDecoder_uniform (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (hdet : 0 < e.A * e.B - e.C ^ 2) :
    ∀ xs, ValidInput K xs → ∀ N : ℂ,
      |e.explicitVarianceDecoder K (asComplex (received e.encoder xs) + N) - variance K xs| ≤
        (varianceAmplification K e.encoder : ℝ) * ‖N‖ := by
  have hu := Decoder.lipschitz_exact_uniform
    (r := complexReceived K e.encoder) (f := varianceTarget K)
    (e.explicitVarianceDecoder_lipschitz hK hdet)
    (fun x => e.explicitVarianceDecoder_exact (by omega) hdet x.val x.property)
  intro xs hx N
  exact (Decoder.uniform_iff_additive_noise _ _ _ _).mp hu ⟨xs, hx⟩ N

/-- The explicit decoder attains the smallest possible finite uniform
constant among every decoder, including discontinuous alternatives. -/
theorem Curve.explicitVarianceDecoder_optimal (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (hdet : 0 < e.A * e.B - e.C ^ 2) :
    (∀ xs, ValidInput K xs → ∀ N : ℂ,
      |e.explicitVarianceDecoder K (asComplex (received e.encoder xs) + N) - variance K xs| ≤
        (varianceAmplification K e.encoder : ℝ) * ‖N‖) ∧
      ∀ (L : ℝ≥0) (D : ℂ → ℝ),
        (∀ xs, ValidInput K xs → ∀ N : ℂ,
          |D (asComplex (received e.encoder xs) + N) - variance K xs| ≤ (L : ℝ) * ‖N‖) →
        varianceAmplification K e.encoder ≤ L := by
  obtain ⟨_, _, _, _, hmin⟩ := sharp_variance_decoder hK e.encoder
    (e.actual_varianceScore_positive hK hdet)
  exact ⟨e.explicitVarianceDecoder_uniform hK hdet, hmin⟩

end Analog
