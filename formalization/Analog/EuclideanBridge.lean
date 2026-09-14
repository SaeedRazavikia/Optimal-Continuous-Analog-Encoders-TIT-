import Analog.Amplification
import Analog.Implementation
import Mathlib.Analysis.Complex.Norm

/-!
# The Euclidean received plane

Mathlib's default metric on a product of real lines is the maximum metric.
The manuscript instead uses Euclidean squared distance. Embedding the
coordinate pair into the complex plane proves the exact cost identity and
connects the list-based variance score with sharp additive-noise decoding.
-/

noncomputable section

namespace Analog.ArbitraryEncoder

open scoped NNReal

def asComplex (p : ℝ × ℝ) : ℂ := ⟨p.1, p.2⟩

/-- The complex metric gives precisely the Euclidean squared distance used
in the variance score, rather than the product maximum metric. -/
theorem asComplex_squared_distance (p q : ℝ × ℝ) :
    dist (asComplex p) (asComplex q) ^ 2 = squaredDistance p q := by
  rw [dist_eq_norm, Complex.sq_norm]
  simp [asComplex, squaredDistance, Complex.normSq_apply, pow_two]

/-- Complex embedding commutes with the actual multiple-access sum. -/
theorem asComplex_received (E : ℝ → ℝ × ℝ) (xs : List ℝ) :
    asComplex (received E xs) = (xs.map (fun s => asComplex (E s))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [received, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih]
    rfl

abbrev AdmissibleInput (K : ℕ) := {xs : List ℝ // ValidInput K xs}

def complexReceived (K : ℕ) (E : ℝ → ℝ × ℝ) (x : AdmissibleInput K) : ℂ :=
  asComplex (received E x.val)

def varianceTarget (K : ℕ) (x : AdmissibleInput K) : ℝ := variance K x.val

/-- Restricting the input type and using the complex Euclidean metric leaves
the defining quotient set, and therefore the operational infimum, unchanged. -/
theorem metricScore_eq_varianceScore (K : ℕ) (E : ℝ → ℝ × ℝ) :
    Decoder.metricScore (complexReceived K E) (varianceTarget K) = varianceScore K E := by
  unfold Decoder.metricScore varianceScore Operational.score
  congr 1
  ext q
  constructor
  · rintro ⟨x, _, y, _, hne, hq⟩
    refine ⟨x.val, x.property, y.val, y.property, hne, ?_⟩
    simpa only [complexReceived, varianceTarget, asComplex_squared_distance] using hq
  · rintro ⟨xs, hxs, ys, hys, hne, hq⟩
    refine ⟨⟨xs, hxs⟩, Set.mem_univ _, ⟨ys, hys⟩, Set.mem_univ _, hne, ?_⟩
    simpa only [complexReceived, varianceTarget, asComplex_squared_distance] using hq

theorem varianceTarget_nonconstant {K : ℕ} (hK : 2 ≤ K) :
    Operational.NonconstantOn Set.univ (varianceTarget K) := by
  obtain ⟨xs, hxs, ys, hys, hne⟩ := variance_nonconstant hK
  exact ⟨⟨xs, hxs⟩, Set.mem_univ _, ⟨ys, hys⟩, Set.mem_univ _, hne⟩

/-- Reciprocal-root amplification, interpreted as the attained finite constant
only when the operational variance score is positive. At zero score, the
separate impossibility theorem applies; total real division here returns zero. -/
def varianceAmplification (K : ℕ) (E : ℝ → ℝ × ℝ) : ℝ≥0 :=
  ⟨1 / Real.sqrt (varianceScore K E),
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)⟩

theorem sharpConstant_eq_varianceAmplification (K : ℕ) (E : ℝ → ℝ × ℝ) :
    Decoder.sharpConstant (complexReceived K E) (varianceTarget K) =
      varianceAmplification K E := by
  apply Subtype.ext
  simp [Decoder.sharpConstant, varianceAmplification, metricScore_eq_varianceScore]

/-- Any encoder with positive operational variance score admits a global
Lipschitz decoder with sharp reciprocal-root amplification on the complex
additive channel. Every valid input and every complex disturbance are covered. -/
theorem sharp_variance_decoder {K : ℕ} (hK : 2 ≤ K) (E : ℝ → ℝ × ℝ)
    (hscore : 0 < varianceScore K E) :
    ∃ D : ℂ → ℝ, LipschitzWith (varianceAmplification K E) D ∧ Continuous D ∧
      (∀ xs, ValidInput K xs → ∀ N : ℂ,
        |D (asComplex (received E xs) + N) - variance K xs| ≤
          (varianceAmplification K E : ℝ) * ‖N‖) ∧
      ∀ (L : ℝ≥0) (D' : ℂ → ℝ),
        (∀ xs, ValidInput K xs → ∀ N : ℂ,
          |D' (asComplex (received E xs) + N) - variance K xs| ≤ (L : ℝ) * ‖N‖) →
        varianceAmplification K E ≤ L := by
  have hs : 0 < Decoder.metricScore (complexReceived K E) (varianceTarget K) := by
    simpa only [metricScore_eq_varianceScore] using hscore
  obtain ⟨D, hD, hc, _, hu, hmin⟩ := Decoder.sharp_uniform_decoder
    (complexReceived K E) (varianceTarget K) (varianceTarget_nonconstant hK) hs
  rw [sharpConstant_eq_varianceAmplification] at hD hu hmin
  refine ⟨D, hD, hc, ?_, ?_⟩
  · intro xs hxs N
    exact (Decoder.uniform_iff_additive_noise _ _ _ _).mp hu ⟨xs, hxs⟩ N
  · intro L D' hnoise
    apply hmin L D'
    apply (Decoder.uniform_iff_additive_noise _ _ _ _).mpr
    intro x N
    exact hnoise x.val x.property N

/-- A zero operational variance score admits no finite all-disturbance
guarantee, regardless of decoder regularity. -/
theorem zero_varianceScore_no_finite_decoder {K : ℕ} (hK : 2 ≤ K)
    (E : ℝ → ℝ × ℝ) (hzero : varianceScore K E = 0) :
    ¬ ∃ (L : ℝ≥0) (D : ℂ → ℝ),
      ∀ xs, ValidInput K xs → ∀ N : ℂ,
        |D (asComplex (received E xs) + N) - variance K xs| ≤ (L : ℝ) * ‖N‖ := by
  have hz : Decoder.metricScore (complexReceived K E) (varianceTarget K) = 0 := by
    simpa only [metricScore_eq_varianceScore] using hzero
  intro ⟨L, D, hnoise⟩
  apply Decoder.zero_score_no_finite_uniform_decoder
    (complexReceived K E) (varianceTarget K) (varianceTarget_nonconstant hK) hz
  refine ⟨L, D, (Decoder.uniform_iff_additive_noise _ _ _ _).mpr ?_⟩
  intro x N
  exact hnoise x.val x.property N

end Analog.ArbitraryEncoder
