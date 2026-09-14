import Analog.PowerScaling
import Analog.VarianceScore

/-! Operational variance optimality over all planar quadratic encoders,
for every positive peak power and every terminal count K >= 2. The score in
the conclusion is the actual all-pair infimum, not a stipulated Gram objective.
The extension of the competitor class to arbitrary continuous encoders still
requires the unformalized continuous rigidity theorem.
-/

noncomputable section
namespace Analog
open ArbitraryEncoder

lemma Curve.variance_gramScore (e : Curve) :
    GeneralQuadratic.gramScore e 2 = e.score := by
  unfold GeneralQuadratic.gramScore Curve.score
  norm_num

theorem Curve.scale_varianceScore (e : Curve) (a : ℝ) :
    (e.scale a).score = a ^ 2 * e.score := by
  simpa only [Curve.variance_gramScore] using e.scale_gramScore a 2

/-- General-power converse for the variance Gram expression. -/
theorem quadratic_variance_score_le_all_power (e : Curve) {P : ℝ}
    (hP : 0 < P) (he : e.PeakFeasibleAt P) :
    e.score ≤ P * (4 / (9 + 6 * Real.sqrt 3)) := by
  have hn := quadratic_score_le (e.scale (1 / Real.sqrt P)) (e.normalize_peak hP he)
  rw [Curve.scale_varianceScore, div_pow, one_pow, Real.sq_sqrt (le_of_lt hP)] at hn
  have hh := mul_le_mul_of_nonneg_left hn (le_of_lt hP)
  have hi : P * ((1 / P) * e.score) = e.score := by field_simp
  rwa [hi] at hh

/-- A complete operational optimization theorem for all quadratic competitors.
Feasibility ranges over every real input in the closed interval; the score
ranges over every admissible K-terminal pair with unequal variances. -/
theorem quadratic_variance_operational_optimal {K : ℕ} (hK : 2 ≤ K)
    (P : ℝ) (hP : 0 < P) :
    let e := optimalCurve.scale (Real.sqrt P)
    e.PeakFeasibleAt P ∧
    varianceScore K e.encoder = 4 * (K : ℝ) ^ 2 * P / (9 + 6 * Real.sqrt 3) ∧
    ∀ other : Curve, other.PeakFeasibleAt P →
      varianceScore K other.encoder ≤ varianceScore K e.encoder := by
  dsimp only
  have hs2 := Real.sq_sqrt (le_of_lt hP)
  have hpeak := optimalCurve.scale_peak (Real.sqrt P) 1 optimal_peak
  simp only [hs2, mul_one] at hpeak
  have hscore : (optimalCurve.scale (Real.sqrt P)).score =
      P * (4 / (9 + 6 * Real.sqrt 3)) := by
    rw [Curve.scale_varianceScore, hs2, optimal_score]
  refine ⟨hpeak, ?_, ?_⟩
  · rw [Curve.variance_operational_score _ hK, hscore]
    ring
  · intro other hother
    rw [Curve.variance_operational_score _ hK, Curve.variance_operational_score _ hK, hscore]
    exact mul_le_mul_of_nonneg_left (quadratic_variance_score_le_all_power other hP hother)
      (sq_nonneg (K : ℝ))

end Analog
