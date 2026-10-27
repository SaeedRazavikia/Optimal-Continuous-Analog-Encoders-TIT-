import Analog.PowerScaling
import Analog.QuarticPower
import Analog.GeneralScore

/-!
# Explicit polynomial optimizer identities

The positive-power quadratic and quartic optimizers have nonsingular common
columns. Their planar encoders and the quartic reciprocal objective are exactly
the formulas displayed in Proposition 4 (`thm:parabola`).
-/

noncomputable section
namespace Analog.PolynomialOptimizerFacts
open GramSynthesis

lemma scale_det (e : Curve) (a : ℝ) :
    det (e.scale a).A (e.scale a).B (e.scale a).C =
      a ^ 4 * det e.A e.B e.C := by
  rw [Curve.scale_A, Curve.scale_B, Curve.scale_C]
  dsimp [det]
  ring

/-- The quadratic optimizer remains nonsingular at every positive power. -/
theorem quadratic_det_pos (M P : ℝ) (hM : 0 < M) (hP : 0 < P) :
    let e := (GeneralQuadratic.optimalCurve (GeneralQuadratic.optimalParameter M)).scale
      (Real.sqrt P)
    0 < det e.A e.B e.C := by
  dsimp only
  rw [scale_det]
  have hb := GeneralQuadratic.optimalParameter_bounds M hM
  have hb0 : 0 < GeneralQuadratic.optimalParameter M := by linarith [hb.1]
  have hdiff : 0 < 2 - GeneralQuadratic.optimalParameter M := sub_pos.mpr hb.2
  rw [GeneralQuadratic.optimal_A _ hb0.le hb.2.le,
    GeneralQuadratic.optimal_B, GeneralQuadratic.optimal_C]
  dsimp [det]
  simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using
    mul_pos (pow_pos (Real.sqrt_pos.mpr hP) 4)
      (mul_pos (mul_pos hb0 hdiff) (sq_pos_of_pos hb0))

/-- The quartic optimizer remains nonsingular at every positive power. -/
theorem quartic_det_pos (P r : ℝ) (hP : 0 < P) (hr : 0 < r) :
    let e := (Quartic.optimalPlanarCurve r).scale (Real.sqrt P)
    0 < det e.A e.B e.C := by
  dsimp only
  rw [scale_det]
  obtain ⟨hA, hb⟩ := Quartic.coefficient_pos r hr
  have ha : (Quartic.optimalPlanarCurve r).A = Quartic.optA r := by
    simp [Curve.A, Quartic.optimalPlanarCurve, Real.sq_sqrt hA.le]
  have hbb : (Quartic.optimalPlanarCurve r).B = Quartic.optb r ^ 2 := by
    simp [Curve.B, Quartic.optimalPlanarCurve]
  have hc : (Quartic.optimalPlanarCurve r).C = 0 := by
    simp [Curve.C, Quartic.optimalPlanarCurve]
  rw [ha, hbb, hc]
  dsimp [det]
  simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using
    mul_pos (pow_pos (Real.sqrt_pos.mpr hP) 4) (mul_pos hA (sq_pos_of_pos hb))

/-- The quadratic planar encoder is the real/imaginary coordinate form of
`√P [a s + i (b s² - 1)]`. -/
theorem quadratic_encoder_formula (b P s : ℝ) :
    GeneralScore.encoder ((GeneralQuadratic.optimalCurve b).scale (Real.sqrt P))
      (fun t => t ^ 2) s =
      (Real.sqrt P * (Real.sqrt (b * (2 - b)) * s),
       Real.sqrt P * (b * s ^ 2 - 1)) := by
  apply Prod.ext <;>
    dsimp [GeneralScore.encoder, GeneralQuadratic.optimalCurve, Curve.scale] <;> ring

/-- The quartic planar encoder is the real/imaginary coordinate form of
`√P [aᵨ s + i (bᵨ s⁴ + cᵨ)]`, with the displayed coefficients. -/
theorem quartic_encoder_formula (r P s : ℝ) :
    GeneralScore.encoder ((Quartic.optimalPlanarCurve r).scale (Real.sqrt P))
      (fun t => t ^ 4) s =
      (Real.sqrt P * (Real.sqrt (Quartic.optA r) * s),
       Real.sqrt P * (Quartic.optb r * s ^ 4 + Quartic.optc r)) := by
  apply Prod.ext <;>
    dsimp [GeneralScore.encoder, Quartic.optimalPlanarCurve, Curve.scale] <;> ring

/-- The quartic optimum has exactly the reciprocal coefficient form displayed
in the paper; the operational multiplier `K²` is supplied by the score theorem. -/
theorem quartic_score_formula (M P r : ℝ) (hP : 0 < P) (hr : 0 < r) :
    GeneralQuadratic.gramScore ((Quartic.optimalPlanarCurve r).scale (Real.sqrt P)) M =
      P / (M ^ 2 / (Real.sqrt (Quartic.optA r)) ^ 2 + 1 / Quartic.optb r ^ 2) := by
  rw [Curve.scale_gramScore, Real.sq_sqrt hP.le]
  change P * Quartic.curveScore M (Quartic.optimalPlanarCurve r) = _
  rw [Quartic.optimal_planar_score M r hr, ← Quartic.optimal_score M r hr]
  rw [Real.sq_sqrt (Quartic.coefficient_pos r hr).1.le]
  simp only [Quartic.objective, mul_one_div]

/-- The explicit quadratic score is positive. -/
theorem quadratic_score_pos (M P : ℝ) (hM : 0 < M) (hP : 0 < P) :
    0 < GeneralQuadratic.gramScore
      ((GeneralQuadratic.optimalCurve (GeneralQuadratic.optimalParameter M)).scale
        (Real.sqrt P)) M := by
  rw [(quadratic_optimal_all_power M P hM hP).2.1]
  have hb := GeneralQuadratic.optimalParameter_bounds M hM
  exact mul_pos hP (mul_pos (sq_pos_of_pos (lt_trans (by norm_num) hb.1))
    (sub_pos.mpr hb.1))

/-- The explicit quartic score is positive even for a zero endpoint parameter. -/
theorem quartic_score_pos (M P r : ℝ) (hP : 0 < P) (hr : 0 < r) :
    0 < GeneralQuadratic.gramScore
      ((Quartic.optimalPlanarCurve r).scale (Real.sqrt P)) M := by
  rw [quartic_score_formula M P r hP hr]
  obtain ⟨hA, hb⟩ := Quartic.coefficient_pos r hr
  apply div_pos hP
  have hn : 0 ≤ M ^ 2 / (Real.sqrt (Quartic.optA r)) ^ 2 := by positivity
  exact add_pos_of_nonneg_of_pos hn (one_div_pos.mpr (sq_pos_of_pos hb))

end Analog.PolynomialOptimizerFacts
