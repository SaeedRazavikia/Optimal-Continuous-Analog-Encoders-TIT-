import Analog.Quartic
import Analog.PowerScaling

/-!
# Quartic Gram optimization at every positive power

This module restores the pointwise power budget P and, optionally, an algebraic
K^2 multiplier. The score remains the explicitly defined Gram objective: the
connection to an operational separation infimum and continuous-encoder rigidity
are not asserted by these theorems.
-/

noncomputable section

namespace Analog.Quartic

def CurvePeakFeasibleAt (e : Analog.Curve) (P : ℝ) : Prop :=
  ∀ s : ℝ, -1 ≤ s → s ≤ 1 → curveEnergy e s ≤ P

theorem scale_energy (a : ℝ) (e : Analog.Curve) (s : ℝ) :
    curveEnergy (e.scale a) s = a ^ 2 * curveEnergy e s := by
  dsimp [Analog.Curve.scale, curveEnergy]
  ring

theorem scale_peak (a : ℝ) (e : Analog.Curve) (P : ℝ)
    (hpeak : CurvePeakFeasibleAt e P) :
    CurvePeakFeasibleAt (e.scale a) (a ^ 2 * P) := by
  intro s hslo hshi
  rw [scale_energy]
  exact mul_le_mul_of_nonneg_left (hpeak s hslo hshi) (sq_nonneg a)

theorem scale_score (a : ℝ) (e : Analog.Curve) (M : ℝ) :
    curveScore M (e.scale a) = a ^ 2 * curveScore M e := by
  exact Analog.Curve.scale_gramScore a e M

theorem normalize_peak (e : Analog.Curve) {P : ℝ} (hP : 0 < P)
    (hpeak : CurvePeakFeasibleAt e P) :
    CurvePeakFeasible (e.scale (1 / Real.sqrt P)) := by
  have hs2 := Real.sq_sqrt hP.le
  have hi : (1 / Real.sqrt P) ^ 2 * P = 1 := by
    rw [div_pow, one_pow, hs2]
    exact div_mul_cancel₀ 1 hP.ne'
  have hp := scale_peak (1 / Real.sqrt P) e P hpeak
  rw [hi] at hp
  exact hp

/-- Universal quartic Gram-score bound at arbitrary positive peak power. -/
theorem quartic_curve_score_le_all_power (M P r : ℝ) (hM : 0 < M) (hP : 0 < P)
    (hr : 0 < r) (hrthird : r < 1 / 3) (hroot : RootEquation M r)
    (e : Analog.Curve) (hpeak : CurvePeakFeasibleAt e P) :
    curveScore M e ≤
      P * (8 * r / (denominator r * (M ^ 2 + 2 * r * (1 + r) ^ 2))) := by
  have hs2 := Real.sq_sqrt hP.le
  have hn := quartic_curve_score_le M r hM hr hrthird hroot
    (e.scale (1 / Real.sqrt P)) (normalize_peak e hP hpeak)
  rw [scale_score, div_pow, one_pow, hs2] at hn
  have hp := mul_le_mul_of_nonneg_left hn hP.le
  have hi : P * ((1 / P) * curveScore M e) = curveScore M e := by field_simp
  rwa [hi] at hp

/-- A root-characterized optimizer attains the bound at every positive power. -/
theorem quartic_optimal_at_root_all_power (M P r : ℝ) (hM : 0 < M) (hP : 0 < P)
    (hr : 0 < r) (hrthird : r < 1 / 3) (hroot : RootEquation M r) :
    let e := (optimalPlanarCurve r).scale (Real.sqrt P)
    CurvePeakFeasibleAt e P ∧
    curveScore M e =
      P * (8 * r / (denominator r * (M ^ 2 + 2 * r * (1 + r) ^ 2))) ∧
    ∀ other : Analog.Curve, CurvePeakFeasibleAt other P →
      curveScore M other ≤ curveScore M e := by
  dsimp only
  have hs2 := Real.sq_sqrt hP.le
  have hp := scale_peak (Real.sqrt P) (optimalPlanarCurve r) 1 (optimal_planar_peak r hr)
  simp only [hs2, mul_one] at hp
  have hvalue : curveScore M ((optimalPlanarCurve r).scale (Real.sqrt P)) =
      P * (8 * r / (denominator r * (M ^ 2 + 2 * r * (1 + r) ^ 2))) := by
    rw [scale_score, hs2, optimal_planar_score M r hr]
  refine ⟨hp, hvalue, ?_⟩
  intro other hother
  rw [hvalue]
  exact quartic_curve_score_le_all_power M P r hM hP hr hrthird hroot other hother

/-- Complete finite-dimensional quartic Gram optimization for all M>0 and P>0.
The root is proved to exist, and the competitors include every planar quartic
coefficient curve obeying the continuum peak constraint. -/
theorem quartic_optimal_all_power (M P : ℝ) (hM : 0 < M) (hP : 0 < P) :
    ∃ r : ℝ, (0 < r ∧ r < 1 / 3 ∧ RootEquation M r) ∧
      let e := (optimalPlanarCurve r).scale (Real.sqrt P)
      CurvePeakFeasibleAt e P ∧
      curveScore M e =
        P * (8 * r / (denominator r * (M ^ 2 + 2 * r * (1 + r) ^ 2))) ∧
      ∀ other : Analog.Curve, CurvePeakFeasibleAt other P →
        curveScore M other ≤ curveScore M e := by
  obtain ⟨r, hr, hrthird, hroot⟩ := root_exists M hM
  exact ⟨r, ⟨hr, hrthird, hroot⟩,
    quartic_optimal_at_root_all_power M P r hM hP hr hrthird hroot⟩

/-- Multiplication by K^2 preserves the Gram bound. This is an algebraic
normalization statement, not an operational-score identification. -/
theorem quartic_gram_bound_with_users (K M P r : ℝ) (hM : 0 < M) (hP : 0 < P)
    (hr : 0 < r) (hrthird : r < 1 / 3) (hroot : RootEquation M r)
    (e : Analog.Curve) (hpeak : CurvePeakFeasibleAt e P) :
    K ^ 2 * curveScore M e ≤
      K ^ 2 * P * (8 * r / (denominator r * (M ^ 2 + 2 * r * (1 + r) ^ 2))) := by
  have h := mul_le_mul_of_nonneg_left
    (quartic_curve_score_le_all_power M P r hM hP hr hrthird hroot e hpeak) (sq_nonneg K)
  simpa only [mul_assoc] using h

end Analog.Quartic
