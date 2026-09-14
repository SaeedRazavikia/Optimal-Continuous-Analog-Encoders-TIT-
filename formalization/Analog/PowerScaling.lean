import Analog.GeneralQuadratic
import Analog.Operational

/-! General-power scaling of the complete quadratic Gram optimization.
The operational separation score also has the corresponding power law,
proved independently for arbitrary encoders in `Operational.lean`.
-/

noncomputable section
namespace Analog

def Curve.scale (a : ℝ) (e : Curve) : Curve where
  cx := a * e.cx
  cy := a * e.cy
  ux := a * e.ux
  uy := a * e.uy
  vx := a * e.vx
  vy := a * e.vy

def Curve.PeakFeasibleAt (e : Curve) (P : ℝ) : Prop :=
  ∀ s : ℝ, -1 ≤ s → s ≤ 1 → e.energy s ≤ P

lemma Curve.scale_energy (a : ℝ) (e : Curve) (s : ℝ) :
    (e.scale a).energy s = a ^ 2 * e.energy s := by
  dsimp [Curve.scale, Curve.energy]
  ring

lemma Curve.scale_A (a : ℝ) (e : Curve) : (e.scale a).A = a ^ 2 * e.A := by
  dsimp [Curve.scale, Curve.A]
  ring

lemma Curve.scale_B (a : ℝ) (e : Curve) : (e.scale a).B = a ^ 2 * e.B := by
  dsimp [Curve.scale, Curve.B]
  ring

lemma Curve.scale_C (a : ℝ) (e : Curve) : (e.scale a).C = a ^ 2 * e.C := by
  dsimp [Curve.scale, Curve.C]
  ring

/-- Scaling coefficients scales the peak-power budget by the squared amplitude. -/
theorem Curve.scale_peak (a : ℝ) (e : Curve) (P : ℝ) (h : e.PeakFeasibleAt P) :
    (e.scale a).PeakFeasibleAt (a ^ 2 * P) := by
  intro s hlo hhi
  rw [Curve.scale_energy]
  exact mul_le_mul_of_nonneg_left (h s hlo hhi) (sq_nonneg a)

/-- The Gram objective is homogeneous of degree two in encoder amplitude. -/
theorem Curve.scale_gramScore (a : ℝ) (e : Curve) (M : ℝ) :
    GeneralQuadratic.gramScore (e.scale a) M = a ^ 2 * GeneralQuadratic.gramScore e M := by
  unfold GeneralQuadratic.gramScore
  rw [Curve.scale_A, Curve.scale_B, Curve.scale_C, abs_mul, abs_of_nonneg (sq_nonneg a)]
  by_cases ha : a = 0
  · simp [ha]
  · have haa : a ^ 2 ≠ 0 := pow_ne_zero _ ha
    have hnum : a ^ 2 * e.A * (a ^ 2 * e.B) - (a ^ 2 * e.C) ^ 2 =
        a ^ 2 * (a ^ 2 * (e.A * e.B - e.C ^ 2)) := by ring
    have hden : a ^ 2 * e.A + M ^ 2 * (a ^ 2 * e.B) + 2 * M * (a ^ 2 * |e.C|) =
        a ^ 2 * (e.A + M ^ 2 * e.B + 2 * M * |e.C|) := by ring
    rw [hnum, hden, mul_div_mul_left _ _ haa, mul_div_assoc]

/-- Every positive-power feasible curve normalizes to a unit-power curve. -/
theorem Curve.normalize_peak (e : Curve) {P : ℝ} (hP : 0 < P)
    (h : e.PeakFeasibleAt P) : (e.scale (1 / Real.sqrt P)).PeakFeasible := by
  have hs : Real.sqrt P ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hP)
  have hs2 := Real.sq_sqrt (le_of_lt hP)
  have hi : (1 / Real.sqrt P) ^ 2 * P = 1 := by
    rw [div_pow, one_pow, hs2]
    exact div_mul_cancel₀ 1 hP.ne'
  have hp := e.scale_peak (1 / Real.sqrt P) P h
  rw [hi] at hp
  exact hp

/-- All positive powers and positive endpoint-slope parameters are covered.
The competitors range over every feasible planar quadratic coefficient choice. -/
theorem quadratic_optimal_all_power (M P : ℝ) (hM : 0 < M) (hP : 0 < P) :
    let b := GeneralQuadratic.optimalParameter M
    let e := (GeneralQuadratic.optimalCurve b).scale (Real.sqrt P)
    e.PeakFeasibleAt P ∧
    GeneralQuadratic.gramScore e M = P * (b ^ 2 * (b - 1)) ∧
    ∀ other : Curve, other.PeakFeasibleAt P →
      GeneralQuadratic.gramScore other M ≤ GeneralQuadratic.gramScore e M := by
  dsimp only
  have hbase := GeneralQuadratic.quadratic_optimal_closed_form M hM
  have hs2 := Real.sq_sqrt (le_of_lt hP)
  have hpeak := (GeneralQuadratic.optimalCurve (GeneralQuadratic.optimalParameter M)).scale_peak
    (Real.sqrt P) 1 hbase.1
  simp only [hs2, mul_one] at hpeak
  have hvalue : GeneralQuadratic.gramScore
      ((GeneralQuadratic.optimalCurve (GeneralQuadratic.optimalParameter M)).scale (Real.sqrt P)) M =
      P * ((GeneralQuadratic.optimalParameter M) ^ 2 * (GeneralQuadratic.optimalParameter M - 1)) := by
    rw [Curve.scale_gramScore, hs2, hbase.2.1]
  refine ⟨hpeak, hvalue, ?_⟩
  intro other hother
  have hn := hbase.2.2 (other.scale (1 / Real.sqrt P)) (other.normalize_peak hP hother)
  rw [Curve.scale_gramScore, hbase.2.1, div_pow, one_pow, hs2] at hn
  have hh := mul_le_mul_of_nonneg_left hn (le_of_lt hP)
  rw [hvalue]
  have hi : P * ((1 / P) * GeneralQuadratic.gramScore other M) =
      GeneralQuadratic.gramScore other M := by field_simp
  rwa [hi] at hh

end Analog
