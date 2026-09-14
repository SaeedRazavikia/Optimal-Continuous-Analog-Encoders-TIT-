import Analog.Certificate
import Mathlib.Data.Real.Sqrt

/-!+# The normalized quadratic moment-curve design problem

The plane is represented by two real coordinates. This file formalizes the
finite-dimensional algebraic optimization problem. It does not assume or prove
the manuscript's continuous-encoder rigidity or operational score theorem.
-/

noncomputable section

namespace Analog

/-- Coefficients of the planar curve c + u s + v s². -/
structure Curve where
  cx : ℝ
  cy : ℝ
  ux : ℝ
  uy : ℝ
  vx : ℝ
  vy : ℝ

def Curve.energy (e : Curve) (s : ℝ) : ℝ :=
  (e.cx + e.ux * s + e.vx * s ^ 2) ^ 2 +
  (e.cy + e.uy * s + e.vy * s ^ 2) ^ 2

/-- The full continuum constraint, with normalized peak power P = 1. -/
def Curve.PeakFeasible (e : Curve) : Prop :=
  ∀ s : ℝ, -1 ≤ s → s ≤ 1 → e.energy s ≤ 1

def Curve.A (e : Curve) : ℝ := e.ux ^ 2 + e.uy ^ 2
def Curve.B (e : Curve) : ℝ := e.vx ^ 2 + e.vy ^ 2
def Curve.C (e : Curve) : ℝ := e.ux * e.vx + e.uy * e.vy

/-- The variance specialization (M = 2) of the manuscript's Gram score.
Its equality to the operational separation infimum is outside this module. -/
def Curve.score (e : Curve) : ℝ :=
  (e.A * e.B - e.C ^ 2) / (e.A + 4 * e.B + 4 * |e.C|)

lemma sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma sqrt_three_bounds : 1 < Real.sqrt 3 ∧ Real.sqrt 3 < 2 := by
  have h := Real.sqrt_nonneg (3 : ℝ)
  have hs := sqrt_three_sq
  constructor <;> nlinarith

/-- A weighted consequence of just the three peak constraints at -1, 0, 1. -/
theorem supporting_bound (e : Curve) (h : e.PeakFeasible) :
    2 * Real.sqrt 3 * e.A + (2 * Real.sqrt 3 - 3) * e.B ≤ 4 := by
  have h0 := h 0 (by norm_num) (by norm_num)
  have hp := h 1 (by norm_num) (by norm_num)
  have hm := h (-1) (by norm_num) (by norm_num)
  simp only [Curve.energy] at h0 hp hm
  norm_num at h0 hp hm
  have hav : e.A + (e.cx + e.vx) ^ 2 + (e.cy + e.vy) ^ 2 ≤ 1 := by
    dsimp [Curve.A]
    nlinarith [hp, hm]
  have hr := sqrt_three_bounds
  have hs := sqrt_three_sq
  have hi :
      2 * Real.sqrt 3 * e.A + (2 * Real.sqrt 3 - 3) * e.B +
        (2 * e.cx + Real.sqrt 3 * e.vx) ^ 2 +
        (2 * e.cy + Real.sqrt 3 * e.vy) ^ 2 =
      2 * Real.sqrt 3 *
        (e.A + (e.cx + e.vx) ^ 2 + (e.cy + e.vy) ^ 2) +
      (4 - 2 * Real.sqrt 3) * (e.cx ^ 2 + e.cy ^ 2) := by
    calc
      _ = 2 * Real.sqrt 3 *
          (e.A + (e.cx + e.vx) ^ 2 + (e.cy + e.vy) ^ 2) +
          (4 - 2 * Real.sqrt 3) * (e.cx ^ 2 + e.cy ^ 2) +
          ((Real.sqrt 3) ^ 2 - 3) * (e.vx ^ 2 + e.vy ^ 2) := by
            dsimp [Curve.A, Curve.B]
            ring
      _ = _ := by rw [sqrt_three_sq]; ring
  have hav' := mul_le_mul_of_nonneg_left hav (by positivity : 0 ≤ 2 * Real.sqrt 3)
  have h0' := mul_le_mul_of_nonneg_left h0 (by nlinarith : 0 ≤ 4 - 2 * Real.sqrt 3)
  nlinarith [sq_nonneg (2 * e.cx + Real.sqrt 3 * e.vx),
    sq_nonneg (2 * e.cy + Real.sqrt 3 * e.vy)]

def optimalCurve : Curve where
  cx := 0
  cy := -1
  ux := Real.sqrt (4 * (Real.sqrt 3 - 1) / 3)
  uy := 0
  vx := 0
  vy := 2 * Real.sqrt 3 / 3

lemma optimal_A : optimalCurve.A = 4 * (Real.sqrt 3 - 1) / 3 := by
  have h := sqrt_three_bounds.1
  have hx : 0 ≤ 4 * (Real.sqrt 3 - 1) / 3 := by linarith
  dsimp [Curve.A, optimalCurve]
  rw [Real.sq_sqrt hx]
  ring

lemma optimal_B : optimalCurve.B = 4 / 3 := by
  dsimp [Curve.B, optimalCurve]
  nlinarith only [sqrt_three_sq]

lemma optimal_C : optimalCurve.C = 0 := by
  simp [Curve.C, optimalCurve]

/-- Exact identity establishing continuum feasibility of the optimizer. -/
theorem optimal_energy (s : ℝ) :
    optimalCurve.energy s = 1 - (4 / 3) * s ^ 2 * (1 - s ^ 2) := by
  have hab : optimalCurve.A + optimalCurve.B - 2 * (2 * Real.sqrt 3 / 3) = 0 := by
    rw [optimal_A, optimal_B]
    ring
  have hi : optimalCurve.energy s =
      1 - optimalCurve.B * s ^ 2 * (1 - s ^ 2) +
        (optimalCurve.A + optimalCurve.B - 2 * (2 * Real.sqrt 3 / 3)) * s ^ 2 := by
    dsimp [Curve.energy, Curve.A, Curve.B, optimalCurve]
    ring
  rw [hab, optimal_B] at hi
  nlinarith only [hi]

theorem optimal_peak : optimalCurve.PeakFeasible := by
  intro s hlo hhi
  rw [optimal_energy]
  have hs : s ^ 2 ≤ 1 := by nlinarith
  have ht : 0 ≤ (4 / 3 : ℝ) * s ^ 2 * (1 - s ^ 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg s)) (by linarith)
  linarith

theorem optimal_score : optimalCurve.score = 4 / (9 + 6 * Real.sqrt 3) := by
  have hr := sqrt_three_bounds.1
  have hs := sqrt_three_sq
  unfold Curve.score
  rw [optimal_A, optimal_B, optimal_C]
  simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, abs_zero, mul_zero, add_zero]
  have hd : 0 < 4 * (Real.sqrt 3 - 1) / 3 + 4 * (4 / 3 : ℝ) := by linarith
  have hc : 0 < 9 + 6 * Real.sqrt 3 := by linarith
  apply (div_eq_div_iff (ne_of_gt hd) (ne_of_gt hc)).2
  nlinarith

/-- Global converse for every peak-feasible quadratic planar curve, including
correlated and degenerate coefficient choices. -/
theorem quadratic_score_le (e : Curve) (h : e.PeakFeasible) :
    e.score ≤ 4 / (9 + 6 * Real.sqrt 3) := by
  apply variance_score_bound_all (Real.sqrt 3) e.A e.B e.C
  · positivity
  · exact sqrt_three_sq
  · dsimp [Curve.A]; positivity
  · dsimp [Curve.B]; positivity
  · exact supporting_bound e h

/-- Main result: a continuum-feasible curve attains the universal bound for
the normalized finite-dimensional quadratic Gram-score problem. -/
theorem quadratic_variance_optimal :
    optimalCurve.PeakFeasible ∧
    optimalCurve.score = 4 / (9 + 6 * Real.sqrt 3) ∧
    ∀ e : Curve, e.PeakFeasible → e.score ≤ optimalCurve.score := by
  refine ⟨optimal_peak, optimal_score, ?_⟩
  intro e h
  rw [optimal_score]
  exact quadratic_score_le e h

end Analog
