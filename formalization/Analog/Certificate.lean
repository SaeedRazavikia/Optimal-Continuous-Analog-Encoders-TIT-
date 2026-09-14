import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Algebraic converse for the quadratic variance encoder

This file proves the reduced converse over real Gram entries. The supporting
inequality is established from encoder peak constraints in a separate module.
No claim about rigidity or the operational separation formula is made here.
-/

namespace Analog

/-- The exact sum-of-squares identity underlying the variance converse. -/
theorem variance_sos_identity (r A B : ℝ) (hr : r ^ 2 = 3) :
    (A + 4 * B) * (2 * r * A + (2 * r - 3) * B)
        - (9 + 6 * r) * A * B =
      2 * r * (A - (r - 1) * B) ^ 2 := by
  calc
    (A + 4 * B) * (2 * r * A + (2 * r - 3) * B)
          - (9 + 6 * r) * A * B =
        2 * r * (A - (r - 1) * B) ^ 2
          + (r ^ 2 - 3) * (4 * A * B + (4 - 2 * r) * B ^ 2) := by ring
    _ = 2 * r * (A - (r - 1) * B) ^ 2 := by rw [hr]; ring

/-- A supporting peak inequality implies a sharp polynomial score bound. -/
theorem variance_certificate (r A B : ℝ)
    (hrpos : 0 < r) (hr : r ^ 2 = 3)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpeak : 2 * r * A + (2 * r - 3) * B ≤ 4) :
    (9 + 6 * r) * A * B ≤ 4 * (A + 4 * B) := by
  have hsum : 0 ≤ A + 4 * B := by positivity
  have hupper :
      (A + 4 * B) * (2 * r * A + (2 * r - 3) * B)
        ≤ 4 * (A + 4 * B) := by
    calc
      (A + 4 * B) * (2 * r * A + (2 * r - 3) * B)
          ≤ (A + 4 * B) * 4 := mul_le_mul_of_nonneg_left hpeak hsum
      _ = 4 * (A + 4 * B) := by ring
  have hidentity := variance_sos_identity r A B hr
  have hsquare : 0 ≤ 2 * r * (A - (r - 1) * B) ^ 2 := by positivity
  linarith

/-- The algebraic score bound includes arbitrary correlation between the two
encoder coefficients. The operational meaning of this expression is outside
the present formalization. -/
theorem variance_score_bound (r A B C : ℝ)
    (hrpos : 0 < r) (hr : r ^ 2 = 3)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpeak : 2 * r * A + (2 * r - 3) * B ≤ 4)
    (hnonzero : 0 < A + 4 * B) :
    (A * B - C ^ 2) / (A + 4 * B + 4 * |C|) ≤ 4 / (9 + 6 * r) := by
  have hden : 0 < A + 4 * B + 4 * |C| := by
    linarith [abs_nonneg C]
  have hconstant : 0 < 9 + 6 * r := by linarith
  have hbound := variance_certificate r A B hrpos hr hA hB hpeak
  have hcorr : 0 ≤ (9 + 6 * r) * C ^ 2 :=
    mul_nonneg (le_of_lt hconstant) (sq_nonneg C)
  apply (div_le_div_iff₀ hden hconstant).2
  nlinarith [abs_nonneg C]

/-- A version covering the degenerate boundary as well. Lean's real division
is total, with division by zero defined to be zero. -/
theorem variance_score_bound_all (r A B C : ℝ)
    (hrpos : 0 < r) (hr : r ^ 2 = 3)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpeak : 2 * r * A + (2 * r - 3) * B ≤ 4) :
    (A * B - C ^ 2) / (A + 4 * B + 4 * |C|) ≤ 4 / (9 + 6 * r) := by
  by_cases hnonzero : 0 < A + 4 * B
  · exact variance_score_bound r A B C hrpos hr hA hB hpeak hnonzero
  · have hAzero : A = 0 := by linarith
    have hBzero : B = 0 := by linarith
    have hnegative : (-C ^ 2) / (4 * |C|) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg C))
        (mul_nonneg (by norm_num) (abs_nonneg C))
    rw [hAzero, hBzero]
    calc
      (0 * 0 - C ^ 2) / (0 + 4 * 0 + 4 * |C|) ≤ 0 := by
        simpa only [zero_mul, mul_zero, zero_add, zero_sub] using hnegative
      _ ≤ 4 / (9 + 6 * r) := by positivity

end Analog
