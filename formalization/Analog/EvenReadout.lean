import Analog.GeneralScore
import Analog.GeneralQuadratic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Even strictly curved receiver readouts

Endpoint derivatives are derivatives within the closed source interval, matching
`GeneralScore.readoutSlope`. Evenness only needs to hold on that interval.
-/
noncomputable section
open Set
open scoped Pointwise
namespace Analog.EvenReadout
open GeneralScore GramSynthesis

/-- The closed-interval derivative of an even readout is odd. -/
theorem readoutSlope_neg (ψ : ℝ → ℝ)
    (heven : ∀ x ∈ Icc (-1 : ℝ) 1, ψ (-x) = ψ x)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    readoutSlope ψ (-x) = -readoutSlope ψ x := by
  have hset : -(Icc (-1 : ℝ) 1) = Icc (-1 : ℝ) 1 := by
    ext z
    simp only [Set.mem_neg, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hc := derivWithin_congr heven (heven x hx)
  have hn := derivWithin_comp_neg ψ (Icc (-1 : ℝ) 1) x
  rw [hset, hc] at hn
  dsimp [readoutSlope]
  linarith only [hn]

/-- In particular, the two endpoint derivatives have opposite signs. -/
theorem endpoint_slopes_opposite (ψ : ℝ → ℝ)
    (heven : ∀ x ∈ Icc (-1 : ℝ) 1, ψ (-x) = ψ x) :
    readoutSlope ψ (-1) = -readoutSlope ψ 1 :=
  readoutSlope_neg ψ heven (by norm_num)

/-- Strict curvature excludes the degenerate endpoint-slope parameter M = 0. -/
theorem endpoint_magnitude_pos (ψ : ℝ → ℝ)
    (heven : ∀ x ∈ Icc (-1 : ℝ) 1, ψ (-x) = ψ x)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hshape : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ) :
    0 < |readoutSlope ψ 1| := by
  have he := endpoint_slopes_opposite ψ heven
  apply abs_pos.mpr
  intro hz
  rcases hshape with hc | hc
  · have hm := hc.strictMonoOn_derivWithin hd (by norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1)
      (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) (by norm_num : (-1 : ℝ) < 1)
    change readoutSlope ψ (-1) < readoutSlope ψ 1 at hm
    rw [he, hz] at hm
    linarith
  · have hm := hc.strictAntiOn_derivWithin hd (by norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1)
      (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) (by norm_num : (-1 : ℝ) < 1)
    change readoutSlope ψ 1 < readoutSlope ψ (-1) at hm
    rw [he, hz] at hm
    linarith

/-- Every derivative lies between the symmetric endpoint bounds. -/
theorem readoutSlope_abs_le (ψ : ℝ → ℝ)
    (heven : ∀ x ∈ Icc (-1 : ℝ) 1, ψ (-x) = ψ x)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨
      ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |readoutSlope ψ x| ≤ |readoutSlope ψ 1| := by
  have he := endpoint_slopes_opposite ψ heven
  have hleft : -|readoutSlope ψ 1| ≤ readoutSlope ψ 1 := neg_abs_le _
  have hright : readoutSlope ψ 1 ≤ |readoutSlope ψ 1| := le_abs_self _
  apply abs_le.mpr
  rcases hshape with hc | hc
  · have hm := hc.monotoneOn_derivWithin hd
    have hlo := hm (by norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1) hx hx.1
    have hhi := hm hx (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) hx.2
    change readoutSlope ψ (-1) ≤ readoutSlope ψ x at hlo
    change readoutSlope ψ x ≤ readoutSlope ψ 1 at hhi
    rw [he] at hlo
    constructor <;> linarith
  · have hm := hc.antitoneOn_derivWithin hd
    have hhi := hm (by norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1) hx hx.1
    have hlo := hm hx (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) hx.2
    change readoutSlope ψ x ≤ readoutSlope ψ (-1) at hhi
    change readoutSlope ψ 1 ≤ readoutSlope ψ x at hlo
    rw [he] at hhi
    constructor <;> linarith

/-- The endpoint maximum reduces to the scalar Gram expression used by the
quadratic and quartic optimization certificates. -/
theorem endpointDual_eq (e : Curve) (ψ : ℝ → ℝ)
    (heven : ∀ x ∈ Icc (-1 : ℝ) 1, ψ (-x) = ψ x)
    (hD : 0 < det e.A e.B e.C) :
    endpointDual e ψ =
      (e.A + |readoutSlope ψ 1| ^ 2 * e.B +
        2 * |readoutSlope ψ 1| * |e.C|) / det e.A e.B e.C := by
  rw [endpointDual, endpoint_slopes_opposite ψ heven]
  simp only [neg_neg, dual_formula]
  rw [max_div_div_right hD.le]
  congr 1
  let q := readoutSlope ψ 1
  have hfirst : e.B * q ^ 2 - 2 * e.C * q * 1 + e.A * 1 ^ 2 =
      (e.A + e.B * q ^ 2) + -(2 * e.C * q) := by ring
  have hsecond : e.B * (-q) ^ 2 - 2 * e.C * (-q) * 1 + e.A * 1 ^ 2 =
      (e.A + e.B * q ^ 2) + (2 * e.C * q) := by ring
  change max (e.B * q ^ 2 - 2 * e.C * q * 1 + e.A * 1 ^ 2)
    (e.B * (-q) ^ 2 - 2 * e.C * (-q) * 1 + e.A * 1 ^ 2) = _
  rw [hfirst, hsecond, max_add_add_left, max_comm, ← abs_eq_max_neg,
    abs_mul, abs_mul]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  change e.A + e.B * q ^ 2 + 2 * |e.C| * |q| =
    e.A + |q| ^ 2 * e.B + 2 * |q| * |e.C|
  rw [sq_abs]
  ring

/-- The exact endpoint expression agrees with the Gram objective for every
positive-definite coefficient matrix and every even readout. -/
theorem endpoint_score_eq_gramScore (K : ℕ) (e : Curve) (ψ : ℝ → ℝ)
    (heven : ∀ x ∈ Icc (-1 : ℝ) 1, ψ (-x) = ψ x)
    (hD : 0 < det e.A e.B e.C) :
    (K : ℝ) ^ 2 / endpointDual e ψ =
      (K : ℝ) ^ 2 * GeneralQuadratic.gramScore e |readoutSlope ψ 1| := by
  rw [endpointDual_eq e ψ heven hD]
  simp only [GeneralQuadratic.gramScore, det, div_div_eq_mul_div, mul_div_assoc]

/-- A C¹ readout supplies exactly the endpoint regularity used in the score theorem. -/
theorem c1_readout_regular (ψ : ℝ → ℝ)
    (hψ : ContDiffOn ℝ 1 ψ (Icc (-1 : ℝ) 1)) :
    DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1) ∧
      ContinuousOn (readoutSlope ψ) (Icc (-1 : ℝ) 1) := by
  refine ⟨hψ.differentiableOn (by norm_num), ?_⟩
  exact hψ.continuousOn_derivWithin (uniqueDiffOn_Icc (by norm_num)) (by norm_num)

end Analog.EvenReadout
