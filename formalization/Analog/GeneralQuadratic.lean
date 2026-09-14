import Analog.Quadratic

/-! General positive endpoint-slope quadratic Gram-score optimum.
The operational-score identification and continuous-encoder rigidity are not
assumed or proved here. -/

noncomputable section
namespace Analog
namespace GeneralQuadratic

def gramScore (e : Curve) (M : ℝ) : ℝ :=
  (e.A * e.B - e.C ^ 2) / (e.A + M ^ 2 * e.B + 2 * M * |e.C|)

/-- An elementary weighted peak bound, valid even for correlated coefficients. -/
theorem supporting_bound (e : Curve) (h : e.PeakFeasible)
    (b : ℝ) (hb : 1 ≤ b) :
    b * e.A + (b - 1) * e.B ≤ b ^ 2 := by
  have h0 := h 0 (by norm_num) (by norm_num)
  have hp := h 1 (by norm_num) (by norm_num)
  have hm := h (-1) (by norm_num) (by norm_num)
  simp only [Curve.energy] at h0 hp hm
  norm_num at h0 hp hm
  have hav : e.A + (e.cx + e.vx) ^ 2 + (e.cy + e.vy) ^ 2 ≤ 1 := by
    dsimp [Curve.A]
    nlinarith [hp, hm]
  have hi :
      b * e.A + (b - 1) * e.B +
        (b * e.cx + e.vx) ^ 2 + (b * e.cy + e.vy) ^ 2 =
      b * (e.A + (e.cx + e.vx) ^ 2 + (e.cy + e.vy) ^ 2) +
        b * (b - 1) * (e.cx ^ 2 + e.cy ^ 2) := by
    dsimp [Curve.A, Curve.B]
    ring
  have hleft := mul_le_mul_of_nonneg_left hav (by linarith : 0 ≤ b)
  have hright := mul_le_mul_of_nonneg_left h0
    (mul_nonneg (by linarith : 0 ≤ b) (by linarith : 0 ≤ b - 1))
  nlinarith [sq_nonneg (b * e.cx + e.vx), sq_nonneg (b * e.cy + e.vy)]

/-- Polynomial identity used by the general-slope converse. -/
theorem sos_identity (M b A B : ℝ)
    (hroot : M ^ 2 * b * (b - 1) = (2 - b) ^ 2) :
    b * (b - 1) * (A + M ^ 2 * B) * (b * A + (b - 1) * B) -
      b * A * B = (b - 1) * (b * A - (2 - b) * B) ^ 2 := by
  have h1 := congrArg (fun x : ℝ => x * b * A * B) hroot
  have h2 := congrArg (fun x : ℝ => x * (b - 1) * B ^ 2) hroot
  nlinarith only [h1, h2]

/-- The Gram product bound, derived from the peak constraint. -/
theorem product_bound (e : Curve) (h : e.PeakFeasible)
    (M b : ℝ) (hb : 1 < b)
    (hroot : M ^ 2 * b * (b - 1) = (2 - b) ^ 2) :
    e.A * e.B ≤ b ^ 2 * (b - 1) * (e.A + M ^ 2 * e.B) := by
  have hb0 : 0 < b := by linarith
  have hbsub : 0 < b - 1 := by linarith
  have hpeak := supporting_bound e h b (le_of_lt hb)
  have hA : 0 ≤ e.A := by dsimp [Curve.A]; positivity
  have hB : 0 ≤ e.B := by dsimp [Curve.B]; positivity
  have hD : 0 ≤ e.A + M ^ 2 * e.B := by positivity
  have hweight : 0 ≤ b * (b - 1) * (e.A + M ^ 2 * e.B) := by positivity
  have hu := mul_le_mul_of_nonneg_left hpeak hweight
  have hi := sos_identity M b e.A e.B hroot
  have hsq : 0 ≤ (b - 1) * (b * e.A - (2 - b) * e.B) ^ 2 := by positivity
  have hmul : b * (e.A * e.B) ≤
      b * (b ^ 2 * (b - 1) * (e.A + M ^ 2 * e.B)) := by
    nlinarith only [hu, hi, hsq]
  exact (mul_le_mul_iff_right₀ hb0).mp hmul

/-- Converse for every feasible planar quadratic curve. -/
theorem quadratic_score_le (e : Curve) (h : e.PeakFeasible)
    (M b : ℝ) (hM : 0 < M) (hb : 1 < b)
    (hroot : M ^ 2 * b * (b - 1) = (2 - b) ^ 2) :
    gramScore e M ≤ b ^ 2 * (b - 1) := by
  have hb0 : 0 < b := by linarith
  have hbsub : 0 < b - 1 := by linarith
  have hA : 0 ≤ e.A := by dsimp [Curve.A]; positivity
  have hB : 0 ≤ e.B := by dsimp [Curve.B]; positivity
  have hcorr : 0 ≤ 2 * M * |e.C| := by positivity
  have hval : 0 ≤ b ^ 2 * (b - 1) := by positivity
  have hp := product_bound e h M b hb hroot
  unfold gramScore
  by_cases hd : 0 < e.A + M ^ 2 * e.B + 2 * M * |e.C|
  · apply (div_le_iff₀ hd).2
    have hx := mul_nonneg hval hcorr
    nlinarith [sq_nonneg e.C]
  · have hd0 : e.A + M ^ 2 * e.B + 2 * M * |e.C| = 0 := by
      have : 0 ≤ e.A + M ^ 2 * e.B + 2 * M * |e.C| := by positivity
      linarith
    rw [hd0, div_zero]
    exact hval

def optimalCurve (b : ℝ) : Curve where
  cx := 0
  cy := -1
  ux := Real.sqrt (b * (2 - b))
  uy := 0
  vx := 0
  vy := b

lemma optimal_A (b : ℝ) (hb0 : 0 ≤ b) (hb2 : b ≤ 2) :
    (optimalCurve b).A = b * (2 - b) := by
  have hdiff : 0 ≤ 2 - b := by linarith
  have hx : 0 ≤ b * (2 - b) := by positivity
  simp [Curve.A, optimalCurve, Real.sq_sqrt hx]

lemma optimal_B (b : ℝ) : (optimalCurve b).B = b ^ 2 := by
  simp [Curve.B, optimalCurve]

lemma optimal_C (b : ℝ) : (optimalCurve b).C = 0 := by
  simp [Curve.C, optimalCurve]

theorem optimal_energy (b s : ℝ) (hb0 : 0 ≤ b) (hb2 : b ≤ 2) :
    (optimalCurve b).energy s = 1 - b ^ 2 * s ^ 2 * (1 - s ^ 2) := by
  have hdiff : 0 ≤ 2 - b := by linarith
  have hx : (Real.sqrt (b * (2 - b))) ^ 2 = b * (2 - b) :=
    Real.sq_sqrt (by positivity)
  dsimp [Curve.energy, optimalCurve]
  nlinarith only [congrArg (fun x : ℝ => x * s ^ 2) hx]

theorem optimal_peak (b : ℝ) (hb0 : 0 ≤ b) (hb2 : b ≤ 2) :
    (optimalCurve b).PeakFeasible := by
  intro s hlo hhi
  rw [optimal_energy b s hb0 hb2]
  have hs : s ^ 2 ≤ 1 := by nlinarith
  have hdiff : 0 ≤ 1 - s ^ 2 := by linarith
  have hx : 0 ≤ b ^ 2 * s ^ 2 * (1 - s ^ 2) := by positivity
  linarith

theorem optimal_score (M b : ℝ) (hM : 0 < M) (hb1 : 1 < b) (hb2 : b < 2)
    (hroot : M ^ 2 * b * (b - 1) = (2 - b) ^ 2) :
    gramScore (optimalCurve b) M = b ^ 2 * (b - 1) := by
  unfold gramScore
  rw [optimal_A b (by linarith) (le_of_lt hb2), optimal_B, optimal_C]
  simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, abs_zero, mul_zero, add_zero]
  have hb0 : 0 < b := by linarith
  have hdiff : 0 < 2 - b := by linarith
  have hd : 0 < b * (2 - b) + M ^ 2 * b ^ 2 := by positivity
  apply (div_eq_iff hd.ne').2
  have hx := congrArg (fun x : ℝ => x * b ^ 3) hroot
  nlinarith only [hx]

/-- Complete unit-power quadratic Gram optimization, for every positive M
and every parameter satisfying the exact root characterization. -/
theorem quadratic_optimal (M b : ℝ) (hM : 0 < M) (hb1 : 1 < b) (hb2 : b < 2)
    (hroot : M ^ 2 * b * (b - 1) = (2 - b) ^ 2) :
    (optimalCurve b).PeakFeasible ∧
    gramScore (optimalCurve b) M = b ^ 2 * (b - 1) ∧
    ∀ e : Curve, e.PeakFeasible → gramScore e M ≤ gramScore (optimalCurve b) M := by
  refine ⟨optimal_peak b (by linarith) (le_of_lt hb2),
    optimal_score M b hM hb1 hb2 hroot, ?_⟩
  intro e he
  rw [optimal_score M b hM hb1 hb2 hroot]
  exact quadratic_score_le e he M b hM hb1 hroot


/-- Cancellation-free closed form of the optimizer parameter. -/
def optimalParameter (M : ℝ) : ℝ :=
  2 * (Real.sqrt (M ^ 2 + 8) + M) / (Real.sqrt (M ^ 2 + 8) + 3 * M)

lemma radical_bound (M : ℝ) (hM : 0 < M) : M < Real.sqrt (M ^ 2 + 8) := by
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ M ^ 2 + 8)
  have hnonneg := Real.sqrt_nonneg (M ^ 2 + 8)
  nlinarith

theorem optimalParameter_bounds (M : ℝ) (hM : 0 < M) :
    1 < optimalParameter M ∧ optimalParameter M < 2 := by
  have hr := radical_bound M hM
  have hd : 0 < Real.sqrt (M ^ 2 + 8) + 3 * M := by positivity
  unfold optimalParameter
  constructor
  · apply (lt_div_iff₀ hd).2
    linarith
  · apply (div_lt_iff₀ hd).2
    linarith

theorem optimalParameter_root (M : ℝ) (hM : 0 < M) :
    M ^ 2 * optimalParameter M * (optimalParameter M - 1) =
      (2 - optimalParameter M) ^ 2 := by
  have hr := radical_bound M hM
  have hd : Real.sqrt (M ^ 2 + 8) + 3 * M ≠ 0 := by positivity
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ M ^ 2 + 8)
  unfold optimalParameter
  field_simp
  nlinarith only [congrArg (fun x : ℝ => 2 * M ^ 2 * x) hsq]

/-- The characterized parameter is unique on the relevant interval. -/
theorem root_unique (M b c : ℝ) (hM : 0 < M)
    (hb1 : 1 < b) (hb2 : b < 2) (hc1 : 1 < c) (hc2 : c < 2)
    (hb : M ^ 2 * b * (b - 1) = (2 - b) ^ 2)
    (hc : M ^ 2 * c * (c - 1) = (2 - c) ^ 2) : b = c := by
  have hsq : 0 < M ^ 2 := sq_pos_of_pos hM
  have hmono : ∀ x y : ℝ, 1 < x → x < y → y < 2 →
      M ^ 2 * x * (x - 1) < M ^ 2 * y * (y - 1) ∧
        (2 - y) ^ 2 < (2 - x) ^ 2 := by
    intro x y hx hxy hy
    have hsum : 0 < x + y - 1 := by linarith
    have hdiff : 0 < y - x := by linarith
    have hp := mul_pos hdiff hsum
    have hm := mul_pos hsq hp
    have hsum' : 0 < 4 - x - y := by linarith
    have hp' := mul_pos hdiff hsum'
    constructor <;> nlinarith
  rcases lt_trichotomy b c with hlt | heq | hgt
  · have hh := hmono b c hb1 hlt hc2
    nlinarith [hh.1, hh.2]
  · exact heq
  · have hh := hmono c b hc1 hgt hb2
    nlinarith [hh.1, hh.2]

/-- Existence, feasibility, value, and global optimality for every positive M. -/
theorem quadratic_optimal_closed_form (M : ℝ) (hM : 0 < M) :
    (optimalCurve (optimalParameter M)).PeakFeasible ∧
    gramScore (optimalCurve (optimalParameter M)) M =
      (optimalParameter M) ^ 2 * (optimalParameter M - 1) ∧
    ∀ e : Curve, e.PeakFeasible →
      gramScore e M ≤ gramScore (optimalCurve (optimalParameter M)) M := by
  have hb := optimalParameter_bounds M hM
  exact quadratic_optimal M (optimalParameter M) hM hb.1 hb.2
    (optimalParameter_root M hM)

/-- The stable formula equals the expression printed in the manuscript. -/
theorem optimalParameter_manuscript (M : ℝ) (hM : 0 < M) :
    optimalParameter M =
      2 / (1 - (M / 2) ^ 2 + (M / 2) * Real.sqrt ((M / 2) ^ 2 + 2)) := by
  have hr := radical_bound M hM
  have hd : Real.sqrt (M ^ 2 + 8) + 3 * M ≠ 0 := by positivity
  have hp : 0 < Real.sqrt (M ^ 2 + 8) + M := by positivity
  have hs := Real.sq_sqrt (by positivity : 0 ≤ M ^ 2 + 8)
  have hs' := Real.sq_sqrt (by positivity : 0 ≤ (M / 2) ^ 2 + 2)
  have hhalf : Real.sqrt ((M / 2) ^ 2 + 2) = Real.sqrt (M ^ 2 + 8) / 2 := by
    have hnonneg := Real.sqrt_nonneg ((M / 2) ^ 2 + 2)
    have hnonneg' := Real.sqrt_nonneg (M ^ 2 + 8)
    nlinarith
  rw [hhalf]
  have hi : (1 - (M / 2) ^ 2 + (M / 2) * (Real.sqrt (M ^ 2 + 8) / 2)) *
      (Real.sqrt (M ^ 2 + 8) + M) = Real.sqrt (M ^ 2 + 8) + 3 * M := by
    nlinarith only [congrArg (fun x : ℝ => M * x) hs]
  have hd' : 1 - (M / 2) ^ 2 + (M / 2) * (Real.sqrt (M ^ 2 + 8) / 2) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hi
    exact hd hi.symm
  unfold optimalParameter
  apply (div_eq_div_iff hd hd').2
  nlinarith only [hi]

end GeneralQuadratic
end Analog
