import Analog.Quadratic
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp

/-!
# The normalized planar quartic design problem

This module treats the complete continuum peak constraint and the algebraic
objective of the planar quartic family. It does not identify that objective
with an operational separation infimum, and does not assert encoder rigidity.
-/

noncomputable section

namespace Analog.Quartic

def denominator (r : ℝ) : ℝ := 1 + 2 * r + 9 * r ^ 2
def optA (r : ℝ) : ℝ := 8 * r / denominator r
def optb (r : ℝ) : ℝ := 2 / ((1 + r) * Real.sqrt (denominator r))
def optc (r : ℝ) : ℝ :=
  -(1 + 2 * r + 3 * r ^ 2) / ((1 + r) * Real.sqrt (denominator r))

def energy (A b c t : ℝ) : ℝ := A * t + (b * t ^ 2 + c) ^ 2
def PeakFeasible (A b c : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ 1 → energy A b c t ≤ 1
def objective (M A b : ℝ) : ℝ := M ^ 2 / A + 1 / b ^ 2

def RootEquation (M r : ℝ) : Prop :=
  8 * r ^ 2 * (1 + r) * (1 + 3 * r) = M ^ 2 * (1 - 3 * r)

theorem root_exists (M : ℝ) (hM : 0 < M) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 3 ∧ RootEquation M r := by
  let f : ℝ → ℝ := fun r =>
    8 * r ^ 2 * (1 + r) * (1 + 3 * r) - M ^ 2 * (1 - 3 * r)
  have hf : Continuous f := by
    unfold f
    fun_prop
  have h0 : f 0 < 0 := by dsimp [f]; nlinarith [sq_pos_of_pos hM]
  have hthird : 0 < f (1 / 3) := by dsimp [f]; norm_num
  obtain ⟨r, hr, heq⟩ := intermediate_value_Ioo
    (by norm_num : (0 : ℝ) ≤ 1 / 3) hf.continuousOn ⟨h0, hthird⟩
  refine ⟨r, hr.1, hr.2, ?_⟩
  dsimp [f] at heq
  dsimp [RootEquation]
  linarith

theorem root_unique (M x y : ℝ) (hM : 0 < M)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hex : RootEquation M x) (hey : RootEquation M y) : x = y := by
  have hstrict : ∀ a b : ℝ, 0 ≤ a → a < b →
      8 * a ^ 2 * (1 + a) * (1 + 3 * a) - M ^ 2 * (1 - 3 * a) <
      8 * b ^ 2 * (1 + b) * (1 + 3 * b) - M ^ 2 * (1 - 3 * b) := by
    intro a b ha hab
    have h2 := pow_le_pow_left₀ ha hab.le 2
    have h3 := pow_le_pow_left₀ ha hab.le 3
    have h4 := pow_le_pow_left₀ ha hab.le 4
    have hp : 0 < M ^ 2 * (b - a) := mul_pos (sq_pos_of_pos hM) (sub_pos.mpr hab)
    nlinarith only [h2, h3, h4, hp]
  rcases lt_trichotomy x y with h | h | h
  · have hs := hstrict x y hx h
    dsimp [RootEquation] at hex hey
    linarith
  · exact h
  · have hs := hstrict y x hy h
    dsimp [RootEquation] at hex hey
    linarith

theorem root_exists_unique (M : ℝ) (hM : 0 < M) :
    ∃! r : ℝ, 0 < r ∧ r < 1 / 3 ∧ RootEquation M r := by
  obtain ⟨r, hr, hrthird, heq⟩ := root_exists M hM
  refine ⟨r, ⟨hr, hrthird, heq⟩, ?_⟩
  intro y hy
  exact root_unique M y r hM hy.1.le hr.le hy.2.2 heq

lemma denominator_pos (r : ℝ) (hr : 0 < r) : 0 < denominator r := by
  dsimp [denominator]
  positivity

lemma coefficient_pos (r : ℝ) (hr : 0 < r) : 0 < optA r ∧ 0 < optb r := by
  have hd := denominator_pos r hr
  dsimp [optA, optb]
  constructor <;> positivity

lemma coefficient_relations (r : ℝ) (hr : 0 < r) :
    optb r ^ 2 * (1 + r) ^ 2 * denominator r = 4 ∧
    optA r = 2 * optb r ^ 2 * r * (1 + r) ^ 2 ∧
    optc r = -optb r * (1 + 2 * r + 3 * r ^ 2) / 2 := by
  have hd := denominator_pos r hr
  have hdne := ne_of_gt hd
  have hspos : 0 < Real.sqrt (denominator r) := Real.sqrt_pos.mpr hd
  have hsne := ne_of_gt hspos
  have hsq := Real.sq_sqrt hd.le
  have hp : (1 + r) ≠ 0 := by positivity
  constructor
  · dsimp [optb]
    field_simp
    nlinarith only [hsq]
  constructor
  · dsimp [optA, optb]
    field_simp
    nlinarith only [hsq]
  · dsimp [optc, optb]
    ring

/-- Polynomial certificate for every point on the interval. -/
theorem peak_identity (r t : ℝ) (hr : 0 < r) :
    1 - energy (optA r) (optb r) (optc r) t =
      optb r ^ 2 * (1 - t) * (t - r) ^ 2 * (t + 1 + 2 * r) := by
  obtain ⟨hb, hA, hc⟩ := coefficient_relations r hr
  dsimp [denominator] at hb
  rw [energy, hA, hc]
  nlinarith only [hb]

theorem optimal_peak (r : ℝ) (hr : 0 < r) :
    PeakFeasible (optA r) (optb r) (optc r) := by
  intro t ht0 ht1
  have hi := peak_identity r t hr
  have hprod : 0 ≤ optb r ^ 2 * (1 - t) * (t - r) ^ 2 * (t + 1 + 2 * r) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith))
      (sq_nonneg _)) (by linarith)
  linarith

theorem optimal_contacts (r : ℝ) (hr : 0 < r) :
    energy (optA r) (optb r) (optc r) r = 1 ∧
    energy (optA r) (optb r) (optc r) 1 = 1 := by
  have h0 := peak_identity r r hr
  have h1 := peak_identity r 1 hr
  constructor <;> nlinarith only [h0, h1]

lemma reciprocal_tangent (m A A₀ : ℝ) (hm : 0 ≤ m)
    (hA : 0 < A) (hA₀ : 0 < A₀) :
    m / A₀ - m / A₀ ^ 2 * (A - A₀) ≤ m / A := by
  have hi : m / A - (m / A₀ - m / A₀ ^ 2 * (A - A₀)) =
      m * (A - A₀) ^ 2 / (A * A₀ ^ 2) := by
    field_simp
    ring
  have hn : 0 ≤ m * (A - A₀) ^ 2 / (A * A₀ ^ 2) := by positivity
  linarith

lemma reciprocal_square_tangent (b b₀ : ℝ) (hb : 0 < b) (hb₀ : 0 < b₀) :
    1 / b₀ ^ 2 - 2 / b₀ ^ 3 * (b - b₀) ≤ 1 / b ^ 2 := by
  have hi : 1 / b ^ 2 - (1 / b₀ ^ 2 - 2 / b₀ ^ 3 * (b - b₀)) =
      (b - b₀) ^ 2 * (2 * b + b₀) / (b₀ ^ 3 * b ^ 2) := by
    field_simp
    ring
  have hn : 0 ≤ (b - b₀) ^ 2 * (2 * b + b₀) / (b₀ ^ 3 * b ^ 2) := by
    positivity
  linarith

lemma contact_tangent (A b c A₀ b₀ c₀ t : ℝ)
    (hc : energy A₀ b₀ c₀ t = 1) (hp : energy A b c t ≤ 1) :
    (A - A₀) * t + 2 * (b₀ * t ^ 2 + c₀) *
      ((b - b₀) * t ^ 2 + c - c₀) ≤ 0 := by
  dsimp [energy] at hc hp
  nlinarith only [hc, hp, sq_nonneg ((b - b₀) * t ^ 2 + c - c₀)]

/-- An elementary sufficient certificate, proved using exact rational tangent
identities rather than invoking an unformalized convex-optimization argument. -/
theorem two_contact_certificate (M A₀ b₀ c₀ r η ζ : ℝ)
    (hA₀ : 0 < A₀) (hb₀ : 0 < b₀) (hη : 0 ≤ η) (hζ : 0 ≤ ζ)
    (hc₀ : energy A₀ b₀ c₀ r = 1) (hc₁ : energy A₀ b₀ c₀ 1 = 1)
    (hsA : -M ^ 2 / A₀ ^ 2 + η * r + ζ = 0)
    (hsb : -2 / b₀ ^ 3 + 2 * η * (b₀ * r ^ 2 + c₀) * r ^ 2 +
      2 * ζ * (b₀ + c₀) = 0)
    (hsc : 2 * η * (b₀ * r ^ 2 + c₀) + 2 * ζ * (b₀ + c₀) = 0)
    (A b c : ℝ) (hA : 0 < A) (hb : 0 < b)
    (hpr : energy A b c r ≤ 1) (hp1 : energy A b c 1 ≤ 1) :
    objective M A₀ b₀ ≤ objective M A b := by
  have htA := reciprocal_tangent (M ^ 2) A A₀ (sq_nonneg M) hA hA₀
  have htb := reciprocal_square_tangent b b₀ hb hb₀
  have htr := mul_le_mul_of_nonneg_left
    (contact_tangent A b c A₀ b₀ c₀ r hc₀ hpr) hη
  have ht1 := mul_le_mul_of_nonneg_left
    (contact_tangent A b c A₀ b₀ c₀ 1 hc₁ hp1) hζ
  have hi : -M ^ 2 / A₀ ^ 2 * (A - A₀) - 2 / b₀ ^ 3 * (b - b₀) +
      η * ((A - A₀) * r + 2 * (b₀ * r ^ 2 + c₀) *
        ((b - b₀) * r ^ 2 + c - c₀)) +
      ζ * ((A - A₀) * 1 + 2 * (b₀ * 1 ^ 2 + c₀) *
        ((b - b₀) * 1 ^ 2 + c - c₀)) = 0 := by
    calc
      _ = (-M ^ 2 / A₀ ^ 2 + η * r + ζ) * (A - A₀) +
          (-2 / b₀ ^ 3 + 2 * η * (b₀ * r ^ 2 + c₀) * r ^ 2 +
            2 * ζ * (b₀ + c₀)) * (b - b₀) +
          (2 * η * (b₀ * r ^ 2 + c₀) + 2 * ζ * (b₀ + c₀)) * (c - c₀) := by ring
      _ = 0 := by rw [hsA, hsb, hsc]; ring
  dsimp [objective]
  simp only [mul_zero] at htr ht1
  simp only [neg_div] at hi
  nlinarith only [htA, htb, hi, htr, ht1]

def multiplierR (r : ℝ) : ℝ :=
  2 / (optb r ^ 4 * (1 + r) ^ 3 * (1 - r))
def multiplierOne (r : ℝ) : ℝ :=
  multiplierR r * (1 + r) / (1 - 3 * r)

theorem multipliers_pos (r : ℝ) (hr : 0 < r) (hrthird : r < 1 / 3) :
    0 < multiplierR r ∧ 0 < multiplierOne r := by
  have hb := (coefficient_pos r hr).2
  have h1 : 0 < 1 - r := by linarith
  have h3 : 0 < 1 - 3 * r := by linarith
  have hη : 0 < multiplierR r := by dsimp [multiplierR]; positivity
  refine ⟨hη, ?_⟩
  dsimp [multiplierOne]
  positivity

/-- All three stationarity equations follow by substitution of the explicit
coefficients and the already well-posed scalar root equation. -/
theorem stationarity (M r : ℝ) (hr : 0 < r) (hrthird : r < 1 / 3)
    (hroot : RootEquation M r) :
    -M ^ 2 / optA r ^ 2 + multiplierR r * r + multiplierOne r = 0 ∧
    -2 / optb r ^ 3 + 2 * multiplierR r * (optb r * r ^ 2 + optc r) * r ^ 2 +
      2 * multiplierOne r * (optb r + optc r) = 0 ∧
    2 * multiplierR r * (optb r * r ^ 2 + optc r) +
      2 * multiplierOne r * (optb r + optc r) = 0 := by
  have hbn := ne_of_gt (coefficient_pos r hr).2
  have hrn := ne_of_gt hr
  have hplus : (1 + r) ≠ 0 := by positivity
  have hminus : (1 - r) ≠ 0 := by linarith
  have hthree : (1 - 3 * r) ≠ 0 := by linarith
  have hthree' : (1 - r * 3) ≠ 0 := by linarith
  obtain ⟨_, hA, hc⟩ := coefficient_relations r hr
  have hM : M ^ 2 = 8 * r ^ 2 * (1 + r) * (1 + 3 * r) / (1 - 3 * r) := by
    apply (eq_div_iff hthree).2
    exact hroot.symm
  rw [hM, hA, hc]
  dsimp [multiplierOne, multiplierR]
  constructor
  · field_simp [hbn, hrn, hplus, hminus, hthree]
    ring_nf
  constructor <;>
    (field_simp [hbn, hrn, hplus, hminus, hthree]; ring_nf)

/-- Global objective converse using only the two peak constraints at the
active contacts. Every competitor satisfying the continuum is covered. -/
theorem objective_optimal (M r : ℝ) (hr : 0 < r) (hrthird : r < 1 / 3)
    (hroot : RootEquation M r) (A b c : ℝ) (hA : 0 < A) (hb : 0 < b)
    (hpeak : PeakFeasible A b c) :
    objective M (optA r) (optb r) ≤ objective M A b := by
  obtain ⟨hA₀, hb₀⟩ := coefficient_pos r hr
  obtain ⟨hη, hζ⟩ := multipliers_pos r hr hrthird
  obtain ⟨hcr, hc1⟩ := optimal_contacts r hr
  obtain ⟨hsA, hsb, hsc⟩ := stationarity M r hr hrthird hroot
  apply two_contact_certificate M (optA r) (optb r) (optc r) r
    (multiplierR r) (multiplierOne r) hA₀ hb₀ hη.le hζ.le
    hcr hc1 hsA hsb hsc A b c hA hb
  · exact hpeak r hr.le (by linarith)
  · exact hpeak 1 (by norm_num) (by norm_num)

/-- The explicit feasible curve globally minimizes the normalized algebraic
objective among all positive orthogonal quartic coefficient choices. -/
theorem quartic_orthogonal_optimal (M : ℝ) (hM : 0 < M) :
    ∃ r : ℝ, (0 < r ∧ r < 1 / 3 ∧ RootEquation M r) ∧
      PeakFeasible (optA r) (optb r) (optc r) ∧
      ∀ A b c : ℝ, 0 < A → 0 < b → PeakFeasible A b c →
        objective M (optA r) (optb r) ≤ objective M A b := by
  obtain ⟨r, hr, hrthird, hroot⟩ := root_exists M hM
  refine ⟨r, ⟨hr, hrthird, hroot⟩, optimal_peak r hr, ?_⟩
  intro A b c hA hb hpeak
  exact objective_optimal M r hr hrthird hroot A b c hA hb hpeak

/-- The amplitude convention in the paper is a = sqrt A. This statement
expresses peak feasibility directly in the original source variable s. -/
theorem optimal_encoder_peak (r : ℝ) (hr : 0 < r) (s : ℝ)
    (hslo : -1 ≤ s) (hshi : s ≤ 1) :
    (Real.sqrt (optA r) * s) ^ 2 + (optb r * s ^ 4 + optc r) ^ 2 ≤ 1 := by
  have hs : s ^ 2 ≤ 1 := by nlinarith
  have hp := optimal_peak r hr (s ^ 2) (sq_nonneg s) hs
  have hA := (coefficient_pos r hr).1
  rw [mul_pow, Real.sq_sqrt hA.le]
  dsimp [energy] at hp
  convert hp using 1
  ring

/-- Closed form of the normalized objective at the explicit coefficients. -/
theorem optimal_objective (M r : ℝ) (hr : 0 < r) :
    objective M (optA r) (optb r) =
      denominator r * (M ^ 2 + 2 * r * (1 + r) ^ 2) / (8 * r) := by
  have hd := denominator_pos r hr
  have hb := (coefficient_relations r hr).1
  have hden : (1 + r) ^ 2 * denominator r ≠ 0 := by positivity
  have hb2 : optb r ^ 2 = 4 / ((1 + r) ^ 2 * denominator r) := by
    apply (eq_div_iff hden).2
    nlinarith only [hb]
  dsimp [objective, optA]
  rw [hb2]
  field_simp
  ring

/-- Closed form of the reciprocal objective, the paper's reduced Gram score. -/
theorem optimal_score (M r : ℝ) (hr : 0 < r) :
    1 / objective M (optA r) (optb r) =
      8 * r / (denominator r * (M ^ 2 + 2 * r * (1 + r) ^ 2)) := by
  rw [optimal_objective M r hr, one_div_div]

/-- The reciprocal algebraic score is maximal throughout the normalized
orthogonal quartic class, with the exact value displayed in the paper. -/
theorem score_optimal (M r : ℝ) (hr : 0 < r) (hrthird : r < 1 / 3)
    (hroot : RootEquation M r) (A b c : ℝ) (hA : 0 < A) (hb : 0 < b)
    (hpeak : PeakFeasible A b c) :
    1 / objective M A b ≤
      8 * r / (denominator r * (M ^ 2 + 2 * r * (1 + r) ^ 2)) := by
  rw [← optimal_score M r hr]
  have hoptpos : 0 < objective M (optA r) (optb r) := by
    obtain ⟨hA₀, hb₀⟩ := coefficient_pos r hr
    dsimp [objective]
    positivity
  have hpos : 0 < objective M A b := by dsimp [objective]; positivity
  apply (div_le_div_iff₀ hpos hoptpos).2
  simpa only [one_mul] using objective_optimal M r hr hrthird hroot A b c hA hb hpeak

/-! ## Reduction of every planar quartic curve to the orthogonal family -/

/-- Reuse the six real coefficient fields, now with feature s^4. -/
def curveEnergy (e : Analog.Curve) (s : ℝ) : ℝ :=
  (e.cx + e.ux * s + e.vx * s ^ 4) ^ 2 +
  (e.cy + e.uy * s + e.vy * s ^ 4) ^ 2

def CurvePeakFeasible (e : Analog.Curve) : Prop :=
  ∀ s : ℝ, -1 ≤ s → s ≤ 1 → curveEnergy e s ≤ 1

/-- Algebraic Gram score for endpoint slopes ±M. -/
def curveScore (M : ℝ) (e : Analog.Curve) : ℝ :=
  (e.A * e.B - e.C ^ 2) / (e.A + M ^ 2 * e.B + 2 * M * |e.C|)

def projectedTranslation (e : Analog.Curve) : ℝ :=
  (e.cx * e.vx + e.cy * e.vy) / Real.sqrt e.B

lemma projection_square_le (x y u v b : ℝ) (hb : 0 < b)
    (hb2 : b ^ 2 = u ^ 2 + v ^ 2) :
    ((u * x + v * y) / b) ^ 2 ≤ x ^ 2 + y ^ 2 := by
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hb)).2
  rw [hb2]
  nlinarith only [sq_nonneg (x * v - y * u)]

lemma averaged_peak (e : Analog.Curve) (hpeak : CurvePeakFeasible e)
    (s : ℝ) (hslo : -1 ≤ s) (hshi : s ≤ 1) :
    e.A * s ^ 2 + (e.cx + e.vx * s ^ 4) ^ 2 +
      (e.cy + e.vy * s ^ 4) ^ 2 ≤ 1 := by
  have hp := hpeak s hslo hshi
  have hm := hpeak (-s) (by linarith) (by linarith)
  dsimp [curveEnergy] at hp hm
  dsimp [Analog.Curve.A]
  nlinarith only [hp, hm]

/-- Averaging the two source signs and projecting the translation preserves
A and B, removes correlation, and satisfies every peak constraint. -/
theorem orthogonal_reduction (e : Analog.Curve) (hpeak : CurvePeakFeasible e)
    (hB : 0 < e.B) :
    PeakFeasible e.A (Real.sqrt e.B) (projectedTranslation e) := by
  have hb : 0 < Real.sqrt e.B := Real.sqrt_pos.mpr hB
  have hbn := ne_of_gt hb
  have hb2 := Real.sq_sqrt hB.le
  intro t ht0 ht1
  have hs0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hs2 : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht0
  have hslo : -1 ≤ Real.sqrt t := by linarith
  have hshi : Real.sqrt t ≤ 1 := by nlinarith only [hs2, hs0, ht1]
  have hs4 : (Real.sqrt t) ^ 4 = t ^ 2 := by
    calc
      _ = ((Real.sqrt t) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hs2]
  have hav := averaged_peak e hpeak (Real.sqrt t) hslo hshi
  rw [hs2, hs4] at hav
  have hproj := projection_square_le (e.cx + e.vx * t ^ 2)
    (e.cy + e.vy * t ^ 2) e.vx e.vy (Real.sqrt e.B) hb hb2
  have hi : Real.sqrt e.B * t ^ 2 + projectedTranslation e =
      (e.vx * (e.cx + e.vx * t ^ 2) + e.vy * (e.cy + e.vy * t ^ 2)) /
        Real.sqrt e.B := by
    apply (eq_div_iff hbn).2
    dsimp [projectedTranslation]
    calc
      _ = (Real.sqrt e.B) ^ 2 * t ^ 2 + (e.cx * e.vx + e.cy * e.vy) := by
        rw [add_mul, div_mul_cancel₀ _ hbn]
        ring
      _ = _ := by rw [hb2]; dsimp [Analog.Curve.B]; ring
  dsimp [energy]
  rw [hi]
  linarith only [hav, hproj]

lemma remove_correlation (M A B C : ℝ) (hM : 0 < M) (hA : 0 < A) (hB : 0 < B) :
    (A * B - C ^ 2) / (A + M ^ 2 * B + 2 * M * |C|) ≤
      A * B / (A + M ^ 2 * B) := by
  have hd : 0 < A + M ^ 2 * B := by positivity
  have hd' : 0 < A + M ^ 2 * B + 2 * M * |C| := by positivity
  apply (div_le_div_iff₀ hd' hd).2
  have hcorr : 0 ≤ C ^ 2 * (A + M ^ 2 * B) := by positivity
  have hincrease : 0 ≤ A * B * (2 * M * |C|) := by positivity
  nlinarith only [hcorr, hincrease]

lemma orthogonal_score_identity (M A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    A * B / (A + M ^ 2 * B) = 1 / objective M A (Real.sqrt B) := by
  have hb2 := Real.sq_sqrt hB.le
  have hd : A + M ^ 2 * B ≠ 0 := by positivity
  have hobj : M ^ 2 / A + 1 / B ≠ 0 := by positivity
  dsimp [objective]
  rw [hb2]
  field_simp
  ring

lemma degenerate_score_nonpos (M : ℝ) (hM : 0 < M) (e : Analog.Curve)
    (hdeg : e.A = 0 ∨ e.B = 0) : curveScore M e ≤ 0 := by
  have hA : 0 ≤ e.A := by dsimp [Analog.Curve.A]; positivity
  have hB : 0 ≤ e.B := by dsimp [Analog.Curve.B]; positivity
  have hden : 0 ≤ e.A + M ^ 2 * e.B + 2 * M * |e.C| := by positivity
  dsimp [curveScore]
  apply div_nonpos_of_nonpos_of_nonneg _ hden
  rcases hdeg with h | h
  · rw [h]; nlinarith only [sq_nonneg e.C]
  · rw [h]; nlinarith only [sq_nonneg e.C]

/-- Global converse for every peak-feasible planar quartic curve. The result
includes arbitrary translation, correlation, orientation, and degeneracy. -/
theorem quartic_curve_score_le (M r : ℝ) (hM : 0 < M)
    (hr : 0 < r) (hrthird : r < 1 / 3) (hroot : RootEquation M r)
    (e : Analog.Curve) (hpeak : CurvePeakFeasible e) :
    curveScore M e ≤
      8 * r / (denominator r * (M ^ 2 + 2 * r * (1 + r) ^ 2)) := by
  have hA0 : 0 ≤ e.A := by dsimp [Analog.Curve.A]; positivity
  have hB0 : 0 ≤ e.B := by dsimp [Analog.Curve.B]; positivity
  have hvalue : 0 ≤ 8 * r / (denominator r * (M ^ 2 + 2 * r * (1 + r) ^ 2)) := by
    have hd := denominator_pos r hr
    positivity
  by_cases hA : 0 < e.A
  · by_cases hB : 0 < e.B
    · calc
        curveScore M e ≤ e.A * e.B / (e.A + M ^ 2 * e.B) :=
          remove_correlation M e.A e.B e.C hM hA hB
        _ = 1 / objective M e.A (Real.sqrt e.B) := orthogonal_score_identity M e.A e.B hA hB
        _ ≤ _ := score_optimal M r hr hrthird hroot e.A (Real.sqrt e.B)
          (projectedTranslation e) hA (Real.sqrt_pos.mpr hB) (orthogonal_reduction e hpeak hB)
    · have hBzero : e.B = 0 := by linarith
      exact (degenerate_score_nonpos M hM e (Or.inr hBzero)).trans hvalue
  · have hAzero : e.A = 0 := by linarith
    exact (degenerate_score_nonpos M hM e (Or.inl hAzero)).trans hvalue

def optimalPlanarCurve (r : ℝ) : Analog.Curve where
  cx := 0
  cy := optc r
  ux := Real.sqrt (optA r)
  uy := 0
  vx := 0
  vy := optb r

theorem optimal_planar_peak (r : ℝ) (hr : 0 < r) :
    CurvePeakFeasible (optimalPlanarCurve r) := by
  intro s hslo hshi
  simpa [curveEnergy, optimalPlanarCurve, add_comm] using
    optimal_encoder_peak r hr s hslo hshi

theorem optimal_planar_score (M r : ℝ) (hr : 0 < r) :
    curveScore M (optimalPlanarCurve r) =
      8 * r / (denominator r * (M ^ 2 + 2 * r * (1 + r) ^ 2)) := by
  obtain ⟨hApos, hbpos⟩ := coefficient_pos r hr
  have hA : (optimalPlanarCurve r).A = optA r := by
    dsimp [Analog.Curve.A, optimalPlanarCurve]
    rw [Real.sq_sqrt hApos.le]
    ring
  have hB : (optimalPlanarCurve r).B = optb r ^ 2 := by
    simp [Analog.Curve.B, optimalPlanarCurve]
  have hC : (optimalPlanarCurve r).C = 0 := by
    simp [Analog.Curve.C, optimalPlanarCurve]
  dsimp [curveScore]
  rw [hA, hB, hC]
  simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, abs_zero, mul_zero, add_zero]
  have hi := orthogonal_score_identity M (optA r) (optb r ^ 2) hApos (sq_pos_of_pos hbpos)
  rw [Real.sqrt_sq hbpos.le] at hi
  rw [hi]
  exact optimal_score M r hr

/-- The full normalized finite-dimensional quartic Gram-score optimum.
The universal quantifier ranges over every planar quartic coefficient curve,
and its constraint covers every real source value in [-1,1]. -/
theorem quartic_planar_optimal (M : ℝ) (hM : 0 < M) :
    ∃ r : ℝ, (0 < r ∧ r < 1 / 3 ∧ RootEquation M r) ∧
      CurvePeakFeasible (optimalPlanarCurve r) ∧
      curveScore M (optimalPlanarCurve r) =
        8 * r / (denominator r * (M ^ 2 + 2 * r * (1 + r) ^ 2)) ∧
      ∀ e : Analog.Curve, CurvePeakFeasible e →
        curveScore M e ≤ curveScore M (optimalPlanarCurve r) := by
  obtain ⟨r, hr, hrthird, hroot⟩ := root_exists M hM
  refine ⟨r, ⟨hr, hrthird, hroot⟩, optimal_planar_peak r hr,
    optimal_planar_score M r hr, ?_⟩
  intro e hpeak
  rw [optimal_planar_score M r hr]
  exact quartic_curve_score_le M r hM hr hrthird hroot e hpeak

end Analog.Quartic
