import Analog.Quadratic
import Analog.VarianceCollision
import Analog.Operational
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Operational variance separation for quadratic planar encoders

This file connects the quadratic coefficient representation to actual finite
lists of channel inputs. In particular, its separation result is a uniform
inequality for every pair of admissible source tuples.
-/

noncomputable section

namespace Analog

def Curve.encoder (e : Curve) (s : ℝ) : ℝ × ℝ :=
  (e.cx + e.ux * s + e.vx * s ^ 2,
    e.cy + e.uy * s + e.vy * s ^ 2)

open ArbitraryEncoder

lemma Curve.received_encoder (e : Curve) (xs : List ℝ) :
    received e.encoder xs =
      ((xs.length : ℝ) * e.cx + e.ux * firstMoment xs + e.vx * secondMoment xs,
       (xs.length : ℝ) * e.cy + e.uy * firstMoment xs + e.vy * secondMoment xs) := by
  induction xs with
  | nil => simp [received, firstMoment, secondMoment]; rfl
  | cons x xs ih =>
    simp only [received, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    apply Prod.ext <;>
      simp [Curve.encoder, firstMoment, secondMoment, Nat.cast_add, Nat.cast_one] <;> ring

lemma Curve.received_squaredDistance (e : Curve) {K : ℕ} (xs ys : List ℝ)
    (hx : ValidInput K xs) (hy : ValidInput K ys) :
    squaredDistance (received e.encoder xs) (received e.encoder ys) =
      e.A * (firstMoment xs - firstMoment ys) ^ 2 +
      2 * e.C * (firstMoment xs - firstMoment ys) *
        (secondMoment xs - secondMoment ys) +
      e.B * (secondMoment xs - secondMoment ys) ^ 2 := by
  rw [e.received_encoder, e.received_encoder]
  rw [hx.1, hy.1]
  dsimp [squaredDistance, Curve.A, Curve.B, Curve.C]
  ring

lemma firstMoment_bounds (xs : List ℝ)
    (h : ∀ x ∈ xs, InSource x) :
    -(xs.length : ℝ) ≤ firstMoment xs ∧ firstMoment xs ≤ (xs.length : ℝ) := by
  induction xs with
  | nil => simp [firstMoment]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hi := ih (fun t ht => h t (by simp [ht]))
    simp only [firstMoment, List.sum_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one] at *
    constructor <;> linarith [hx.1, hx.2, hi.1, hi.2]

lemma quadratic_dual_identity (A B C x y q : ℝ) :
    (A + 2 * q * C + q ^ 2 * B) * (A * x ^ 2 + 2 * C * x * y + B * y ^ 2) -
      (A * B - C ^ 2) * (y - q * x) ^ 2 =
        ((A + q * C) * x + (C + q * B) * y) ^ 2 := by ring

lemma Curve.denominator_pos (e : Curve) (hdet : 0 < e.A * e.B - e.C ^ 2) :
    0 < e.A + 4 * e.B + 4 * |e.C| := by
  have ha : 0 ≤ e.A := by dsimp [Curve.A]; positivity
  have hb : 0 ≤ e.B := by dsimp [Curve.B]; positivity
  have hab : 0 < e.A * e.B := by nlinarith [sq_nonneg e.C]
  have ha' : 0 < e.A := by nlinarith
  positivity

lemma Curve.dual_bound (e : Curve) (q : ℝ) (hq : -2 ≤ q ∧ q ≤ 2) :
    e.A + 2 * q * e.C + q ^ 2 * e.B ≤ e.A + 4 * e.B + 4 * |e.C| := by
  have hb : 0 ≤ e.B := by dsimp [Curve.B]; positivity
  have hq2 : q ^ 2 ≤ 4 := by nlinarith
  have hqabs : |q| ≤ 2 := abs_le.mpr hq
  have hc : q * e.C ≤ 2 * |e.C| := calc
    q * e.C ≤ |q * e.C| := le_abs_self _
    _ = |q| * |e.C| := abs_mul _ _
    _ ≤ 2 * |e.C| := mul_le_mul_of_nonneg_right hqabs (abs_nonneg _)
  have hbq := mul_le_mul_of_nonneg_right hq2 hb
  linarith

/-- The Gram score yields a lower bound on the actual channel separation for
every pair of source lists, with the correct K² normalization. -/
theorem Curve.variance_separation_lower_bound (e : Curve) {K : ℕ} (hK : 0 < K)
    (hdet : 0 < e.A * e.B - e.C ^ 2) :
    SeparationLowerBound K e.encoder ((K : ℝ) ^ 2 * e.score) := by
  intro xs ys hxs hys
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hk0 : (K : ℝ) ≠ 0 := ne_of_gt hk
  have hx := firstMoment_bounds xs hxs.2
  have hy := firstMoment_bounds ys hys.2
  rw [hxs.1] at hx
  rw [hys.1] at hy
  let x := firstMoment xs - firstMoment ys
  let y := secondMoment xs - secondMoment ys
  let q := (firstMoment xs + firstMoment ys) / (K : ℝ)
  have hq : -2 ≤ q ∧ q ≤ 2 := by
    constructor
    · apply (le_div_iff₀ hk).2
      linarith [hx.1, hy.1]
    · apply (div_le_iff₀ hk).2
      linarith [hx.2, hy.2]
  have hv : variance K xs - variance K ys = (y - q * x) / (K : ℝ) := by
    dsimp [variance, x, y, q]
    field_simp
    ring
  have hn : 0 ≤ e.A * x ^ 2 + 2 * e.C * x * y + e.B * y ^ 2 := by
    have he : e.A * x ^ 2 + 2 * e.C * x * y + e.B * y ^ 2 =
        (e.ux * x + e.vx * y) ^ 2 + (e.uy * x + e.vy * y) ^ 2 := by
      dsimp [Curve.A, Curve.B, Curve.C]
      ring
    rw [he]
    positivity
  have hid := quadratic_dual_identity e.A e.B e.C x y q
  have hdual := e.dual_bound q hq
  have hmul := mul_le_mul_of_nonneg_right hdual hn
  have hcert : (e.A * e.B - e.C ^ 2) * (y - q * x) ^ 2 ≤
      (e.A + 4 * e.B + 4 * |e.C|) *
        (e.A * x ^ 2 + 2 * e.C * x * y + e.B * y ^ 2) := by
    nlinarith only [hid, hmul,
      sq_nonneg ((e.A + q * e.C) * x + (e.C + q * e.B) * y)]
  rw [hv, e.received_squaredDistance xs ys hxs hys]
  change (K : ℝ) ^ 2 * e.score * ((y - q * x) / (K : ℝ)) ^ 2 ≤
    e.A * x ^ 2 + 2 * e.C * x * y + e.B * y ^ 2
  have hs : (K : ℝ) ^ 2 * e.score * ((y - q * x) / (K : ℝ)) ^ 2 =
      ((e.A * e.B - e.C ^ 2) * (y - q * x) ^ 2) /
        (e.A + 4 * e.B + 4 * |e.C|) := by
    dsimp [Curve.score]
    field_simp
  rw [hs]
  apply (div_le_iff₀ (e.denominator_pos hdet)).2
  nlinarith only [hcert]

private lemma small_step {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    ∃ t : ℝ, 0 < t ∧ |t * a| ≤ r ∧ |t * b| ≤ r ∧ t ≤ r := by
  have hd : 0 < |a| + |b| + 1 := by positivity
  refine ⟨r / (|a| + |b| + 1), div_pos hr hd, ?_, ?_, ?_⟩
  · rw [abs_mul, abs_of_pos (div_pos hr hd), div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).2
    nlinarith [abs_nonneg b]
  · rw [abs_mul, abs_of_pos (div_pos hr hd), div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).2
    nlinarith [abs_nonneg a]
  · apply (div_le_iff₀ hd).2
    nlinarith [abs_nonneg a, abs_nonneg b]

private def pairInput (K : ℕ) (m r t a b : ℝ) : List ℝ :=
  (m - r + t * a) :: (m + r + t * b) :: List.replicate (K - 2) m

private lemma pairInput_valid {K : ℕ} (hK : 2 ≤ K) (m r t a b : ℝ)
    (hm : -1 < m ∧ m < 1) (hr : 0 < r) (hmr : |m| + 2 * r = 1)
    (ha : |t * a| ≤ r) (hb : |t * b| ≤ r) :
    ValidInput K (pairInput K m r t a b) := by
  constructor
  · simp only [pairInput, List.length_cons, List.length_replicate]
    omega
  · intro z hz
    simp only [pairInput, List.mem_cons, List.mem_replicate] at hz
    have ha' := abs_le.mp ha
    have hb' := abs_le.mp hb
    have hml := neg_abs_le m
    have hmu := le_abs_self m
    rcases hz with rfl | rfl | ⟨_, rfl⟩
    · constructor <;> linarith [ha'.1, ha'.2]
    · constructor <;> linarith [hb'.1, hb'.2]
    · exact ⟨hm.1.le, hm.2.le⟩

private lemma pairInput_firstMoment {K : ℕ} (hK : 2 ≤ K) (m r t a b : ℝ) :
    firstMoment (pairInput K m r t a b) = (K : ℝ) * m + t * (a + b) := by
  have hk : ((K - 2 : ℕ) : ℝ) + 2 = (K : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hK
  simp [pairInput, firstMoment, List.sum_replicate, nsmul_eq_mul]
  nlinarith only [congrArg (fun z : ℝ => z * m) hk]

private lemma pairInput_secondMoment {K : ℕ} (hK : 2 ≤ K) (m r t a b : ℝ) :
    secondMoment (pairInput K m r t a b) = (K : ℝ) * m ^ 2 + 2 * r ^ 2 +
      2 * t * ((m - r) * a + (m + r) * b) + t ^ 2 * (a ^ 2 + b ^ 2) := by
  have hk : ((K - 2 : ℕ) : ℝ) + 2 = (K : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hK
  simp only [pairInput, secondMoment, List.map_cons, List.map_replicate,
    List.sum_cons, List.sum_replicate, nsmul_eq_mul]
  calc
    _ = (((K - 2 : ℕ) : ℝ) + 2) * m ^ 2 + 2 * r ^ 2 +
      2 * t * ((m - r) * a + (m + r) * b) + t ^ 2 * (a ^ 2 + b ^ 2) := by ring
    _ = _ := by rw [hk]

/-- Symmetric perturbations of two unequal inputs realize every infinitesimal
moment direction with an exact finite difference. No derivative or attainable
moment-set assumption occurs in this construction. -/
lemma realize_moment_direction_small {K : ℕ} (hK : 2 ≤ K) (m x y eta : ℝ)
    (hm : -1 < m ∧ m < 1) (heta : 0 < eta) :
    ∃ (t : ℝ) (xs ys : List ℝ), 0 < t ∧ t < eta ∧ ValidInput K xs ∧ ValidInput K ys ∧
      firstMoment xs - firstMoment ys = t * x ∧
      secondMoment xs - secondMoment ys = t * y ∧
      firstMoment xs + firstMoment ys = 2 * (K : ℝ) * m := by
  let r := (1 - |m|) / 2
  have hmabs : |m| < 1 := abs_lt.mpr hm
  have hr : 0 < r := by dsimp [r]; linarith
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hmr : |m| + 2 * r = 1 := by dsimp [r]; ring
  let a := x / 4 - (y - 2 * m * x) / (8 * r)
  let b := x / 4 + (y - 2 * m * x) / (8 * r)
  have hab : 2 * (a + b) = x := by dsimp [a, b]; ring
  have hmoment : 4 * ((m - r) * a + (m + r) * b) = y := by
    dsimp [a, b]
    field_simp
    ring
  obtain ⟨t, ht, hta', htb', htub⟩ := small_step (lt_min hr (half_pos heta)) a b
  have hta : |t * a| ≤ r := hta'.trans (min_le_left _ _)
  have htb : |t * b| ≤ r := htb'.trans (min_le_left _ _)
  have hteta : t < eta := lt_of_le_of_lt (htub.trans (min_le_right _ _)) (by linarith)
  refine ⟨t, pairInput K m r t a b, pairInput K m r (-t) a b,
    ht, hteta, pairInput_valid hK m r t a b hm hr hmr hta htb,
    pairInput_valid hK m r (-t) a b hm hr hmr ?_ ?_, ?_, ?_, ?_⟩
  · simpa only [neg_mul, abs_neg] using hta
  · simpa only [neg_mul, abs_neg] using htb
  · rw [pairInput_firstMoment hK, pairInput_firstMoment hK]
    nlinarith only [congrArg (fun z : ℝ => t * z) hab]
  · rw [pairInput_secondMoment hK, pairInput_secondMoment hK]
    nlinarith only [congrArg (fun z : ℝ => t * z) hmoment]
  · rw [pairInput_firstMoment hK, pairInput_firstMoment hK]
    ring

lemma realize_moment_direction {K : ℕ} (hK : 2 ≤ K) (m x y : ℝ)
    (hm : -1 < m ∧ m < 1) :
    ∃ (t : ℝ) (xs ys : List ℝ), 0 < t ∧ ValidInput K xs ∧ ValidInput K ys ∧
      firstMoment xs - firstMoment ys = t * x ∧
      secondMoment xs - secondMoment ys = t * y ∧
      firstMoment xs + firstMoment ys = 2 * (K : ℝ) * m := by
  obtain ⟨t, xs, ys, ht, _, hx, hy, hS, hT, hSum⟩ :=
    realize_moment_direction_small hK m x y 1 hm (by norm_num)
  exact ⟨t, xs, ys, ht, hx, hy, hS, hT, hSum⟩

/-- Every uniform operational lower bound obeys the full moment-direction
inequality at each interior mean. -/
theorem Curve.separation_direction_bound (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    {lam : ℝ} (hsep : SeparationLowerBound K e.encoder lam)
    (m x y : ℝ) (hm : -1 < m ∧ m < 1) :
    lam * (y - 2 * m * x) ^ 2 ≤
      (K : ℝ) ^ 2 * (e.A * x ^ 2 + 2 * e.C * x * y + e.B * y ^ 2) := by
  obtain ⟨t, xs, ys, ht, hx, hy, hS, hT, hSum⟩ :=
    realize_moment_direction hK m x y hm
  have hk : (K : ℝ) ≠ 0 := by
    have hn : K ≠ 0 := by omega
    exact_mod_cast hn
  have hv : variance K xs - variance K ys = t * (y - 2 * m * x) / (K : ℝ) := by
    have hdiff : (firstMoment xs) ^ 2 - (firstMoment ys) ^ 2 =
        (firstMoment xs - firstMoment ys) * (firstMoment xs + firstMoment ys) := by ring
    rw [hS, hSum] at hdiff
    dsimp [variance]
    field_simp
    nlinarith only [hT, hdiff]
  have h := hsep xs ys hx hy
  rw [hv, e.received_squaredDistance xs ys hx hy, hS, hT] at h
  have h' := mul_le_mul_of_nonneg_right h (sq_nonneg (K : ℝ))
  have hi : lam * (t * (y - 2 * m * x) / (K : ℝ)) ^ 2 * (K : ℝ) ^ 2 =
      t ^ 2 * (lam * (y - 2 * m * x) ^ 2) := by field_simp
  rw [hi] at h'
  have hj : (e.A * (t * x) ^ 2 + 2 * e.C * (t * x) * (t * y) +
      e.B * (t * y) ^ 2) * (K : ℝ) ^ 2 =
      t ^ 2 * ((K : ℝ) ^ 2 * (e.A * x ^ 2 + 2 * e.C * x * y + e.B * y ^ 2)) := by ring
  rw [hj] at h'
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos ht)).mp h'

lemma Curve.separation_direction_bound_closed (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    {lam : ℝ} (hsep : SeparationLowerBound K e.encoder lam)
    (m x y : ℝ) (hm : -1 ≤ m ∧ m ≤ 1) :
    lam * (y - 2 * m * x) ^ 2 ≤
      (K : ℝ) ^ 2 * (e.A * x ^ 2 + 2 * e.C * x * y + e.B * y ^ 2) := by
  have hcl : m ∈ closure (Set.Ioo (-1 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    exact hm
  apply le_on_closure (fun z hz => e.separation_direction_bound hK hsep z x y hz)
    (x := m) (s := Set.Ioo (-1 : ℝ) 1) _ _ hcl
  · fun_prop
  · fun_prop

/-- The sharp converse uses actual input pairs constructed above and the
continuity of their directional inequality at the two endpoint means. -/
theorem Curve.variance_separation_upper_bound_of_denominator_pos
    (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (hden : 0 < e.A + 4 * e.B + 4 * |e.C|) {lam : ℝ}
    (hsep : SeparationLowerBound K e.encoder lam) :
    lam ≤ (K : ℝ) ^ 2 * e.score := by
  let D := e.A + 4 * e.B + 4 * |e.C|
  have hD : 0 < D := hden
  have hd : lam * D ^ 2 ≤ (K : ℝ) ^ 2 * ((e.A * e.B - e.C ^ 2) * D) := by
    by_cases hc : 0 ≤ e.C
    · have h := e.separation_direction_bound_closed hK hsep 1
        (-(2 * e.B + e.C)) (e.A + 2 * e.C) (by norm_num)
      have h1 : e.A + 2 * e.C - 2 * (1 : ℝ) * (-(2 * e.B + e.C)) = D := by
        dsimp [D]
        rw [abs_of_nonneg hc]
        ring
      have h2 : e.A * (-(2 * e.B + e.C)) ^ 2 +
          2 * e.C * (-(2 * e.B + e.C)) * (e.A + 2 * e.C) +
          e.B * (e.A + 2 * e.C) ^ 2 = (e.A * e.B - e.C ^ 2) * D := by
        dsimp [D]
        rw [abs_of_nonneg hc]
        ring
      rwa [h1, h2] at h
    · have hc' : e.C ≤ 0 := le_of_lt (lt_of_not_ge hc)
      have h := e.separation_direction_bound_closed hK hsep (-1)
        (2 * e.B - e.C) (e.A - 2 * e.C) (by norm_num)
      have h1 : e.A - 2 * e.C - 2 * (-1 : ℝ) * (2 * e.B - e.C) = D := by
        dsimp [D]
        rw [abs_of_nonpos hc']
        ring
      have h2 : e.A * (2 * e.B - e.C) ^ 2 +
          2 * e.C * (2 * e.B - e.C) * (e.A - 2 * e.C) +
          e.B * (e.A - 2 * e.C) ^ 2 = (e.A * e.B - e.C ^ 2) * D := by
        dsimp [D]
        rw [abs_of_nonpos hc']
        ring
      rwa [h1, h2] at h
  have hd' : (lam * D) * D ≤ ((K : ℝ) ^ 2 * (e.A * e.B - e.C ^ 2)) * D := by
    nlinarith only [hd]
  have hh := (mul_le_mul_iff_left₀ hD).mp hd'
  change lam ≤ (K : ℝ) ^ 2 * ((e.A * e.B - e.C ^ 2) / D)
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hD).2 hh

theorem Curve.variance_separation_upper_bound (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (hdet : 0 < e.A * e.B - e.C ^ 2) {lam : ℝ}
    (hsep : SeparationLowerBound K e.encoder lam) :
    lam ≤ (K : ℝ) ^ 2 * e.score :=
  e.variance_separation_upper_bound_of_denominator_pos hK (e.denominator_pos hdet) hsep

/-- Exact operational characterization of the squared separation constant
for every nondegenerate quadratic planar encoder and every K >= 2. -/
theorem Curve.variance_separation_iff (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (hdet : 0 < e.A * e.B - e.C ^ 2) (lam : ℝ) :
    SeparationLowerBound K e.encoder lam ↔ lam ≤ (K : ℝ) ^ 2 * e.score := by
  constructor
  · exact e.variance_separation_upper_bound hK hdet
  · intro h xs ys hx hy
    have hbound := e.variance_separation_lower_bound (by omega : 0 < K) hdet xs ys hx hy
    exact le_trans (mul_le_mul_of_nonneg_right h (sq_nonneg _)) hbound

lemma Curve.determinant_nonneg (e : Curve) : 0 ≤ e.A * e.B - e.C ^ 2 := by
  have h : e.A * e.B - e.C ^ 2 = (e.ux * e.vy - e.uy * e.vx) ^ 2 := by
    dsimp [Curve.A, Curve.B, Curve.C]
    ring
  rw [h]
  positivity

/-- Degenerate quadratic encoders are included: their Gram score is zero,
which remains a valid separation lower bound. -/
theorem Curve.variance_separation_lower_bound_all (e : Curve) {K : ℕ} (hK : 0 < K) :
    SeparationLowerBound K e.encoder ((K : ℝ) ^ 2 * e.score) := by
  by_cases hd : 0 < e.A * e.B - e.C ^ 2
  · exact e.variance_separation_lower_bound hK hd
  · have hd0 : e.A * e.B - e.C ^ 2 = 0 :=
      le_antisymm (le_of_not_gt hd) e.determinant_nonneg
    have hs : e.score = 0 := by simp [Curve.score, hd0]
    intro xs ys hx hy
    rw [hs]
    simp only [mul_zero, zero_mul]
    dsimp [squaredDistance]
    positivity

/-- Sharp operational converse for all quadratic curves, including the
rank-one and constant encoders. -/
theorem Curve.variance_separation_upper_bound_all (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    {lam : ℝ} (hsep : SeparationLowerBound K e.encoder lam) :
    lam ≤ (K : ℝ) ^ 2 * e.score := by
  by_cases hd : 0 < e.A + 4 * e.B + 4 * |e.C|
  · exact e.variance_separation_upper_bound_of_denominator_pos hK hd hsep
  · have ha : 0 ≤ e.A := by dsimp [Curve.A]; positivity
    have hb : 0 ≤ e.B := by dsimp [Curve.B]; positivity
    have hc := abs_nonneg e.C
    have hd0 : e.A + 4 * e.B + 4 * |e.C| = 0 := by linarith
    have hb0 : e.B = 0 := by linarith
    have hs : e.score = 0 := by simp [Curve.score, hd0]
    have h := e.separation_direction_bound hK hsep 0 0 1 (by norm_num)
    simpa [hs, hb0] using h

/-- The complete operational characterization covers every planar quadratic
encoder and every number of terminals K >= 2. -/
theorem Curve.variance_separation_iff_all (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (lam : ℝ) :
    SeparationLowerBound K e.encoder lam ↔ lam ≤ (K : ℝ) ^ 2 * e.score := by
  constructor
  · exact e.variance_separation_upper_bound_all hK
  · intro h xs ys hx hy
    have hbound := e.variance_separation_lower_bound_all (by omega : 0 < K) xs ys hx hy
    exact le_trans (mul_le_mul_of_nonneg_right h (sq_nonneg _)) hbound

/-- The actual infimum of squared received-distance / squared variance
differences equals the closed-form Gram score, with its K² factor. This
statement covers correlated, rank-one, and constant quadratic encoders. -/
theorem Curve.variance_operational_score (e : Curve) {K : ℕ} (hK : 2 ≤ K) :
    varianceScore K e.encoder = (K : ℝ) ^ 2 * e.score := by
  apply le_antisymm
  · apply (e.variance_separation_iff_all hK _).mp
    exact (varianceScore_characterization hK e.encoder _).mp le_rfl
  · apply (varianceScore_characterization hK e.encoder _).mpr
    exact (e.variance_separation_iff_all hK _).mpr le_rfl

private lemma secondMoment_bounds (xs : List ℝ) (h : ∀ x ∈ xs, InSource x) :
    secondMoment xs ≤ (xs.length : ℝ) ∧
      2 * firstMoment xs - (xs.length : ℝ) ≤ secondMoment xs ∧
      -2 * firstMoment xs - (xs.length : ℝ) ≤ secondMoment xs := by
  induction xs with
  | nil => simp [firstMoment, secondMoment]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hi := ih (fun z hz => h z (by simp [hz]))
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
    simp only [firstMoment, secondMoment, List.map_cons, List.sum_cons,
      List.length_cons, Nat.cast_add, Nat.cast_one] at *
    refine ⟨?_, ?_, ?_⟩ <;>
      nlinarith [hi.1, hi.2.1, hi.2.2, sq_nonneg (x - 1), sq_nonneg (x + 1)]

private lemma pair_mean_interior {K : ℕ} (hK : 0 < K) (xs ys : List ℝ)
    (hx : ValidInput K xs) (hy : ValidInput K ys)
    (hne : variance K xs ≠ variance K ys) :
    -1 < (firstMoment xs + firstMoment ys) / (2 * (K : ℝ)) ∧
      (firstMoment xs + firstMoment ys) / (2 * (K : ℝ)) < 1 := by
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hxm := firstMoment_bounds xs hx.2
  have hym := firstMoment_bounds ys hy.2
  have hxt := secondMoment_bounds xs hx.2
  have hyt := secondMoment_bounds ys hy.2
  rw [hx.1] at hxm hxt
  rw [hy.1] at hym hyt
  have hsum : -2 * (K : ℝ) < firstMoment xs + firstMoment ys ∧
      firstMoment xs + firstMoment ys < 2 * (K : ℝ) := by
    constructor
    · by_contra! h
      have hSx : firstMoment xs = -(K : ℝ) := by linarith [hxm.1, hym.1]
      have hSy : firstMoment ys = -(K : ℝ) := by linarith [hxm.1, hym.1]
      have hTx : secondMoment xs = (K : ℝ) := by linarith [hxt.1, hxt.2.2]
      have hTy : secondMoment ys = (K : ℝ) := by linarith [hyt.1, hyt.2.2]
      exact hne (by simp only [variance, hSx, hSy, hTx, hTy])
    · by_contra! h
      have hSx : firstMoment xs = (K : ℝ) := by linarith [hxm.2, hym.2]
      have hSy : firstMoment ys = (K : ℝ) := by linarith [hxm.2, hym.2]
      have hTx : secondMoment xs = (K : ℝ) := by linarith [hxt.1, hxt.2.1]
      have hTy : secondMoment ys = (K : ℝ) := by linarith [hyt.1, hyt.2.1]
      exact hne (by simp only [variance, hSx, hSy, hTx, hTy])
  constructor
  · apply (lt_div_iff₀ (by positivity : 0 < 2 * (K : ℝ))).2
    linarith [hsum.1]
  · apply (div_lt_iff₀ (by positivity : 0 < 2 * (K : ℝ))).2
    linarith [hsum.2]

private lemma variance_difference (K : ℕ) (hk : (K : ℝ) ≠ 0) (xs ys : List ℝ) :
    variance K xs - variance K ys =
      ((secondMoment xs - secondMoment ys) -
        ((firstMoment xs + firstMoment ys) / (K : ℝ)) *
          (firstMoment xs - firstMoment ys)) / (K : ℝ) := by
  dsimp [variance]
  field_simp
  ring

/-- Any nontrivial separation quotient of a quadratic curve can be realized
at arbitrarily small received distance by other valid source tuples. -/
theorem Curve.shrink_separation_pair (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (xs ys : List ℝ) (hx : ValidInput K xs) (hy : ValidInput K ys)
    (hne : variance K xs ≠ variance K ys) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ us vs : List ℝ, ValidInput K us ∧ ValidInput K vs ∧
      variance K us ≠ variance K vs ∧
      squaredDistance (received e.encoder us) (received e.encoder vs) < delta ^ 2 ∧
      squaredDistance (received e.encoder us) (received e.encoder vs) /
        (variance K us - variance K vs) ^ 2 =
      squaredDistance (received e.encoder xs) (received e.encoder ys) /
        (variance K xs - variance K ys) ^ 2 := by
  let n := squaredDistance (received e.encoder xs) (received e.encoder ys)
  have hn : 0 ≤ n := squaredDistance_nonnegative _ _
  let eta := delta / (Real.sqrt n + 1)
  have heta : 0 < eta := div_pos hdelta (by positivity)
  have hk : (K : ℝ) ≠ 0 := by
    have hk' : K ≠ 0 := by omega
    exact_mod_cast hk'
  obtain ⟨t, us, vs, ht, hteta, hu, hv, hS, hT, hSum⟩ :=
    realize_moment_direction_small hK
      ((firstMoment xs + firstMoment ys) / (2 * (K : ℝ)))
      (firstMoment xs - firstMoment ys) (secondMoment xs - secondMoment ys)
      eta (pair_mean_interior (by omega) xs ys hx hy hne) heta
  have hSum' : firstMoment us + firstMoment vs = firstMoment xs + firstMoment ys := by
    rw [hSum]
    field_simp
  have hvar : variance K us - variance K vs = t * (variance K xs - variance K ys) := by
    rw [variance_difference K hk us vs, variance_difference K hk xs ys,
      hSum', hS, hT]
    ring
  have hcost : squaredDistance (received e.encoder us) (received e.encoder vs) = t ^ 2 * n := by
    dsimp [n]
    rw [e.received_squaredDistance us vs hu hv, e.received_squaredDistance xs ys hx hy,
      hS, hT]
    ring
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hvar0 : variance K xs - variance K ys ≠ 0 := sub_ne_zero.mpr hne
  refine ⟨us, vs, hu, hv, ?_, ?_, ?_⟩
  · apply sub_ne_zero.mp
    rw [hvar]
    exact mul_ne_zero ht0 hvar0
  · rw [hcost]
    have hs := Real.sqrt_nonneg n
    have hs2 := Real.sq_sqrt hn
    have ht' : t * (Real.sqrt n + 1) < delta := by
      exact (lt_div_iff₀ (by positivity : 0 < Real.sqrt n + 1)).mp hteta
    have hta : 0 ≤ t * Real.sqrt n := mul_nonneg ht.le hs
    have hta' : t * Real.sqrt n < delta := by nlinarith only [ht', ht]
    have hsq : (t * Real.sqrt n) ^ 2 < delta ^ 2 := by nlinarith only [hta, hta', hdelta]
    have hh : (t * Real.sqrt n) ^ 2 = t ^ 2 * n := by rw [mul_pow, hs2]
    rwa [hh] at hsq
  · rw [hcost, hvar]
    dsimp [n]
    field_simp

/-- The operational infimum is approached by actual admissible pairs whose
received distances are arbitrarily small. The target values remain distinct.
This is valid even for degenerate quadratic encoders. -/
theorem Curve.variance_score_small_distance_sharpness (e : Curve) {K : ℕ}
    (hK : 2 ≤ K) (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta) :
    ∃ xs ys : List ℝ, ValidInput K xs ∧ ValidInput K ys ∧
      variance K xs ≠ variance K ys ∧
      squaredDistance (received e.encoder xs) (received e.encoder ys) < delta ^ 2 ∧
      squaredDistance (received e.encoder xs) (received e.encoder ys) /
        (variance K xs - variance K ys) ^ 2 < (K : ℝ) ^ 2 * e.score + eps := by
  let Q := Operational.Quotients {xs | ValidInput K xs} (variance K)
    (fun xs ys => squaredDistance (received e.encoder xs) (received e.encoder ys))
  have hQ : Q.Nonempty := Operational.quotients_nonempty _ (variance_nonconstant hK)
  have hlt : sInf Q < (K : ℝ) ^ 2 * e.score + eps := by
    change varianceScore K e.encoder < _
    rw [e.variance_operational_score hK]
    linarith
  obtain ⟨q, hq, hq_lt⟩ := exists_lt_of_csInf_lt hQ hlt
  obtain ⟨xs, hx, ys, hy, hne, hquot⟩ := hq
  obtain ⟨us, vs, hu, hv, huv, hsmall, hsame⟩ :=
    e.shrink_separation_pair hK xs ys hx hy hne delta hdelta
  refine ⟨us, vs, hu, hv, huv, hsmall, ?_⟩
  rw [hsame, ← hquot]
  exact hq_lt

end Analog
