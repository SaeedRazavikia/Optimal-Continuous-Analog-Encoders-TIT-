import Analog.Decoder
import Analog.VarianceScore

/-!
# Projection onto a correlated moment strip

The Gram matrix has entries A, C, B. Its positive determinant and B > 0
ensure positive definiteness. We verify the actual clipping-and-correction
formula, its unique metric-minimizing property, its squared nonexpansiveness,
and the variance readout bound after projection.
-/

noncomputable section

namespace Analog.Strip

def InStrip (p : ℝ × ℝ) : Prop := -1 ≤ p.1 ∧ p.1 ≤ 1

def energy (A B C x y : ℝ) : ℝ := A * x ^ 2 + 2 * C * x * y + B * y ^ 2

def gramDistance (A B C : ℝ) (p q : ℝ × ℝ) : ℝ :=
  energy A B C (p.1 - q.1) (p.2 - q.2)

def project (B C : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (Decoder.clip (-1) 1 p.1, p.2 + C / B * (p.1 - Decoder.clip (-1) 1 p.1))

lemma energy_complete_square (A B C x y : ℝ) (hB : B ≠ 0) :
    energy A B C x y = (A - C ^ 2 / B) * x ^ 2 + B * (y + C / B * x) ^ 2 := by
  unfold energy
  field_simp
  ring

lemma schur_positive {A B C : ℝ} (hB : 0 < B) (hdet : 0 < A * B - C ^ 2) :
    0 < A - C ^ 2 / B := by
  have hid : A - C ^ 2 / B = (A * B - C ^ 2) / B := by
    field_simp
  rw [hid]
  exact div_pos hdet hB

lemma energy_nonnegative {A B C : ℝ} (hB : 0 < B) (hdet : 0 < A * B - C ^ 2)
    (x y : ℝ) : 0 ≤ energy A B C x y := by
  rw [energy_complete_square A B C x y hB.ne']
  exact add_nonneg (mul_nonneg (schur_positive hB hdet).le (sq_nonneg _))
    (mul_nonneg hB.le (sq_nonneg _))

lemma energy_eq_zero_iff {A B C : ℝ} (hB : 0 < B) (hdet : 0 < A * B - C ^ 2)
    (x y : ℝ) : energy A B C x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    rw [energy_complete_square A B C x y hB.ne'] at h
    have hα := schur_positive hB hdet
    have hxnon := mul_nonneg hα.le (sq_nonneg x)
    have hynon := mul_nonneg hB.le (sq_nonneg (y + C / B * x))
    have hxzero : (A - C ^ 2 / B) * x ^ 2 = 0 := by linarith
    have hx : x = 0 := (sq_eq_zero_iff).mp
      ((mul_eq_zero.mp hxzero).resolve_left hα.ne')
    subst x
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, zero_add] at h
    exact ⟨rfl, sq_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_left hB.ne')⟩
  · rintro ⟨rfl, rfl⟩
    simp [energy]

theorem project_in_strip (B C : ℝ) (p : ℝ × ℝ) : InStrip (project B C p) := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem project_fixes_strip (B C : ℝ) {p : ℝ × ℝ} (hp : InStrip p) :
    project B C p = p := by
  simp only [project, Decoder.clip_fixed hp.1 hp.2, sub_self, mul_zero, add_zero]

/-- The correction preserves the unbounded coordinate after diagonalizing
the correlated Gram metric. -/
theorem project_preserves_transformed_coordinate (B C : ℝ) (p : ℝ × ℝ) :
    (project B C p).2 + C / B * (project B C p).1 = p.2 + C / B * p.1 := by
  dsimp [project]
  ring

lemma clip_normal (x m : ℝ) (hm : -1 ≤ m ∧ m ≤ 1) :
    0 ≤ (x - Decoder.clip (-1) 1 x) * (Decoder.clip (-1) 1 x - m) := by
  by_cases hlo : x < -1
  · have hc : Decoder.clip (-1) 1 x = -1 := by
      simp [Decoder.clip, min_eq_right (by linarith : x ≤ 1), max_eq_left hlo.le]
    rw [hc]
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [hm.1])
  · by_cases hhi : 1 < x
    · have hc : Decoder.clip (-1) 1 x = 1 := by
        simp [Decoder.clip, min_eq_left hhi.le]
      rw [hc]
      exact mul_nonneg (by linarith) (by linarith [hm.2])
    · rw [Decoder.clip_fixed (le_of_not_gt hlo) (le_of_not_gt hhi), sub_self, zero_mul]

/-- Projection satisfies the Gram-metric Pythagorean inequality, which is
stronger than merely minimizing the distance to the strip. -/
theorem projection_pythagorean {A B C : ℝ}
    (hB : 0 < B) (hdet : 0 < A * B - C ^ 2)
    (p q : ℝ × ℝ) (hq : InStrip q) :
    gramDistance A B C p (project B C p) +
      gramDistance A B C (project B C p) q ≤ gramDistance A B C p q := by
  have hid : gramDistance A B C p q -
      gramDistance A B C p (project B C p) -
      gramDistance A B C (project B C p) q =
        2 * (A - C ^ 2 / B) *
          ((p.1 - Decoder.clip (-1) 1 p.1) * (Decoder.clip (-1) 1 p.1 - q.1)) := by
    dsimp [gramDistance, energy, project]
    field_simp
    ring
  have hn := mul_nonneg (by linarith [schur_positive hB hdet] : 0 ≤ 2 * (A - C ^ 2 / B))
    (clip_normal p.1 q.1 hq)
  linarith

/-- The explicit corrected-clipping formula is the unique metric minimizer
over the entire unbounded strip. -/
theorem project_unique_minimizer {A B C : ℝ}
    (hB : 0 < B) (hdet : 0 < A * B - C ^ 2) (p : ℝ × ℝ) :
    InStrip (project B C p) ∧
      (∀ q, InStrip q → gramDistance A B C p (project B C p) ≤ gramDistance A B C p q) ∧
      ∀ q, InStrip q →
        (gramDistance A B C p q = gramDistance A B C p (project B C p) ↔
          q = project B C p) := by
  refine ⟨project_in_strip B C p, ?_, ?_⟩
  · intro q hq
    have hpy := projection_pythagorean hB hdet p q hq
    have hnon := energy_nonnegative hB hdet
      ((project B C p).1 - q.1) ((project B C p).2 - q.2)
    change 0 ≤ gramDistance A B C (project B C p) q at hnon
    linarith
  · intro q hq
    constructor
    · intro he
      have hpy := projection_pythagorean hB hdet p q hq
      have hnon := energy_nonnegative hB hdet
        ((project B C p).1 - q.1) ((project B C p).2 - q.2)
      have hz : energy A B C ((project B C p).1 - q.1) ((project B C p).2 - q.2) = 0 := by
        change gramDistance A B C (project B C p) q = 0
        change 0 ≤ gramDistance A B C (project B C p) q at hnon
        linarith
      obtain ⟨hx, hy⟩ := (energy_eq_zero_iff hB hdet _ _).mp hz
      apply Prod.ext <;> linarith
    · rintro rfl
      rfl

/-- The actual correlated projection is nonexpansive in squared Gram
distance for every two points in the plane. -/
theorem project_squared_nonexpansive {A B C : ℝ}
    (hB : 0 < B) (hdet : 0 < A * B - C ^ 2) (p q : ℝ × ℝ) :
    gramDistance A B C (project B C p) (project B C q) ≤ gramDistance A B C p q := by
  have hc := (Decoder.clip_lipschitz (-1) 1).dist_le_mul p.1 q.1
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hc
  have hcs : (Decoder.clip (-1) 1 p.1 - Decoder.clip (-1) 1 q.1) ^ 2 ≤
      (p.1 - q.1) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hc
  have ht : ((project B C p).2 - (project B C q).2) +
      C / B * ((project B C p).1 - (project B C q).1) =
        (p.2 - q.2) + C / B * (p.1 - q.1) := by
    dsimp [project]
    ring
  unfold gramDistance
  rw [energy_complete_square A B C _ _ hB.ne',
    energy_complete_square A B C _ _ hB.ne', ht]
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left hcs (schur_positive hB hdet).le) _

def varianceReadout (p : ℝ × ℝ) : ℝ := p.2 - p.1 ^ 2

lemma dual_endpoint_bound {A B C q : ℝ} (hB : 0 ≤ B) (hq : -2 ≤ q ∧ q ≤ 2) :
    A + 2 * q * C + q ^ 2 * B ≤ A + 4 * B + 4 * |C| := by
  have hq2 : q ^ 2 ≤ 4 := by nlinarith
  have hqabs : |q| ≤ 2 := abs_le.mpr hq
  have hc : q * C ≤ 2 * |C| := calc
    q * C ≤ |q * C| := le_abs_self _
    _ = |q| * |C| := abs_mul _ _
    _ ≤ 2 * |C| := mul_le_mul_of_nonneg_right hqabs (abs_nonneg _)
  have hbq := mul_le_mul_of_nonneg_right hq2 hB
  linarith

/-- The variance readout has the sharp endpoint dual-norm bound on the
entire strip, including pairs that are not attainable empirical moments. -/
theorem variance_readout_squared_bound {A B C : ℝ}
    (hB : 0 < B) (hdet : 0 < A * B - C ^ 2)
    (p q : ℝ × ℝ) (hp : InStrip p) (hq : InStrip q) :
    (varianceReadout p - varianceReadout q) ^ 2 ≤
      ((A + 4 * B + 4 * |C|) / (A * B - C ^ 2)) * gramDistance A B C p q := by
  have hm : -2 ≤ p.1 + q.1 ∧ p.1 + q.1 ≤ 2 := by
    constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]
  have he := energy_nonnegative hB hdet (p.1 - q.1) (p.2 - q.2)
  have hd := dual_endpoint_bound (A := A) (C := C) hB.le hm
  have hi := Analog.quadratic_dual_identity A B C (p.1 - q.1) (p.2 - q.2) (p.1 + q.1)
  have hv : varianceReadout p - varianceReadout q =
      (p.2 - q.2) - (p.1 + q.1) * (p.1 - q.1) := by
    unfold varianceReadout
    ring
  rw [hv, div_mul_eq_mul_div]
  apply (le_div_iff₀ hdet).mpr
  have hmul := mul_le_mul_of_nonneg_right hd he
  dsimp [gramDistance, energy] at *
  nlinarith only [hi, hmul, sq_nonneg
    ((A + (p.1 + q.1) * C) * (p.1 - q.1) +
      (C + (p.1 + q.1) * B) * (p.2 - q.2))]

/-- The implementable corrected-clipping decoder preserves the same
variance error factor globally, including arbitrary off-strip observations. -/
theorem projected_variance_squared_bound {A B C : ℝ}
    (hB : 0 < B) (hdet : 0 < A * B - C ^ 2) (p q : ℝ × ℝ) :
    (varianceReadout (project B C p) - varianceReadout (project B C q)) ^ 2 ≤
      ((A + 4 * B + 4 * |C|) / (A * B - C ^ 2)) * gramDistance A B C p q := by
  have hA : 0 < A := by nlinarith [sq_nonneg C]
  have hfactor : 0 ≤ (A + 4 * B + 4 * |C|) / (A * B - C ^ 2) :=
    div_nonneg (by positivity) hdet.le
  exact (variance_readout_squared_bound hB hdet _ _
    (project_in_strip B C p) (project_in_strip B C q)).trans
      (mul_le_mul_of_nonneg_left (project_squared_nonexpansive hB hdet p q) hfactor)

/-- Exactness and a uniform squared disturbance bound against any true
moment point in the strip. -/
theorem projected_variance_error {A B C : ℝ}
    (hB : 0 < B) (hdet : 0 < A * B - C ^ 2)
    (truth observation : ℝ × ℝ) (ht : InStrip truth) :
    (varianceReadout (project B C observation) - varianceReadout truth) ^ 2 ≤
      ((A + 4 * B + 4 * |C|) / (A * B - C ^ 2)) *
        gramDistance A B C observation truth := by
  simpa only [project_fixes_strip B C ht] using
    projected_variance_squared_bound hB hdet observation truth

end Analog.Strip
