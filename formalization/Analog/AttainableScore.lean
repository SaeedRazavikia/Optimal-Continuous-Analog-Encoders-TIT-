import Analog.Operational

/-!
# Operational separation on the actual attainable statistic set

For a desired function that factors through a statistic, and a received-distance
cost that factors through the same statistic, the operational quotient set is
exactly the quotient set on its attainable image. No convexification or closure
of that image is used. The results hold for arbitrary admissible input sets and
do not assume continuity, differentiability, or encoder rigidity.

The squared scaling specialization records the factor `K^2` arising when a
channel sums `K` contributions while the statistic is normalized by `K`.
-/

noncomputable section

namespace Analog.Operational

variable {X Y : Type*}

/-- Changing a received-distance formula away from admissible pairs has no
effect on its operational quotient set. -/
theorem quotients_cost_congr_on {D : Set X} {f : X → ℝ}
    {cost cost' : X → X → ℝ}
    (hcost : ∀ x ∈ D, ∀ y ∈ D, cost x y = cost' x y) :
    Quotients D f cost = Quotients D f cost' := by
  ext q
  constructor
  · rintro ⟨x, hx, y, hy, hxy, hq⟩
    exact ⟨x, hx, y, hy, hxy, hq.trans (by rw [hcost x hx y hy])⟩
  · rintro ⟨x, hx, y, hy, hxy, hq⟩
    exact ⟨x, hx, y, hy, hxy, hq.trans (by rw [hcost x hx y hy])⟩

/-- The operational score only depends on the cost at admissible pairs. -/
theorem score_cost_congr_on {D : Set X} {f : X → ℝ}
    {cost cost' : X → X → ℝ}
    (hcost : ∀ x ∈ D, ∀ y ∈ D, cost x y = cost' x y) :
    score D f cost = score D f cost' := by
  unfold score
  rw [quotients_cost_congr_on hcost]

/-- Nonconstancy is unchanged when the domain is replaced by the actual image
of the statistic through which the desired function factors. -/
theorem nonconstantOn_stat_image_iff (D : Set X) (stat : X → Y) (F : Y → ℝ) :
    NonconstantOn D (F ∘ stat) ↔ NonconstantOn (stat '' D) F := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨stat x, ⟨x, hx, rfl⟩, stat y, ⟨y, hy, rfl⟩, hxy⟩
  · rintro ⟨a, ⟨x, hx, rfl⟩, b, ⟨y, hy, rfl⟩, hxy⟩
    exact ⟨x, hx, y, hy, hxy⟩

/-- Reindexing the quotient set uses all and only attainable statistic pairs. -/
theorem quotients_stat_image (D : Set X) (stat : X → Y) (F : Y → ℝ)
    (cost : Y → Y → ℝ) :
    Quotients D (F ∘ stat) (fun x y => cost (stat x) (stat y)) =
      Quotients (stat '' D) F cost := by
  ext q
  constructor
  · rintro ⟨x, hx, y, hy, hxy, hq⟩
    exact ⟨stat x, ⟨x, hx, rfl⟩, stat y, ⟨y, hy, rfl⟩, hxy, hq⟩
  · rintro ⟨a, ⟨x, hx, rfl⟩, b, ⟨y, hy, rfl⟩, hxy, hq⟩
    exact ⟨x, hx, y, hy, hxy, hq⟩

/-- The operational score equals the score on the actual attainable image.
This identity itself does not require a nonconstant desired function. -/
theorem score_stat_image (D : Set X) (stat : X → Y) (F : Y → ℝ)
    (cost : Y → Y → ℝ) :
    score D (F ∘ stat) (fun x y => cost (stat x) (stat y)) =
      score (stat '' D) F cost := by
  unfold score
  rw [quotients_stat_image]

/-- All-input-pair constraints are equivalent to constraints on every actual
attainable statistic pair, including pairs with equal desired function values. -/
theorem lowerBound_stat_image_iff (D : Set X) (stat : X → Y) (F : Y → ℝ)
    (cost : Y → Y → ℝ) (lam : ℝ) :
    LowerBound D (F ∘ stat) (fun x y => cost (stat x) (stat y)) lam ↔
      LowerBound (stat '' D) F cost lam := by
  constructor
  · intro h a ha b hb
    rcases ha with ⟨x, hx, rfl⟩
    rcases hb with ⟨y, hy, rfl⟩
    exact h x hx y hy
  · intro h x hx y hy
    exact h (stat x) ⟨x, hx, rfl⟩ (stat y) ⟨y, hy, rfl⟩

/-- A score threshold is exactly the family of attained-pair inequalities. -/
theorem le_score_stat_image_iff {D : Set X} {stat : X → Y} {F : Y → ℝ}
    {cost : Y → Y → ℝ} (hn : NonconstantOn (stat '' D) F)
    (hc : ∀ a ∈ stat '' D, ∀ b ∈ stat '' D, 0 ≤ cost a b) (lam : ℝ) :
    lam ≤ score D (F ∘ stat) (fun x y => cost (stat x) (stat y)) ↔
      ∀ a ∈ stat '' D, ∀ b ∈ stat '' D,
        lam * (F a - F b) ^ 2 ≤ cost a b := by
  rw [score_stat_image]
  exact le_score_iff hn hc lam

/-- Positive scaling commutes with attainable-image reindexing of the score. -/
theorem score_stat_image_scale {D : Set X} {stat : X → Y} {F : Y → ℝ}
    {cost : Y → Y → ℝ} (hn : NonconstantOn (stat '' D) F)
    (hc : ∀ a ∈ stat '' D, ∀ b ∈ stat '' D, 0 ≤ cost a b)
    {p : ℝ} (hp : 0 < p) :
    score D (F ∘ stat) (fun x y => p * cost (stat x) (stat y)) =
      p * score (stat '' D) F cost := by
  rw [score_stat_image D stat F (fun a b => p * cost a b)]
  exact score_cost_scale hn hc hp

/-- The normalized-statistic score has the exact squared channel-sum factor. -/
theorem score_stat_image_sq_scale {D : Set X} {stat : X → Y} {F : Y → ℝ}
    {cost : Y → Y → ℝ} (hn : NonconstantOn (stat '' D) F)
    (hc : ∀ a ∈ stat '' D, ∀ b ∈ stat '' D, 0 ≤ cost a b)
    {k : ℝ} (hk : k ≠ 0) :
    score D (F ∘ stat) (fun x y => k ^ 2 * cost (stat x) (stat y)) =
      k ^ 2 * score (stat '' D) F cost :=
  score_stat_image_scale hn hc (sq_pos_of_ne_zero hk)

/-- Explicit infimum formula over the actual attained statistic pairs. -/
theorem score_stat_image_sq_formula {D : Set X} {stat : X → Y} {F : Y → ℝ}
    {cost : Y → Y → ℝ} (hn : NonconstantOn (stat '' D) F)
    (hc : ∀ a ∈ stat '' D, ∀ b ∈ stat '' D, 0 ≤ cost a b)
    {k : ℝ} (hk : k ≠ 0) :
    score D (F ∘ stat) (fun x y => k ^ 2 * cost (stat x) (stat y)) =
      k ^ 2 * sInf {q : ℝ | ∃ a ∈ stat '' D, ∃ b ∈ stat '' D,
        F a ≠ F b ∧ q = cost a b / (F a - F b) ^ 2} :=
  score_stat_image_sq_scale hn hc hk

/-- Cancellation of the squared channel-sum factor in all-pair constraints. -/
theorem lowerBound_stat_image_sq_iff (D : Set X) (stat : X → Y) (F : Y → ℝ)
    (cost : Y → Y → ℝ) (lam : ℝ) {k : ℝ} (hk : k ≠ 0) :
    LowerBound D (F ∘ stat)
      (fun x y => k ^ 2 * cost (stat x) (stat y)) (k ^ 2 * lam) ↔
      LowerBound (stat '' D) F cost lam := by
  rw [lowerBound_stat_image_iff D stat F (fun a b => k ^ 2 * cost a b)]
  constructor
  · intro h a ha b hb
    have hh := h a ha b hb
    rw [mul_assoc] at hh
    exact (mul_le_mul_iff_right₀ (sq_pos_of_ne_zero hk)).mp hh
  · intro h a ha b hb
    have hh := mul_le_mul_of_nonneg_left (h a ha b hb) (sq_nonneg k)
    simpa only [mul_assoc] using hh

/-- A scaled operational threshold is equivalent to the unscaled Gram-type
pair constraints over the actual attainable set. -/
theorem sq_mul_le_score_stat_image_iff {D : Set X} {stat : X → Y} {F : Y → ℝ}
    {cost : Y → Y → ℝ} (hn : NonconstantOn (stat '' D) F)
    (hc : ∀ a ∈ stat '' D, ∀ b ∈ stat '' D, 0 ≤ cost a b)
    (lam : ℝ) {k : ℝ} (hk : k ≠ 0) :
    k ^ 2 * lam ≤ score D (F ∘ stat)
      (fun x y => k ^ 2 * cost (stat x) (stat y)) ↔
      ∀ a ∈ stat '' D, ∀ b ∈ stat '' D,
        lam * (F a - F b) ^ 2 ≤ cost a b := by
  rw [score_stat_image_sq_scale hn hc hk,
    mul_le_mul_iff_right₀ (sq_pos_of_ne_zero hk)]
  exact le_score_iff hn hc lam

/-- Specialization of the exact score formula to a positive number of users. -/
theorem score_stat_image_user_count {D : Set X} {stat : X → Y} {F : Y → ℝ}
    {cost : Y → Y → ℝ} (hn : NonconstantOn (stat '' D) F)
    (hc : ∀ a ∈ stat '' D, ∀ b ∈ stat '' D, 0 ≤ cost a b)
    {K : ℕ} (hK : 0 < K) :
    score D (F ∘ stat) (fun x y => (K : ℝ) ^ 2 * cost (stat x) (stat y)) =
      (K : ℝ) ^ 2 * score (stat '' D) F cost := by
  apply score_stat_image_sq_scale hn hc
  exact_mod_cast Nat.ne_of_gt hK

end Analog.Operational
