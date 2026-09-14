import Analog.VarianceCollision
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Operational squared separation

The score is the actual infimum of squared-separation quotients. We prove
its characterization by all-pair inequalities, positive-score exactness,
and scaling. The target must be nonconstant on the admissible domain, so
the defining set is nonempty. No continuity or parametric encoder model is
assumed. These results do not classify continuous encoders.
-/

noncomputable section

namespace Analog.Operational

variable {X : Type*}

def NonconstantOn (D : Set X) (f : X → ℝ) : Prop :=
  ∃ x ∈ D, ∃ y ∈ D, f x ≠ f y

def Quotients (D : Set X) (f : X → ℝ) (cost : X → X → ℝ) : Set ℝ :=
  {q | ∃ x ∈ D, ∃ y ∈ D, f x ≠ f y ∧ q = cost x y / (f x - f y) ^ 2}

def score (D : Set X) (f : X → ℝ) (cost : X → X → ℝ) : ℝ :=
  sInf (Quotients D f cost)

def LowerBound (D : Set X) (f : X → ℝ) (cost : X → X → ℝ) (lam : ℝ) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, lam * (f x - f y) ^ 2 ≤ cost x y

lemma quotients_nonempty {D : Set X} {f : X → ℝ} (cost : X → X → ℝ)
    (h : NonconstantOn D f) : (Quotients D f cost).Nonempty := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  exact ⟨_, x, hx, y, hy, hxy, rfl⟩

lemma quotients_bddBelow {D : Set X} {f : X → ℝ} {cost : X → X → ℝ}
    (hc : ∀ x ∈ D, ∀ y ∈ D, 0 ≤ cost x y) : BddBelow (Quotients D f cost) := by
  refine ⟨0, ?_⟩
  rintro q ⟨x, hx, y, hy, _, rfl⟩
  exact div_nonneg (hc x hx y hy) (sq_nonneg _)

/-- The operational infimum is precisely the largest valid pairwise bound. -/
theorem le_score_iff {D : Set X} {f : X → ℝ} {cost : X → X → ℝ}
    (hn : NonconstantOn D f) (hc : ∀ x ∈ D, ∀ y ∈ D, 0 ≤ cost x y)
    (lam : ℝ) : lam ≤ score D f cost ↔ LowerBound D f cost lam := by
  constructor
  · intro h x hx y hy
    by_cases hxy : f x = f y
    · simpa only [hxy, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero] using hc x hx y hy
    · have hd : 0 < (f x - f y) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)
      have hm : cost x y / (f x - f y) ^ 2 ∈ Quotients D f cost :=
        ⟨x, hx, y, hy, hxy, rfl⟩
      exact (le_div_iff₀ hd).mp (h.trans (csInf_le (quotients_bddBelow hc) hm))
  · intro h
    apply le_csInf (quotients_nonempty cost hn)
    rintro q ⟨x, hx, y, hy, hxy, rfl⟩
    exact (le_div_iff₀ (sq_pos_of_ne_zero (sub_ne_zero.mpr hxy))).mpr (h x hx y hy)

theorem score_nonnegative {D : Set X} {f : X → ℝ} {cost : X → X → ℝ}
    (hn : NonconstantOn D f) (hc : ∀ x ∈ D, ∀ y ∈ D, 0 ≤ cost x y) :
    0 ≤ score D f cost := by
  apply (le_score_iff hn hc 0).mpr
  intro x hx y hy
  simpa using hc x hx y hy

theorem score_is_lowerBound {D : Set X} {f : X → ℝ} {cost : X → X → ℝ}
    (hn : NonconstantOn D f) (hc : ∀ x ∈ D, ∀ y ∈ D, 0 ≤ cost x y) :
    LowerBound D f cost (score D f cost) :=
  (le_score_iff hn hc _).mp le_rfl

/-- Multiplying every squared received distance by p multiplies the score by p. -/
theorem score_cost_scale {D : Set X} {f : X → ℝ} {cost : X → X → ℝ}
    (hn : NonconstantOn D f) (hc : ∀ x ∈ D, ∀ y ∈ D, 0 ≤ cost x y)
    {p : ℝ} (hp : 0 < p) :
    score D f (fun x y => p * cost x y) = p * score D f cost := by
  have hpc : ∀ x ∈ D, ∀ y ∈ D, 0 ≤ p * cost x y :=
    fun x hx y hy => mul_nonneg (le_of_lt hp) (hc x hx y hy)
  apply le_antisymm
  · have h : score D f (fun x y => p * cost x y) / p ≤ score D f cost := by
      apply (le_score_iff hn hc _).mpr
      intro x hx y hy
      have hh := score_is_lowerBound hn hpc x hx y hy
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hp).mpr
      simpa only [mul_comm] using hh
    have hh := (div_le_iff₀ hp).mp h
    simpa only [mul_comm] using hh
  · apply (le_score_iff hn hpc _).mpr
    intro x hx y hy
    have hh := mul_le_mul_of_nonneg_left (score_is_lowerBound hn hc x hx y hy) (le_of_lt hp)
    simpa only [mul_assoc] using hh

end Analog.Operational

namespace Analog.ArbitraryEncoder

def varianceScore (K : ℕ) (E : ℝ → ℝ × ℝ) : ℝ :=
  Operational.score {xs | ValidInput K xs} (variance K)
    (fun xs ys => squaredDistance (received E xs) (received E ys))

lemma squaredDistance_nonnegative (p q : ℝ × ℝ) : 0 ≤ squaredDistance p q := by
  unfold squaredDistance
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The operational infimum and the earlier pairwise definition agree. -/
theorem le_varianceScore_iff {K : ℕ} (E : ℝ → ℝ × ℝ)
    (hn : Operational.NonconstantOn {xs | ValidInput K xs} (variance K)) (lam : ℝ) :
    lam ≤ varianceScore K E ↔ SeparationLowerBound K E lam := by
  have h := Operational.le_score_iff hn
    (fun xs _ ys _ => squaredDistance_nonnegative (received E xs) (received E ys)) lam
  constructor
  · intro hl xs ys hxs hys
    exact h.mp hl xs hxs ys hys
  · intro hl
    exact h.mpr (fun xs hxs ys hys => hl xs ys hxs hys)

theorem positive_varianceScore_implies_exact {K : ℕ} (E : ℝ → ℝ × ℝ)
    (hn : Operational.NonconstantOn {xs | ValidInput K xs} (variance K))
    (hpos : 0 < varianceScore K E) : ExactVariance K E := by
  apply positive_separation_implies_exact hpos
  exact (le_varianceScore_iff E hn _).mp le_rfl

lemma variance_nonconstant {K : ℕ} (hK : 2 ≤ K) :
    Operational.NonconstantOn {xs | ValidInput K xs} (variance K) := by
  have hk2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hk : 1 < (K : ℝ) := by linarith
  have hk0 : (K : ℝ) ≠ 0 := by linarith
  have hz : ValidInput K (List.replicate K 0) := by
    constructor
    · simp
    · intro x hx
      have hx0 : x = 0 := (List.mem_replicate.mp hx).2
      subst x
      norm_num [InSource]
  have ho : ValidInput K (1 :: List.replicate (K - 1) 0) := by
    constructor
    · simp only [List.length_cons, List.length_replicate]
      omega
    · intro x hx
      simp only [List.mem_cons, List.mem_replicate] at hx
      rcases hx with hx | ⟨_, hx⟩ <;> subst x <;> norm_num [InSource]
  have hv0 : variance K (List.replicate K 0) = 0 := by
    simp [variance, firstMoment, secondMoment]
  have hv1 : variance K (1 :: List.replicate (K - 1) 0) =
      1 / (K : ℝ) - (1 / (K : ℝ)) ^ 2 := by
    simp [variance, firstMoment, secondMoment]
  have hid : 1 / (K : ℝ) - (1 / (K : ℝ)) ^ 2 =
      ((K : ℝ) - 1) / (K : ℝ) ^ 2 := by
    field_simp
  refine ⟨_, hz, _, ho, ?_⟩
  rw [hv0, hv1, hid]
  exact ne_of_lt (div_pos (by linarith) (sq_pos_of_ne_zero hk0))

/-- For every K >= 2, the actual variance score characterizes all pairwise bounds. -/
theorem varianceScore_characterization {K : ℕ} (hK : 2 ≤ K)
    (E : ℝ → ℝ × ℝ) (lam : ℝ) :
    lam ≤ varianceScore K E ↔ SeparationLowerBound K E lam :=
  le_varianceScore_iff E (variance_nonconstant hK) lam

def scalePoint (a : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (a * p.1, a * p.2)

def scaleEncoder (a : ℝ) (E : ℝ → ℝ × ℝ) : ℝ → ℝ × ℝ :=
  fun s => scalePoint a (E s)

lemma received_scale (a : ℝ) (E : ℝ → ℝ × ℝ) (xs : List ℝ) :
    received (scaleEncoder a E) xs = scalePoint a (received E xs) := by
  induction xs with
  | nil => ext <;> simp [received, scalePoint]
  | cons x xs ih =>
    simp only [received, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    ext <;> dsimp [scaleEncoder, scalePoint] <;> ring

lemma squaredDistance_scale (a : ℝ) (p q : ℝ × ℝ) :
    squaredDistance (scalePoint a p) (scalePoint a q) = a ^ 2 * squaredDistance p q := by
  dsimp [squaredDistance, scalePoint]
  ring

/-- Amplitude scaling by a nonzero a scales the operational score by a squared. -/
theorem varianceScore_scale {K : ℕ} (hK : 2 ≤ K) (E : ℝ → ℝ × ℝ)
    {a : ℝ} (ha : a ≠ 0) :
    varianceScore K (scaleEncoder a E) = a ^ 2 * varianceScore K E := by
  unfold varianceScore
  simp only [received_scale, squaredDistance_scale]
  exact Operational.score_cost_scale (variance_nonconstant hK)
    (fun xs _ ys _ => squaredDistance_nonnegative (received E xs) (received E ys))
    (sq_pos_of_ne_zero ha)

end Analog.ArbitraryEncoder
