import Analog.VarianceCollision
import Mathlib.Analysis.Convex.Slope

/-! Collision preservation for arbitrary features and strictly convex or
strictly concave mean readouts. The proof uses two common completions and strict secant inequalities; no
differentiability of the readout is needed. No regularity restriction is
placed on the encoder or the feature. -/

noncomputable section
open Set
namespace Analog
namespace GeneralCollision
open ArbitraryEncoder

def featureMoment (φ : ℝ → ℝ) (xs : List ℝ) : ℝ := (xs.map φ).sum

def target (K : ℕ) (φ ψ : ℝ → ℝ) (xs : List ℝ) : ℝ :=
  featureMoment φ xs / (K : ℝ) - ψ (firstMoment xs / (K : ℝ))

/-- Exactness imposes no continuity or formula for the decoder. -/
def ExactTarget (K : ℕ) (φ ψ : ℝ → ℝ) (E : ℝ → ℝ × ℝ) : Prop :=
  ∀ xs ys : List ℝ, ValidInput K xs → ValidInput K ys →
    received E xs = received E ys → target K φ ψ xs = target K φ ψ ys

/-- A positive uniform operational separation bound for the general target. -/
def SeparationLowerBound (K : ℕ) (φ ψ : ℝ → ℝ) (E : ℝ → ℝ × ℝ) (lam : ℝ) : Prop :=
  ∀ xs ys : List ℝ, ValidInput K xs → ValidInput K ys →
    lam * (target K φ ψ xs - target K φ ψ ys) ^ 2 ≤
      squaredDistance (received E xs) (received E ys)

theorem positive_separation_implies_exact {K : ℕ} {φ ψ : ℝ → ℝ}
    {E : ℝ → ℝ × ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hsep : SeparationLowerBound K φ ψ E lam) : ExactTarget K φ ψ E := by
  intro xs ys hxs hys hcollision
  have hh := hsep xs ys hxs hys
  simp only [squaredDistance, hcollision, sub_self, zero_pow (by decide : 2 ≠ 0),
    add_zero] at hh
  have hsq : (target K φ ψ xs - target K φ ψ ys) ^ 2 ≤ 0 :=
    (mul_le_mul_iff_right₀ hlam).mp (by simpa only [mul_zero] using hh)
  nlinarith [sq_nonneg (target K φ ψ xs - target K φ ψ ys)]

lemma featureMoment_complete (K : ℕ) (φ : ℝ → ℝ) (xs : List ℝ) (w : ℝ) :
    featureMoment φ (completeTriple K xs w) =
      featureMoment φ xs + (φ w + (K - 4) • φ 0) := by
  simp [featureMoment, completeTriple]

lemma firstMoment_bounds (xs : List ℝ) (hxs : ∀ x ∈ xs, InSource x) :
    -(xs.length : ℝ) ≤ firstMoment xs ∧ firstMoment xs ≤ (xs.length : ℝ) := by
  induction xs with
  | nil => simp [firstMoment]
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have htail : ∀ y ∈ xs, InSource y := by
      intro y hy
      exact hxs y (by simp [hy])
    have hh := ih htail
    simp only [firstMoment, List.sum_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one] at hh ⊢
    rcases hx with ⟨hlo, hhi⟩
    constructor <;> linarith [hh.1, hh.2]

lemma triple_mean_interior {K : ℕ} (hK : 4 ≤ K) (xs : List ℝ)
    (hxs : ValidInput 3 xs) : firstMoment xs / (K : ℝ) ∈ Ioo (-1) 1 := by
  have hk : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hkpos : 0 < (K : ℝ) := by linarith
  have hx := firstMoment_bounds xs hxs.2
  rw [hxs.1] at hx
  norm_num at hx
  constructor
  · apply (lt_div_iff₀ hkpos).2
    linarith [hx.1]
  · apply (div_lt_iff₀ hkpos).2
    linarith [hx.2]

/-- Exact computation makes the shifted readout difference constant on an
open interval of common fourth-terminal inputs. -/
lemma completion_readout_difference {K : ℕ} (hK : 4 ≤ K)
    (φ ψ : ℝ → ℝ) (E : ℝ → ℝ × ℝ) (hexact : ExactTarget K φ ψ E)
    (xs ys : List ℝ) (hxs : ValidInput 3 xs) (hys : ValidInput 3 ys)
    (hcollision : received E xs = received E ys) (w : ℝ) (hw : InSource w) :
    ψ ((firstMoment xs + w) / (K : ℝ)) -
        ψ ((firstMoment ys + w) / (K : ℝ)) =
      (featureMoment φ xs - featureMoment φ ys) / (K : ℝ) := by
  have hh := hexact (completeTriple K xs w) (completeTriple K ys w)
    (completeTriple_valid hK hxs hw) (completeTriple_valid hK hys hw)
    (received_complete_collision K E xs ys w hcollision)
  simp only [target, featureMoment_complete, firstMoment_complete, add_div] at hh
  simp only [add_div, sub_div]
  linarith

/-- Strict convexity makes increments of fixed positive length strictly
increase with their starting point. -/
lemma strict_increment (ψ : ℝ → ℝ) (D : Set ℝ) (hψ : StrictConvexOn ℝ D ψ)
    (a b δ : ℝ) (ha : a ∈ D) (hbδ : b + δ ∈ D) (hab : a < b) (hδ : 0 < δ) :
    ψ (a + δ) - ψ a < ψ (b + δ) - ψ b := by
  have hlen : 0 < b + δ - a := by linarith
  have h1 := hψ.secant_strict_mono_aux1 ha hbδ
    (by linarith : a < a + δ) (by linarith : a + δ < b + δ)
  have h2 := hψ.secant_strict_mono_aux1 ha hbδ hab (by linarith : b < b + δ)
  have hh : (b + δ - a) * (ψ (a + δ) - ψ a) <
      (b + δ - a) * (ψ (b + δ) - ψ b) := by
    nlinarith only [h1, h2]
  exact (mul_lt_mul_iff_right₀ hlen).mp hh

/-- Equal positive-length increments identify the starting point for strictly
convex or strictly concave readouts. -/
lemma equal_increments_determine_center (ψ : ℝ → ℝ) (D : Set ℝ)
    (hshape : StrictConvexOn ℝ D ψ ∨ StrictConcaveOn ℝ D ψ)
    (a b δ : ℝ) (ha : a ∈ D) (haδ : a + δ ∈ D)
    (hb : b ∈ D) (hbδ : b + δ ∈ D) (hδ : 0 < δ)
    (heq : ψ (a + δ) - ψ a = ψ (b + δ) - ψ b) : a = b := by
  have hinj (g : ℝ → ℝ) (hg : StrictConvexOn ℝ D g)
      (he : g (a + δ) - g a = g (b + δ) - g b) : a = b := by
    rcases lt_trichotomy a b with hlt | heq | hgt
    · have hh := strict_increment g D hg a b δ ha hbδ hlt hδ
      linarith
    · exact heq
    · have hh := strict_increment g D hg b a δ hb haδ hgt hδ
      linarith
  rcases hshape with hc | hc
  · exact hinj ψ hc heq
  · apply hinj (-ψ) hc.neg
    simp only [Pi.neg_apply]
    linarith

lemma triple_shifted_mean_interior {K : ℕ} (hK : 4 ≤ K) (xs : List ℝ)
    (hxs : ValidInput 3 xs) (w : ℝ) (hw : w ∈ Ioo (-1 : ℝ) 1) :
    (firstMoment xs + w) / (K : ℝ) ∈ Ioo (-1) 1 := by
  have hk : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hkpos : 0 < (K : ℝ) := by linarith
  have hx := firstMoment_bounds xs hxs.2
  rw [hxs.1] at hx
  norm_num at hx
  constructor
  · apply (lt_div_iff₀ hkpos).2
    linarith [hx.1, hw.1]
  · apply (div_lt_iff₀ hkpos).2
    linarith [hx.2, hw.2]

/-- General triple-collision lemma. It covers arbitrary encoders and arbitrary
features, and even permits endpoint entries in the two triples. Strict
convexity/concavity is an actual hypothesis, not a derivative-injectivity proxy. -/
theorem triple_collision_preserves_moments {K : ℕ} (hK : 4 ≤ K)
    (φ ψ : ℝ → ℝ) (E : ℝ → ℝ × ℝ)
    (hshape : StrictConvexOn ℝ (Ioo (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Ioo (-1 : ℝ) 1) ψ)
    (hexact : ExactTarget K φ ψ E)
    (xs ys : List ℝ) (hxs : ValidInput 3 xs) (hys : ValidInput 3 ys)
    (hcollision : received E xs = received E ys) :
    firstMoment xs = firstMoment ys ∧ featureMoment φ xs = featureMoment φ ys := by
  have hk : (K : ℝ) ≠ 0 := by
    have hh : K ≠ 0 := by omega
    exact_mod_cast hh
  have hmx := triple_mean_interior hK xs hxs
  have hmy := triple_mean_interior hK ys hys
  have hkpos : 0 < (K : ℝ) := by
    have hh : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hδ : 0 < (1 / 2 : ℝ) / (K : ℝ) := div_pos (by norm_num) hkpos
  have hmxδ : firstMoment xs / (K : ℝ) + (1 / 2 : ℝ) / (K : ℝ) ∈ Ioo (-1) 1 := by
    rw [← add_div]
    exact triple_shifted_mean_interior hK xs hxs (1 / 2) (by norm_num)
  have hmyδ : firstMoment ys / (K : ℝ) + (1 / 2 : ℝ) / (K : ℝ) ∈ Ioo (-1) 1 := by
    rw [← add_div]
    exact triple_shifted_mean_interior hK ys hys (1 / 2) (by norm_num)
  have hz := completion_readout_difference hK φ ψ E hexact xs ys hxs hys hcollision
    0 (by norm_num [InSource])
  have hh := completion_readout_difference hK φ ψ E hexact xs ys hxs hys hcollision
    (1 / 2) (by norm_num [InSource])
  simp only [add_zero] at hz
  simp only [add_div] at hh
  have hmean := equal_increments_determine_center ψ (Ioo (-1 : ℝ) 1) hshape
    (firstMoment xs / (K : ℝ)) (firstMoment ys / (K : ℝ)) ((1 / 2 : ℝ) / (K : ℝ))
    hmx hmxδ hmy hmyδ hδ (by linarith)
  have hS : firstMoment xs = firstMoment ys := (div_left_inj' hk).mp hmean
  refine ⟨hS, ?_⟩
  have hzero := completion_readout_difference hK φ ψ E hexact xs ys hxs hys hcollision
    0 (by norm_num [InSource])
  simp only [add_zero, hS, sub_self] at hzero
  have ht : featureMoment φ xs - featureMoment φ ys = 0 :=
    (div_eq_zero_iff.mp hzero.symm).resolve_right hk
  linarith

/-- The general collision conclusion also follows from any positive uniform
separation bound, without requiring a supplied decoder. -/
theorem positive_separation_triple_collision {K : ℕ} (hK : 4 ≤ K)
    (φ ψ : ℝ → ℝ) (E : ℝ → ℝ × ℝ)
    (hshape : StrictConvexOn ℝ (Ioo (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Ioo (-1 : ℝ) 1) ψ)
    {lam : ℝ} (hlam : 0 < lam) (hsep : SeparationLowerBound K φ ψ E lam)
    (xs ys : List ℝ) (hxs : ValidInput 3 xs) (hys : ValidInput 3 ys)
    (hcollision : received E xs = received E ys) :
    firstMoment xs = firstMoment ys ∧ featureMoment φ xs = featureMoment φ ys := by
  exact triple_collision_preserves_moments hK φ ψ E hshape
    (positive_separation_implies_exact hlam hsep) xs ys hxs hys hcollision

end GeneralCollision
end Analog
