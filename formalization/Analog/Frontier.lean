import Analog.GramSynthesis
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Convex Gram frontier

The feasible set below uses the continuum peak inequalities and actual
positive-semidefinite quadratic forms. The risk is the inverse-Gram trace
for a prior with slope mean `μ` and positive slope variance `v`. We prove
convexity directly by completing the square, and define the frontier as an
actual infimum. No encoder rigidity, probabilistic limit, or existence of
an optimizer is assumed or asserted by these definitions.
-/

noncomputable section

namespace Analog.Frontier
open Analog.GramSynthesis

structure Gram where
  A : ℝ
  B : ℝ
  C : ℝ
  deriving DecidableEq

def Gram.Positive (G : Gram) : Prop := 0 < G.A ∧ 0 < det G.A G.B G.C

def Gram.mix (G H : Gram) (t : ℝ) : Gram :=
  ⟨(1-t)*G.A+t*H.A, (1-t)*G.B+t*H.B, (1-t)*G.C+t*H.C⟩

def Gram.quad (G : Gram) (x y : ℝ) : ℝ := form2 G.A G.B G.C x y

def Gram.dual (G : Gram) (x y : ℝ) : ℝ := GramSynthesis.dual G.A G.B G.C x y

def Gram.ix (G : Gram) (x y : ℝ) : ℝ := invX G.A G.B G.C x y

def Gram.iy (G : Gram) (x y : ℝ) : ℝ := invY G.A G.B G.C x y

lemma Gram.quad_mix (G H : Gram) (t x y : ℝ) :
    (G.mix H t).quad x y = (1-t)*G.quad x y+t*H.quad x y := by
  dsimp [Gram.mix, Gram.quad, form2]; ring

lemma Gram.positive_of_quad (G : Gram)
    (h : ∀ x y : ℝ, x ≠ 0 ∨ y ≠ 0 → 0 < G.quad x y) : G.Positive := by
  have hA : 0 < G.A := by simpa [Gram.quad, form2] using h 1 0 (Or.inl one_ne_zero)
  refine ⟨hA, ?_⟩
  have ht := h (-G.C) G.A (Or.inr (ne_of_gt hA))
  have he : G.quad (-G.C) G.A = G.A * det G.A G.B G.C := by
    dsimp [Gram.quad, form2, det]; ring
  rw [he] at ht
  nlinarith

lemma Gram.positive_mix (G H : Gram) (hG : G.Positive) (hH : H.Positive)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : (G.mix H t).Positive := by
  apply Gram.positive_of_quad
  intro x y hxy
  have hp := form2_pos G.A G.B G.C hG.1 hG.2 x y hxy
  have hq := form2_pos H.A H.B H.C hH.1 hH.2 x y hxy
  rw [Gram.quad_mix]
  change 0 < (1-t)*form2 G.A G.B G.C x y + t*form2 H.A H.B H.C x y
  by_cases ht0 : t = 0
  · simpa [ht0] using hp
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht1) hp.le)
      (mul_pos (lt_of_le_of_ne ht (Ne.symm ht0)) hq)

/-- The variational gap for the inverse quadratic form is itself a positive
quadratic form. This is the algebraic source of inverse-Gram convexity. -/
lemma Gram.dual_gap (G : Gram) (hG : G.Positive) (a b x y : ℝ) :
    G.dual a b - (2*(a*x+b*y)-G.quad x y) =
      G.quad (x-G.ix a b) (y-G.iy a b) := by
  have he := inverse_equations G.A G.B G.C a b (ne_of_gt hG.2)
  have hf := form2_inverse G.A G.B G.C a b (ne_of_gt hG.2)
  change G.A*G.ix a b + G.C*G.iy a b = a ∧
    G.C*G.ix a b + G.B*G.iy a b = b at he
  change G.quad (G.ix a b) (G.iy a b) = G.dual a b at hf
  have expand : G.quad (x-G.ix a b) (y-G.iy a b) =
      G.quad x y - 2*((G.A*G.ix a b+G.C*G.iy a b)*x +
        (G.C*G.ix a b+G.B*G.iy a b)*y)+G.quad (G.ix a b) (G.iy a b) := by
    dsimp [Gram.quad, form2]; ring
  rw [expand, he.1, he.2, hf]
  ring

lemma Gram.dual_variational_bound (G : Gram) (hG : G.Positive) (a b x y : ℝ) :
    2*(a*x+b*y)-G.quad x y ≤ G.dual a b := by
  have he := G.dual_gap hG a b x y
  have hn := form2_nonneg G.A G.B G.C hG.1 hG.2 (x-G.ix a b) (y-G.iy a b)
  change 0 ≤ G.quad (x-G.ix a b) (y-G.iy a b) at hn
  linarith

lemma Gram.dual_variational_eq (G : Gram) (hG : G.Positive) (a b : ℝ) :
    G.dual a b = 2*(a*G.ix a b+b*G.iy a b)-G.quad (G.ix a b) (G.iy a b) := by
  have he := G.dual_gap hG a b (G.ix a b) (G.iy a b)
  have hz : G.quad (G.ix a b-G.ix a b) (G.iy a b-G.iy a b) = 0 := by
    simp [Gram.quad, form2]
  rw [hz] at he
  linarith

/-- Convexity of every inverse-Gram directional cost, with no matrix inverse
convexity theorem assumed. -/
theorem Gram.dual_convex (G H : Gram) (hG : G.Positive) (hH : H.Positive)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (a b : ℝ) :
    (G.mix H t).dual a b ≤ (1-t)*G.dual a b+t*H.dual a b := by
  let J := G.mix H t
  have hJ := G.positive_mix H hG hH ht ht1
  have h₁ := G.dual_variational_bound hG a b (J.ix a b) (J.iy a b)
  have h₂ := H.dual_variational_bound hH a b (J.ix a b) (J.iy a b)
  have hw₁ := mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr ht1)
  have hw₂ := mul_le_mul_of_nonneg_left h₂ ht
  rw [Gram.dual_variational_eq J hJ]
  change 2*(a*J.ix a b+b*J.iy a b)-(G.mix H t).quad (J.ix a b) (J.iy a b) ≤ _
  rw [Gram.quad_mix]
  nlinarith

/-- The inverse trace for Q = [[v+μ², μ], [μ, 1]]. -/
def risk (μ v : ℝ) (G : Gram) : ℝ := v*G.dual 1 0+G.dual μ 1

theorem risk_trace_formula (μ v : ℝ) (G : Gram) :
    risk μ v G = ((v+μ^2)*G.B-2*μ*G.C+G.A)/det G.A G.B G.C := by
  dsimp [risk, Gram.dual]
  rw [dual_formula, dual_formula]
  ring

lemma risk_nonneg {μ v : ℝ} (hv : 0 ≤ v) (G : Gram) (hG : G.Positive) :
    0 ≤ risk μ v G := by
  have h₁ := dual_pos G.A G.B G.C 1 0 hG.1 hG.2 (Or.inl one_ne_zero)
  have h₂ := dual_pos G.A G.B G.C μ 1 hG.1 hG.2 (Or.inr one_ne_zero)
  exact add_nonneg (mul_nonneg hv h₁.le) h₂.le

theorem risk_convex {μ v : ℝ} (hv : 0 ≤ v) (G H : Gram)
    (hG : G.Positive) (hH : H.Positive) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    risk μ v (G.mix H t) ≤ (1-t)*risk μ v G+t*risk μ v H := by
  have h₁ := G.dual_convex H hG hH ht ht1 1 0
  have h₂ := G.dual_convex H hG hH ht ht1 μ 1
  have hw := mul_le_mul_of_nonneg_left h₁ hv
  dsimp [risk]
  nlinarith


lemma Gram.quad_eq_zero (G : Gram) (hG : G.Positive) {x y : ℝ}
    (h : G.quad x y = 0) : x = 0 ∧ y = 0 := by
  by_contra hn
  push_neg at hn
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_cases hx : x = 0
    · exact Or.inr (hn hx)
    · exact Or.inl hx
  have hp := form2_pos G.A G.B G.C hG.1 hG.2 x y hxy
  change 0 < G.quad x y at hp
  linarith

/-- Equality in directional inverse convexity forces the two inverse images
of that direction to coincide. -/
lemma Gram.dual_convex_equality (G H : Gram) (hG : G.Positive) (hH : H.Positive)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (a b : ℝ)
    (heq : (G.mix H t).dual a b = (1-t)*G.dual a b+t*H.dual a b) :
    G.ix a b = H.ix a b ∧ G.iy a b = H.iy a b := by
  let J := G.mix H t
  have hJ := G.positive_mix H hG hH ht.le ht1.le
  let x := J.ix a b
  let y := J.iy a b
  have h₁ := G.dual_variational_bound hG a b x y
  have h₂ := H.dual_variational_bound hH a b x y
  have he := J.dual_variational_eq hJ a b
  change J.dual a b = 2*(a*x+b*y)-(G.mix H t).quad x y at he
  rw [Gram.quad_mix] at he
  have hw₁ := mul_nonneg (sub_nonneg.mpr ht1.le)
    (sub_nonneg.mpr h₁)
  have hw₂ := mul_nonneg ht.le (sub_nonneg.mpr h₂)
  have he₁ : G.dual a b-(2*(a*x+b*y)-G.quad x y) = 0 := by
    change J.dual a b = _ at heq
    nlinarith
  have he₂ : H.dual a b-(2*(a*x+b*y)-H.quad x y) = 0 := by
    change J.dual a b = _ at heq
    nlinarith
  rw [G.dual_gap hG] at he₁
  rw [H.dual_gap hH] at he₂
  have hz₁ := G.quad_eq_zero hG he₁
  have hz₂ := H.quad_eq_zero hH he₂
  constructor <;> linarith [hz₁.1,hz₁.2,hz₂.1,hz₂.2]

lemma Gram.inverse_basis_det (G : Gram) (hG : G.Positive) (μ : ℝ) :
    G.ix 1 0*G.iy μ 1-G.iy 1 0*G.ix μ 1 = 1/det G.A G.B G.C := by
  have hD := ne_of_gt hG.2
  dsimp [Gram.ix, Gram.iy, invX, invY]
  field_simp
  dsimp [det]
  ring

private lemma vanish_of_two_rows (a b c d p q : ℝ)
    (hind : a*d-b*c ≠ 0) (h₁ : a*p+b*q = 0) (h₂ : c*p+d*q = 0) :
    p = 0 ∧ q = 0 := by
  have hp : (a*d-b*c)*p = 0 := by
    calc
      _ = d*(a*p+b*q)-b*(c*p+d*q) := by ring
      _ = 0 := by rw [h₁,h₂]; ring
  have hq : (a*d-b*c)*q = 0 := by
    calc
      _ = a*(c*p+d*q)-c*(a*p+b*q) := by ring
      _ = 0 := by rw [h₁,h₂]; ring
  exact ⟨(mul_eq_zero.mp hp).resolve_left hind,(mul_eq_zero.mp hq).resolve_left hind⟩

lemma Gram.inverse_basis_injective (G H : Gram) (hG : G.Positive) (hH : H.Positive)
    (μ : ℝ) (hx : G.ix 1 0 = H.ix 1 0) (hy : G.iy 1 0 = H.iy 1 0)
    (hx' : G.ix μ 1 = H.ix μ 1) (hy' : G.iy μ 1 = H.iy μ 1) : G = H := by
  have h₁ := inverse_equations G.A G.B G.C 1 0 (ne_of_gt hG.2)
  have h₂ := inverse_equations H.A H.B H.C 1 0 (ne_of_gt hH.2)
  have h₃ := inverse_equations G.A G.B G.C μ 1 (ne_of_gt hG.2)
  have h₄ := inverse_equations H.A H.B H.C μ 1 (ne_of_gt hH.2)
  change G.A*G.ix 1 0+G.C*G.iy 1 0 = 1 ∧ G.C*G.ix 1 0+G.B*G.iy 1 0 = 0 at h₁
  change H.A*H.ix 1 0+H.C*H.iy 1 0 = 1 ∧ H.C*H.ix 1 0+H.B*H.iy 1 0 = 0 at h₂
  change G.A*G.ix μ 1+G.C*G.iy μ 1 = μ ∧ G.C*G.ix μ 1+G.B*G.iy μ 1 = 1 at h₃
  change H.A*H.ix μ 1+H.C*H.iy μ 1 = μ ∧ H.C*H.ix μ 1+H.B*H.iy μ 1 = 1 at h₄
  rw [← hx,← hy] at h₂
  rw [← hx',← hy'] at h₄
  have hdet := G.inverse_basis_det hG μ
  have hn : G.ix 1 0*G.iy μ 1-G.iy 1 0*G.ix μ 1 ≠ 0 := by
    rw [hdet]
    exact one_div_ne_zero (ne_of_gt hG.2)
  have hrow₁ : G.ix 1 0*(G.A-H.A)+G.iy 1 0*(G.C-H.C) = 0 := by
    nlinarith [h₁.1,h₂.1]
  have hrow₂ : G.ix μ 1*(G.A-H.A)+G.iy μ 1*(G.C-H.C) = 0 := by
    nlinarith [h₃.1,h₄.1]
  have hrow₃ : G.ix 1 0*(G.C-H.C)+G.iy 1 0*(G.B-H.B) = 0 := by
    nlinarith [h₁.2,h₂.2]
  have hrow₄ : G.ix μ 1*(G.C-H.C)+G.iy μ 1*(G.B-H.B) = 0 := by
    nlinarith [h₃.2,h₄.2]
  have hac := vanish_of_two_rows _ _ _ _ _ _ hn hrow₁ hrow₂
  have hcb := vanish_of_two_rows _ _ _ _ _ _ hn hrow₃ hrow₄
  have hA := sub_eq_zero.mp hac.1
  have hC := sub_eq_zero.mp hac.2
  have hB := sub_eq_zero.mp hcb.2
  cases G
  cases H
  simp_all

/-- Positive prior variance makes the inverse trace strictly convex in the
feature Gram matrix. -/
theorem risk_strict_convex {μ v : ℝ} (hv : 0 < v) (G H : Gram)
    (hG : G.Positive) (hH : H.Positive) (hne : G ≠ H)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    risk μ v (G.mix H t) < (1-t)*risk μ v G+t*risk μ v H := by
  have hc := risk_convex (μ := μ) hv.le G H hG hH ht.le ht1.le
  apply lt_of_le_of_ne hc
  intro heq
  have h₁ := G.dual_convex H hG hH ht.le ht1.le 1 0
  have h₂ := G.dual_convex H hG hH ht.le ht1.le μ 1
  have hw := mul_le_mul_of_nonneg_left h₁ hv.le
  have he₁ : (G.mix H t).dual 1 0 = (1-t)*G.dual 1 0+t*H.dual 1 0 := by
    dsimp [risk] at heq
    nlinarith
  have he₂ : (G.mix H t).dual μ 1 = (1-t)*G.dual μ 1+t*H.dual μ 1 := by
    dsimp [risk] at heq
    nlinarith
  have hi₁ := G.dual_convex_equality H hG hH ht ht1 1 0 he₁
  have hi₂ := G.dual_convex_equality H hG hH ht ht1 μ 1 he₂
  exact hne (G.inverse_basis_injective H hG hH μ hi₁.1 hi₁.2 hi₂.1 hi₂.2)

structure Design where
  gram : Gram
  h : ℝ
  l₁ : ℝ
  l₂ : ℝ

def Design.mix (D E : Design) (t : ℝ) : Design :=
  ⟨D.gram.mix E.gram t, (1-t)*D.h+t*E.h,
    (1-t)*D.l₁+t*E.l₁, (1-t)*D.l₂+t*E.l₂⟩

def Design.energy (D : Design) (s z : ℝ) : ℝ :=
  form3 D.h D.l₁ D.l₂ D.gram.A D.gram.B D.gram.C 1 s z

lemma Design.form_mix (D E : Design) (t u x y : ℝ) :
    form3 (D.mix E t).h (D.mix E t).l₁ (D.mix E t).l₂
      (D.mix E t).gram.A (D.mix E t).gram.B (D.mix E t).gram.C u x y =
    (1-t)*form3 D.h D.l₁ D.l₂ D.gram.A D.gram.B D.gram.C u x y +
      t*form3 E.h E.l₁ E.l₂ E.gram.A E.gram.B E.gram.C u x y := by
  dsimp [Design.mix, Gram.mix, form3, form2]; ring

/-- The exact Gram feasibility constraints. Positive definiteness is imposed
explicitly to describe exact two-feature encoders also at zero floor. -/
def Feasible (φ : ℝ → ℝ) (P a b γ : ℝ) (D : Design) : Prop :=
  D.gram.Positive ∧ PSD3 D.h D.l₁ D.l₂ D.gram.A D.gram.B D.gram.C ∧
  (∀ s : ℝ, -1 ≤ s → s ≤ 1 → D.energy s (φ s) ≤ P) ∧
  RankOnePSD D.gram.A D.gram.B D.gram.C γ a 1 ∧
  RankOnePSD D.gram.A D.gram.B D.gram.C γ b 1

lemma rank_one_mono (G : Gram) {γ δ a b : ℝ} (hγδ : γ ≤ δ)
    (h : RankOnePSD G.A G.B G.C δ a b) : RankOnePSD G.A G.B G.C γ a b := by
  intro x y
  have hh := h x y
  have hw := mul_le_mul_of_nonneg_right hγδ (sq_nonneg (a*x+b*y))
  linarith

theorem feasible_nested {φ : ℝ → ℝ} {P a b γ δ : ℝ} {D : Design}
    (hγδ : γ ≤ δ) (hD : Feasible φ P a b δ D) : Feasible φ P a b γ D := by
  exact ⟨hD.1,hD.2.1,hD.2.2.1,rank_one_mono D.gram hγδ hD.2.2.2.1,
    rank_one_mono D.gram hγδ hD.2.2.2.2⟩

lemma rank_one_mix (G H : Gram) {γ δ a b t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hG : RankOnePSD G.A G.B G.C γ a b) (hH : RankOnePSD H.A H.B H.C δ a b) :
    RankOnePSD (G.mix H t).A (G.mix H t).B (G.mix H t).C ((1-t)*γ+t*δ) a b := by
  intro x y
  have h₁ := mul_nonneg (sub_nonneg.mpr ht1) (hG x y)
  have h₂ := mul_nonneg ht (hH x y)
  change 0 ≤ (G.mix H t).quad x y-((1-t)*γ+t*δ)*(a*x+b*y)^2
  rw [Gram.quad_mix]
  dsimp [Gram.quad] at *
  nlinarith

/-- Joint convexity in the full six-coordinate Gram design and the requested
separation floor. The peak condition is checked for every source value. -/
theorem feasible_mix {φ : ℝ → ℝ} {P a b γ δ t : ℝ} {D E : Design}
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hD : Feasible φ P a b γ D) (hE : Feasible φ P a b δ E) :
    Feasible φ P a b ((1-t)*γ+t*δ) (D.mix E t) := by
  refine ⟨D.gram.positive_mix E.gram hD.1 hE.1 ht ht1, ?_, ?_,
    rank_one_mix D.gram E.gram ht ht1 hD.2.2.2.1 hE.2.2.2.1,
    rank_one_mix D.gram E.gram ht ht1 hD.2.2.2.2 hE.2.2.2.2⟩
  · intro u x y
    rw [Design.form_mix]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (hD.2.1 u x y))
      (mul_nonneg ht (hE.2.1 u x y))
  · intro s hs hs1
    change form3 _ _ _ _ _ _ 1 s (φ s) ≤ P
    rw [Design.form_mix]
    have hd := mul_le_mul_of_nonneg_left (hD.2.2.1 s hs hs1) (sub_nonneg.mpr ht1)
    have he := mul_le_mul_of_nonneg_left (hE.2.2.1 s hs hs1) ht
    dsimp [Design.energy] at hd he
    nlinarith

/-- Objective values of actual continuum-feasible Gram designs. -/
def Values (φ : ℝ → ℝ) (P a b μ v γ : ℝ) : Set ℝ :=
  {r | ∃ D : Design, Feasible φ P a b γ D ∧ r = risk μ v D.gram}

def value (φ : ℝ → ℝ) (P a b μ v γ : ℝ) : ℝ :=
  sInf (Values φ P a b μ v γ)

lemma values_nonempty {φ : ℝ → ℝ} {P a b μ v γ : ℝ}
    (h : ∃ D, Feasible φ P a b γ D) : (Values φ P a b μ v γ).Nonempty := by
  obtain ⟨D,hD⟩ := h
  exact ⟨_,D,hD,rfl⟩

lemma values_bddBelow {φ : ℝ → ℝ} {P a b μ v γ : ℝ} (hv : 0 ≤ v) :
    BddBelow (Values φ P a b μ v γ) := by
  refine ⟨0, ?_⟩
  rintro r ⟨D,hD,rfl⟩
  exact risk_nonneg hv D.gram hD.1

lemma value_le {φ : ℝ → ℝ} {P a b μ v γ : ℝ} (hv : 0 ≤ v)
    {D : Design} (hD : Feasible φ P a b γ D) :
    value φ P a b μ v γ ≤ risk μ v D.gram :=
  csInf_le (values_bddBelow hv) ⟨D,hD,rfl⟩

lemma value_nonneg {φ : ℝ → ℝ} {P a b μ v γ : ℝ} (hv : 0 ≤ v)
    (h : ∃ D, Feasible φ P a b γ D) : 0 ≤ value φ P a b μ v γ := by
  apply le_csInf (values_nonempty h)
  rintro r ⟨D,hD,rfl⟩
  exact risk_nonneg hv D.gram hD.1

/-- The frontier is nondecreasing on every nonempty feasible range. -/
theorem value_monotone {φ : ℝ → ℝ} {P a b μ v γ δ : ℝ} (hv : 0 ≤ v)
    (hγδ : γ ≤ δ) (hδ : ∃ D, Feasible φ P a b δ D) :
    value φ P a b μ v γ ≤ value φ P a b μ v δ := by
  apply le_csInf (values_nonempty hδ)
  rintro r ⟨D,hD,rfl⟩
  exact value_le hv (feasible_nested hγδ hD)

lemma exists_risk_lt {φ : ℝ → ℝ} {P a b μ v γ ε : ℝ}
    (h : ∃ D, Feasible φ P a b γ D) (hε : 0 < ε) :
    ∃ D, Feasible φ P a b γ D ∧ risk μ v D.gram < value φ P a b μ v γ+ε := by
  obtain ⟨r,⟨D,hD,hr⟩,hbound⟩ :=
    exists_lt_of_csInf_lt (values_nonempty (μ := μ) (v := v) h)
      (show value φ P a b μ v γ < value φ P a b μ v γ+ε by linarith)
  exact ⟨D,hD,hr ▸ hbound⟩

/-- Convexity of the actual infimum frontier follows from feasible Gram mixing
and inverse-trace convexity. Approximate minimizers suffice; attainment is not
an extra hypothesis in this result. -/
theorem value_convex {φ : ℝ → ℝ} {P a b μ v γ δ t : ℝ} (hv : 0 ≤ v)
    (hγ : ∃ D, Feasible φ P a b γ D) (hδ : ∃ D, Feasible φ P a b δ D)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    value φ P a b μ v ((1-t)*γ+t*δ) ≤
      (1-t)*value φ P a b μ v γ+t*value φ P a b μ v δ := by
  by_contra hn
  have hgap : 0 < value φ P a b μ v ((1-t)*γ+t*δ)-
      ((1-t)*value φ P a b μ v γ+t*value φ P a b μ v δ) := by linarith
  let ε := (value φ P a b μ v ((1-t)*γ+t*δ)-
      ((1-t)*value φ P a b μ v γ+t*value φ P a b μ v δ))/2
  have hε : 0 < ε := half_pos hgap
  obtain ⟨D,hD,hd⟩ := exists_risk_lt (μ := μ) (v := v) hγ hε
  obtain ⟨E,hE,he⟩ := exists_risk_lt (μ := μ) (v := v) hδ hε
  have hc := value_le (μ := μ) hv (feasible_mix ht ht1 hD hE)
  have hr := risk_convex (μ := μ) hv D.gram E.gram hD.1 hE.1 ht ht1
  have hw₁ := mul_le_mul_of_nonneg_left hd.le (sub_nonneg.mpr ht1)
  have hw₂ := mul_le_mul_of_nonneg_left he.le ht
  change value φ P a b μ v ((1-t)*γ+t*δ) ≤ risk μ v (D.gram.mix E.gram t) at hc
  dsimp [ε] at *
  nlinarith


/-- An optimizer is an actual feasible design whose risk equals the infimum. -/
def Optimal (φ : ℝ → ℝ) (P a b μ v γ : ℝ) (D : Design) : Prop :=
  Feasible φ P a b γ D ∧ risk μ v D.gram = value φ P a b μ v γ

/-- Whenever optima exist, their feature Gram matrix is unique. Translation
coordinates need not be unique. -/
theorem optimum_unique_gram {φ : ℝ → ℝ} {P a b μ v γ : ℝ} (hv : 0 < v)
    {D E : Design} (hD : Optimal φ P a b μ v γ D)
    (hE : Optimal φ P a b μ v γ E) : D.gram = E.gram := by
  by_contra hn
  have hf := feasible_mix (t := (1:ℝ)/2) (by norm_num) (by norm_num) hD.1 hE.1
  have hfloor : (1-(1:ℝ)/2)*γ+((1:ℝ)/2)*γ = γ := by ring
  rw [hfloor] at hf
  have hl := value_le (μ := μ) hv.le hf
  have hs := risk_strict_convex (μ := μ) hv D.gram E.gram hD.1.1 hE.1.1 hn
    (t := (1:ℝ)/2) (by norm_num) (by norm_num)
  change value φ P a b μ v γ ≤ risk μ v (D.gram.mix E.gram ((1:ℝ)/2)) at hl
  rw [hD.2,hE.2] at hs
  linarith

/-- The unconstrained optimizer gives the full constant part of the frontier:
any floor it satisfies has exactly the unconstrained objective value. -/
theorem plateau_of_zero_floor_optimum {φ : ℝ → ℝ} {P a b μ v γ : ℝ}
    (hv : 0 ≤ v) (hγ : 0 ≤ γ) {D : Design}
    (hD : Optimal φ P a b μ v 0 D) (hfloor : Feasible φ P a b γ D) :
    value φ P a b μ v γ = value φ P a b μ v 0 := by
  apply le_antisymm
  · exact (value_le hv hfloor).trans hD.2.le
  · exact value_monotone hv hγ ⟨D,hfloor⟩

lemma feasible_of_same_gram {φ : ℝ → ℝ} {P a b γ δ : ℝ} {D E : Design}
    (hD : Feasible φ P a b γ D) (hE : Feasible φ P a b δ E)
    (hgram : D.gram = E.gram) : Feasible φ P a b δ D := by
  refine ⟨hD.1,hD.2.1,hD.2.2.1,?_,?_⟩
  · rw [hgram]; exact hE.2.2.2.1
  · rw [hgram]; exact hE.2.2.2.2

/-- Above the floors achieved by the zero-floor optimum, any attained optimum
must use the requested floor exactly: no strictly larger floor is feasible
for the same design. This is an activity statement independent of an assumed
formula for the score. -/
theorem optimal_floor_active {φ : ℝ → ℝ} {P a b μ v γ δ : ℝ}
    (hv : 0 < v) (hγ : 0 ≤ γ) (hγδ : γ < δ) {D₀ D : Design}
    (h₀ : Optimal φ P a b μ v 0 D₀) (hD : Optimal φ P a b μ v γ D)
    (hnot : ¬ Feasible φ P a b γ D₀) : ¬ Feasible φ P a b δ D := by
  intro hδ
  have hδpos : 0 < δ := lt_of_le_of_lt hγ hγδ
  have hn : D.gram ≠ D₀.gram := by
    intro he
    exact hnot (feasible_of_same_gram h₀.1 hD.1 he.symm)
  let t := (δ-γ)/(2*δ)
  have ht : 0 < t := div_pos (sub_pos.mpr hγδ) (mul_pos (by norm_num) hδpos)
  have ht1 : t < 1 := by
    apply (div_lt_one (mul_pos (by norm_num : (0:ℝ)<2) hδpos)).2
    linarith
  have hbudget : γ ≤ (1-t)*δ+t*0 := by
    have he : t*(2*δ) = δ-γ := div_mul_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) hδpos))
    nlinarith
  have hf := feasible_nested hbudget (feasible_mix ht.le ht1.le hδ h₀.1)
  have hl := value_le (μ := μ) hv.le hf
  have hs := risk_strict_convex (μ := μ) hv D.gram D₀.gram hD.1.1 h₀.1.1 hn ht ht1
  have hzero := value_monotone (μ := μ) hv.le hγ ⟨D,hD.1⟩
  have hw := mul_le_mul_of_nonneg_left hzero ht.le
  change value φ P a b μ v γ ≤ risk μ v (D.gram.mix D₀.gram t) at hl
  rw [hD.2,h₀.2] at hs
  nlinarith

/-- Strict increase above the constant portion, whenever the larger-floor
minimum is attained. Existence of such a minimum is a separate analytic issue. -/
theorem value_strict_after_plateau {φ : ℝ → ℝ} {P a b μ v γ δ : ℝ}
    (hv : 0 < v) (hγ : 0 ≤ γ) (hγδ : γ < δ) {D₀ D : Design}
    (h₀ : Optimal φ P a b μ v 0 D₀) (hD : Optimal φ P a b μ v δ D)
    (hnot : ¬ Feasible φ P a b γ D₀) :
    value φ P a b μ v γ < value φ P a b μ v δ := by
  have hm := value_monotone (μ := μ) hv.le hγδ.le ⟨D,hD.1⟩
  apply lt_of_le_of_ne hm
  intro he
  have hDγ : Optimal φ P a b μ v γ D :=
    ⟨feasible_nested hγδ.le hD.1,hD.2.trans he.symm⟩
  exact optimal_floor_active hv hγ hγδ h₀ hDγ hnot hD.1


/-- The actual endpoint separation floor of a positive feature Gram matrix. -/
def Gram.floor (G : Gram) (a b : ℝ) : ℝ := 1 / max (G.dual a 1) (G.dual b 1)

lemma Gram.floor_pos (G : Gram) (hG : G.Positive) (a b : ℝ) : 0 < G.floor a b := by
  apply one_div_pos.mpr
  exact lt_of_lt_of_le (dual_pos G.A G.B G.C a 1 hG.1 hG.2 (Or.inr one_ne_zero))
    (le_max_left _ _)

lemma Gram.le_floor_iff (G : Gram) (hG : G.Positive) (a b γ : ℝ) :
    γ ≤ G.floor a b ↔ γ ≤ 1/G.dual a 1 ∧ γ ≤ 1/G.dual b 1 := by
  have ha : 0 < G.dual a 1 := dual_pos G.A G.B G.C a 1 hG.1 hG.2 (Or.inr one_ne_zero)
  have hb : 0 < G.dual b 1 := dual_pos G.A G.B G.C b 1 hG.1 hG.2 (Or.inr one_ne_zero)
  dsimp [Gram.floor]
  rcases le_total (G.dual a 1) (G.dual b 1) with hab | hba
  · rw [max_eq_right hab]
    exact ⟨fun h => ⟨h.trans (one_div_le_one_div_of_le ha hab),h⟩,fun h => h.2⟩
  · rw [max_eq_left hba]
    exact ⟨fun h => ⟨h,h.trans (one_div_le_one_div_of_le hb hba)⟩,fun h => h.1⟩

/-- The feasible floor interval of each design is exactly its reciprocal
maximum endpoint inverse norm. -/
theorem feasible_iff_floor {φ : ℝ → ℝ} {P a b γ : ℝ} {D : Design}
    (hD : Feasible φ P a b 0 D) (hγ : 0 ≤ γ) :
    Feasible φ P a b γ D ↔ γ ≤ D.gram.floor a b := by
  rw [D.gram.le_floor_iff hD.1]
  have ha := rank_one_psd_iff D.gram.A D.gram.B D.gram.C γ a 1 hD.1.1 hD.1.2
    hγ (Or.inr one_ne_zero)
  have hb := rank_one_psd_iff D.gram.A D.gram.B D.gram.C γ b 1 hD.1.1 hD.1.2
    hγ (Or.inr one_ne_zero)
  constructor
  · intro h
    exact ⟨ha.mp h.2.2.2.1,hb.mp h.2.2.2.2⟩
  · intro h
    exact ⟨hD.1,hD.2.1,hD.2.2.1,ha.mpr h.1,hb.mpr h.2⟩

/-- The constant portion ends at the actual floor of the zero-floor optimizer,
provided the candidate higher-floor optimum is attained. -/
theorem plateau_exact {φ : ℝ → ℝ} {P a b μ v γ : ℝ} (hv : 0 < v)
    (hγ : 0 ≤ γ) {D₀ D : Design} (h₀ : Optimal φ P a b μ v 0 D₀)
    (hD : Optimal φ P a b μ v γ D) :
    value φ P a b μ v γ = value φ P a b μ v 0 ↔ γ ≤ D₀.gram.floor a b := by
  constructor
  · intro he
    have hd0 : Optimal φ P a b μ v 0 D :=
      ⟨feasible_nested hγ hD.1,hD.2.trans he⟩
    have hg := optimum_unique_gram hv h₀ hd0
    exact (feasible_iff_floor h₀.1 hγ).mp (feasible_of_same_gram h₀.1 hD.1 hg)
  · intro h
    exact plateau_of_zero_floor_optimum hv.le hγ h₀ ((feasible_iff_floor h₀.1 hγ).mpr h)

/-- On the increasing branch, the actual endpoint floor equals the requested
floor at every attained optimum. -/
theorem optimal_actual_floor_eq {φ : ℝ → ℝ} {P a b μ v γ : ℝ} (hv : 0 < v)
    (hγ : 0 ≤ γ) {D₀ D : Design} (h₀ : Optimal φ P a b μ v 0 D₀)
    (hD : Optimal φ P a b μ v γ D) (hbranch : D₀.gram.floor a b < γ) :
    D.gram.floor a b = γ := by
  have hd0 := feasible_nested hγ hD.1
  have hle := (feasible_iff_floor hd0 hγ).mp hD.1
  apply le_antisymm _ hle
  by_contra hn
  have hs : γ < D.gram.floor a b := lt_of_not_ge hn
  have hnot : ¬ Feasible φ P a b γ D₀ := by
    intro hf
    have ht := (feasible_iff_floor h₀.1 hγ).mp hf
    linarith
  have hdf := (feasible_iff_floor hd0 (D.gram.floor_pos hD.1.1 a b).le).mpr le_rfl
  exact optimal_floor_active hv hγ hs h₀ hD hnot hdf

/-- The manuscript's coefficient is the inverse trace divided by 2K². -/
def mseValue (K : ℝ) (φ : ℝ → ℝ) (P a b μ v γ : ℝ) : ℝ :=
  value φ P a b μ v γ/(2*K^2)

theorem mseValue_monotone {K : ℝ} (hK : 0 < K) {φ : ℝ → ℝ}
    {P a b μ v γ δ : ℝ} (hv : 0 ≤ v) (hγδ : γ ≤ δ)
    (hδ : ∃ D, Feasible φ P a b δ D) :
    mseValue K φ P a b μ v γ ≤ mseValue K φ P a b μ v δ := by
  exact div_le_div_of_nonneg_right (value_monotone hv hγδ hδ)
    (mul_pos (by norm_num) (sq_pos_of_pos hK)).le

theorem mseValue_convex {K : ℝ} (hK : 0 < K) {φ : ℝ → ℝ}
    {P a b μ v γ δ t : ℝ} (hv : 0 ≤ v)
    (hγ : ∃ D, Feasible φ P a b γ D) (hδ : ∃ D, Feasible φ P a b δ D)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    mseValue K φ P a b μ v ((1-t)*γ+t*δ) ≤
      (1-t)*mseValue K φ P a b μ v γ+t*mseValue K φ P a b μ v δ := by
  have h := div_le_div_of_nonneg_right (value_convex (μ := μ) hv hγ hδ ht ht1)
    (mul_pos (by norm_num : (0:ℝ) < 2) (sq_pos_of_pos hK)).le
  dsimp [mseValue]
  convert h using 1
  ring


/-- Every feasible frontier design admits a planar realization with unchanged
feature Gram matrix, endpoint constraints, and all continuum peak inequalities.
The Schur reduction handles the translation coordinate constructively. -/
theorem feasible_planar_realization {φ : ℝ → ℝ} {P a b γ : ℝ} {D : Design}
    (hD : Feasible φ P a b γ D) :
    ∃ e : Planar,
      e.A = D.gram.A ∧ e.B = D.gram.B ∧ e.C = D.gram.C ∧
      RankOnePSD e.A e.B e.C γ a 1 ∧ RankOnePSD e.A e.B e.C γ b 1 ∧
      ∀ s : ℝ, -1 ≤ s → s ≤ 1 → e.energy 1 s (φ s) ≤ P := by
  let e := reconstruct D.gram.A D.gram.B D.gram.C D.l₁ D.l₂
  have hg := reconstruct_lower_gram D.gram.A D.gram.B D.gram.C D.l₁ D.l₂ hD.1.1 hD.1.2
  have he := planar_synthesis D.h D.l₁ D.l₂ D.gram.A D.gram.B D.gram.C P φ
    hD.1.1 hD.1.2 hD.2.1 hD.2.2.1
  refine ⟨e,hg.1,hg.2.1,hg.2.2,?_,?_,he⟩
  · change RankOnePSD (reconstruct _ _ _ _ _).A (reconstruct _ _ _ _ _).B
      (reconstruct _ _ _ _ _).C γ a 1
    rw [hg.1,hg.2.1,hg.2.2]
    exact hD.2.2.2.1
  · change RankOnePSD (reconstruct _ _ _ _ _).A (reconstruct _ _ _ _ _).B
      (reconstruct _ _ _ _ _).C γ b 1
    rw [hg.1,hg.2.1,hg.2.2]
    exact hD.2.2.2.2

end Analog.Frontier
