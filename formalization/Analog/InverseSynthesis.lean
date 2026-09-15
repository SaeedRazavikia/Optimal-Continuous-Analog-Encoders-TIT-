import Analog.FrontierAttainment

/-!
# Enclosing-ellipse coordinates

We prove the automatic positive definiteness of the five-variable block
constraints, their Schur-complement interpretation, and their equivalence
with the continuum Gram design after reducing the translation diagonal.
-/

noncomputable section
open Set
namespace Analog.InverseSynthesis
open Analog.GramSynthesis Analog.Frontier Analog.SynthesisAttainment
open Analog.FrontierAttainment

/-- If a direction has zero lower-block energy in a positive-semidefinite
block matrix, it is orthogonal to the off-diagonal column. -/
lemma psd3_null_orthogonal {h l₁ l₂ A B C x y : ℝ}
    (hp : PSD3 h l₁ l₂ A B C) (hz : form2 A B C x y = 0) :
    l₁*x+l₂*y = 0 := by
  have hh := hp 1 0 0
  norm_num [form3,form2] at hh
  let L := l₁*x+l₂*y
  have ht := hp L (-(h+1)*x) (-(h+1)*y)
  have he : form3 h l₁ l₂ A B C L (-(h+1)*x) (-(h+1)*y) =
      -(h+2)*L^2 + (h+1)^2*form2 A B C x y := by
    dsimp [L,form3,form2]; ring
  rw [he,hz,mul_zero,add_zero] at ht
  by_contra hn
  have hs : 0 < L^2 := sq_pos_of_ne_zero hn
  have hm := mul_pos (show 0 < h+2 by linarith) hs
  nlinarith

/-- The paper's five real variables: a symmetric inverse Gram matrix and an
ellipse center. No positive-definiteness condition is built into feasibility. -/
structure Ellipse where
  inverseGram : Gram
  center₁ : ℝ
  center₂ : ℝ

def Feasible (φ : ℝ → ℝ) (P : ℝ) (E : Ellipse) : Prop :=
  ∀ s ∈ Icc (-1 : ℝ) 1,
    PSD3 P (s-E.center₁) (φ s-E.center₂)
      E.inverseGram.A E.inverseGram.B E.inverseGram.C

/-- Three noncollinear points of the preprocessing graph force every feasible
inverse Gram matrix to be positive definite. -/
theorem positive_of_feasible {φ : ℝ → ℝ} {P : ℝ} {E : Ellipse}
    (hgap : anchorGap φ ≠ 0) (hE : Feasible φ P E) : E.inverseGram.Positive := by
  apply Gram.positive_of_quad
  intro x y hxy
  have h₀ := hE 0 (by norm_num)
  have hn := h₀ 0 x y
  simp only [form3,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_mul,zero_add] at hn
  change 0 ≤ E.inverseGram.quad x y at hn
  apply lt_of_le_of_ne hn
  intro he
  have hz : form2 E.inverseGram.A E.inverseGram.B E.inverseGram.C x y = 0 := he.symm
  have hm := psd3_null_orthogonal (hE (-1) (by norm_num)) hz
  have hc := psd3_null_orthogonal h₀ hz
  have hp := psd3_null_orthogonal (hE 1 (by norm_num)) hz
  have hgapY : anchorGap φ * y = 0 := by
    dsimp [anchorGap]
    nlinarith
  have hy : y = 0 := (mul_eq_zero.mp hgapY).resolve_left hgap
  have hx : x = 0 := by rw [hy] at hm hc; nlinarith
  rcases hxy with hxy | hxy
  · exact hxy hx
  · exact hxy hy

/-- The continuum block inequalities describe exactly the enclosing ellipse.
Positive definiteness is derived from the graph, rather than assumed. -/
theorem feasible_iff_ellipse {φ : ℝ → ℝ} {P : ℝ} {E : Ellipse}
    (hgap : anchorGap φ ≠ 0) :
    Feasible φ P E ↔ E.inverseGram.Positive ∧
      ∀ s ∈ Icc (-1 : ℝ) 1,
        E.inverseGram.dual (s-E.center₁) (φ s-E.center₂) ≤ P := by
  constructor
  · intro hE
    have hp := positive_of_feasible hgap hE
    exact ⟨hp, fun s hs => (psd3_iff_schur _ _ _ _ _ _ hp.1 hp.2).mp (hE s hs)⟩
  · rintro ⟨hp,hE⟩ s hs
    exact (psd3_iff_schur _ _ _ _ _ _ hp.1 hp.2).mpr (hE s hs)

/-- Inversion in the three coordinates of a symmetric two-dimensional Gram
matrix. -/
def inverse (G : Gram) : Gram :=
  ⟨G.B/det G.A G.B G.C, G.A/det G.A G.B G.C, -G.C/det G.A G.B G.C⟩

lemma inverse_det (G : Gram) (hG : G.Positive) :
    det (inverse G).A (inverse G).B (inverse G).C = 1/det G.A G.B G.C := by
  have hn := ne_of_gt hG.2
  dsimp [inverse,det] at *
  field_simp

lemma inverse_positive (G : Gram) (hG : G.Positive) : (inverse G).Positive := by
  refine ⟨div_pos (gram_B_pos G hG) hG.2, ?_⟩
  rw [inverse_det G hG]
  exact one_div_pos.mpr hG.2

lemma inverse_quad (G : Gram) (x y : ℝ) : (inverse G).quad x y = G.dual x y := by
  dsimp [Gram.quad,Gram.dual,inverse,form2]
  rw [dual_formula]
  ring

lemma inverse_involutive (G : Gram) (hG : G.Positive) : inverse (inverse G) = G := by
  have hn := ne_of_gt hG.2
  have hd := inverse_det G hG
  change (⟨(inverse G).B / det (inverse G).A (inverse G).B (inverse G).C,
    (inverse G).A / det (inverse G).A (inverse G).B (inverse G).C,
    -(inverse G).C / det (inverse G).A (inverse G).B (inverse G).C⟩ : Gram) = G
  rw [hd]
  cases G
  dsimp only [inverse]
  congr 1 <;> field_simp

lemma inverse_dual (G : Gram) (hG : G.Positive) (x y : ℝ) :
    (inverse G).dual x y = G.quad x y := by
  rw [← inverse_quad, inverse_involutive G hG]

/-- Centering the preprocessing graph gives a Gram design with its translation
diagonal already at the Schur value. -/
def ellipseDesign (E : Ellipse) : Design :=
  let G := inverse E.inverseGram
  ⟨G, G.quad E.center₁ E.center₂,
    -(G.A*E.center₁+G.C*E.center₂), -(G.C*E.center₁+G.B*E.center₂)⟩

lemma ellipseDesign_form (E : Ellipse) (t x y : ℝ) :
    form3 (ellipseDesign E).h (ellipseDesign E).l₁ (ellipseDesign E).l₂
      (ellipseDesign E).gram.A (ellipseDesign E).gram.B (ellipseDesign E).gram.C t x y =
    (inverse E.inverseGram).quad (x-t*E.center₁) (y-t*E.center₂) := by
  dsimp [ellipseDesign,Gram.quad,form3,form2]
  ring

/-- Every feasible enclosing ellipse produces a genuine continuum-feasible
Gram design at zero floor; all nonnegative robustness floors can subsequently
be imposed through their endpoint budgets. -/
theorem ellipse_to_gram {φ : ℝ → ℝ} {P a b : ℝ} {E : Ellipse}
    (hgap : anchorGap φ ≠ 0) (hE : Feasible φ P E) :
    Frontier.Feasible φ P a b 0 (ellipseDesign E) := by
  have hp := positive_of_feasible hgap hE
  have hG := inverse_positive E.inverseGram hp
  have he := (feasible_iff_ellipse hgap).mp hE
  refine ⟨hG, ?_, ?_, ?_, ?_⟩
  · intro t x y
    rw [ellipseDesign_form]
    exact form2_nonneg _ _ _ hG.1 hG.2 _ _
  · intro s hs hs1
    change form3 _ _ _ _ _ _ 1 s (φ s) ≤ P
    rw [ellipseDesign_form,one_mul,one_mul,inverse_quad]
    exact he.2 s ⟨hs,hs1⟩
  · intro x y
    simpa only [zero_mul,sub_zero] using
      form2_nonneg _ _ _ hG.1 hG.2 x y
  · intro x y
    simpa only [zero_mul,sub_zero] using
      form2_nonneg _ _ _ hG.1 hG.2 x y

/-- A Gram design determines its enclosing ellipse by inverting the lower
block and absorbing the translation into the center. -/
def designEllipse (D : Design) : Ellipse :=
  ⟨inverse D.gram, -D.gram.ix D.l₁ D.l₂, -D.gram.iy D.l₁ D.l₂⟩

/-- Conversely, every continuum-feasible positive Gram design gives a feasible
enclosing ellipse, including when the translation diagonal has Schur slack. -/
theorem gram_to_ellipse {φ : ℝ → ℝ} {P a b γ : ℝ} {D : Design}
    (hgap : anchorGap φ ≠ 0) (hD : Frontier.Feasible φ P a b γ D) :
    Feasible φ P (designEllipse D) := by
  apply (feasible_iff_ellipse hgap).mpr
  refine ⟨inverse_positive D.gram hD.1, ?_⟩
  intro s hs
  change (inverse D.gram).dual (s - -D.gram.ix D.l₁ D.l₂)
    (φ s - -D.gram.iy D.l₁ D.l₂) ≤ P
  rw [inverse_dual D.gram hD.1]
  have he := schur_identity D.h D.l₁ D.l₂ D.gram.A D.gram.B D.gram.C
    1 s (φ s) (ne_of_gt hD.1.2)
  have hn := (psd3_iff_schur _ _ _ _ _ _ hD.1.1 hD.1.2).mp hD.2.1
  have hb := hD.2.2.1 s hs.1 hs.2
  simp only [one_pow,mul_one,one_mul] at he
  dsimp [Design.energy] at hb
  simp only [sub_neg_eq_add]
  change form2 _ _ _ _ _ ≤ P
  change _ = _ + form2 _ _ _ (s + D.gram.ix D.l₁ D.l₂)
    (φ s + D.gram.iy D.l₁ D.l₂) at he
  linarith

/-- The round trip preserves the two-statistic Gram matrix exactly; only a
possible surplus in the translation diagonal is removed. -/
theorem roundtrip_gram {D : Design} (hD : D.gram.Positive) :
    (ellipseDesign (designEllipse D)).gram = D.gram :=
  inverse_involutive D.gram hD

/-- Inverse-coordinate endpoint costs are the original directional inverse
norms, so the objective and every robustness budget are unchanged. -/
theorem endpoint_cost_preserved (D : Design) (w : ℝ) :
    (designEllipse D).inverseGram.quad w 1 = D.gram.dual w 1 :=
  inverse_quad D.gram w 1

/-- The five-variable ellipse class and the positive Gram design class are
both nonempty under exactly the same peak constraints. -/
theorem feasible_class_nonempty_iff {φ : ℝ → ℝ} {P a b : ℝ}
    (hgap : anchorGap φ ≠ 0) :
    (∃ E : Ellipse, Feasible φ P E) ↔
      ∃ D : Design, Frontier.Feasible φ P a b 0 D := by
  constructor
  · rintro ⟨E,hE⟩
    exact ⟨ellipseDesign E,ellipse_to_gram hgap hE⟩
  · rintro ⟨D,hD⟩
    exact ⟨designEllipse D,gram_to_ellipse hgap hD⟩

/-- Maximum endpoint sensitivity in inverse coordinates. -/
def objective (E : Ellipse) (a b : ℝ) : ℝ :=
  max (E.inverseGram.quad a 1) (E.inverseGram.quad b 1)

lemma objective_pos {φ : ℝ → ℝ} {P : ℝ} {E : Ellipse}
    (hgap : anchorGap φ ≠ 0) (hE : Feasible φ P E) (a b : ℝ) :
    0 < objective E a b := by
  have hp := positive_of_feasible hgap hE
  exact lt_of_lt_of_le (form2_pos _ _ _ hp.1 hp.2 a 1 (Or.inr one_ne_zero))
    (le_max_left _ _)

lemma objective_designEllipse (D : Design) (a b : ℝ) :
    objective (designEllipse D) a b = 1 / D.gram.floor a b := by
  unfold objective
  rw [endpoint_cost_preserved,endpoint_cost_preserved]
  simp [Gram.floor]

lemma ellipseDesign_floor {φ : ℝ → ℝ} {P : ℝ} {E : Ellipse}
    (hgap : anchorGap φ ≠ 0) (hE : Feasible φ P E) (a b : ℝ) :
    (ellipseDesign E).gram.floor a b = 1 / objective E a b := by
  have hp := positive_of_feasible hgap hE
  change 1 / max ((inverse E.inverseGram).dual a 1)
    ((inverse E.inverseGram).dual b 1) = _
  rw [inverse_dual E.inverseGram hp,inverse_dual E.inverseGram hp]
  rfl

/-- The enclosing-ellipse program attains a positive optimum reciprocal to
the maximal Gram separation floor. Existence, positive definiteness, and the
reciprocity relation are all conclusions under the manuscript assumptions. -/
theorem inverse_optimum_attained_of_strict_shape {φ : ℝ → ℝ} {P a b : ℝ}
    (hP : 0 < P) (hab : a ≠ b)
    (hcφ : ContinuousOn φ (Icc (-1 : ℝ) 1))
    (hshape : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ) :
    ∃ E : Ellipse, ∃ q : Coordinates,
      Feasible φ P E ∧ 0 < objective E a b ∧
      SynthesisAttainment.Feasible φ P a b q ∧ 0 < q 6 ∧
      (∀ r : Coordinates, SynthesisAttainment.Feasible φ P a b r → r 6 ≤ q 6) ∧
      objective E a b = 1 / q 6 ∧
      ∀ E' : Ellipse, Feasible φ P E' → objective E a b ≤ objective E' a b := by
  have hgap := anchorGap_ne_zero_of_strict_shape hshape
  obtain ⟨q,hq,hqpos,hmax⟩ := positive_maximum_attained_of_strict_shape
    (a := a) (b := b) hP hcφ hshape
  have hind : a*1-1*b ≠ 0 := by simpa only [mul_one,one_mul] using sub_ne_zero.mpr hab
  have hpd := two_rank_one_constraints_positive (q 3) (q 4) (q 5) (q 6) a 1 b 1
    hqpos hind hq.2.2.2.1 hq.2.2.2.2
  let D := toDesign q
  have hD : Frontier.Feasible φ P a b (q 6) D := to_design_feasible hq rfl hpd.2
  have hD0 := feasible_nested hqpos.le hD
  have hfloorpos := D.gram.floor_pos hD.1 a b
  have hfloorfeas := (feasible_iff_floor hD0 hfloorpos.le).mpr (le_refl (D.gram.floor a b))
  have hfloorle := hmax (fromDesign D (D.gram.floor a b))
    (from_design_feasible hfloorpos.le hfloorfeas)
  have hfloor : D.gram.floor a b = q 6 :=
    le_antisymm hfloorle ((feasible_iff_floor hD0 hqpos.le).mp hD)
  have hE := gram_to_ellipse hgap hD
  have hobj : objective (designEllipse D) a b = 1/q 6 := by
    rw [objective_designEllipse,hfloor]
  refine ⟨designEllipse D,q,hE,objective_pos hgap hE a b,hq,hqpos,hmax,hobj,?_⟩
  intro E' hE'
  have hp := objective_pos hgap hE' a b
  have hF0 : Frontier.Feasible φ P a b 0 (ellipseDesign E') := ellipse_to_gram hgap hE'
  have hFfloor := (feasible_iff_floor hF0 (one_div_pos.mpr hp).le).mpr
    (le_of_eq (ellipseDesign_floor hgap hE' a b).symm)
  have hbound := hmax (fromDesign (ellipseDesign E') (1/objective E' a b))
    (from_design_feasible (one_div_pos.mpr hp).le hFfloor)
  change 1/objective E' a b ≤ q 6 at hbound
  rw [hobj]
  apply (div_le_iff₀ hqpos).mpr
  have ht := (div_le_iff₀ hp).mp hbound
  nlinarith

end Analog.InverseSynthesis
