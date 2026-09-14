import Analog.SynthesisAttainment

/-!
# Attainment of the inverse-risk frontier

Positive prior variance supplies a quantitative determinant barrier on risk
sublevels. Together with the compact continuum SDP set, this proves actual
frontier attainment, including at zero floor. Optimizer existence and
compactness are conclusions, not hypotheses.
-/

noncomputable section
open Set
namespace Analog.FrontierAttainment
open Analog.GramSynthesis
open Analog.Frontier
open Analog.SynthesisAttainment

lemma gram_B_pos (G : Gram) (hG : G.Positive) : 0 < G.B := by
  have hD := hG.2
  dsimp [det] at hD
  nlinarith [sq_nonneg G.C,hG.1]

lemma risk_pos {μ v : ℝ} (hv : 0 < v) (G : Gram) (hG : G.Positive) :
    0 < risk μ v G := by
  have h₁ := dual_pos G.A G.B G.C 1 0 hG.1 hG.2 (Or.inl one_ne_zero)
  have h₂ := dual_pos G.A G.B G.C μ 1 hG.1 hG.2 (Or.inr one_ne_zero)
  exact add_pos (mul_pos hv h₁) h₂

/-- Prior risk is bounded below by the reciprocal of the second feature
energy. This follows from the actual dual Cauchy inequality. -/
lemma risk_times_B_ge_one {μ v : ℝ} (hv : 0 ≤ v) (G : Gram) (hG : G.Positive) :
    1 ≤ risk μ v G * G.B := by
  have hc := dual_cauchy G.A G.B G.C μ 1 0 1 hG.2
  norm_num [form2] at hc
  have h₁ := dual_pos G.A G.B G.C 1 0 hG.1 hG.2 (Or.inl one_ne_zero)
  have hn := mul_nonneg (mul_nonneg hv h₁.le) (gram_B_pos G hG).le
  dsimp [risk, Gram.dual]
  nlinarith

lemma risk_times_det_ge_variance_B {μ v : ℝ} (hv : 0 ≤ v)
    (G : Gram) (hG : G.Positive) : v*G.B ≤ risk μ v G*det G.A G.B G.C := by
  have h₂ := dual_pos G.A G.B G.C μ 1 hG.1 hG.2 (Or.inr one_ne_zero)
  have he : G.dual 1 0*det G.A G.B G.C = G.B := by
    dsimp [Gram.dual]
    rw [dual_formula]
    simp only [one_pow, zero_pow (by decide : 2 ≠ 0), mul_one, mul_zero, sub_zero, add_zero]
    exact div_mul_cancel₀ _ (ne_of_gt hG.2)
  have hn := mul_nonneg h₂.le hG.2.le
  dsimp [risk]
  change 0 ≤ G.dual μ 1*det G.A G.B G.C at hn
  nlinarith

/-- An explicit barrier excludes singular Gram matrices from every finite
risk sublevel: det G >= v/R². It applies also when the floor is zero. -/
theorem determinant_barrier {μ v R : ℝ} (hv : 0 < v) (G : Gram)
    (hG : G.Positive) (hR : risk μ v G ≤ R) :
    0 < R ∧ v/R^2 ≤ det G.A G.B G.C := by
  have hp := risk_pos (μ := μ) hv G hG
  have hRp : 0 < R := hp.trans_le hR
  refine ⟨hRp, (div_le_iff₀ (sq_pos_of_pos hRp)).mpr ?_⟩
  have hB := gram_B_pos G hG
  have hc₁ := risk_times_B_ge_one (μ := μ) hv.le G hG
  have hc₂ := risk_times_det_ge_variance_B (μ := μ) hv.le G hG
  have hBR := mul_le_mul_of_nonneg_right hR hB.le
  have hDR := mul_le_mul_of_nonneg_right hR hG.2.le
  have hmul := mul_le_mul_of_nonneg_left (le_trans hc₂ hDR) hRp.le
  have hvar := mul_le_mul_of_nonneg_left (le_trans hc₁ hBR) hv.le
  nlinarith

def fromDesign (D : Design) (γ : ℝ) : Coordinates :=
  ![D.h,D.l₁,D.l₂,D.gram.A,D.gram.B,D.gram.C,γ]

def toDesign (q : Coordinates) : Design :=
  ⟨⟨q 3,q 4,q 5⟩,q 0,q 1,q 2⟩

lemma to_from_design (D : Design) (γ : ℝ) : toDesign (fromDesign D γ) = D := by
  cases D
  rfl

lemma from_design_feasible {φ : ℝ → ℝ} {P a b γ : ℝ} {D : Design}
    (hγ : 0 ≤ γ) (hD : Frontier.Feasible φ P a b γ D) :
    SynthesisAttainment.Feasible φ P a b (fromDesign D γ) := by
  refine ⟨hγ,hD.2.1,?_,hD.2.2.2.1,hD.2.2.2.2⟩
  intro s hs hs1
  exact hD.2.2.1 s hs hs1

lemma positive_of_psd_det {q : Coordinates}
    (hq : PSD3 (q 0) (q 1) (q 2) (q 3) (q 4) (q 5))
    (hd : 0 < det (q 3) (q 4) (q 5)) : (toDesign q).gram.Positive := by
  have ha := hq 0 1 0
  norm_num [form3,form2] at ha
  refine ⟨?_,hd⟩
  change 0 < q 3
  have hdet := hd
  dsimp [det] at hdet
  by_contra hn
  have hz : q 3 = 0 := le_antisymm (le_of_not_gt hn) ha
  rw [hz] at hdet
  nlinarith [sq_nonneg (q 5)]

lemma to_design_feasible {φ : ℝ → ℝ} {P a b γ : ℝ} {q : Coordinates}
    (hq : SynthesisAttainment.Feasible φ P a b q) (hγ : q 6 = γ)
    (hd : 0 < det (q 3) (q 4) (q 5)) : Frontier.Feasible φ P a b γ (toDesign q) := by
  refine ⟨positive_of_psd_det hq.2.1 hd,hq.2.1,?_,?_,?_⟩
  · intro s hs hs1
    exact hq.2.2.1 s hs hs1
  · simpa only [toDesign,hγ] using hq.2.2.2.1
  · simpa only [toDesign,hγ] using hq.2.2.2.2

lemma continuous_det : Continuous (fun q : Coordinates => det (q 3) (q 4) (q 5)) := by
  unfold det
  fun_prop

/-- A compact truncation at fixed floor and positive determinant margin. -/
def Truncated (φ : ℝ → ℝ) (P a b γ ε : ℝ) : Set Coordinates :=
  {q | SynthesisAttainment.Feasible φ P a b q ∧ q 6 = γ ∧ ε ≤ det (q 3) (q 4) (q 5)}

lemma truncated_isCompact {φ : ℝ → ℝ} (W : Anchors φ) {P a b γ ε : ℝ} (hP : 0 ≤ P) :
    IsCompact (Truncated φ P a b γ ε) := by
  exact (feasible_isCompact W hP).inter_right
    ((isClosed_eq (continuous_apply 6) continuous_const).inter
      (isClosed_le continuous_const continuous_det))

lemma risk_continuousOn_truncated (φ : ℝ → ℝ) (P a b γ μ v ε : ℝ) (hε : 0 < ε) :
    ContinuousOn (fun q : Coordinates => risk μ v (toDesign q).gram)
      (Truncated φ P a b γ ε) := by
  have hn : Continuous (fun q : Coordinates => ((v+μ^2)*q 4-2*μ*q 5+q 3)) := by
    fun_prop
  have hd := continuous_det
  have h := hn.continuousOn.div hd.continuousOn
    (s := Truncated φ P a b γ ε)
    (fun q hq => ne_of_gt (hε.trans_le hq.2.2))
  convert h using 1
  funext q
  exact risk_trace_formula μ v (toDesign q).gram

/-- The inverse-risk continuum Gram frontier attains its minimum, including
at zero floor. Only a feasible positive reference design and spanning feature
anchors are required; all compactness and barrier arguments are proved. -/
theorem minimum_attained {φ : ℝ → ℝ} (W : Anchors φ) {P a b μ v γ : ℝ}
    (hP : 0 ≤ P) (hv : 0 < v) (hγ : 0 ≤ γ)
    (hne : ∃ D : Design, Frontier.Feasible φ P a b γ D) :
    ∃ D : Design, Optimal φ P a b μ v γ D := by
  obtain ⟨D₀,h₀⟩ := hne
  let R := risk μ v D₀.gram
  have hR : 0 < R := risk_pos hv D₀.gram h₀.1
  let ε := v/R^2
  have hε : 0 < ε := div_pos hv (sq_pos_of_pos hR)
  have hbar₀ := (determinant_barrier hv D₀.gram h₀.1 (le_refl R)).2
  have hq₀ : fromDesign D₀ γ ∈ Truncated φ P a b γ ε :=
    ⟨from_design_feasible hγ h₀,rfl,hbar₀⟩
  obtain ⟨q,hq,hmin⟩ := (truncated_isCompact (a := a) (b := b) (γ := γ) (ε := ε) W hP).exists_isMinOn
    ⟨fromDesign D₀ γ,hq₀⟩ (risk_continuousOn_truncated φ P a b γ μ v ε hε)
  have hqd := to_design_feasible hq.1 hq.2.1 (hε.trans_le hq.2.2)
  have hqR : risk μ v (toDesign q).gram ≤ R := by
    have h := hmin hq₀
    simpa only [to_from_design] using h
  have hglobal : ∀ D : Design, Frontier.Feasible φ P a b γ D →
      risk μ v (toDesign q).gram ≤ risk μ v D.gram := by
    intro D hD
    by_cases hb : risk μ v D.gram ≤ R
    · have hbar := (determinant_barrier hv D.gram hD.1 hb).2
      have hmem : fromDesign D γ ∈ Truncated φ P a b γ ε :=
        ⟨from_design_feasible hγ hD,rfl,hbar⟩
      have h := hmin hmem
      simpa only [to_from_design] using h
    · exact hqR.trans (le_of_not_ge hb)
  refine ⟨toDesign q,hqd,le_antisymm ?_ (value_le hv.le hqd)⟩
  apply le_csInf (values_nonempty ⟨toDesign q,hqd⟩)
  rintro r ⟨D,hD,rfl⟩
  exact hglobal D hD


/-- Strict feature shape supplies the required anchors automatically. -/
theorem minimum_attained_of_strict_shape {φ : ℝ → ℝ} {P a b μ v γ : ℝ}
    (hP : 0 ≤ P) (hv : 0 < v) (hγ : 0 ≤ γ)
    (hshape : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ)
    (hne : ∃ D : Design, Frontier.Feasible φ P a b γ D) :
    ∃ D : Design, Optimal φ P a b μ v γ D :=
  minimum_attained (endpointAnchors φ (anchorGap_ne_zero_of_strict_shape hshape))
    hP hv hγ hne

/-- A positive maximum floor exists, and the risk minimum is attained at every
floor from zero through that maximum. The only requirements are the paper's
continuous strict feature shape, positive power and prior variance, and two
distinct endpoint directions. Neither a reference design nor anchors nor an
optimizer witness is supplied as an assumption. -/
theorem frontier_attained_on_maximal_interval {φ : ℝ → ℝ} {P a b μ v : ℝ}
    (hP : 0 < P) (hv : 0 < v) (hab : a ≠ b)
    (hcφ : ContinuousOn φ (Icc (-1 : ℝ) 1))
    (hshape : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ) :
    ∃ q : Coordinates, SynthesisAttainment.Feasible φ P a b q ∧ 0 < q 6 ∧
      (∀ r : Coordinates, SynthesisAttainment.Feasible φ P a b r → r 6 ≤ q 6) ∧
      ∀ γ : ℝ, 0 ≤ γ → γ ≤ q 6 → ∃ D : Design, Optimal φ P a b μ v γ D := by
  obtain ⟨q,hq,hqpos,hmax⟩ := positive_maximum_attained_of_strict_shape
    (a := a) (b := b) hP hcφ hshape
  have hind : a*1-1*b ≠ 0 := by simpa only [mul_one,one_mul] using sub_ne_zero.mpr hab
  have hpd := two_rank_one_constraints_positive (q 3) (q 4) (q 5) (q 6) a 1 b 1
    hqpos hind hq.2.2.2.1 hq.2.2.2.2
  have hD := to_design_feasible hq rfl hpd.2
  refine ⟨q,hq,hqpos,hmax,?_⟩
  intro γ hγ hγmax
  exact minimum_attained_of_strict_shape hP.le hv hγ hshape
    ⟨toDesign q,feasible_nested hγmax hD⟩

/-- Attainment and strict convexity together give a unique minimizing feature
Gram matrix. This existence statement includes zero floor. -/
theorem minimum_unique_gram_of_strict_shape {φ : ℝ → ℝ} {P a b μ v γ : ℝ}
    (hP : 0 ≤ P) (hv : 0 < v) (hγ : 0 ≤ γ)
    (hshape : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ)
    (hne : ∃ D : Design, Frontier.Feasible φ P a b γ D) :
    ∃ D : Design, Optimal φ P a b μ v γ D ∧
      ∀ E : Design, Optimal φ P a b μ v γ E → E.gram = D.gram := by
  obtain ⟨D,hD⟩ := minimum_attained_of_strict_shape hP hv hγ hshape hne
  exact ⟨D,hD,fun E hE => optimum_unique_gram hv hE hD⟩

end Analog.FrontierAttainment
