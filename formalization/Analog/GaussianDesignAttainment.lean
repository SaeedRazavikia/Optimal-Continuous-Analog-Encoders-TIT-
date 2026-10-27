import Analog.GaussianDesignCompactness

/-!
# Attainment of the worst-case Gaussian design coefficient

We minimize its exact quadratic epigraph on the compact coefficient set. The
gradient spanning condition makes every finite epigraph point nonsingular;
therefore no singular minimizer or assumed boundary-divergence estimate is
needed. The peak-feasible identity competitor is constructed explicitly.
-/
noncomputable section
set_option maxHeartbeats 800000
namespace Analog.GaussianDesignAttainment
open Set HeterogeneousAttainment GaussianDesignCompactness GramSynthesis

def channelEnergy {K : ℕ} (p : Parameters K) (x y : ℝ) : ℝ :=
  (p.2.1.1*x + p.2.2.1*y)^2 + (p.2.1.2*x + p.2.2.2*y)^2

def coefficientDet {K : ℕ} (p : Parameters K) : ℝ :=
  p.2.1.1*p.2.2.2-p.2.1.2*p.2.2.1

def GradientSpans {X : Type*} (M : Set X) (w : X → ℝ × ℝ) : Prop :=
  ∀ x y : ℝ, (∀ m ∈ M, (w m).1*x + (w m).2*y = 0) → x = 0 ∧ y = 0

def QuadraticBound {K : ℕ} {X : Type*} (M : Set X) (w : X → ℝ × ℝ)
    (p : Parameters K) (t : ℝ) : Prop :=
  ∀ m ∈ M, ∀ x y : ℝ, ((w m).1*x + (w m).2*y)^2 ≤ t*channelEnergy p x y

theorem quadraticBound_nonsingular {K : ℕ} {X : Type*} {M : Set X}
    {w : X → ℝ × ℝ} (hspan : GradientSpans M w) {p : Parameters K} {t : ℝ}
    (hbound : QuadraticBound M w p t) : coefficientDet p ≠ 0 := by
  have hker (x y : ℝ) (hr : p.2.1.1*x+p.2.2.1*y=0)
      (hi : p.2.1.2*x+p.2.2.2*y=0) : x=0 ∧ y=0 := by
    apply hspan x y
    intro m hm
    have hh := hbound m hm x y
    simp only [channelEnergy, hr, hi, zero_pow (by norm_num : 2 ≠ 0),
      add_zero, mul_zero] at hh
    nlinarith [sq_nonneg ((w m).1*x+(w m).2*y)]
  intro hd
  dsimp [coefficientDet] at hd
  have h₁ := hker (-p.2.2.1) p.2.1.1 (by ring) (by nlinarith)
  have h₂ := hker (-p.2.2.2) p.2.1.2 (by nlinarith) (by ring)
  have h := hker 1 0 (by simp [h₁.2]) (by simp [h₂.2])
  norm_num at h

theorem quadraticBound_isClosed {K : ℕ} {X : Type*} (M : Set X) (w : X → ℝ × ℝ) :
    IsClosed {q : Parameters K × ℝ | QuadraticBound M w q.1 q.2} := by
  simp only [QuadraticBound, setOf_forall]
  apply isClosed_iInter
  intro m
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro y
  change IsClosed {q : Parameters K × ℝ |
    ((w m).1*x+(w m).2*y)^2 ≤ q.2*channelEnergy q.1 x y}
  exact isClosed_le continuous_const (by unfold channelEnergy; fun_prop)

theorem parameter_gram_positive {K : ℕ} {p : Parameters K} (hp : coefficientDet p ≠ 0) :
    0 < (parameterPlanar p).A ∧
      0 < det (parameterPlanar p).A (parameterPlanar p).B (parameterPlanar p).C := by
  have heq : det (parameterPlanar p).A (parameterPlanar p).B (parameterPlanar p).C =
      coefficientDet p ^ 2 := by
    unfold det parameterPlanar Planar.A Planar.B Planar.C coefficientDet
    ring
  refine ⟨?_, by rw [heq]; exact sq_pos_of_ne_zero hp⟩
  dsimp [parameterPlanar, Planar.A]
  by_contra hn
  have hzero : p.2.1.1 = 0 ∧ p.2.1.2 = 0 := by
    constructor <;> nlinarith [sq_nonneg p.2.1.1, sq_nonneg p.2.1.2]
  apply hp
  simp [coefficientDet, hzero.1, hzero.2]

theorem channelEnergy_eq_gram {K : ℕ} (p : Parameters K) (x y : ℝ) :
    channelEnergy p x y = form2 (parameterPlanar p).A (parameterPlanar p).B
      (parameterPlanar p).C x y := by
  unfold channelEnergy form2 parameterPlanar Planar.A Planar.B Planar.C
  ring

theorem dual_le_iff_quadratic (A B C w₁ w₂ t : ℝ)
    (hA : 0 < A) (hD : 0 < det A B C) (ht : 0 ≤ t) :
    dual A B C w₁ w₂ ≤ t ↔
      ∀ x y, (w₁*x+w₂*y)^2 ≤ t*form2 A B C x y := by
  constructor
  · intro hd x y
    exact (dual_cauchy A B C w₁ w₂ x y hD).trans
      (mul_le_mul_of_nonneg_right hd (form2_nonneg A B C hA hD x y))
  · intro hb
    by_cases hw : w₁ = 0 ∧ w₂ = 0
    · simpa [dual, hw.1, hw.2] using ht
    · have hp := dual_pos A B C w₁ w₂ hA hD (by tauto)
      have hh := hb (invX A B C w₁ w₂) (invY A B C w₁ w₂)
      rw [form2_inverse A B C w₁ w₂ (ne_of_gt hD)] at hh
      change (dual A B C w₁ w₂)^2 ≤ t*dual A B C w₁ w₂ at hh
      nlinarith

def inverseCoefficient {K : ℕ} {X : Type*} (p : Parameters K) (w : X → ℝ × ℝ) (m : X) : ℝ :=
  dual (parameterPlanar p).A (parameterPlanar p).B (parameterPlanar p).C (w m).1 (w m).2

theorem inverseCoefficient_nonneg {K : ℕ} {X : Type*} {p : Parameters K}
    (hp : coefficientDet p ≠ 0) (w : X → ℝ × ℝ) (m : X) :
    0 ≤ inverseCoefficient p w m := by
  obtain ⟨hA, hD⟩ := parameter_gram_positive hp
  rw [inverseCoefficient, ← form2_inverse _ _ _ _ _ (ne_of_gt hD)]
  exact form2_nonneg _ _ _ hA hD _ _

theorem quadraticBound_iff_inverseCoefficient {K : ℕ} {X : Type*} (M : Set X)
    (w : X → ℝ × ℝ) {p : Parameters K} (hp : coefficientDet p ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    QuadraticBound M w p t ↔ ∀ m ∈ M, inverseCoefficient p w m ≤ t := by
  obtain ⟨hA, hD⟩ := parameter_gram_positive hp
  simp only [QuadraticBound, channelEnergy_eq_gram, inverseCoefficient,
    dual_le_iff_quadratic _ _ _ _ _ _ hA hD ht]

theorem inverseCoefficient_continuousOn {K : ℕ} {X : Type*} [TopologicalSpace X]
    (p : Parameters K) {M : Set X} {w : X → ℝ × ℝ} (hw : ContinuousOn w M) :
    ContinuousOn (inverseCoefficient p w) M := by
  unfold inverseCoefficient dual invX invY
  exact (hw.fst.mul (((continuousOn_const.mul hw.fst).sub
    (continuousOn_const.mul hw.snd)).div_const _)).add
    (hw.snd.mul (((continuousOn_const.mul hw.snd).sub
    (continuousOn_const.mul hw.fst)).div_const _))

section CompactDesign
variable {K : ℕ} {S X : Type*} [TopologicalSpace S] [CompactSpace S]
    [TopologicalSpace X]

/-- The exact minimax-coefficient epigraph has a nonsingular minimizer under
the original feature-independence and gradient-spanning assumptions. -/
theorem quadratic_design_minimum (hK : 0 < K) (γ : Fin K → C(S, ℝ × ℝ))
    (hind : IndependentFeatures γ) {P : ℝ} (hP : 0 < P)
    (M : Set X) (hM : IsCompact M) (hne : M.Nonempty)
    (w : X → ℝ × ℝ) (hw : ContinuousOn w M) (hspan : GradientSpans M w) :
    ∃ p : Parameters K, ∃ t : ℝ,
      p ∈ coefficientPeakSet γ P ∧ 0 ≤ t ∧ QuadraticBound M w p t ∧
      coefficientDet p ≠ 0 ∧
      ∀ p' ∈ coefficientPeakSet γ P, ∀ t' : ℝ,
        0 ≤ t' → QuadraticBound M w p' t' → t ≤ t' := by
  obtain ⟨ε, hε, hpeak⟩ := exists_identity_peak γ hP
  obtain ⟨m₀, hm₀, hmax⟩ := hM.exists_isMaxOn hne
    ((hw.fst.pow 2).add (hw.snd.pow 2))
  let B := (w m₀).1^2+(w m₀).2^2
  have hB : 0 ≤ B := add_nonneg (sq_nonneg _) (sq_nonneg _)
  let p₀ : Parameters K := ((fun _ => (0, 0)), (ε, 0), (0, ε))
  let t₀ : ℝ := B / ε^2
  have ht₀ : 0 ≤ t₀ := div_nonneg hB (sq_nonneg _)
  have hq₀ : QuadraticBound M w p₀ t₀ := by
    intro m hm x y
    have hcs : ((w m).1*x+(w m).2*y)^2 ≤
        ((w m).1^2+(w m).2^2)*(x^2+y^2) := by
      nlinarith [sq_nonneg ((w m).1*y-(w m).2*x)]
    have hb := mul_le_mul_of_nonneg_right (hmax hm) (add_nonneg (sq_nonneg x) (sq_nonneg y))
    have heq : t₀ * channelEnergy p₀ x y = B*(x^2+y^2) := by
      dsimp [t₀, p₀, channelEnergy]
      field_simp [ne_of_gt hε]
      ring
    rw [heq]
    exact hcs.trans hb
  let C := coefficientPeakSet γ P
  let T : Set (Parameters K × ℝ) :=
    (C ×ˢ Icc 0 t₀) ∩ {q | QuadraticBound M w q.1 q.2}
  have hTc : IsCompact T :=
    ((coefficientPeakSet_isCompact hK γ hind hP.le).prod isCompact_Icc).inter_right
      (quadraticBound_isClosed M w)
  have hTne : T.Nonempty := ⟨(p₀,t₀), ⟨⟨hpeak, ⟨ht₀, le_rfl⟩⟩, hq₀⟩⟩
  obtain ⟨q, hq, hmin⟩ := hTc.exists_isMinOn hTne continuous_snd.continuousOn
  refine ⟨q.1, q.2, hq.1.1, hq.1.2.1, hq.2,
    quadraticBound_nonsingular hspan hq.2, ?_⟩
  intro p' hp' t' ht' hb'
  by_cases htt : t' ≤ t₀
  · exact hmin (show (p', t') ∈ T from ⟨⟨hp', ⟨ht', htt⟩⟩, hb'⟩)
  · exact hq.1.2.2.trans (le_of_not_ge htt)

/-- The actual maximum inverse-Gram energy is minimized by a fixed
nonsingular peak-feasible encoder. Maxima over moments and the minimum over
encoders are both attained. The Gaussian coefficient is this value / (2K²). -/
theorem inverse_gram_design_minimum (hK : 0 < K) (γ : Fin K → C(S, ℝ × ℝ))
    (hind : IndependentFeatures γ) {P : ℝ} (hP : 0 < P)
    (M : Set X) (hM : IsCompact M) (hne : M.Nonempty)
    (w : X → ℝ × ℝ) (hw : ContinuousOn w M) (hspan : GradientSpans M w) :
    ∃ p : Parameters K, p ∈ coefficientPeakSet γ P ∧ coefficientDet p ≠ 0 ∧
      ∃ m ∈ M, (∀ m' ∈ M, inverseCoefficient p w m' ≤ inverseCoefficient p w m) ∧
        ∀ p' ∈ coefficientPeakSet γ P, coefficientDet p' ≠ 0 →
          ∃ m' ∈ M, inverseCoefficient p w m ≤ inverseCoefficient p' w m' := by
  obtain ⟨p,t,hp,ht,hq,hd,hmin⟩ := quadratic_design_minimum hK γ hind hP M hM hne w hw hspan
  obtain ⟨m, hm, hmax⟩ := hM.exists_isMaxOn hne (inverseCoefficient_continuousOn p hw)
  have hm0 := inverseCoefficient_nonneg hd w m
  have hmt : inverseCoefficient p w m ≤ t :=
    (quadraticBound_iff_inverseCoefficient M w hd ht).mp hq m hm
  have htm : t ≤ inverseCoefficient p w m := hmin p hp _ hm0
    ((quadraticBound_iff_inverseCoefficient M w hd hm0).mpr hmax)
  refine ⟨p,hp,hd,m,hm,hmax,?_⟩
  intro p' hp' hd'
  obtain ⟨m', hm', hmax'⟩ := hM.exists_isMaxOn hne (inverseCoefficient_continuousOn p' hw)
  have hm0' := inverseCoefficient_nonneg hd' w m'
  refine ⟨m',hm',hmt.trans ?_⟩
  exact hmin p' hp' _ hm0'
    ((quadraticBound_iff_inverseCoefficient M w hd' hm0').mpr hmax')

end CompactDesign
end Analog.GaussianDesignAttainment
