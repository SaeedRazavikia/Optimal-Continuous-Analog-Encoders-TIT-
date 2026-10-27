import Analog.FrontierAttainment
import Mathlib.Topology.Semicontinuous

/-!
# Continuity of the robust small-noise frontier

The actual inverse-risk value is lower semicontinuous because each finite
risk sublevel projects from a compact set of continuum-feasible Gram designs.
This proves continuity at the maximal floor as well as on the interior. At
zero, the positive actual floor of the unconstrained optimizer supplies a
neighborhood on which the frontier is constant.
-/

noncomputable section
open Set Filter Topology
namespace Analog.FrontierContinuity
open Analog.GramSynthesis Analog.Frontier Analog.SynthesisAttainment
open Analog.FrontierAttainment

/-- Polynomial description of a finite risk sublevel; the determinant margin
is supplied by the proved inverse-risk barrier. -/
def RiskSublevel (φ : ℝ → ℝ) (P a b μ v R : ℝ) : Set Coordinates :=
  {q | SynthesisAttainment.Feasible φ P a b q ∧
    v / R^2 ≤ det (q 3) (q 4) (q 5) ∧
    (v + μ^2) * q 4 - 2*μ*q 5 + q 3 ≤ R * det (q 3) (q 4) (q 5)}

lemma riskSublevel_isCompact {φ : ℝ → ℝ} (W : Anchors φ)
    {P a b μ v R : ℝ} (hP : 0 ≤ P) :
    IsCompact (RiskSublevel φ P a b μ v R) := by
  have hn : Continuous (fun q : Coordinates => (v + μ^2)*q 4 - 2*μ*q 5 + q 3) := by
    fun_prop
  exact (feasible_isCompact W hP).inter_right
    ((isClosed_le continuous_const continuous_det).inter
      (isClosed_le hn (continuous_const.mul continuous_det)))

lemma riskSublevel_of_optimal {φ : ℝ → ℝ} {P a b μ v γ R : ℝ}
    (hv : 0 < v) (hγ : 0 ≤ γ) {D : Design}
    (hD : Optimal φ P a b μ v γ D) (hR : value φ P a b μ v γ ≤ R) :
    fromDesign D γ ∈ RiskSublevel φ P a b μ v R := by
  have hr : risk μ v D.gram ≤ R := hD.2.trans_le hR
  refine ⟨from_design_feasible hγ hD.1,
    (determinant_barrier hv D.gram hD.1.1 hr).2, ?_⟩
  have he := (div_le_iff₀ hD.1.1.2).mp (show
    ((v+μ^2)*D.gram.B-2*μ*D.gram.C+D.gram.A)/det D.gram.A D.gram.B D.gram.C ≤ R by
    rw [← risk_trace_formula]; exact hr)
  simpa only [fromDesign, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons,
    Matrix.head_fin_const] using he

lemma value_le_of_riskSublevel {φ : ℝ → ℝ} {P a b μ v R : ℝ}
    (hv : 0 < v) (hR : 0 < R) {q : Coordinates}
    (hq : q ∈ RiskSublevel φ P a b μ v R) :
    value φ P a b μ v (q 6) ≤ R := by
  have hd : 0 < det (q 3) (q 4) (q 5) :=
    (div_pos hv (sq_pos_of_pos hR)).trans_le hq.2.1
  have hf := to_design_feasible hq.1 rfl hd
  refine (value_le hv.le hf).trans ?_
  rw [risk_trace_formula]
  exact (div_le_iff₀ hd).mpr hq.2.2

/-- Lower semicontinuity on any feasible closed floor interval. Neither
continuity nor compactness of optimizer sets is assumed. -/
theorem value_lowerSemicontinuousOn {φ : ℝ → ℝ} (W : Anchors φ)
    {P a b μ v M : ℝ} (hP : 0 ≤ P) (hv : 0 < v)
    (hne : ∃ D : Design, Frontier.Feasible φ P a b M D) :
    LowerSemicontinuousOn (value φ P a b μ v) (Icc 0 M) := by
  intro γ hγ R hR
  have hf : ∀ δ ∈ Icc (0 : ℝ) M, ∃ D : Design, Optimal φ P a b μ v δ D := by
    intro δ hδ
    obtain ⟨E,hE⟩ := hne
    exact minimum_attained W hP hv hδ.1 ⟨E, feasible_nested hδ.2 hE⟩
  by_cases hRp : 0 < R
  · let C := (fun q : Coordinates => q 6) '' RiskSublevel φ P a b μ v R
    have hC : IsClosed C :=
      ((riskSublevel_isCompact (μ := μ) (v := v) (R := R) W hP).image
        (continuous_apply 6)).isClosed
    have hnot : γ ∉ C := by
      rintro ⟨q,hq,hqγ⟩
      have hle := value_le_of_riskSublevel hv hRp hq
      change q 6 = γ at hqγ
      rw [hqγ] at hle
      exact (not_le_of_gt hR) hle
    have hnb : Cᶜ ∈ 𝓝[Icc (0 : ℝ) M] γ :=
      mem_nhdsWithin_of_mem_nhds (hC.isOpen_compl.mem_nhds hnot)
    filter_upwards [hnb, self_mem_nhdsWithin] with δ hδ hδI
    by_contra hn
    obtain ⟨D,hD⟩ := hf δ hδI
    exact hδ ⟨fromDesign D δ, riskSublevel_of_optimal hv hδI.1 hD (le_of_not_gt hn), rfl⟩
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    obtain ⟨D,hD⟩ := hf δ hδ
    have hp := risk_pos (μ := μ) hv D.gram hD.1.1
    rw [hD.2] at hp
    exact (le_of_not_gt hRp).trans_lt hp

/-- At the largest feasible floor, compact finite-risk sublevels rule out an
upward jump. Monotonicity supplies the other one-sided inequality. -/
theorem value_continuousWithinAt_max {φ : ℝ → ℝ} (W : Anchors φ)
    {P a b μ v M : ℝ} (hP : 0 ≤ P) (hv : 0 < v) (hM : 0 ≤ M)
    (hne : ∃ D : Design, Frontier.Feasible φ P a b M D) :
    ContinuousWithinAt (value φ P a b μ v) (Icc 0 M) M := by
  rw [continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]
  refine ⟨value_lowerSemicontinuousOn W hP hv hne M ⟨hM, le_rfl⟩, ?_⟩
  intro R hR
  filter_upwards [self_mem_nhdsWithin] with γ hγ
  exact (value_monotone hv.le hγ.2 hne).trans_lt hR

/-- The zero-floor optimum has a positive actual floor, so the value is
locally constant on the feasible interval at its left endpoint. -/
theorem value_continuousWithinAt_zero {φ : ℝ → ℝ} (W : Anchors φ)
    {P a b μ v M : ℝ} (hP : 0 ≤ P) (hv : 0 < v) (hM : 0 ≤ M)
    (hne : ∃ D : Design, Frontier.Feasible φ P a b M D) :
    ContinuousWithinAt (value φ P a b μ v) (Icc 0 M) 0 := by
  obtain ⟨E,hE⟩ := hne
  obtain ⟨D,hD⟩ := minimum_attained (μ := μ) W hP hv (le_refl (0 : ℝ))
    ⟨E,feasible_nested hM hE⟩
  have hc : 0 < D.gram.floor a b := D.gram.floor_pos hD.1.1 a b
  have heq : (value φ P a b μ v) =ᶠ[𝓝[Icc (0 : ℝ) M] 0]
      (fun _ => value φ P a b μ v 0) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hc)] with γ hγ hγc
    exact plateau_of_zero_floor_optimum hv.le hγ.1 hD
      ((feasible_iff_floor hD.1 hγ.1).mpr hγc.le)
  exact continuousWithinAt_const.congr_of_eventuallyEq heq (by rfl)

/-- The true value function is convex on every feasible floor interval. -/
lemma value_convexOn {φ : ℝ → ℝ} {P a b μ v M : ℝ} (hv : 0 ≤ v)
    (hne : ∃ D : Design, Frontier.Feasible φ P a b M D) :
    ConvexOn ℝ (Icc 0 M) (value φ P a b μ v) := by
  refine ⟨convex_Icc 0 M, ?_⟩
  intro x hx y hy u t hu ht hut
  obtain ⟨D,hD⟩ := hne
  have he := value_convex (μ := μ) hv ⟨D,feasible_nested hx.2 hD⟩
    ⟨D,feasible_nested hy.2 hD⟩ ht (by linarith : t ≤ 1)
  have heu : 1-t = u := by linarith
  simpa only [heu, smul_eq_mul] using he

/-- Below the maximal floor, Gram mixing bounds the value by a continuous
secant majorant. Together with monotonicity this excludes an upward jump. -/
lemma value_upperSemicontinuousWithinAt_lt_max {φ : ℝ → ℝ}
    {P a b μ v M γ : ℝ} (hv : 0 ≤ v) (hγM : γ < M)
    (hne : ∃ D : Design, Frontier.Feasible φ P a b M D) :
    UpperSemicontinuousWithinAt (value φ P a b μ v) (Icc 0 M) γ := by
  intro R hR
  let f := value φ P a b μ v
  let U := fun δ : ℝ => f γ + |δ-γ|/(M-γ)*(f M-f γ)
  have hU : Continuous U := by dsimp [U]; fun_prop
  have hnear : ∀ᶠ δ in 𝓝 γ, U δ < R :=
    hU.continuousAt (Iio_mem_nhds (by simpa [U] using hR))
  have hm : f γ ≤ f M := value_monotone hv hγM.le hne
  filter_upwards [mem_nhdsWithin_of_mem_nhds hnear, self_mem_nhdsWithin]
    with δ hδR hδ
  apply lt_of_le_of_lt _ hδR
  change f δ ≤ U δ
  by_cases hδγ : δ ≤ γ
  · have hfeas : ∃ D : Design, Frontier.Feasible φ P a b γ D := by
      obtain ⟨D,hD⟩ := hne
      exact ⟨D,feasible_nested hγM.le hD⟩
    have hd : f δ ≤ f γ := value_monotone hv hδγ hfeas
    have hn : 0 ≤ |δ-γ|/(M-γ)*(f M-f γ) :=
      mul_nonneg (div_nonneg (abs_nonneg _) (sub_pos.mpr hγM).le) (sub_nonneg.mpr hm)
    exact hd.trans (by dsimp [U]; linarith)
  · have hγδ : γ ≤ δ := (lt_of_not_ge hδγ).le
    let t := (δ-γ)/(M-γ)
    have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hγδ) (sub_pos.mpr hγM).le
    have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hγM)).mpr (by linarith [hδ.2])
    obtain ⟨D,hD⟩ := hne
    have hc := value_convex (μ := μ) hv ⟨D,feasible_nested hγM.le hD⟩ ⟨D,hD⟩ ht ht1
    have htden : t*(M-γ) = δ-γ := div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hγM))
    have hx : (1-t)*γ+t*M = δ := by nlinarith
    rw [hx] at hc
    change f δ ≤ (1-t)*f γ+t*f M at hc
    have he : U δ = (1-t)*f γ+t*f M := by
      dsimp [U,t]
      rw [abs_of_nonneg (sub_nonneg.mpr hγδ)]
      ring
    exact he ▸ hc

/-- Full continuity, including both endpoints, of the attained Gram frontier. -/
theorem value_continuousOn {φ : ℝ → ℝ} (W : Anchors φ)
    {P a b μ v M : ℝ} (hP : 0 ≤ P) (hv : 0 < v) (hM : 0 ≤ M)
    (hne : ∃ D : Design, Frontier.Feasible φ P a b M D) :
    ContinuousOn (value φ P a b μ v) (Icc 0 M) := by
  intro γ hγ
  by_cases hmax : γ = M
  · subst γ
    exact value_continuousWithinAt_max W hP hv hM hne
  rw [continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]
  exact ⟨value_lowerSemicontinuousOn W hP hv hne γ hγ,
    value_upperSemicontinuousWithinAt_lt_max hv.le (lt_of_le_of_ne hγ.2 hmax) hne⟩

/-- The normalized small-noise mean-square coefficient inherits continuity
from the inverse-risk frontier. -/
theorem mseValue_continuousOn {φ : ℝ → ℝ} (W : Anchors φ)
    {P a b μ v M K : ℝ} (hP : 0 ≤ P) (hv : 0 < v) (hM : 0 ≤ M)
    (hne : ∃ D : Design, Frontier.Feasible φ P a b M D) :
    ContinuousOn (mseValue K φ P a b μ v) (Icc 0 M) :=
  (value_continuousOn W hP hv hM hne).div_const (2*K^2)

/-- Under the manuscript's continuous strict-shape, positive-power and
positive-prior-variance assumptions, the maximal floor exists and the actual
frontier is attained and continuous throughout the entire closed interval.
No feasible witness, anchor system, or endpoint continuity is assumed. -/
theorem attained_continuous_frontier_of_strict_shape {φ : ℝ → ℝ}
    {P a b μ v : ℝ} (hP : 0 < P) (hv : 0 < v) (hab : a ≠ b)
    (hcφ : ContinuousOn φ (Icc (-1 : ℝ) 1))
    (hshape : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ) :
    ∃ q : Coordinates, SynthesisAttainment.Feasible φ P a b q ∧ 0 < q 6 ∧
      (∀ r : Coordinates, SynthesisAttainment.Feasible φ P a b r → r 6 ≤ q 6) ∧
      (∀ γ : ℝ, 0 ≤ γ → γ ≤ q 6 → ∃ D : Design, Optimal φ P a b μ v γ D) ∧
      ContinuousOn (value φ P a b μ v) (Icc 0 (q 6)) := by
  obtain ⟨q,hq,hqpos,hmax,hatt⟩ :=
    frontier_attained_on_maximal_interval (μ := μ) hP hv hab hcφ hshape
  obtain ⟨D,hD⟩ := hatt (q 6) hqpos.le le_rfl
  exact ⟨q,hq,hqpos,hmax,hatt,
    value_continuousOn (endpointAnchors φ (anchorGap_ne_zero_of_strict_shape hshape))
      hP.le hv hqpos.le ⟨D,hD.1⟩⟩

end Analog.FrontierContinuity
