import Analog.GeneralDesign
import Analog.SynthesisAttainment
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Continuous peak certification from sampled values

The interpolation bound is derived from actual first and second derivatives.
No interpolation remainder is assumed. The scalar scaling lemmas preserve
the continuum peak bound and quantify the loss in the homogeneous objective.
-/

noncomputable section
open Set
namespace Analog.CertifiedGrid

/-- A lower second-derivative bound makes the quadratic correction convex. -/
theorem quadratic_correction_convex (q q' q'' : ℝ → ℝ) (a b M : ℝ)
    (hq : ContinuousOn q (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt q (q' x) x)
    (hdd : ∀ x ∈ Ioo a b, HasDerivAt q' (q'' x) x)
    (hbound : ∀ x ∈ Ioo a b, -M ≤ q'' x) :
    ConvexOn ℝ (Icc a b) (fun x => q x + M / 2 * x ^ 2) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
    (f' := fun x => q' x + M * x) (f'' := fun x => q'' x + M)
  · exact hq.add (continuousOn_const.mul (continuousOn_id.pow 2))
  · intro x hx
    rw [interior_Icc] at hx
    have hh := (hd x hx).add (((hasDerivAt_id x).pow 2).const_mul (M / 2))
    convert hh.hasDerivWithinAt using 1
    dsimp
    ring
  · intro x hx
    rw [interior_Icc] at hx
    have hh := (hdd x hx).add ((hasDerivAt_id x).const_mul M)
    convert hh.hasDerivWithinAt using 1
    dsimp
    ring
  · intro x hx
    rw [interior_Icc] at hx
    linarith [hbound x hx]

/-- A genuine twice differentiable function lies at most `M (b-a)^2 / 8`
above the larger endpoint value when its second derivative is bounded below
by `-M`. The constant `1/8` is the sharp linear-interpolation constant. -/
theorem interval_peak_bound (q q' q'' : ℝ → ℝ) (a b M P : ℝ)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (hq : ContinuousOn q (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt q (q' x) x)
    (hdd : ∀ x ∈ Ioo a b, HasDerivAt q' (q'' x) x)
    (hbound : ∀ x ∈ Ioo a b, -M ≤ q'' x)
    (ha : q a ≤ P) (hb : q b ≤ P) (x : ℝ) (hx : x ∈ Icc a b) :
    q x ≤ P + M * (b - a) ^ 2 / 8 := by
  by_cases heq : a = b
  · have hxa : x = a := by rcases hx with ⟨h1, h2⟩; linarith
    simpa [heq, hxa] using ha
  have hpos : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab heq)
  let t : ℝ := (x - a) / (b - a)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx.1) hpos.le
  have ht1 : t ≤ 1 := (div_le_one hpos).mpr (by linarith [hx.2])
  have htx : (1 - t) * a + t * b = x := by
    dsimp [t]
    field_simp
    ring
  have hc := quadratic_correction_convex q q' q'' a b M hq hd hdd hbound
  have hc' := hc.2 (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    (sub_nonneg.mpr ht1) ht0 (show (1 - t) + t = 1 by ring)
  simp only [smul_eq_mul, htx] at hc'
  have hpa := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht1)
  have hpb := mul_le_mul_of_nonneg_left hb ht0
  have hid : (1 - t) * a ^ 2 + t * b ^ 2 - x ^ 2 =
      t * (1 - t) * (b - a) ^ 2 := by
    rw [← htx]
    ring
  have hmid : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
  have hmul := mul_le_mul_of_nonneg_right hmid (mul_nonneg hM (sq_nonneg (b - a)))
  nlinarith

/-- The same endpoint bound using the usual absolute second-derivative bound. -/
theorem interval_peak_bound_of_abs (q q' q'' : ℝ → ℝ) (a b M P : ℝ)
    (hab : a ≤ b) (hM : 0 ≤ M)
    (hq : ContinuousOn q (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt q (q' x) x)
    (hdd : ∀ x ∈ Ioo a b, HasDerivAt q' (q'' x) x)
    (hbound : ∀ x ∈ Ioo a b, |q'' x| ≤ M)
    (ha : q a ≤ P) (hb : q b ≤ P) (x : ℝ) (hx : x ∈ Icc a b) :
    q x ≤ P + M * (b - a) ^ 2 / 8 :=
  interval_peak_bound q q' q'' a b M P hab hM hq hd hdd
    (fun x hx => (abs_le.mp (hbound x hx)).1) ha hb x hx

/-- Every point between the first and last grid points is enclosed by two
consecutive grid points (possibly the same point). -/
theorem finite_grid_bracket (T : Finset ℝ) (a b x : ℝ)
    (ha : a ∈ T) (hb : b ∈ T) (hx : x ∈ Icc a b) :
    ∃ l ∈ T, ∃ r ∈ T, l ≤ x ∧ x ≤ r ∧
      ∀ t ∈ T, l < t → t < r → False := by
  classical
  let left := T.filter (fun t => t ≤ x)
  let right := T.filter (fun t => x ≤ t)
  have hl : left.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, hx.1⟩⟩
  have hr : right.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, hx.2⟩⟩
  have hlm := Finset.mem_filter.mp (Finset.max'_mem left hl)
  have hrm := Finset.mem_filter.mp (Finset.min'_mem right hr)
  refine ⟨left.max' hl, hlm.1, right.min' hr, hrm.1, hlm.2, hrm.2, ?_⟩
  intro t ht hlt htr
  by_cases htx : t ≤ x
  · have hh := Finset.le_max' left t (Finset.mem_filter.mpr ⟨ht, htx⟩)
    linarith
  · have hh := Finset.min'_le right t (Finset.mem_filter.mpr ⟨ht, le_of_not_ge htx⟩)
    linarith

/-- The finite-grid spacing condition alone yields a full-interval peak
certificate; no samplewise approximation is used between grid points. -/
theorem finite_grid_peak_bound (q q' q'' : ℝ → ℝ) (T : Finset ℝ)
    (a b M P h : ℝ) (hM : 0 ≤ M) (hh : 0 ≤ h)
    (hTa : a ∈ T) (hTb : b ∈ T) (hT : ∀ t ∈ T, t ∈ Icc a b)
    (hspacing : ∀ l ∈ T, ∀ r ∈ T, l < r →
      (∀ t ∈ T, l < t → t < r → False) → r - l ≤ h)
    (hq : ContinuousOn q (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt q (q' x) x)
    (hdd : ∀ x ∈ Ioo a b, HasDerivAt q' (q'' x) x)
    (hbound : ∀ x ∈ Ioo a b, |q'' x| ≤ M)
    (hpeak : ∀ t ∈ T, q t ≤ P) :
    ∀ x ∈ Icc a b, q x ≤ P + M * h ^ 2 / 8 := by
  intro x hx
  obtain ⟨l, hl, r, hr, hlx, hxr, hadj⟩ := finite_grid_bracket T a b x hTa hTb hx
  have hlr : l ≤ r := hlx.trans hxr
  by_cases heq : l = r
  · have hxl : x = l := by linarith
    rw [hxl]
    have herror : 0 ≤ M * h ^ 2 / 8 := by positivity
    linarith [hpeak l hl]
  have hlt : l < r := lt_of_le_of_ne hlr heq
  have hlen := hspacing l hl r hr hlt hadj
  have hsub : Icc l r ⊆ Icc a b := Icc_subset_Icc (hT l hl).1 (hT r hr).2
  have hisub : Ioo l r ⊆ Ioo a b := Ioo_subset_Ioo (hT l hl).1 (hT r hr).2
  have hbnd := interval_peak_bound_of_abs q q' q'' l r M P hlr hM (hq.mono hsub)
    (fun t ht => hd t (hisub ht)) (fun t ht => hdd t (hisub ht))
    (fun t ht => hbound t (hisub ht)) (hpeak l hl) (hpeak r hr) x ⟨hlx, hxr⟩
  have hsquare : (r - l) ^ 2 ≤ h ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsquare hM
  linarith

/-- Scaling a certified continuous peak bound restores the prescribed power. -/
theorem peak_scaling (q : ℝ → ℝ) (D : Set ℝ) (P B : ℝ)
    (hP : 0 < P) (hB : 0 < B) (hq : ∀ x ∈ D, q x ≤ B) :
    ∀ x ∈ D, (P / B) * q x ≤ P := by
  intro x hx
  calc
    (P / B) * q x ≤ (P / B) * B :=
      mul_le_mul_of_nonneg_left (hq x hx) (div_nonneg hP.le hB.le)
    _ = P := div_mul_cancel₀ P (ne_of_gt hB)

/-- An explicit uniform quadratic gap bound for the grid scaling factor. -/
theorem scaling_gap_bound (P M h U C : ℝ) (hP : 0 < P) (hM : 0 ≤ M)
    (hU : 0 ≤ U) (hUC : U ≤ C) :
    0 ≤ U - (P / (P + M * h ^ 2 / 8)) * U ∧
      U - (P / (P + M * h ^ 2 / 8)) * U ≤ (C * M / (8 * P)) * h ^ 2 := by
  have hE : 0 ≤ M * h ^ 2 / 8 := by positivity
  have hden : 0 < P + M * h ^ 2 / 8 := by linarith
  have hC : 0 ≤ C := hU.trans hUC
  have hid : U - (P / (P + M * h ^ 2 / 8)) * U =
      U * (M * h ^ 2 / 8) / (P + M * h ^ 2 / 8) := by
    field_simp
    ring
  rw [hid]
  constructor
  · exact div_nonneg (mul_nonneg hU hE) hden.le
  · calc
      U * (M * h ^ 2 / 8) / (P + M * h ^ 2 / 8) ≤
          C * (M * h ^ 2 / 8) / (P + M * h ^ 2 / 8) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hUC hE) hden.le
      _ ≤ C * (M * h ^ 2 / 8) / P :=
        div_le_div_of_nonneg_left (mul_nonneg hC hE) hP (by linarith)
      _ = (C * M / (8 * P)) * h ^ 2 := by ring

open GramSynthesis SynthesisAttainment

/-- The actual finite SDP: only the continuum peak constraints are sampled. -/
def GridFeasible (φ : ℝ → ℝ) (T : Finset ℝ) (P a b : ℝ) (q : Coordinates) : Prop :=
  0 ≤ q 6 ∧ PSD3 (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) ∧
  (∀ s ∈ T, quad q (feature φ s) ≤ P) ∧
  RankOnePSD (q 3) (q 4) (q 5) (q 6) a 1 ∧
  RankOnePSD (q 3) (q 4) (q 5) (q 6) b 1

/-- Removing off-grid peak constraints relaxes the continuum feasible set. -/
theorem continuum_implies_grid (φ : ℝ → ℝ) (T : Finset ℝ) (P a b : ℝ)
    (hT : ∀ t ∈ T, t ∈ Icc (-1 : ℝ) 1) (q : Coordinates)
    (hq : Feasible φ P a b q) : GridFeasible φ T P a b q := by
  exact ⟨hq.1, hq.2.1, fun s hs => hq.2.2.1 s (hT s hs).1 (hT s hs).2,
    hq.2.2.2⟩

lemma coordinate_scaling_quad (q : Coordinates) (ρ : ℝ) (v : Vector3) :
    quad (fun i => ρ * q i) v = ρ * quad q v := by
  dsimp [quad, form3, form2]
  ring

/-- Nonnegative simultaneous scaling preserves every homogeneous SDP
constraint, and the proved continuous peak bound supplies the remaining one. -/
theorem grid_scaled_feasible (φ : ℝ → ℝ) (T : Finset ℝ) (P a b B : ℝ)
    (hP : 0 < P) (hB : 0 < B) (q : Coordinates)
    (hq : GridFeasible φ T P a b q)
    (hpeak : ∀ s ∈ Icc (-1 : ℝ) 1, quad q (feature φ s) ≤ B) :
    Feasible φ P a b (fun i => (P / B) * q i) := by
  have hρ : 0 ≤ P / B := div_nonneg hP.le hB.le
  refine ⟨mul_nonneg hρ hq.1, ?_, ?_, ?_, ?_⟩
  · intro t x y
    have hh := mul_nonneg hρ (hq.2.1 t x y)
    convert hh using 1
    dsimp [form3, form2]
    ring
  · intro s hs hs1
    rw [coordinate_scaling_quad]
    exact peak_scaling (fun s => quad q (feature φ s)) (Icc (-1 : ℝ) 1)
      P B hP hB hpeak s ⟨hs, hs1⟩
  · intro x y
    have hh := mul_nonneg hρ (hq.2.2.2.1 x y)
    convert hh using 1
    dsimp [form2]
    ring
  · intro x y
    have hh := mul_nonneg hρ (hq.2.2.2.2 x y)
    convert hh using 1
    dsimp [form2]
    ring

/-- The computed peak function is continuous whenever its local preprocessing
function is continuous. -/
lemma gram_peak_continuous (φ : ℝ → ℝ) (q : Coordinates)
    (hφ : ContinuousOn φ (Icc (-1 : ℝ) 1)) :
    ContinuousOn (fun s => quad q (feature φ s)) (Icc (-1 : ℝ) 1) := by
  dsimp [quad, feature, form3, form2]
  fun_prop

/-- A certified SDP bracket. The continuum optimizer is obtained from the
previously proved compactness theorem; only the grid optimizer named in the
statement is supplied. Derivative hypotheses refer to the actual Gram peak
function, rather than an assumed interpolation estimate. -/
theorem certified_grid_bracket (φ q' q'' : ℝ → ℝ) (W : Anchors φ)
    (T : Finset ℝ) (P a b M h : ℝ) (hP : 0 < P) (hM : 0 ≤ M) (hh : 0 ≤ h)
    (hTa : (-1 : ℝ) ∈ T) (hTb : (1 : ℝ) ∈ T)
    (hT : ∀ t ∈ T, t ∈ Icc (-1 : ℝ) 1)
    (hspacing : ∀ l ∈ T, ∀ r ∈ T, l < r →
      (∀ t ∈ T, l < t → t < r → False) → r - l ≤ h)
    (hφ : ContinuousOn φ (Icc (-1 : ℝ) 1))
    (q : Coordinates) (hq : GridFeasible φ T P a b q)
    (hmax : ∀ r : Coordinates, GridFeasible φ T P a b r → r 6 ≤ q 6)
    (hd : ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s => quad q (feature φ s)) (q' x) x)
    (hdd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt q' (q'' x) x)
    (hbound : ∀ x ∈ Ioo (-1 : ℝ) 1, |q'' x| ≤ M) :
    ∃ qstar : Coordinates, Feasible φ P a b qstar ∧
      (∀ r : Coordinates, Feasible φ P a b r → r 6 ≤ qstar 6) ∧
      Feasible φ P a b (fun i => (P / (P + M * h ^ 2 / 8)) * q i) ∧
      (P / (P + M * h ^ 2 / 8)) * q 6 ≤ qstar 6 ∧ qstar 6 ≤ q 6 := by
  obtain ⟨qstar, hs, hsm⟩ := maximum_attained W hP.le
  have hpeak := finite_grid_peak_bound (fun s => quad q (feature φ s)) q' q'' T
    (-1) 1 M P h hM hh hTa hTb hT hspacing (gram_peak_continuous φ q hφ)
    hd hdd hbound hq.2.2.1
  have hB : 0 < P + M * h ^ 2 / 8 := by positivity
  have hscale := grid_scaled_feasible φ T P a b (P + M * h ^ 2 / 8)
    hP hB q hq hpeak
  exact ⟨qstar, hs, hsm, hscale, hsm _ hscale,
    hmax _ (continuum_implies_grid φ T P a b hT qstar hs)⟩

/-- The three fixed sampled anchors bound each quadratic basis value. -/
theorem grid_anchor_basis_bound {φ : ℝ → ℝ} (W : Anchors φ) (T : Finset ℝ)
    (hW : ∀ i, W.s i ∈ T) {P a b : ℝ} {q : Coordinates}
    (hq : GridFeasible φ T P a b q) (j : Fin 3) :
    quad q (Pi.single j 1) ≤ W.bound P j := by
  have hp (i : Fin 3) := hq.2.2.1 (W.s i) (hW i)
  have h := quad_sum_three_le hq.2.1 (W.coeff j 0 • feature φ (W.s 0))
    (W.coeff j 1 • feature φ (W.s 1)) (W.coeff j 2 • feature φ (W.s 2))
  rw [W.reconstruct j, quad_smul, quad_smul, quad_smul] at h
  have h₀ := mul_le_mul_of_nonneg_left (hp 0) (sq_nonneg (W.coeff j 0))
  have h₁ := mul_le_mul_of_nonneg_left (hp 1) (sq_nonneg (W.coeff j 1))
  have h₂ := mul_le_mul_of_nonneg_left (hp 2) (sq_nonneg (W.coeff j 2))
  dsimp [Anchors.bound]
  nlinarith

/-- Uniform coordinate bounds use only the fixed spanning samples, so their
constant is independent of the number of grid points and the grid spacing. -/
theorem grid_coordinate_bound {φ : ℝ → ℝ} (W : Anchors φ) (T : Finset ℝ)
    (hW : ∀ i, W.s i ∈ T) {P a b : ℝ} (hP : 0 ≤ P) {q : Coordinates}
    (hq : GridFeasible φ T P a b q) : ∀ i : Fin 7, |q i| ≤ W.cap P := by
  have b₀ := grid_anchor_basis_bound W T hW hq 0
  have b₁ := grid_anchor_basis_bound W T hW hq 1
  have b₂ := grid_anchor_basis_bound W T hW hq 2
  norm_num [quad, form3, form2, Pi.single_apply, Fin.ext_iff] at b₀ b₁ b₂
  have p₀ := W.bound_nonneg hP 0
  have p₁ := W.bound_nonneg hP 1
  have p₂ := W.bound_nonneg hP 2
  have d₀ := hq.2.1 1 0 0
  have d₁ := hq.2.1 0 1 0
  have d₂ := hq.2.1 0 0 1
  have n₁p := hq.2.1 1 1 0
  have n₁m := hq.2.1 1 (-1) 0
  have n₂p := hq.2.1 1 0 1
  have n₂m := hq.2.1 1 0 (-1)
  have n₅p := hq.2.1 0 1 1
  have n₅m := hq.2.1 0 1 (-1)
  have h₆ := hq.2.2.2.1 0 1
  norm_num [form3, form2] at d₀ d₁ d₂ n₁p n₁m n₂p n₂m n₅p n₅m h₆
  intro i
  fin_cases i <;> apply abs_le.mpr <;> dsimp [Anchors.cap] <;> constructor <;>
    linarith [hq.1]

/-- The sampled SDP is closed. Its matrix positivity constraints still
quantify over every vector; only the source peak constraints are sampled. -/
theorem grid_feasible_isClosed (φ : ℝ → ℝ) (T : Finset ℝ) (P a b : ℝ) :
    IsClosed {q : Coordinates | GridFeasible φ T P a b q} := by
  have hpsd : IsClosed {q : Coordinates | PSD3 (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)} := by
    simp only [PSD3, setOf_forall]
    exact isClosed_iInter fun t => isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le continuous_const (continuous_quad ![t, x, y])
  have hpeak : IsClosed {q : Coordinates | ∀ s ∈ T, quad q (feature φ s) ≤ P} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun _ =>
      isClosed_le (continuous_quad (feature φ s)) continuous_const
  have hrank (w : ℝ) : IsClosed {q : Coordinates |
      RankOnePSD (q 3) (q 4) (q 5) (q 6) w 1} := by
    simp only [RankOnePSD, one_mul, setOf_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le continuous_const (continuous_rank_form w x y)
  exact (isClosed_le continuous_const (continuous_apply 6)).inter
    (hpsd.inter (hpeak.inter ((hrank a).inter (hrank b))))

/-- Three spanning points retained on every grid prove compactness of every
sampled feasible set, rather than assuming bounded numerical solutions. -/
theorem grid_feasible_isCompact {φ : ℝ → ℝ} (W : Anchors φ) (T : Finset ℝ)
    (hW : ∀ i, W.s i ∈ T) {P a b : ℝ} (hP : 0 ≤ P) :
    IsCompact {q : Coordinates | GridFeasible φ T P a b q} := by
  have hbox : IsCompact {q : Coordinates | ∀ i, q i ∈ Icc (-W.cap P) (W.cap P)} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  apply hbox.of_isClosed_subset (grid_feasible_isClosed φ T P a b)
  intro q hq i
  exact abs_le.mp (grid_coordinate_bound W T hW hP hq i)

/-- Every sampled SDP has an actual maximizing Gram matrix, with a uniform
coordinate bound derived from its fixed anchors. -/
theorem grid_maximum_attained {φ : ℝ → ℝ} (W : Anchors φ) (T : Finset ℝ)
    (hW : ∀ i, W.s i ∈ T) {P a b : ℝ} (hP : 0 ≤ P) :
    ∃ q : Coordinates, GridFeasible φ T P a b q ∧
      (∀ r : Coordinates, GridFeasible φ T P a b r → r 6 ≤ q 6) ∧
      ∀ i : Fin 7, |q i| ≤ W.cap P := by
  have hz : GridFeasible φ T P a b (fun _ => 0) := by
    refine ⟨le_rfl, ?_, ?_, ?_, ?_⟩
    · intro t x y; simp [form3, form2]
    · intro s hs; simpa [quad, form3, form2] using hP
    · intro x y; simp [form2]
    · intro x y; simp [form2]
  obtain ⟨q, hq, hmax⟩ := (grid_feasible_isCompact W T hW hP).exists_isMaxOn
    ⟨fun _ => 0, hz⟩ (continuous_apply 6).continuousOn
  exact ⟨q, hq, hmax, grid_coordinate_bound W T hW hP hq⟩

section OperatorPeak
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic peak function in its Euclidean operator representation. -/
def operatorPeak (H : E →L[ℝ] E) (z : ℝ → E) (s : ℝ) : ℝ :=
  inner ℝ (z s) (H (z s))

def operatorPeakDeriv (H : E →L[ℝ] E) (z z' : ℝ → E) (s : ℝ) : ℝ :=
  inner ℝ (z s) (H (z' s)) + inner ℝ (z' s) (H (z s))

def operatorPeakDeriv2 (H : E →L[ℝ] E) (z z' z'' : ℝ → E) (s : ℝ) : ℝ :=
  inner ℝ (z s) (H (z'' s)) + 2 * inner ℝ (z' s) (H (z' s)) +
    inner ℝ (z'' s) (H (z s))

theorem operator_peak_hasDerivAt (H : E →L[ℝ] E) (z z' : ℝ → E)
    (s : ℝ) (hz : HasDerivAt z (z' s) s) :
    HasDerivAt (operatorPeak H z) (operatorPeakDeriv H z z' s) s := by
  exact hz.inner ℝ (H.hasFDerivAt.comp_hasDerivAt s hz)

/-- Differentiate the actual quadratic peak twice. Self-adjointness is not
needed for the identity or its norm bound. -/
theorem operator_peak_deriv_hasDerivAt (H : E →L[ℝ] E) (z z' z'' : ℝ → E)
    (s : ℝ) (hz : HasDerivAt z (z' s) s) (hz' : HasDerivAt z' (z'' s) s) :
    HasDerivAt (operatorPeakDeriv H z z') (operatorPeakDeriv2 H z z' z'' s) s := by
  have h₁ := hz.inner ℝ (H.hasFDerivAt.comp_hasDerivAt s hz')
  have h₂ := hz'.inner ℝ (H.hasFDerivAt.comp_hasDerivAt s hz)
  convert h₁.add h₂ using 1
  dsimp [operatorPeakDeriv2]
  ring

/-- The exact operator-norm estimate used to define `M_h` in the paper. -/
theorem operator_peak_second_derivative_bound (H : E →L[ℝ] E)
    (z z' z'' : ℝ → E) (s : ℝ) :
    |operatorPeakDeriv2 H z z' z'' s| ≤
      2 * ‖H‖ * (‖z' s‖ ^ 2 + ‖z s‖ * ‖z'' s‖) := by
  have bound (u v : E) : |inner ℝ u (H v)| ≤ ‖H‖ * (‖u‖ * ‖v‖) := by
    calc
      |inner ℝ u (H v)| ≤ ‖u‖ * ‖H v‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖H‖ * ‖v‖) := mul_le_mul_of_nonneg_left (H.le_opNorm v) (norm_nonneg _)
      _ = ‖H‖ * (‖u‖ * ‖v‖) := by ring
  have hb₀ := bound (z s) (z'' s)
  have hb₁ := bound (z' s) (z' s)
  have hb₂ := bound (z'' s) (z s)
  have ht₁ := abs_add_le (inner ℝ (z s) (H (z'' s)))
    (2 * inner ℝ (z' s) (H (z' s)))
  have ht₂ := abs_add_le (inner ℝ (z s) (H (z'' s)) +
    2 * inner ℝ (z' s) (H (z' s))) (inner ℝ (z'' s) (H (z s)))
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht₁
  dsimp [operatorPeakDeriv2]
  nlinarith

/-- Uniform bounds on the curve and its first two derivatives give precisely
`M = 2 ||H|| (Z₁² + Z₀ Z₂)`, without assuming the desired derivative estimate. -/
theorem operator_peak_uniform_bound (H : E →L[ℝ] E) (z z' z'' : ℝ → E)
    (S : Set ℝ) (Z₀ Z₁ Z₂ : ℝ) (h₀ : 0 ≤ Z₀) (h₁ : 0 ≤ Z₁) (_h₂ : 0 ≤ Z₂)
    (hz₀ : ∀ s ∈ S, ‖z s‖ ≤ Z₀) (hz₁ : ∀ s ∈ S, ‖z' s‖ ≤ Z₁)
    (hz₂ : ∀ s ∈ S, ‖z'' s‖ ≤ Z₂) :
    ∀ s ∈ S, |operatorPeakDeriv2 H z z' z'' s| ≤
      2 * ‖H‖ * (Z₁ ^ 2 + Z₀ * Z₂) := by
  intro s hs
  have hsq : ‖z' s‖ ^ 2 ≤ Z₁ ^ 2 := by nlinarith [hz₁ s hs, norm_nonneg (z' s)]
  have hprod := mul_le_mul (hz₀ s hs) (hz₂ s hs) (norm_nonneg _) h₀
  exact (operator_peak_second_derivative_bound H z z' z'' s).trans
    (mul_le_mul_of_nonneg_left (add_le_add hsq hprod) (by positivity))

/-- Certified finite-grid interpolation for an actual Euclidean quadratic
peak, with the precise norm constant used in Theorem 7. -/
theorem operator_grid_peak_bound (H : E →L[ℝ] E) (z z' z'' : ℝ → E)
    (T : Finset ℝ) (a b P h Z₀ Z₁ Z₂ : ℝ) (hh : 0 ≤ h)
    (h₀ : 0 ≤ Z₀) (h₁ : 0 ≤ Z₁) (h₂ : 0 ≤ Z₂)
    (hTa : a ∈ T) (hTb : b ∈ T) (hT : ∀ t ∈ T, t ∈ Icc a b)
    (hspacing : ∀ l ∈ T, ∀ r ∈ T, l < r →
      (∀ t ∈ T, l < t → t < r → False) → r - l ≤ h)
    (hz : ContinuousOn z (Icc a b))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt z (z' s) s)
    (hdd : ∀ s ∈ Ioo a b, HasDerivAt z' (z'' s) s)
    (hz₀ : ∀ s ∈ Icc a b, ‖z s‖ ≤ Z₀)
    (hz₁ : ∀ s ∈ Icc a b, ‖z' s‖ ≤ Z₁)
    (hz₂ : ∀ s ∈ Icc a b, ‖z'' s‖ ≤ Z₂)
    (hpeak : ∀ s ∈ T, operatorPeak H z s ≤ P) :
    ∀ s ∈ Icc a b, operatorPeak H z s ≤
      P + (2 * ‖H‖ * (Z₁ ^ 2 + Z₀ * Z₂)) * h ^ 2 / 8 := by
  apply finite_grid_peak_bound (operatorPeak H z) (operatorPeakDeriv H z z')
    (operatorPeakDeriv2 H z z' z'') T a b (2 * ‖H‖ * (Z₁ ^ 2 + Z₀ * Z₂)) P h
    (by positivity) hh hTa hTb hT hspacing
  · exact hz.inner (H.continuous.comp_continuousOn hz)
  · exact fun s hs => operator_peak_hasDerivAt H z z' s (hd s hs)
  · exact fun s hs => operator_peak_deriv_hasDerivAt H z z' z'' s (hd s hs) (hdd s hs)
  · intro s hs
    exact operator_peak_uniform_bound H z z' z'' (Icc a b) Z₀ Z₁ Z₂ h₀ h₁ h₂
      hz₀ hz₁ hz₂ s (Ioo_subset_Icc_self hs)
  · exact hpeak

end OperatorPeak

open Filter
open scoped Topology

/-- A grid-dependent derivative bound gives the claimed quadratic gap rate
as soon as the sampled optima and derivative bounds have uniform caps. -/
theorem scaling_gap_isBigO (U M : ℝ → ℝ) (P C B : ℝ) (hP : 0 < P)
    (hU : ∀ h > 0, 0 ≤ U h) (hUC : ∀ h > 0, U h ≤ C)
    (hM : ∀ h > 0, 0 ≤ M h) (hMB : ∀ h > 0, M h ≤ B) :
    (fun h => U h - (P / (P + M h * h ^ 2 / 8)) * U h)
      =O[𝓝[>] (0 : ℝ)] (fun h => h ^ 2) := by
  apply Asymptotics.IsBigO.of_bound (C * B / (8 * P))
  filter_upwards [eventually_mem_nhdsWithin] with h hh
  have hgap := scaling_gap_bound P (M h) h (U h) C hP (hM h hh) (hU h hh) (hUC h hh)
  rw [Real.norm_eq_abs, abs_of_nonneg hgap.1, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]
  have hC : 0 ≤ C := (hU h hh).trans (hUC h hh)
  have hb := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hMB h hh) hC) (by positivity : 0 ≤ 8 * P))
    (sq_nonneg h)
  exact hgap.2.trans hb

open scoped Matrix.Norms.L2Operator

def gramMatrix (q : Coordinates) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![q 0, q 1, q 2], ![q 1, q 3, q 5], ![q 2, q 5, q 4]]

def gramOperator (q : Coordinates) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (gramMatrix q)

def euclideanFeature (φ : ℝ → ℝ) (s : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (feature φ s)

/-- The six scalar Gram entries and the Euclidean operator representation
give exactly the same peak function, with no change of norm. -/
theorem gram_operator_peak (φ : ℝ → ℝ) (q : Coordinates) (s : ℝ) :
    operatorPeak (gramOperator q) (euclideanFeature φ) s = quad q (feature φ s) := by
  dsimp [operatorPeak, gramOperator, euclideanFeature]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [gramMatrix, feature, quad, form3, form2, dotProduct, Matrix.mulVec,
    Fin.sum_univ_succ]
  ring

theorem gramOperator_continuous : Continuous gramOperator := by
  have hm : Continuous gramMatrix := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j <;> simp [gramMatrix] <;> fun_prop
  have hc :=
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  exact hc.comp hm

/-- The fixed-anchor coordinate bound supplies a uniform Euclidean operator
norm bound for every feasible Gram matrix on every such grid. -/
theorem grid_operator_uniform_bound {φ : ℝ → ℝ} (W : Anchors φ)
    (P a b : ℝ) (hP : 0 ≤ P) :
    ∃ C ≥ 0, ∀ T : Finset ℝ, (∀ i, W.s i ∈ T) →
      ∀ q : Coordinates, GridFeasible φ T P a b q → ‖gramOperator q‖ ≤ C := by
  let B : Set Coordinates := {q | ∀ i, q i ∈ Icc (-W.cap P) (W.cap P)}
  have hb : IsCompact B := isCompact_pi_infinite fun _ => isCompact_Icc
  have hn : B.Nonempty := ⟨fun _ => 0, fun _ =>
    ⟨by linarith [W.cap_nonneg hP], W.cap_nonneg hP⟩⟩
  obtain ⟨qmax, hqmax, hmax⟩ := hb.exists_isMaxOn hn gramOperator_continuous.norm.continuousOn
  refine ⟨‖gramOperator qmax‖, norm_nonneg _, ?_⟩
  intro T hW q hq
  exact hmax (fun i => abs_le.mp (grid_coordinate_bound W T hW hP hq i))

/-- The actual sampled Gram family has the `O(h²)` scaling gap claimed in
Theorem 7. Both uniform bounds are derived from the fixed spanning anchors;
neither bounded sampled optimizers nor bounded matrix norms are assumed. -/
theorem grid_scaling_gap_isBigO {φ : ℝ → ℝ} (W : Anchors φ)
    (T : ℝ → Finset ℝ) (q : ℝ → Coordinates) (P a b Z₀ Z₁ Z₂ : ℝ)
    (hP : 0 < P) (h₀ : 0 ≤ Z₀) (h₂ : 0 ≤ Z₂)
    (hW : ∀ h > 0, ∀ i, W.s i ∈ T h)
    (hq : ∀ h > 0, GridFeasible φ (T h) P a b (q h)) :
    (fun h => q h 6 -
      (P / (P + (2 * ‖gramOperator (q h)‖ * (Z₁ ^ 2 + Z₀ * Z₂)) * h ^ 2 / 8)) * q h 6)
      =O[𝓝[>] (0 : ℝ)] (fun h => h ^ 2) := by
  obtain ⟨C, hC, hc⟩ := grid_operator_uniform_bound W P a b hP.le
  apply scaling_gap_isBigO (fun h => q h 6)
    (fun h => 2 * ‖gramOperator (q h)‖ * (Z₁ ^ 2 + Z₀ * Z₂))
    P (W.cap P) (2 * C * (Z₁ ^ 2 + Z₀ * Z₂)) hP
  · intro h hh; exact (hq h hh).1
  · intro h hh
    exact (le_abs_self _).trans (grid_coordinate_bound W (T h) (hW h hh) hP.le (hq h hh) 6)
  · intro h hh; positivity
  · intro h hh
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hc (T h) (hW h hh) (q h) (hq h hh)) (by norm_num))
      (by positivity)

/-- A `C²` preprocessing function gives a `C²` Euclidean feature curve. -/
theorem euclidean_feature_contDiffOn (φ : ℝ → ℝ)
    (hφ : ContDiffOn ℝ 2 φ (Icc (-1 : ℝ) 1)) :
    ContDiffOn ℝ 2 (euclideanFeature φ) (Icc (-1 : ℝ) 1) := by
  have hf : ContDiffOn ℝ 2 (feature φ) (Icc (-1 : ℝ) 1) := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · simpa [feature] using (contDiffOn_const : ContDiffOn ℝ 2 (fun _ : ℝ => (1 : ℝ)) _)
    · simpa [feature] using (contDiffOn_id : ContDiffOn ℝ 2 (fun s : ℝ => s) _)
    · simpa [feature] using hφ
  let L : (Fin 3 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  exact L.contDiff.comp_contDiffOn hf

section C2Data
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed-interval `C²` hypothesis provides genuine interior first and
second derivatives, including their finite continuous endpoint extensions. -/
theorem c2_derivative_data (z : ℝ → E) (hz : ContDiffOn ℝ 2 z (Icc (-1 : ℝ) 1)) :
    ContinuousOn (derivWithin z (Icc (-1 : ℝ) 1)) (Icc (-1 : ℝ) 1) ∧
    ContinuousOn (derivWithin (derivWithin z (Icc (-1 : ℝ) 1)) (Icc (-1 : ℝ) 1))
      (Icc (-1 : ℝ) 1) ∧
    (∀ s ∈ Ioo (-1 : ℝ) 1, HasDerivAt z (derivWithin z (Icc (-1 : ℝ) 1) s) s) ∧
    (∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (derivWithin z (Icc (-1 : ℝ) 1))
        (derivWithin (derivWithin z (Icc (-1 : ℝ) 1)) (Icc (-1 : ℝ) 1) s) s) := by
  have hu : UniqueDiffOn ℝ (Icc (-1 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hz₁ : ContDiffOn ℝ 1 (derivWithin z (Icc (-1 : ℝ) 1)) (Icc (-1 : ℝ) 1) :=
    hz.derivWithin hu (by norm_num)
  refine ⟨hz₁.continuousOn, hz₁.continuousOn_derivWithin hu (by norm_num), ?_, ?_⟩
  · intro s hs
    exact ((hz.differentiableOn (by norm_num)) s (Ioo_subset_Icc_self hs)).hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)
  · intro s hs
    exact ((hz₁.differentiableOn (by norm_num)) s (Ioo_subset_Icc_self hs)).hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)

omit [NormedSpace ℝ E] in
/-- On the compact source interval, the norm bound can be chosen as an
attained maximum, exactly as in the definition of each `Z_j`. -/
theorem continuous_norm_maximum (z : ℝ → E)
    (hz : ContinuousOn z (Icc (-1 : ℝ) 1)) :
    ∃ Z ≥ 0, (∀ s ∈ Icc (-1 : ℝ) 1, ‖z s‖ ≤ Z) ∧
      ∃ s ∈ Icc (-1 : ℝ) 1, ‖z s‖ = Z := by
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (-1 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) hz.norm
  exact ⟨‖z s‖, norm_nonneg _, hmax, s, hs, rfl⟩

end C2Data

/-- The complete sampled/continuum SDP certificate under a `C²` local
preprocessing hypothesis. Both optima are attained, all homogeneous Gram
constraints are preserved, and the loss uses the manuscript's exact spectral
norm constant. The `Z_j` bounds may be the attained maxima supplied above. -/
theorem c2_grid_certificate (φ : ℝ → ℝ) (W : Anchors φ) (T : Finset ℝ)
    (P a b h Z₀ Z₁ Z₂ : ℝ) (hP : 0 < P) (hh : 0 ≤ h)
    (h₀ : 0 ≤ Z₀) (h₁ : 0 ≤ Z₁) (h₂ : 0 ≤ Z₂)
    (hW : ∀ i, W.s i ∈ T) (hTa : (-1 : ℝ) ∈ T) (hTb : (1 : ℝ) ∈ T)
    (hT : ∀ t ∈ T, t ∈ Icc (-1 : ℝ) 1)
    (hspacing : ∀ l ∈ T, ∀ r ∈ T, l < r →
      (∀ t ∈ T, l < t → t < r → False) → r - l ≤ h)
    (hφ : ContDiffOn ℝ 2 φ (Icc (-1 : ℝ) 1))
    (hz₀ : ∀ s ∈ Icc (-1 : ℝ) 1, ‖euclideanFeature φ s‖ ≤ Z₀)
    (hz₁ : ∀ s ∈ Icc (-1 : ℝ) 1,
      ‖derivWithin (euclideanFeature φ) (Icc (-1 : ℝ) 1) s‖ ≤ Z₁)
    (hz₂ : ∀ s ∈ Icc (-1 : ℝ) 1,
      ‖derivWithin (derivWithin (euclideanFeature φ) (Icc (-1 : ℝ) 1))
        (Icc (-1 : ℝ) 1) s‖ ≤ Z₂) :
    ∃ q qstar : Coordinates,
      GridFeasible φ T P a b q ∧
      (∀ r : Coordinates, GridFeasible φ T P a b r → r 6 ≤ q 6) ∧
      Feasible φ P a b qstar ∧
      (∀ r : Coordinates, Feasible φ P a b r → r 6 ≤ qstar 6) ∧
      (let ρ := P / (P + (2 * ‖gramOperator q‖ * (Z₁ ^ 2 + Z₀ * Z₂)) * h ^ 2 / 8)
       Feasible φ P a b (fun i => ρ * q i) ∧ ρ * q 6 ≤ qstar 6 ∧ qstar 6 ≤ q 6) := by
  obtain ⟨q, hq, hqm, _⟩ := grid_maximum_attained W T hW hP.le
  obtain ⟨qstar, hs, hsm⟩ := maximum_attained W hP.le
  have hz := euclidean_feature_contDiffOn φ hφ
  obtain ⟨_, _, hd, hdd⟩ := c2_derivative_data (euclideanFeature φ) hz
  have hpeak := operator_grid_peak_bound (gramOperator q) (euclideanFeature φ)
    (derivWithin (euclideanFeature φ) (Icc (-1 : ℝ) 1))
    (derivWithin (derivWithin (euclideanFeature φ) (Icc (-1 : ℝ) 1)) (Icc (-1 : ℝ) 1))
    T (-1) 1 P h Z₀ Z₁ Z₂ hh h₀ h₁ h₂ hTa hTb hT hspacing hz.continuousOn
    hd hdd hz₀ hz₁ hz₂ (fun s hs => by simpa only [gram_operator_peak] using hq.2.2.1 s hs)
  have hp : ∀ s ∈ Icc (-1 : ℝ) 1, quad q (feature φ s) ≤
      P + (2 * ‖gramOperator q‖ * (Z₁ ^ 2 + Z₀ * Z₂)) * h ^ 2 / 8 := by
    intro s hs
    simpa only [gram_operator_peak] using hpeak s hs
  have hB : 0 < P + (2 * ‖gramOperator q‖ * (Z₁ ^ 2 + Z₀ * Z₂)) * h ^ 2 / 8 := by
    positivity
  have hscale := grid_scaled_feasible φ T P a b _ hP hB q hq hp
  exact ⟨q, qstar, hq, hqm, hs, hsm, hscale, hsm _ hscale,
    hqm _ (continuum_implies_grid φ T P a b hT qstar hs)⟩

end Analog.CertifiedGrid
