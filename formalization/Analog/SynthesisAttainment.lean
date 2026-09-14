import Analog.Frontier
import Analog.GeneralDesign
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Convex.Function

/-!
# Attainment of the continuum Gram synthesis problem

This file uses seven real coordinates for the six symmetric Gram entries and
the separation objective. Compactness is derived from the continuum peak
constraints and three spanning feature anchors. It is not an extra assumption.
-/

noncomputable section
open Set
namespace Analog.SynthesisAttainment
open Analog.GramSynthesis

abbrev Coordinates := Fin 7 → ℝ
abbrev Vector3 := Fin 3 → ℝ

def quad (q : Coordinates) (v : Vector3) : ℝ :=
  form3 (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) (v 0) (v 1) (v 2)

def feature (φ : ℝ → ℝ) (s : ℝ) : Vector3 := ![1, s, φ s]

/-- Three admissible feature vectors span the three-dimensional ambient
space, with explicit coefficients for the three standard basis vectors. -/
structure Anchors (φ : ℝ → ℝ) where
  s : Fin 3 → ℝ
  valid : ∀ i, s i ∈ Icc (-1 : ℝ) 1
  coeff : Fin 3 → Fin 3 → ℝ
  reconstruct : ∀ j, coeff j 0 • feature φ (s 0) +
    coeff j 1 • feature φ (s 1) + coeff j 2 • feature φ (s 2) = Pi.single j 1

/-- The closed SDP feasible set, including the zero-score boundary. -/
def Feasible (φ : ℝ → ℝ) (P a b : ℝ) (q : Coordinates) : Prop :=
  0 ≤ q 6 ∧ PSD3 (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) ∧
  (∀ s : ℝ, -1 ≤ s → s ≤ 1 → quad q (feature φ s) ≤ P) ∧
  RankOnePSD (q 3) (q 4) (q 5) (q 6) a 1 ∧
  RankOnePSD (q 3) (q 4) (q 5) (q 6) b 1

lemma quad_nonneg {q : Coordinates}
    (h : PSD3 (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)) (v : Vector3) : 0 ≤ quad q v :=
  h (v 0) (v 1) (v 2)

lemma quad_smul (q : Coordinates) (a : ℝ) (v : Vector3) :
    quad q (a • v) = a ^ 2 * quad q v := by
  dsimp [quad, form3, form2]
  ring

/-- A three-vector quadratic inequality proved directly from genuine PSD. -/
lemma quad_sum_three_le {q : Coordinates}
    (h : PSD3 (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)) (u v w : Vector3) :
    quad q (u + v + w) ≤ 3 * (quad q u + quad q v + quad q w) := by
  have h₁ := quad_nonneg h (u - v)
  have h₂ := quad_nonneg h (u - w)
  have h₃ := quad_nonneg h (v - w)
  have hi : 3 * (quad q u + quad q v + quad q w) - quad q (u + v + w) =
      quad q (u - v) + quad q (u - w) + quad q (v - w) := by
    dsimp [quad, form3, form2]
    ring
  linarith

def Anchors.bound {φ : ℝ → ℝ} (W : Anchors φ) (P : ℝ) (j : Fin 3) : ℝ :=
  3 * (W.coeff j 0 ^ 2 + W.coeff j 1 ^ 2 + W.coeff j 2 ^ 2) * P

def Anchors.cap {φ : ℝ → ℝ} (W : Anchors φ) (P : ℝ) : ℝ :=
  W.bound P 0 + W.bound P 1 + W.bound P 2

lemma Anchors.bound_nonneg {φ : ℝ → ℝ} (W : Anchors φ) {P : ℝ} (hP : 0 ≤ P)
    (j : Fin 3) : 0 ≤ W.bound P j := by
  dsimp [Anchors.bound]
  positivity

lemma Anchors.cap_nonneg {φ : ℝ → ℝ} (W : Anchors φ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ W.cap P := by
  exact add_nonneg (add_nonneg (W.bound_nonneg hP 0) (W.bound_nonneg hP 1))
    (W.bound_nonneg hP 2)

lemma Anchors.quad_basis_bound {φ : ℝ → ℝ} (W : Anchors φ)
    {P a b : ℝ} {q : Coordinates} (hq : Feasible φ P a b q) (j : Fin 3) :
    quad q (Pi.single j 1) ≤ W.bound P j := by
  have hp (i : Fin 3) := hq.2.2.1 (W.s i) (W.valid i).1 (W.valid i).2
  have h := quad_sum_three_le hq.2.1 (W.coeff j 0 • feature φ (W.s 0))
    (W.coeff j 1 • feature φ (W.s 1)) (W.coeff j 2 • feature φ (W.s 2))
  rw [W.reconstruct j, quad_smul, quad_smul, quad_smul] at h
  have h₀ := mul_le_mul_of_nonneg_left (hp 0) (sq_nonneg (W.coeff j 0))
  have h₁ := mul_le_mul_of_nonneg_left (hp 1) (sq_nonneg (W.coeff j 1))
  have h₂ := mul_le_mul_of_nonneg_left (hp 2) (sq_nonneg (W.coeff j 2))
  dsimp [Anchors.bound]
  nlinarith

lemma Anchors.diagonal_bounds {φ : ℝ → ℝ} (W : Anchors φ)
    {P a b : ℝ} (hP : 0 ≤ P) {q : Coordinates} (hq : Feasible φ P a b q) :
    0 ≤ q 0 ∧ q 0 ≤ W.cap P ∧ 0 ≤ q 3 ∧ q 3 ≤ W.cap P ∧
      0 ≤ q 4 ∧ q 4 ≤ W.cap P := by
  have h₀ := W.quad_basis_bound hq 0
  have h₁ := W.quad_basis_bound hq 1
  have h₂ := W.quad_basis_bound hq 2
  norm_num [quad, form3, form2, Pi.single_apply, Fin.ext_iff] at h₀ h₁ h₂
  have n₀ := hq.2.1 1 0 0
  have n₁ := hq.2.1 0 1 0
  have n₂ := hq.2.1 0 0 1
  norm_num [form3, form2] at n₀ n₁ n₂
  have b₀ := W.bound_nonneg hP 0
  have b₁ := W.bound_nonneg hP 1
  have b₂ := W.bound_nonneg hP 2
  dsimp [Anchors.cap]
  exact ⟨n₀, by linarith, n₁, by linarith, n₂, by linarith⟩

/-- Every SDP coordinate has an explicit uniform bound from the three anchors. -/
theorem Anchors.coordinate_bound {φ : ℝ → ℝ} (W : Anchors φ)
    {P a b : ℝ} (hP : 0 ≤ P) {q : Coordinates} (hq : Feasible φ P a b q) :
    ∀ i : Fin 7, |q i| ≤ W.cap P := by
  obtain ⟨h₀, h₀', h₃, h₃', h₄, h₄'⟩ := W.diagonal_bounds hP hq
  have cap0 := W.cap_nonneg hP
  have n₁p := hq.2.1 1 1 0
  have n₁m := hq.2.1 1 (-1) 0
  have n₂p := hq.2.1 1 0 1
  have n₂m := hq.2.1 1 0 (-1)
  have n₅p := hq.2.1 0 1 1
  have n₅m := hq.2.1 0 1 (-1)
  have h₆ := hq.2.2.2.1 0 1
  norm_num [form3, form2] at n₁p n₁m n₂p n₂m n₅p n₅m h₆
  intro i
  fin_cases i
  · change |q 0| ≤ W.cap P
    exact abs_le.mpr ⟨by linarith, h₀'⟩
  · change |q 1| ≤ W.cap P
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · change |q 2| ≤ W.cap P
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · change |q 3| ≤ W.cap P
    exact abs_le.mpr ⟨by linarith, h₃'⟩
  · change |q 4| ≤ W.cap P
    exact abs_le.mpr ⟨by linarith, h₄'⟩
  · change |q 5| ≤ W.cap P
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · change |q 6| ≤ W.cap P
    exact abs_le.mpr ⟨by linarith [hq.1], by linarith⟩

lemma continuous_quad (v : Vector3) : Continuous (fun q : Coordinates => quad q v) := by
  unfold quad form3 form2
  fun_prop

lemma continuous_rank_form (a x y : ℝ) : Continuous (fun q : Coordinates =>
    form2 (q 3) (q 4) (q 5) x y - q 6 * (a * x + y) ^ 2) := by
  unfold form2
  fun_prop

/-- Arbitrary intersections of pointwise polynomial inequalities give the
closed continuum feasible set; continuity of the feature is not required. -/
theorem feasible_isClosed (φ : ℝ → ℝ) (P a b : ℝ) :
    IsClosed {q : Coordinates | Feasible φ P a b q} := by
  have hpsd : IsClosed {q : Coordinates | PSD3 (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)} := by
    simp only [PSD3, setOf_forall]
    apply isClosed_iInter
    intro t
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    exact isClosed_le continuous_const (continuous_quad ![t, x, y])
  have hpeak : IsClosed {q : Coordinates | ∀ s : ℝ, -1 ≤ s → s ≤ 1 →
      quad q (feature φ s) ≤ P} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le (continuous_quad (feature φ s)) continuous_const
  have hrank (a : ℝ) : IsClosed {q : Coordinates |
      RankOnePSD (q 3) (q 4) (q 5) (q 6) a 1} := by
    simp only [RankOnePSD, one_mul, setOf_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le continuous_const (continuous_rank_form a x y)
  exact (isClosed_le continuous_const (continuous_apply 6)).inter
    (hpsd.inter (hpeak.inter ((hrank a).inter (hrank b))))

/-- Compactness follows from the derived anchor bounds and closedness. -/
theorem feasible_isCompact {φ : ℝ → ℝ} (W : Anchors φ) {P a b : ℝ} (hP : 0 ≤ P) :
    IsCompact {q : Coordinates | Feasible φ P a b q} := by
  have hbox : IsCompact {q : Coordinates | ∀ i, q i ∈ Icc (-W.cap P) (W.cap P)} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  apply hbox.of_isClosed_subset (feasible_isClosed φ P a b)
  intro q hq i
  exact abs_le.mp (W.coordinate_bound hP hq i)

lemma zero_feasible (φ : ℝ → ℝ) {P a b : ℝ} (hP : 0 ≤ P) :
    Feasible φ P a b (fun _ => 0) := by
  refine ⟨le_rfl, ?_, ?_, ?_, ?_⟩
  · intro t x y
    simp [form3, form2]
  · intro s _ _
    simpa [quad, form3, form2] using hP
  · intro x y
    simp [form2]
  · intro x y
    simp [form2]

/-- The continuum SDP attains its maximal separation coordinate. Neither
compactness nor existence of an optimizer is assumed. -/
theorem maximum_attained {φ : ℝ → ℝ} (W : Anchors φ) {P a b : ℝ} (hP : 0 ≤ P) :
    ∃ q : Coordinates, Feasible φ P a b q ∧
      ∀ r : Coordinates, Feasible φ P a b r → r 6 ≤ q 6 := by
  obtain ⟨q, hq, hmax⟩ := (feasible_isCompact W hP).exists_isMaxOn
    ⟨fun _ => 0, zero_feasible φ hP⟩ (continuous_apply 6).continuousOn
  exact ⟨q, hq, hmax⟩

def anchorGap (φ : ℝ → ℝ) : ℝ := φ (-1) - 2 * φ 0 + φ 1

def interpolationWeights (φ : ℝ → ℝ) (v : Vector3) : Vector3 :=
  let wMinus := (v 2 - φ 0 * v 0 - (φ 1 - φ 0) * v 1) / anchorGap φ
  let wPlus := (v 2 - φ 0 * v 0 + (φ (-1) - φ 0) * v 1) / anchorGap φ
  ![wMinus, v 0 - wMinus - wPlus, wPlus]

lemma interpolation_reconstruct (φ : ℝ → ℝ) (hgap : anchorGap φ ≠ 0) (v : Vector3) :
    interpolationWeights φ v 0 • feature φ (-1) +
      interpolationWeights φ v 1 • feature φ 0 +
      interpolationWeights φ v 2 • feature φ 1 = v := by
  funext i
  fin_cases i <;> simp [interpolationWeights, feature] <;>
    try field_simp [hgap]
  all_goals
    dsimp [anchorGap]
    ring

/-- Explicit spanning anchors at -1, 0, and 1 whenever the feature is not
collinear at those three points. -/
def endpointAnchors (φ : ℝ → ℝ) (hgap : anchorGap φ ≠ 0) : Anchors φ where
  s := ![-1, 0, 1]
  valid := by intro i; fin_cases i <;> norm_num
  coeff := fun j => interpolationWeights φ (Pi.single j 1)
  reconstruct := fun j => interpolation_reconstruct φ hgap (Pi.single j 1)

/-- Strict convexity or concavity supplies noncollinearity of the explicit
endpoint/midpoint anchors. -/
theorem anchorGap_ne_zero_of_strict_shape {φ : ℝ → ℝ}
    (hshape : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ) : anchorGap φ ≠ 0 := by
  have convex_gap {φ : ℝ → ℝ} (hc : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ) :
      0 < anchorGap φ := by
    have h := hc.2 (by norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1)
      (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) (by norm_num : (-1 : ℝ) ≠ 1)
      (by norm_num : 0 < (1 : ℝ) / 2) (by norm_num : 0 < (1 : ℝ) / 2)
      (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
    norm_num at h
    dsimp [anchorGap]
    linarith
  rcases hshape with hc | hc
  · exact (convex_gap hc).ne'
  · have h := convex_gap hc.neg
    simp only [anchorGap, Pi.neg_apply] at h ⊢
    linarith

lemma rank_one_isotropic {t lam a : ℝ} (hlam : 0 ≤ lam)
    (hbound : lam * (a ^ 2 + 1) ≤ t) : RankOnePSD t t 0 lam a 1 := by
  intro x y
  have hc : (a * x + y) ^ 2 ≤ (a ^ 2 + 1) * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x - a * y)]
  have h₁ := mul_le_mul_of_nonneg_left hc hlam
  have h₂ := mul_le_mul_of_nonneg_right hbound (add_nonneg (sq_nonneg x) (sq_nonneg y))
  dsimp [form2]
  nlinarith

/-- A bounded feature admits an explicit feasible isotropic Gram design with
strictly positive separation for every positive power budget. -/
theorem positive_feasible_of_bounded {φ : ℝ → ℝ} {P a b M : ℝ} (hP : 0 < P)
    (_hM : 0 ≤ M) (hφ : ∀ s ∈ Icc (-1 : ℝ) 1, |φ s| ≤ M) :
    ∃ q : Coordinates, Feasible φ P a b q ∧ 0 < q 6 := by
  let t : ℝ := P / (1 + M ^ 2)
  let N : ℝ := a ^ 2 + b ^ 2 + 1
  let lam : ℝ := t / N
  have hden : 0 < 1 + M ^ 2 := by positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have ht : 0 < t := div_pos hP hden
  have hlam : 0 < lam := div_pos ht hN
  have htId : t * (1 + M ^ 2) = P := div_mul_cancel₀ P hden.ne'
  have hlamId : lam * N = t := div_mul_cancel₀ t hN.ne'
  have hbA : lam * (a ^ 2 + 1) ≤ t := by
    have hp := mul_nonneg hlam.le (sq_nonneg b)
    dsimp [N] at hlamId
    nlinarith
  have hbB : lam * (b ^ 2 + 1) ≤ t := by
    have hp := mul_nonneg hlam.le (sq_nonneg a)
    dsimp [N] at hlamId
    nlinarith
  let q : Coordinates := ![0, 0, 0, t, t, 0, lam]
  refine ⟨q, ?_, hlam⟩
  refine ⟨hlam.le, ?_, ?_, rank_one_isotropic hlam.le hbA, rank_one_isotropic hlam.le hbB⟩
  · intro u x y
    change 0 ≤ form3 0 0 0 t t 0 u x y
    simpa [form3, form2] using add_nonneg (mul_nonneg ht.le (sq_nonneg x))
      (mul_nonneg ht.le (sq_nonneg y))
  · intro s hs hs1
    have hsq : s ^ 2 ≤ 1 := by nlinarith
    have hφs := abs_le.mp (hφ s ⟨hs, hs1⟩)
    have hφsq : (φ s) ^ 2 ≤ M ^ 2 := by nlinarith [hφs.1, hφs.2]
    have hp := mul_le_mul_of_nonneg_left (show s ^ 2 + (φ s) ^ 2 ≤ 1 + M ^ 2 by linarith) ht.le
    change quad q (feature φ s) ≤ P
    simpa [quad, feature, q, form3, form2, mul_add, htId] using hp.trans_eq htId

/-- Feature continuity on the closed interval supplies the boundedness used
by the explicit positive-score design. -/
theorem positive_feasible_of_continuous {φ : ℝ → ℝ} {P a b : ℝ} (hP : 0 < P)
    (hφ : ContinuousOn φ (Icc (-1 : ℝ) 1)) :
    ∃ q : Coordinates, Feasible φ P a b q ∧ 0 < q 6 := by
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (-1 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) hφ.abs
  exact positive_feasible_of_bounded hP (abs_nonneg (φ s)) (fun x hx => hmax hx)

/-- The attained maximum has strictly positive score for every continuous
feature with spanning anchors and every positive power budget. -/
theorem positive_maximum_attained {φ : ℝ → ℝ} (W : Anchors φ) {P a b : ℝ}
    (hP : 0 < P) (hφ : ContinuousOn φ (Icc (-1 : ℝ) 1)) :
    ∃ q : Coordinates, Feasible φ P a b q ∧ 0 < q 6 ∧
      ∀ r : Coordinates, Feasible φ P a b r → r 6 ≤ q 6 := by
  obtain ⟨q, hq, hmax⟩ := maximum_attained W hP.le
  obtain ⟨r, hr, hrpos⟩ := positive_feasible_of_continuous hP hφ
  exact ⟨q, hq, lt_of_lt_of_le hrpos (hmax r hr), hmax⟩

/-- Maximum-separation SDP attainment under the paper's feature shape and
continuity assumptions, with no supplied anchor witness or compactness premise. -/
theorem positive_maximum_attained_of_strict_shape {φ : ℝ → ℝ} {P a b : ℝ}
    (hP : 0 < P) (hφ : ContinuousOn φ (Icc (-1 : ℝ) 1))
    (hshape : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ) :
    ∃ q : Coordinates, Feasible φ P a b q ∧ 0 < q 6 ∧
      ∀ r : Coordinates, Feasible φ P a b r → r 6 ≤ q 6 :=
  positive_maximum_attained (endpointAnchors φ (anchorGap_ne_zero_of_strict_shape hshape)) hP hφ

/-- The full Gram coordinates of a physical affine-feature curve, with its
largest admissible endpoint separation parameter. -/
def coordinatesOfCurve (e : Curve) (ψ : ℝ → ℝ) : Coordinates :=
  let p : Planar := ⟨e.cx, e.cy, e.ux, e.uy, e.vx, e.vy⟩
  ![p.h, p.l₁, p.l₂, p.A, p.B, p.C, 1 / GeneralScore.endpointDual e ψ]

/-- Every nondegenerate peak-feasible physical curve supplies a feasible SDP
point at its reciprocal endpoint dual norm. -/
theorem coordinatesOfCurve_feasible (e : Curve) (φ ψ : ℝ → ℝ) {P : ℝ}
    (hD : 0 < det e.A e.B e.C) (hpeak : GeneralDesign.PeakFeasible e φ P) :
    Feasible φ P (-GeneralScore.readoutSlope ψ (-1)) (-GeneralScore.readoutSlope ψ 1)
      (coordinatesOfCurve e ψ) := by
  let p : Planar := ⟨e.cx, e.cy, e.ux, e.uy, e.vx, e.vy⟩
  have hp : GeneralDesign.curveOfPlanar p = e := by rfl
  have hlam : 0 ≤ 1 / GeneralScore.endpointDual e ψ :=
    (one_div_pos.mpr (GeneralScore.endpointDual_pos e ψ hD)).le
  have hend := (GeneralDesign.endpoint_constraints_iff e ψ
    (1 / GeneralScore.endpointDual e ψ) hD hlam).mpr le_rfl
  refine ⟨hlam, p.gram_psd, ?_, hend.1, hend.2⟩
  intro s hs hs1
  change form3 p.h p.l₁ p.l₂ p.A p.B p.C 1 s (φ s) ≤ P
  rw [← p.energy_eq_form3, ← GeneralDesign.curveOfPlanar_energy, hp]
  exact hpeak s ⟨hs, hs1⟩

/-- Positive actual operational score forces Gram nondegeneracy under strict
readout curvature. Singular and constant feature curves are not excluded by
hypothesis: the two endpoint directional inequalities rule them out. -/
theorem positive_score_implies_positive_gram (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (φ ψ : ℝ → ℝ)
    (hφ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ)
    (hdφ : ∀ z ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ φ z)
    (hψ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (hdψ : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hcψ : ContinuousOn (GeneralScore.readoutSlope ψ) (Icc (-1 : ℝ) 1))
    (hscore : 0 < GeneralScore.score K φ ψ e) : 0 < det e.A e.B e.C := by
  have hk : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hk2 : 0 < (K : ℝ) ^ 2 := sq_pos_of_pos hk
  have hbound := Operational.score_is_lowerBound
    (GeneralScore.target_nonconstant_of_strict_feature hK φ ψ hφ)
    (fun xs _ ys _ => ArbitraryEncoder.squaredDistance_nonnegative
      (ArbitraryEncoder.received (GeneralScore.encoder e φ) xs)
      (ArbitraryEncoder.received (GeneralScore.encoder e φ) ys))
  have hlocal : GeneralScore.LocalSeparation K φ ψ e 1 (GeneralScore.score K φ ψ e) := by
    intro xs ys hxs hys _
    exact hbound xs hxs ys hys
  have hφi : StrictConvexOn ℝ (Ioo (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Ioo (-1 : ℝ) 1) φ := by
    rcases hφ with h | h
    · exact Or.inl (h.subset Ioo_subset_Icc_self (convex_Ioo (-1) 1))
    · exact Or.inr (h.subset Ioo_subset_Icc_self (convex_Ioo (-1) 1))
  have hrank (m : ℝ) (hm : m ∈ Icc (-1 : ℝ) 1) :
      RankOnePSD e.A e.B e.C (GeneralScore.score K φ ψ e / (K : ℝ)^2)
        (-GeneralScore.readoutSlope ψ m) 1 := by
    intro x y
    have h := GeneralScore.local_separation_direction_bound_closed e hK φ ψ 1
      (GeneralScore.score K φ ψ e) (by norm_num) hlocal hφi hdφ hdψ hcψ m x y hm
    have hb : GeneralScore.score K φ ψ e * (y - GeneralScore.readoutSlope ψ m * x)^2 /
        (K : ℝ)^2 ≤ form2 e.A e.B e.C x y := by
      apply (div_le_iff₀ hk2).mpr
      simpa only [mul_comm] using h
    have he : GeneralScore.score K φ ψ e / (K : ℝ)^2 *
        (-GeneralScore.readoutSlope ψ m * x + 1 * y)^2 =
        GeneralScore.score K φ ψ e * (y - GeneralScore.readoutSlope ψ m * x)^2 / (K : ℝ)^2 := by
      ring
    rw [he]
    exact sub_nonneg.mpr hb
  have hind : (-GeneralScore.readoutSlope ψ (-1)) * 1 -
      1 * (-GeneralScore.readoutSlope ψ 1) ≠ 0 := by
    have hh := GeneralDesign.strict_readout_endpoint_slopes ψ hψ hdψ
    intro heq
    apply hh
    linarith
  exact (two_rank_one_constraints_positive e.A e.B e.C
    (GeneralScore.score K φ ψ e / (K : ℝ)^2)
    (-GeneralScore.readoutSlope ψ (-1)) 1 (-GeneralScore.readoutSlope ψ 1) 1
    (div_pos hscore hk2) hind (hrank (-1) (by norm_num)) (hrank 1 (by norm_num))).2

/-- The general operational design problem attains its optimum over all
affine-feature curves, including singular and constant competitors. Both the SDP maximum and its physical
realization are derived, and the objective is the actual input-pair infimum.
This theorem does not enlarge the competitor class to arbitrary continuous
encoders; that still requires the unrestricted rigidity reduction. -/
theorem operational_maximum_attained {K : ℕ} (hK : 2 ≤ K)
    (φ ψ : ℝ → ℝ) {P : ℝ} (hP : 0 < P)
    (hcφ : ContinuousOn φ (Icc (-1 : ℝ) 1))
    (hφ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ)
    (hdφ : ∀ z ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ φ z)
    (hψ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (hdψ : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hcψ : ContinuousOn (GeneralScore.readoutSlope ψ) (Icc (-1 : ℝ) 1)) :
    ∃ e : Curve, 0 < det e.A e.B e.C ∧ GeneralDesign.PeakFeasible e φ P ∧
      ContinuousOn (GeneralScore.encoder e φ) (Icc (-1 : ℝ) 1) ∧
      GeneralCollision.ExactTarget K φ ψ (GeneralScore.encoder e φ) ∧
      0 < GeneralScore.score K φ ψ e ∧
      ∀ f : Curve, GeneralDesign.PeakFeasible f φ P →
        GeneralScore.score K φ ψ f ≤ GeneralScore.score K φ ψ e := by
  obtain ⟨q, hq, hqpos, hmax⟩ := positive_maximum_attained_of_strict_shape
    (a := -GeneralScore.readoutSlope ψ (-1)) (b := -GeneralScore.readoutSlope ψ 1)
    hP hcφ hφ
  obtain ⟨e, _, _, _, hD, hpeak, hcont, hexact, hlower⟩ :=
    GeneralDesign.positive_sdp_operational_synthesis hK φ ψ
      (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) P (q 6)
      hcφ hφ hdφ hψ hdψ hcψ hqpos hq.2.1 hq.2.2.2.1 hq.2.2.2.2 hq.2.2.1
  have hψshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ := by
    rcases hψ with h | h
    · exact Or.inl h.convexOn
    · exact Or.inr h.concaveOn
  have upper (f : Curve) (hfD : 0 < det f.A f.B f.C)
      (hfpeak : GeneralDesign.PeakFeasible f φ P) :
      GeneralScore.score K φ ψ f ≤ (K : ℝ) ^ 2 * q 6 := by
    have hbound := hmax (coordinatesOfCurve f ψ) (coordinatesOfCurve_feasible f φ ψ hfD hfpeak)
    change 1 / GeneralScore.endpointDual f ψ ≤ q 6 at hbound
    rw [GeneralScore.general_operational_score f hK φ ψ hfD hφ hdφ hψshape hdψ hcψ]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hbound (sq_nonneg (K : ℝ))
  have hkpos : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  refine ⟨e, hD, hpeak, hcont, hexact,
    lt_of_lt_of_le (mul_pos (sq_pos_of_pos hkpos) hqpos) hlower, ?_⟩
  intro f hfpeak
  by_cases hfscore : 0 < GeneralScore.score K φ ψ f
  · have hfD := positive_score_implies_positive_gram f hK φ ψ hφ hdφ hψ hdψ hcψ hfscore
    exact (upper f hfD hfpeak).trans hlower
  · exact (le_of_not_gt hfscore).trans
      (le_trans (mul_pos (sq_pos_of_pos hkpos) hqpos).le hlower)

end Analog.SynthesisAttainment
