import Analog.SynthesisAttainment
import Analog.TwoStatisticDesign
import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Attainment for two prescribed additive statistics
We derive compactness and a positive feasible point; neither is assumed. -/

noncomputable section
open Set
open scoped NNReal
namespace Analog.TwoStatisticAttainment
open GramSynthesis SynthesisAttainment AdditiveStatistics

abbrev Coordinates := SynthesisAttainment.Coordinates
abbrev Vector3 := SynthesisAttainment.Vector3

def feature (γ : ℝ → ℝ × ℝ) (s : ℝ) : Vector3 := ![1, (γ s).1, (γ s).2]

/-- Functional independence of 1 and the two prescribed coordinates. -/
def IndependentStatistics (γ : ℝ → ℝ × ℝ) : Prop :=
  ∀ c a b : ℝ, (∀ s ∈ Icc (-1 : ℝ) 1,
    c + a * (γ s).1 + b * (γ s).2 = 0) → c = 0 ∧ a = 0 ∧ b = 0

structure Anchors (γ : ℝ → ℝ × ℝ) where
  s : Fin 3 → ℝ
  valid : ∀ i, s i ∈ Icc (-1 : ℝ) 1
  coeff : Fin 3 → Fin 3 → ℝ
  reconstruct : ∀ j, coeff j 0 • feature γ (s 0) +
    coeff j 1 • feature γ (s 1) + coeff j 2 • feature γ (s 2) = Pi.single j 1

/-- Continuum peak and exact attained-pair separation constraints. -/
def Feasible (γ : ℝ → ℝ × ℝ) (M : Set (ℝ × ℝ))
    (F : ℝ × ℝ → ℝ) (P : ℝ) (q : Coordinates) : Prop :=
  0 ≤ q 6 ∧ PSD3 (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) ∧
  (∀ s ∈ Icc (-1 : ℝ) 1, quad q (feature γ s) ≤ P) ∧
  ∀ μ ∈ M, ∀ ν ∈ M, q 6 * (F μ - F ν) ^ 2 ≤
    form2 (q 3) (q 4) (q 5) (μ.1 - ν.1) (μ.2 - ν.2)

def Anchors.bound {γ : ℝ → ℝ × ℝ} (W : Anchors γ) (P : ℝ) (j : Fin 3) : ℝ :=
  3 * (W.coeff j 0 ^ 2 + W.coeff j 1 ^ 2 + W.coeff j 2 ^ 2) * P

def Anchors.cap {γ : ℝ → ℝ × ℝ} (W : Anchors γ) (P : ℝ) : ℝ :=
  W.bound P 0 + W.bound P 1 + W.bound P 2

lemma Anchors.bound_nonneg {γ : ℝ → ℝ × ℝ} (W : Anchors γ) {P : ℝ} (hP : 0 ≤ P)
    (j : Fin 3) : 0 ≤ W.bound P j := by
  dsimp [Anchors.bound]
  positivity

lemma Anchors.cap_nonneg {γ : ℝ → ℝ × ℝ} (W : Anchors γ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ W.cap P := by
  exact add_nonneg (add_nonneg (W.bound_nonneg hP 0) (W.bound_nonneg hP 1))
    (W.bound_nonneg hP 2)

lemma Anchors.quad_basis_bound {γ : ℝ → ℝ × ℝ} (W : Anchors γ)
    {P : ℝ} {M : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {q : Coordinates} (hq : Feasible γ M F P q) (j : Fin 3) :
    quad q (Pi.single j 1) ≤ W.bound P j := by
  have hp (i : Fin 3) := hq.2.2.1 (W.s i) (W.valid i)
  have h := quad_sum_three_le hq.2.1 (W.coeff j 0 • feature γ (W.s 0))
    (W.coeff j 1 • feature γ (W.s 1)) (W.coeff j 2 • feature γ (W.s 2))
  rw [W.reconstruct j, quad_smul, quad_smul, quad_smul] at h
  have h₀ := mul_le_mul_of_nonneg_left (hp 0) (sq_nonneg (W.coeff j 0))
  have h₁ := mul_le_mul_of_nonneg_left (hp 1) (sq_nonneg (W.coeff j 1))
  have h₂ := mul_le_mul_of_nonneg_left (hp 2) (sq_nonneg (W.coeff j 2))
  dsimp [Anchors.bound]
  nlinarith

lemma Anchors.diagonal_bounds {γ : ℝ → ℝ × ℝ} (W : Anchors γ)
    {P : ℝ} {M : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} (hP : 0 ≤ P) {q : Coordinates} (hq : Feasible γ M F P q) :
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

/-- Bounds on all six Gram entries. -/
theorem Anchors.gram_bound {γ : ℝ → ℝ × ℝ} (W : Anchors γ)
    {P : ℝ} {M : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ}
    (hP : 0 ≤ P) {q : Coordinates} (hq : Feasible γ M F P q) :
    ∀ i : Fin 7, i ≠ 6 → |q i| ≤ W.cap P := by
  obtain ⟨h₀, h₀', h₃, h₃', h₄, h₄'⟩ := W.diagonal_bounds hP hq
  have cap0 := W.cap_nonneg hP
  have n₁p := hq.2.1 1 1 0
  have n₁m := hq.2.1 1 (-1) 0
  have n₂p := hq.2.1 1 0 1
  have n₂m := hq.2.1 1 0 (-1)
  have n₅p := hq.2.1 0 1 1
  have n₅m := hq.2.1 0 1 (-1)
  norm_num [form3, form2] at n₁p n₁m n₂p n₂m n₅p n₅m
  intro i hi
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
  · exact False.elim (hi rfl)

lemma form2_bound {A B C R : ℝ} (hA : A ≤ R) (hB : B ≤ R)
    (hC : |C| ≤ R) (x y : ℝ) :
    form2 A B C x y ≤ R * (x ^ 2 + y ^ 2 + 2 * |x * y|) := by
  have ha := mul_le_mul_of_nonneg_right hA (sq_nonneg x)
  have hb := mul_le_mul_of_nonneg_right hB (sq_nonneg y)
  have hc := mul_le_mul_of_nonneg_right hC (abs_nonneg (x*y))
  have he : C * x * y ≤ |C| * |x*y| := by
    rw [← abs_mul]
    simpa [mul_assoc] using le_abs_self (C*(x*y))
  unfold form2
  nlinarith

def Anchors.totalCap {γ : ℝ → ℝ × ℝ} (W : Anchors γ) (P : ℝ)
    (F : ℝ × ℝ → ℝ) (μ ν : ℝ × ℝ) : ℝ :=
  max (W.cap P) (W.cap P * ((μ.1-ν.1)^2 + (μ.2-ν.2)^2 +
    2*|(μ.1-ν.1)*(μ.2-ν.2)|) / (F μ-F ν)^2)

/-- One unequal desired-function pair bounds the seventh coordinate. -/
theorem Anchors.coordinate_bound {γ : ℝ → ℝ × ℝ} (W : Anchors γ)
    {P : ℝ} {M : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} (hP : 0 ≤ P)
    {μ ν : ℝ × ℝ} (hμ : μ ∈ M) (hν : ν ∈ M) (hne : F μ ≠ F ν)
    {q : Coordinates} (hq : Feasible γ M F P q) :
    ∀ i : Fin 7, |q i| ≤ W.totalCap P F μ ν := by
  have hgram := W.gram_bound hP hq
  intro i
  by_cases hi : i = 6
  · subst i
    have hp := hq.2.2.2 μ hμ ν hν
    have hu := form2_bound (abs_le.mp (hgram 3 (by decide))).2
      (abs_le.mp (hgram 4 (by decide))).2 (hgram 5 (by decide))
      (μ.1-ν.1) (μ.2-ν.2)
    have hd : 0 < (F μ-F ν)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    rw [abs_of_nonneg hq.1]
    exact ((le_div_iff₀ hd).mpr (hp.trans hu)).trans (le_max_right _ _)
  · exact (hgram i hi).trans (le_max_left _ _)

lemma continuous_pair (F : ℝ × ℝ → ℝ) (μ ν : ℝ × ℝ) :
    Continuous (fun q : Coordinates => form2 (q 3) (q 4) (q 5)
      (μ.1-ν.1) (μ.2-ν.2) - q 6 * (F μ-F ν)^2) := by
  unfold form2
  fun_prop

/-- Closedness does not require continuity of either prescribed function. -/
theorem feasible_isClosed (γ : ℝ → ℝ × ℝ) (M : Set (ℝ × ℝ))
    (F : ℝ × ℝ → ℝ) (P : ℝ) : IsClosed {q : Coordinates | Feasible γ M F P q} := by
  have hpsd : IsClosed {q : Coordinates | PSD3 (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)} := by
    simp only [PSD3, setOf_forall]
    exact isClosed_iInter fun t => isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le continuous_const (continuous_quad ![t, x, y])
  have hpeak : IsClosed {q : Coordinates | ∀ s ∈ Icc (-1 : ℝ) 1,
      quad q (feature γ s) ≤ P} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun _ =>
      isClosed_le (continuous_quad (feature γ s)) continuous_const
  have hpairs : IsClosed {q : Coordinates | ∀ μ ∈ M, ∀ ν ∈ M,
      q 6 * (F μ-F ν)^2 ≤ form2 (q 3) (q 4) (q 5) (μ.1-ν.1) (μ.2-ν.2)} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun μ => isClosed_iInter fun _ =>
      isClosed_iInter fun ν => isClosed_iInter fun _ =>
        isClosed_le ((continuous_apply 6).mul continuous_const) (by unfold form2; fun_prop)
  exact (isClosed_le continuous_const (continuous_apply 6)).inter
    (hpsd.inter (hpeak.inter hpairs))

/-- Compactness is derived using an actual unequal pair. -/
theorem feasible_isCompact {γ : ℝ → ℝ × ℝ} (W : Anchors γ)
    {M : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {P : ℝ} (hP : 0 ≤ P)
    (hn : Operational.NonconstantOn M F) :
    IsCompact {q : Coordinates | Feasible γ M F P q} := by
  obtain ⟨μ, hμ, ν, hν, hne⟩ := hn
  have hbox : IsCompact {q : Coordinates | ∀ i,
      q i ∈ Icc (-W.totalCap P F μ ν) (W.totalCap P F μ ν)} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  apply hbox.of_isClosed_subset (feasible_isClosed γ M F P)
  intro q hq i
  exact abs_le.mp (W.coordinate_bound hP hμ hν hne hq i)

lemma zero_feasible (γ : ℝ → ℝ × ℝ) (M : Set (ℝ × ℝ))
    (F : ℝ × ℝ → ℝ) {P : ℝ} (hP : 0 ≤ P) :
    Feasible γ M F P (fun _ => 0) := by
  refine ⟨le_rfl, ?_, ?_, ?_⟩
  · intro t x y
    simp [form3, form2]
  · intro s _
    simpa [quad, form3, form2] using hP
  · intro μ _ ν _
    simp [form2]

theorem maximum_attained {γ : ℝ → ℝ × ℝ} (W : Anchors γ)
    {M : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {P : ℝ} (hP : 0 ≤ P)
    (hn : Operational.NonconstantOn M F) :
    ∃ q : Coordinates, Feasible γ M F P q ∧
      ∀ r : Coordinates, Feasible γ M F P r → r 6 ≤ q 6 := by
  obtain ⟨q, hq, hmax⟩ := (feasible_isCompact W hP hn).exists_isMaxOn
    ⟨fun _ => 0, zero_feasible γ M F hP⟩ (continuous_apply 6).continuousOn
  exact ⟨q, hq, hmax⟩


def anchorDet (γ : ℝ → ℝ × ℝ) (x y : ℝ) : ℝ :=
  ((γ x).1-(γ 0).1)*((γ y).2-(γ 0).2) -
    ((γ y).1-(γ 0).1)*((γ x).2-(γ 0).2)

/-- Functional independence supplies three affinely independent input images. -/
theorem independent_has_nondegenerate_anchors {γ : ℝ → ℝ × ℝ}
    (hind : IndependentStatistics γ) :
    ∃ x ∈ Icc (-1 : ℝ) 1, ∃ y ∈ Icc (-1 : ℝ) 1, anchorDet γ x y ≠ 0 := by
  have hex : ∃ x ∈ Icc (-1 : ℝ) 1, (γ x).1 ≠ (γ 0).1 := by
    by_contra h
    push_neg at h
    have hh := hind (-(γ 0).1) 1 0 (by
      intro s hs
      rw [h s hs]
      ring)
    norm_num at hh
  obtain ⟨x, hx, hdiff⟩ := hex
  have hey : ∃ y ∈ Icc (-1 : ℝ) 1, anchorDet γ x y ≠ 0 := by
    by_contra h
    push_neg at h
    have hh := hind (((γ x).2-(γ 0).2)*(γ 0).1 -
        ((γ x).1-(γ 0).1)*(γ 0).2)
      (-((γ x).2-(γ 0).2)) ((γ x).1-(γ 0).1) (by
        intro s hs
        have hd := h s hs
        dsimp [anchorDet] at hd
        nlinarith only [hd])
    exact hdiff (sub_eq_zero.mp hh.2.2)
  obtain ⟨y, hy, hd⟩ := hey
  exact ⟨x, hx, y, hy, hd⟩

def interpolationWeights (γ : ℝ → ℝ × ℝ) (x y : ℝ) (v : Vector3) : Vector3 :=
  let r := v 1 - (γ 0).1*v 0
  let z := v 2 - (γ 0).2*v 0
  let w₁ := (r*((γ y).2-(γ 0).2)-((γ y).1-(γ 0).1)*z)/anchorDet γ x y
  let w₂ := (((γ x).1-(γ 0).1)*z-r*((γ x).2-(γ 0).2))/anchorDet γ x y
  ![v 0-w₁-w₂, w₁, w₂]

lemma interpolation_reconstruct (γ : ℝ → ℝ × ℝ) (x y : ℝ)
    (hd : anchorDet γ x y ≠ 0) (v : Vector3) :
    interpolationWeights γ x y v 0 • feature γ 0 +
      interpolationWeights γ x y v 1 • feature γ x +
      interpolationWeights γ x y v 2 • feature γ y = v := by
  funext i
  fin_cases i <;> simp [interpolationWeights, feature] <;> field_simp [hd]
  all_goals dsimp [anchorDet]; ring

/-- The paper's independence hypothesis supplies the anchor data used in
compactness, without any extra spanning assumption. -/
theorem anchors_nonempty {γ : ℝ → ℝ × ℝ} (hind : IndependentStatistics γ) :
    Nonempty (Anchors γ) := by
  obtain ⟨x, hx, y, hy, hd⟩ := independent_has_nondegenerate_anchors hind
  refine ⟨{ s := ![0, x, y]
            valid := ?_
            coeff := fun j => interpolationWeights γ x y (Pi.single j 1)
            reconstruct := ?_ }⟩
  · intro i
    fin_cases i
    · norm_num
    · exact hx
    · exact hy
  · intro j
    exact interpolation_reconstruct γ x y hd (Pi.single j 1)

/-- Compactness under precisely functional independence and a nonconstant
postprocessing function on the chosen statistic set. -/
theorem feasible_isCompact_of_independent {γ : ℝ → ℝ × ℝ}
    (hind : IndependentStatistics γ) {M : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ}
    {P : ℝ} (hP : 0 ≤ P) (hn : Operational.NonconstantOn M F) :
    IsCompact {q : Coordinates | Feasible γ M F P q} := by
  obtain ⟨W⟩ := anchors_nonempty hind
  exact feasible_isCompact W hP hn


/-- A Lipschitz bound in the standard product metric yields the Euclidean
squared-distance bound used by the Gram program. -/
lemma lipschitz_squared_bound {M : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {L : ℝ≥0}
    (hL : LipschitzOnWith L F M) {μ ν : ℝ × ℝ} (hμ : μ ∈ M) (hν : ν ∈ M) :
    (F μ-F ν)^2 ≤ (L : ℝ)^2*((μ.1-ν.1)^2+(μ.2-ν.2)^2) := by
  have hh := hL.dist_le_mul μ hμ ν hν
  rw [Real.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hh
  have hr : 0 ≤ (L : ℝ)*max |μ.1-ν.1| |μ.2-ν.2| :=
    mul_nonneg L.coe_nonneg ((abs_nonneg _).trans (le_max_left _ _))
  have hs := (sq_le_sq₀ (abs_nonneg (F μ-F ν)) hr).mpr hh
  rw [sq_abs, mul_pow] at hs
  have hm : (max |μ.1-ν.1| |μ.2-ν.2|)^2 ≤
      (μ.1-ν.1)^2+(μ.2-ν.2)^2 := by
    rcases le_total |μ.1-ν.1| |μ.2-ν.2| with h | h
    · rw [max_eq_right h, sq_abs]
      linarith [sq_nonneg (μ.1-ν.1)]
    · rw [max_eq_left h, sq_abs]
      linarith [sq_nonneg (μ.2-ν.2)]
  exact hs.trans (mul_le_mul_of_nonneg_left hm (sq_nonneg (L : ℝ)))

/-- A bounded prescribed curve and Lipschitz postprocessing admit an explicit
positive isotropic Gram design. -/
theorem positive_feasible_of_bounded {γ : ℝ → ℝ × ℝ}
    {M : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {P R : ℝ} {L : ℝ≥0}
    (hP : 0 < P) (hR : 0 ≤ R)
    (hγ : ∀ s ∈ Icc (-1 : ℝ) 1, (γ s).1^2+(γ s).2^2 ≤ R)
    (hL : LipschitzOnWith L F M) :
    ∃ q : Coordinates, Feasible γ M F P q ∧ 0 < q 6 := by
  let t : ℝ := P/(1+R)
  let lam : ℝ := t/(1+(L : ℝ)^2)
  have hden : 0 < 1+R := by linarith
  have hN : 0 < 1+(L : ℝ)^2 := by positivity
  have ht : 0 < t := div_pos hP hden
  have hlam : 0 < lam := div_pos ht hN
  have htId : t*(1+R) = P := div_mul_cancel₀ P hden.ne'
  have hlamId : lam*(1+(L : ℝ)^2) = t := div_mul_cancel₀ t hN.ne'
  have hb : lam*(L : ℝ)^2 ≤ t := by nlinarith
  let q : Coordinates := ![0, 0, 0, t, t, 0, lam]
  refine ⟨q, ⟨hlam.le, ?_, ?_, ?_⟩, hlam⟩
  · intro u x y
    change 0 ≤ form3 0 0 0 t t 0 u x y
    simpa [form3, form2] using add_nonneg (mul_nonneg ht.le (sq_nonneg x))
      (mul_nonneg ht.le (sq_nonneg y))
  · intro s hs
    have hbγ : (γ s).1^2+(γ s).2^2 ≤ 1+R := by linarith [hγ s hs]
    have hp := mul_le_mul_of_nonneg_left hbγ ht.le
    change quad q (feature γ s) ≤ P
    simpa [quad, feature, q, form3, form2, mul_add, htId] using hp.trans_eq htId
  · intro μ hμ ν hν
    have h₁ := mul_le_mul_of_nonneg_left (lipschitz_squared_bound hL hμ hν) hlam.le
    have h₂ := mul_le_mul_of_nonneg_right hb
      (add_nonneg (sq_nonneg (μ.1-ν.1)) (sq_nonneg (μ.2-ν.2)))
    change lam * (F μ-F ν)^2 ≤ form2 t t 0 (μ.1-ν.1) (μ.2-ν.2)
    dsimp [form2]
    nlinarith only [h₁, h₂]

/-- Continuity on the source interval supplies the boundedness needed by the
positive construction. -/
theorem positive_feasible_of_continuous {γ : ℝ → ℝ × ℝ}
    {M : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {P : ℝ} {L : ℝ≥0}
    (hP : 0 < P) (hγ : ContinuousOn γ (Icc (-1 : ℝ) 1))
    (hL : LipschitzOnWith L F M) :
    ∃ q : Coordinates, Feasible γ M F P q ∧ 0 < q 6 := by
  have henergy : ContinuousOn (fun s => (γ s).1^2+(γ s).2^2) (Icc (-1 : ℝ) 1) :=
    (hγ.fst.pow 2).add (hγ.snd.pow 2)
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (-1 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) henergy
  exact positive_feasible_of_bounded hP
    (add_nonneg (sq_nonneg (γ s).1) (sq_nonneg (γ s).2)) (fun x hx => hmax hx) hL

/-- The general seven-variable SDP has a positive attained maximum under the
paper's independence, continuity, nonconstancy, Lipschitz, and power assumptions.
The statistic set may be the actual finite-K attainable set, with no convexity
assumption. This theorem concerns the SDP; planar nondegeneracy is separate. -/
theorem positive_maximum_attained {γ : ℝ → ℝ × ℝ}
    {M : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {P : ℝ} {L : ℝ≥0}
    (hP : 0 < P) (hγ : ContinuousOn γ (Icc (-1 : ℝ) 1))
    (hind : IndependentStatistics γ) (hn : Operational.NonconstantOn M F)
    (hL : LipschitzOnWith L F M) :
    ∃ q : Coordinates, Feasible γ M F P q ∧ 0 < q 6 ∧
      ∀ r : Coordinates, Feasible γ M F P r → r 6 ≤ q 6 := by
  obtain ⟨W⟩ := anchors_nonempty hind
  obtain ⟨q, hq, hmax⟩ := maximum_attained W hP.le hn
  obtain ⟨r, hr, hrpos⟩ := positive_feasible_of_continuous hP hγ hL
  exact ⟨q, hq, lt_of_lt_of_le hrpos (hmax r hr), hmax⟩

/-- Specialization to empirical statistics of actual admissible K-input tuples. -/
theorem attained_statistic_maximum {K : ℕ} {γ : ℝ → ℝ × ℝ}
    {F : ℝ × ℝ → ℝ} {P : ℝ} {L : ℝ≥0}
    (hP : 0 < P) (hγ : ContinuousOn γ (Icc (-1 : ℝ) 1))
    (hind : IndependentStatistics γ)
    (hn : Operational.NonconstantOn (attainable K γ) F)
    (hL : LipschitzOnWith L F (attainable K γ)) :
    ∃ q : Coordinates, Feasible γ (attainable K γ) F P q ∧ 0 < q 6 ∧
      ∀ r : Coordinates, Feasible γ (attainable K γ) F P r → r 6 ≤ q 6 :=
  positive_maximum_attained hP hγ hind hn hL


lemma quad_mix (q r : Coordinates) (a b : ℝ) (v : Vector3) :
    quad (a • q+b • r) v = a*quad q v+b*quad r v := by
  dsimp [quad, form3, form2]
  ring

/-- All the generalized peak and attained-pair constraints are affine in
the seven coordinates, so their common feasible set is convex. -/
theorem feasible_convex (γ : ℝ → ℝ × ℝ) (M : Set (ℝ × ℝ))
    (F : ℝ × ℝ → ℝ) (P : ℝ) : Convex ℝ {q : Coordinates | Feasible γ M F P q} := by
  intro q hq r hr a b ha hb hab
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 0 ≤ a*q 6+b*r 6
    exact add_nonneg (mul_nonneg ha hq.1) (mul_nonneg hb hr.1)
  · intro t x y
    change 0 ≤ quad (a • q+b • r) ![t,x,y]
    rw [quad_mix]
    exact add_nonneg (mul_nonneg ha (hq.2.1 t x y))
      (mul_nonneg hb (hr.2.1 t x y))
  · intro s hs
    rw [quad_mix]
    calc
      _ ≤ a*P+b*P := add_le_add (mul_le_mul_of_nonneg_left (hq.2.2.1 s hs) ha)
        (mul_le_mul_of_nonneg_left (hr.2.2.1 s hs) hb)
      _ = (a+b)*P := by ring
      _ = P := by rw [hab, one_mul]
  · intro μ hμ ν hν
    have h₁ := mul_le_mul_of_nonneg_left (hq.2.2.2 μ hμ ν hν) ha
    have h₂ := mul_le_mul_of_nonneg_left (hr.2.2.2 μ hμ ν hν) hb
    change (a*q 6+b*r 6)*(F μ-F ν)^2 ≤
      form2 (a*q 3+b*r 3) (a*q 4+b*r 4) (a*q 5+b*r 5) (μ.1-ν.1) (μ.2-ν.2)
    dsimp [form2] at h₁ h₂ ⊢
    nlinarith only [h₁, h₂]

end Analog.TwoStatisticAttainment
