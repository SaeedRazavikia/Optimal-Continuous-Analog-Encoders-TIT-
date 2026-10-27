import Analog.TwoStatisticAttainment
import Analog.CertifiedGrid
import Analog.HeterogeneousSynthesis

/-!
# Actual heterogeneous secant programs with arbitrary peak sets

Every node has its own six Gram entries, with the lower three entries and
separation coordinate constrained to agree. All attainable secant inequalities
remain present. Fixed spanning samples imply compactness and attained maxima
for both sampled and continuum peak constraints.
-/

noncomputable section
namespace Analog.HeterogeneousGridFeasible
open Set GramSynthesis SynthesisAttainment
open TwoStatisticAttainment (form2_bound)

/-- Only the peak domain varies between sampled and continuum programs. -/
def LocalFeasible (γ : ℝ → ℝ × ℝ) (D : Set ℝ) (M : Set (ℝ × ℝ))
    (F : ℝ × ℝ → ℝ) (P : ℝ) (q : Coordinates) : Prop :=
  0 ≤ q 6 ∧ PSD3 (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) ∧
  (∀ s ∈ D, quad q (TwoStatisticAttainment.feature γ s) ≤ P) ∧
  ∀ μ ∈ M, ∀ ν ∈ M, q 6 * (F μ - F ν) ^ 2 ≤
    form2 (q 3) (q 4) (q 5) (μ.1 - ν.1) (μ.2 - ν.2)

/-- Common lower Gram block and common objective, with node-specific offsets. -/
def Shared {ι : Type*} (q : ι → Coordinates) : Prop :=
  ∀ k j (i : Fin 7), 3 ≤ i.val → q k i = q j i

/-- The actual node-dependent program, retaining all moment-pair constraints. -/
def Feasible {ι : Type*} (γ : ι → ℝ → ℝ × ℝ) (D : ι → Set ℝ)
    (M : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (P : ℝ) (q : ι → Coordinates) : Prop :=
  Shared q ∧ ∀ k, LocalFeasible (γ k) (D k) M F P (q k)

lemma local_basis_bound {γ : ℝ → ℝ × ℝ} (W : TwoStatisticAttainment.Anchors γ)
    {D : Set ℝ} (hW : ∀ i, W.s i ∈ D)
    {P : ℝ} {M : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {q : Coordinates}
    (hq : LocalFeasible γ D M F P q) (j : Fin 3) :
    quad q (Pi.single j 1) ≤ W.bound P j := by
  have hp (i : Fin 3) := hq.2.2.1 (W.s i) (hW i)
  have h := quad_sum_three_le hq.2.1
    (W.coeff j 0 • TwoStatisticAttainment.feature γ (W.s 0))
    (W.coeff j 1 • TwoStatisticAttainment.feature γ (W.s 1))
    (W.coeff j 2 • TwoStatisticAttainment.feature γ (W.s 2))
  rw [W.reconstruct j, quad_smul, quad_smul, quad_smul] at h
  have h₀ := mul_le_mul_of_nonneg_left (hp 0) (sq_nonneg (W.coeff j 0))
  have h₁ := mul_le_mul_of_nonneg_left (hp 1) (sq_nonneg (W.coeff j 1))
  have h₂ := mul_le_mul_of_nonneg_left (hp 2) (sq_nonneg (W.coeff j 2))
  dsimp [TwoStatisticAttainment.Anchors.bound]
  nlinarith

/-- Six Gram coordinates are bounded by fixed sampled spanning vectors. -/
theorem local_gram_bound {γ : ℝ → ℝ × ℝ} (W : TwoStatisticAttainment.Anchors γ)
    {D : Set ℝ} (hW : ∀ i, W.s i ∈ D)
    {P : ℝ} {M : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} (hP : 0 ≤ P)
    {q : Coordinates} (hq : LocalFeasible γ D M F P q) :
    ∀ i : Fin 7, i ≠ 6 → |q i| ≤ W.cap P := by
  have b₀ := local_basis_bound W hW hq 0
  have b₁ := local_basis_bound W hW hq 1
  have b₂ := local_basis_bound W hW hq 2
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
  norm_num [form3, form2] at d₀ d₁ d₂ n₁p n₁m n₂p n₂m n₅p n₅m
  intro i hi
  fin_cases i <;> try { exact False.elim (hi rfl) }
  all_goals apply abs_le.mpr; dsimp [TwoStatisticAttainment.Anchors.cap]; constructor <;> linarith

/-- A fixed unequal target pair also bounds the common objective coordinate. -/
theorem local_coordinate_bound {γ : ℝ → ℝ × ℝ}
    (W : TwoStatisticAttainment.Anchors γ) {D : Set ℝ} (hW : ∀ i, W.s i ∈ D)
    {P : ℝ} {M : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} (hP : 0 ≤ P)
    {μ ν : ℝ × ℝ} (hμ : μ ∈ M) (hν : ν ∈ M) (hne : F μ ≠ F ν)
    {q : Coordinates} (hq : LocalFeasible γ D M F P q) :
    ∀ i : Fin 7, |q i| ≤ W.totalCap P F μ ν := by
  have hgram := local_gram_bound W hW hP hq
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

lemma local_feasible_isClosed (γ : ℝ → ℝ × ℝ) (D : Set ℝ) (M : Set (ℝ × ℝ))
    (F : ℝ × ℝ → ℝ) (P : ℝ) : IsClosed {q : Coordinates | LocalFeasible γ D M F P q} := by
  have hpsd : IsClosed {q : Coordinates | PSD3 (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)} := by
    simp only [PSD3, setOf_forall]
    exact isClosed_iInter fun t => isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le continuous_const (continuous_quad ![t, x, y])
  have hpeak : IsClosed {q : Coordinates | ∀ s ∈ D,
      quad q (TwoStatisticAttainment.feature γ s) ≤ P} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun _ =>
      isClosed_le (continuous_quad (TwoStatisticAttainment.feature γ s)) continuous_const
  have hpairs : IsClosed {q : Coordinates | ∀ μ ∈ M, ∀ ν ∈ M,
      q 6 * (F μ-F ν)^2 ≤ form2 (q 3) (q 4) (q 5) (μ.1-ν.1) (μ.2-ν.2)} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun μ => isClosed_iInter fun _ =>
      isClosed_iInter fun ν => isClosed_iInter fun _ =>
        isClosed_le ((continuous_apply 6).mul continuous_const) (by unfold form2; fun_prop)
  exact (isClosed_le continuous_const (continuous_apply 6)).inter
    (hpsd.inter (hpeak.inter hpairs))

theorem feasible_isClosed {ι : Type*} (γ : ι → ℝ → ℝ × ℝ) (D : ι → Set ℝ)
    (M : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (P : ℝ) :
    IsClosed {q : ι → Coordinates | Feasible γ D M F P q} := by
  have hs : IsClosed {q : ι → Coordinates | Shared q} := by
    simp only [Shared, setOf_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun j => isClosed_iInter fun i =>
      isClosed_iInter fun _ => isClosed_eq (by fun_prop) (by fun_prop)
  have hl : IsClosed {q : ι → Coordinates | ∀ k, LocalFeasible (γ k) (D k) M F P (q k)} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun k =>
      (local_feasible_isClosed (γ k) (D k) M F P).preimage
        (show Continuous (fun q : ι → Coordinates => q k) from continuous_apply k)
  exact hs.inter hl

/-- Fixed nodewise spanning samples imply compactness of the actual program. -/
theorem feasible_isCompact {ι : Type*} (γ : ι → ℝ → ℝ × ℝ)
    (W : ∀ k, TwoStatisticAttainment.Anchors (γ k)) (D : ι → Set ℝ)
    (hW : ∀ k i, (W k).s i ∈ D k) (M : Set (ℝ × ℝ))
    (F : ℝ × ℝ → ℝ) {P : ℝ} (hP : 0 ≤ P)
    (hn : Operational.NonconstantOn M F) :
    IsCompact {q : ι → Coordinates | Feasible γ D M F P q} := by
  obtain ⟨μ, hμ, ν, hν, hne⟩ := hn
  have hbox : IsCompact {q : ι → Coordinates | ∀ k i,
      q k i ∈ Icc (-(W k).totalCap P F μ ν) ((W k).totalCap P F μ ν)} :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_Icc
  apply hbox.of_isClosed_subset (feasible_isClosed γ D M F P)
  intro q hq k i
  exact abs_le.mp (local_coordinate_bound (W k) (hW k) hP hμ hν hne (hq.2 k) i)

theorem zero_feasible {ι : Type*} (γ : ι → ℝ → ℝ × ℝ) (D : ι → Set ℝ)
    (M : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) {P : ℝ} (hP : 0 ≤ P) :
    Feasible γ D M F P (fun _ _ => 0) := by
  refine ⟨fun _ _ _ _ => rfl, ?_⟩
  intro k
  refine ⟨le_rfl, ?_, ?_, ?_⟩
  · intro t x y; simp [form3, form2]
  · intro s _; simpa [quad, form3, form2] using hP
  · intro μ _ ν _; simp [form2]

/-- Sampled or continuum maxima exist, including a zero optimum. -/
theorem maximum_attained {ι : Type*} (k₀ : ι) (γ : ι → ℝ → ℝ × ℝ)
    (W : ∀ k, TwoStatisticAttainment.Anchors (γ k)) (D : ι → Set ℝ)
    (hW : ∀ k i, (W k).s i ∈ D k) (M : Set (ℝ × ℝ))
    (F : ℝ × ℝ → ℝ) {P : ℝ} (hP : 0 ≤ P)
    (hn : Operational.NonconstantOn M F) :
    ∃ q : ι → Coordinates, Feasible γ D M F P q ∧
      ∀ r : ι → Coordinates, Feasible γ D M F P r → r k₀ 6 ≤ q k₀ 6 := by
  obtain ⟨q, hq, hmax⟩ := (feasible_isCompact γ W D hW M F hP hn).exists_isMaxOn
    ⟨fun _ _ => 0, zero_feasible γ D M F hP⟩
      (show ContinuousOn (fun q : ι → Coordinates => q k₀ 6) _ from
        ((continuous_apply 6).comp (continuous_apply k₀)).continuousOn)
  exact ⟨q, hq, hmax⟩

/-- Enlarging the peak test sets restricts feasibility; all secants are retained. -/
theorem feasible_mono {ι : Type*} {γ : ι → ℝ → ℝ × ℝ} {D E : ι → Set ℝ}
    {M : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {P : ℝ} {q : ι → Coordinates}
    (hDE : ∀ k, D k ⊆ E k) (hq : Feasible γ E M F P q) : Feasible γ D M F P q := by
  refine ⟨hq.1, fun k => ⟨(hq.2 k).1, (hq.2 k).2.1, ?_, (hq.2 k).2.2.2⟩⟩
  intro s hs
  exact (hq.2 k).2.2.1 s (hDE k hs)

/-- One positive common scaling restores all continuum peaks and preserves every secant. -/
theorem scaled_feasible {ι : Type*} {γ : ι → ℝ → ℝ × ℝ} {D : ι → Set ℝ}
    {M : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ} {P B : ℝ}
    (hP : 0 < P) (hB : 0 < B) {q : ι → Coordinates}
    (hq : Feasible γ D M F P q)
    (hpeak : ∀ k s, s ∈ Icc (-1 : ℝ) 1 →
      quad (q k) (TwoStatisticAttainment.feature (γ k) s) ≤ B) :
    Feasible γ (fun _ => Icc (-1 : ℝ) 1) M F P (fun k i => (P / B) * q k i) := by
  have hr : 0 ≤ P / B := div_nonneg hP.le hB.le
  refine ⟨?_, fun k => ⟨mul_nonneg hr (hq.2 k).1, ?_, ?_, ?_⟩⟩
  · intro k j i hi; change (P / B) * q k i = (P / B) * q j i; rw [hq.1 k j i hi]
  · intro t x y
    have h := mul_nonneg hr ((hq.2 k).2.1 t x y)
    convert h using 1; dsimp [form3, form2]; ring
  · intro s hs
    rw [CertifiedGrid.coordinate_scaling_quad]
    calc
      (P / B) * quad (q k) (TwoStatisticAttainment.feature (γ k) s) ≤ (P / B) * B :=
        mul_le_mul_of_nonneg_left (hpeak k s hs) hr
      _ = P := div_mul_cancel₀ P (ne_of_gt hB)
  · intro μ hμ ν hν
    have h := mul_le_mul_of_nonneg_left ((hq.2 k).2.2.2 μ hμ ν hν) hr
    convert h using 1 <;> dsimp [form2] <;> ring

end Analog.HeterogeneousGridFeasible
