import Analog.HeterogeneousGridFeasible

/-!
# Certified discretization for node-dependent preprocessing

The actual heterogeneous SDP retains every moment-pair constraint. This file
assembles C² interpolation with the maximum of the nodewise spectral constants,
attained sampled and continuum optima, feasible rescaling, operational encoder
reconstruction, and a uniform quadratic scaling loss from fixed anchors.
-/
noncomputable section
namespace Analog.HeterogeneousGrid
open Set GramSynthesis SynthesisAttainment HeterogeneousGridFeasible
open CertifiedGrid (gramOperator operatorPeak operator_grid_peak_bound c2_derivative_data)
open scoped BigOperators Topology

/-- Actual Euclidean feature vector `(1, φ₁,k(s), φ₂,k(s))`. -/
def euclideanFeature (γ : ℝ → ℝ × ℝ) (s : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (TwoStatisticAttainment.feature γ s)

theorem gram_operator_peak (γ : ℝ → ℝ × ℝ) (q : Coordinates) (s : ℝ) :
    operatorPeak (gramOperator q) (euclideanFeature γ) s =
      quad q (TwoStatisticAttainment.feature γ s) := by
  dsimp [operatorPeak, gramOperator, euclideanFeature]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [CertifiedGrid.gramMatrix, TwoStatisticAttainment.feature, quad, form3, form2,
    dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  ring

theorem euclidean_feature_contDiffOn (γ : ℝ → ℝ × ℝ)
    (hγ : ContDiffOn ℝ 2 γ (Icc (-1 : ℝ) 1)) :
    ContDiffOn ℝ 2 (euclideanFeature γ) (Icc (-1 : ℝ) 1) := by
  have hf : ContDiffOn ℝ 2 (TwoStatisticAttainment.feature γ) (Icc (-1 : ℝ) 1) := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · simpa [TwoStatisticAttainment.feature] using
        (contDiffOn_const : ContDiffOn ℝ 2 (fun _ : ℝ => (1 : ℝ)) _)
    · simpa [TwoStatisticAttainment.feature] using hγ.fst
    · simpa [TwoStatisticAttainment.feature] using hγ.snd
  let L : (Fin 3 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  exact L.contDiff.comp_contDiffOn hf

/-- The first and second derivative curves use the closed-interval extensions. -/
def firstFeature (γ : ℝ → ℝ × ℝ) : ℝ → EuclideanSpace ℝ (Fin 3) :=
  derivWithin (euclideanFeature γ) (Icc (-1 : ℝ) 1)

def secondFeature (γ : ℝ → ℝ × ℝ) : ℝ → EuclideanSpace ℝ (Fin 3) :=
  derivWithin (firstFeature γ) (Icc (-1 : ℝ) 1)

/-- All three constants in the theorem are attained norm maxima. -/
theorem feature_norm_maxima (γ : ℝ → ℝ × ℝ)
    (hγ : ContDiffOn ℝ 2 γ (Icc (-1 : ℝ) 1)) :
    ∃ Z₀ Z₁ Z₂ : ℝ, 0 ≤ Z₀ ∧ 0 ≤ Z₁ ∧ 0 ≤ Z₂ ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, ‖euclideanFeature γ s‖ ≤ Z₀) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, ‖firstFeature γ s‖ ≤ Z₁) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, ‖secondFeature γ s‖ ≤ Z₂) ∧
      (∃ s ∈ Icc (-1 : ℝ) 1, ‖euclideanFeature γ s‖ = Z₀) ∧
      (∃ s ∈ Icc (-1 : ℝ) 1, ‖firstFeature γ s‖ = Z₁) ∧
      (∃ s ∈ Icc (-1 : ℝ) 1, ‖secondFeature γ s‖ = Z₂) := by
  have hz := euclidean_feature_contDiffOn γ hγ
  obtain ⟨h₁, h₂, _, _⟩ := c2_derivative_data (euclideanFeature γ) hz
  obtain ⟨Z₀, hZ₀, hb₀, ha₀⟩ := CertifiedGrid.continuous_norm_maximum _ hz.continuousOn
  obtain ⟨Z₁, hZ₁, hb₁, ha₁⟩ := CertifiedGrid.continuous_norm_maximum _ h₁
  obtain ⟨Z₂, hZ₂, hb₂, ha₂⟩ := CertifiedGrid.continuous_norm_maximum _ h₂
  exact ⟨Z₀, Z₁, Z₂, hZ₀, hZ₁, hZ₂, hb₀, hb₁, hb₂, ha₀, ha₁, ha₂⟩

/-- The maximum nodewise spectral remainder, exactly as in the manuscript. -/
def maxCurvature {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → Coordinates) (Z₀ Z₁ Z₂ : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun k => 2 * ‖gramOperator (q k)‖ * ((Z₁ k)^2 + Z₀ k * Z₂ k))

theorem nodeCurvature_le_max {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → Coordinates) (Z₀ Z₁ Z₂ : ι → ℝ) (k : ι) :
    2 * ‖gramOperator (q k)‖ * ((Z₁ k)^2 + Z₀ k * Z₂ k) ≤ maxCurvature q Z₀ Z₁ Z₂ := by
  exact Finset.le_sup' (fun j => 2 * ‖gramOperator (q j)‖ * ((Z₁ j)^2 + Z₀ j * Z₂ j))
    (Finset.mem_univ k)

theorem maxCurvature_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → Coordinates) (Z₀ Z₁ Z₂ : ι → ℝ)
    (h₀ : ∀ k, 0 ≤ Z₀ k) (h₂ : ∀ k, 0 ≤ Z₂ k) :
    0 ≤ maxCurvature q Z₀ Z₁ Z₂ := by
  obtain ⟨k⟩ := ‹Nonempty ι›
  have h0 := h₀ k
  have h2 := h₂ k
  exact (by positivity : 0 ≤ 2 * ‖gramOperator (q k)‖ * ((Z₁ k)^2 + Z₀ k * Z₂ k)).trans
    (nodeCurvature_le_max q Z₀ Z₁ Z₂ k)

/-- C² interpolation bounds every node between grid samples with one common M. -/
theorem c2_peak_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (γ : ι → ℝ → ℝ × ℝ) (T : ι → Finset ℝ) (q : ι → Coordinates)
    (P h : ℝ) (Z₀ Z₁ Z₂ : ι → ℝ) (hh : 0 ≤ h)
    (h₀ : ∀ k, 0 ≤ Z₀ k) (h₁ : ∀ k, 0 ≤ Z₁ k) (h₂ : ∀ k, 0 ≤ Z₂ k)
    (hTa : ∀ k, (-1 : ℝ) ∈ T k) (hTb : ∀ k, (1 : ℝ) ∈ T k)
    (hT : ∀ k t, t ∈ T k → t ∈ Icc (-1 : ℝ) 1)
    (hspacing : ∀ k l, l ∈ T k → ∀ r, r ∈ T k → l < r →
      (∀ t ∈ T k, l < t → t < r → False) → r-l ≤ h)
    (hγ : ∀ k, ContDiffOn ℝ 2 (γ k) (Icc (-1 : ℝ) 1))
    (hz₀ : ∀ k s, s ∈ Icc (-1 : ℝ) 1 → ‖euclideanFeature (γ k) s‖ ≤ Z₀ k)
    (hz₁ : ∀ k s, s ∈ Icc (-1 : ℝ) 1 → ‖firstFeature (γ k) s‖ ≤ Z₁ k)
    (hz₂ : ∀ k s, s ∈ Icc (-1 : ℝ) 1 → ‖secondFeature (γ k) s‖ ≤ Z₂ k)
    (hpeak : ∀ k s, s ∈ T k → quad (q k) (TwoStatisticAttainment.feature (γ k) s) ≤ P) :
    ∀ k s, s ∈ Icc (-1 : ℝ) 1 → quad (q k) (TwoStatisticAttainment.feature (γ k) s) ≤
      P + maxCurvature q Z₀ Z₁ Z₂ * h^2/8 := by
  intro k s hs
  have hz := euclidean_feature_contDiffOn (γ k) (hγ k)
  obtain ⟨_, _, hd, hdd⟩ := c2_derivative_data _ hz
  have hp := operator_grid_peak_bound (gramOperator (q k)) (euclideanFeature (γ k))
    (firstFeature (γ k)) (secondFeature (γ k)) (T k) (-1) 1 P h
    (Z₀ k) (Z₁ k) (Z₂ k) hh (h₀ k) (h₁ k) (h₂ k)
    (hTa k) (hTb k) (hT k) (hspacing k) hz.continuousOn hd hdd
    (hz₀ k) (hz₁ k) (hz₂ k) (fun t ht => by
      simpa only [gram_operator_peak] using hpeak k t ht) s hs
  rw [gram_operator_peak] at hp
  have hm := mul_le_mul_of_nonneg_right (nodeCurvature_le_max q Z₀ Z₁ Z₂ k) (sq_nonneg h)
  linarith

/-- Complete attained sampled/continuum bracket for heterogeneous curves and
all secants. Only peak constraints are discretized. -/
theorem c2_grid_certificate {ι : Type*} [Fintype ι] [Nonempty ι]
    (k₀ : ι) (γ : ι → ℝ → ℝ × ℝ)
    (W : ∀ k, TwoStatisticAttainment.Anchors (γ k)) (T : ι → Finset ℝ)
    (M : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (P h : ℝ)
    (Z₀ Z₁ Z₂ : ι → ℝ) (hP : 0 < P) (hh : 0 ≤ h)
    (hn : Operational.NonconstantOn M F)
    (h₀ : ∀ k, 0 ≤ Z₀ k) (h₁ : ∀ k, 0 ≤ Z₁ k) (h₂ : ∀ k, 0 ≤ Z₂ k)
    (hW : ∀ k i, (W k).s i ∈ T k)
    (hTa : ∀ k, (-1 : ℝ) ∈ T k) (hTb : ∀ k, (1 : ℝ) ∈ T k)
    (hT : ∀ k t, t ∈ T k → t ∈ Icc (-1 : ℝ) 1)
    (hspacing : ∀ k l, l ∈ T k → ∀ r, r ∈ T k → l < r →
      (∀ t ∈ T k, l < t → t < r → False) → r-l ≤ h)
    (hγ : ∀ k, ContDiffOn ℝ 2 (γ k) (Icc (-1 : ℝ) 1))
    (hz₀ : ∀ k s, s ∈ Icc (-1 : ℝ) 1 → ‖euclideanFeature (γ k) s‖ ≤ Z₀ k)
    (hz₁ : ∀ k s, s ∈ Icc (-1 : ℝ) 1 → ‖firstFeature (γ k) s‖ ≤ Z₁ k)
    (hz₂ : ∀ k s, s ∈ Icc (-1 : ℝ) 1 → ‖secondFeature (γ k) s‖ ≤ Z₂ k) :
    ∃ q qstar : ι → Coordinates,
      Feasible γ (fun k => ↑(T k)) M F P q ∧
      (∀ r, Feasible γ (fun k => ↑(T k)) M F P r → r k₀ 6 ≤ q k₀ 6) ∧
      Feasible γ (fun _ => Icc (-1 : ℝ) 1) M F P qstar ∧
      (∀ r, Feasible γ (fun _ => Icc (-1 : ℝ) 1) M F P r → r k₀ 6 ≤ qstar k₀ 6) ∧
      (let ρ := P / (P + maxCurvature q Z₀ Z₁ Z₂ * h^2/8)
       Feasible γ (fun _ => Icc (-1 : ℝ) 1) M F P (fun k i => ρ * q k i) ∧
       ρ * q k₀ 6 ≤ qstar k₀ 6 ∧ qstar k₀ 6 ≤ q k₀ 6) := by
  obtain ⟨q, hq, hmax⟩ := maximum_attained k₀ γ W (fun k => ↑(T k)) hW M F hP.le hn
  obtain ⟨qstar, hs, hsmax⟩ := maximum_attained k₀ γ W (fun _ => Icc (-1 : ℝ) 1)
    (fun k => (W k).valid) M F hP.le hn
  have hp := c2_peak_bound γ T q P h Z₀ Z₁ Z₂ hh h₀ h₁ h₂ hTa hTb hT hspacing hγ
    hz₀ hz₁ hz₂ (fun k => (hq.2 k).2.2.1)
  have hm := maxCurvature_nonneg q Z₀ Z₁ Z₂ h₀ h₂
  have hB : 0 < P + maxCurvature q Z₀ Z₁ Z₂ * h^2/8 := by positivity
  have hscale := scaled_feasible hP hB hq hp
  exact ⟨q, qstar, hq, hmax, hs, hsmax, hscale, hsmax _ hscale,
    hmax _ (feasible_mono hT hs)⟩

/-- The maximum of the nodewise operator constants is continuous in the actual
finite family of Gram coordinates. -/
theorem maxCurvature_continuous {ι : Type*} [Fintype ι] [Nonempty ι]
    (Z₀ Z₁ Z₂ : ι → ℝ) : Continuous (fun q : ι → Coordinates => maxCurvature q Z₀ Z₁ Z₂) := by
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro k _
  exact (continuous_const.mul ((CertifiedGrid.gramOperator_continuous.comp
    (continuous_apply k)).norm)).mul continuous_const

/-- Uniform objective and remainder caps are derived from fixed spanning
samples and one actual unequal target pair. They are not optimizer hypotheses. -/
theorem uniform_caps {ι : Type*} [Fintype ι] [Nonempty ι]
    (k₀ : ι) (γ : ι → ℝ → ℝ × ℝ)
    (W : ∀ k, TwoStatisticAttainment.Anchors (γ k))
    (M : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (P : ℝ)
    (Z₀ Z₁ Z₂ : ι → ℝ) (hP : 0 ≤ P)
    (hn : Operational.NonconstantOn M F)
    (h₀ : ∀ k, 0 ≤ Z₀ k) (h₂ : ∀ k, 0 ≤ Z₂ k) :
    ∃ U ≥ 0, ∃ C ≥ 0, ∀ (D : ι → Set ℝ),
      (∀ k i, (W k).s i ∈ D k) → ∀ q : ι → Coordinates,
      Feasible γ D M F P q → q k₀ 6 ≤ U ∧ maxCurvature q Z₀ Z₁ Z₂ ≤ C := by
  obtain ⟨μ, hμ, ν, hν, hne⟩ := hn
  let B : Set (ι → Coordinates) := {q | ∀ k i,
    q k i ∈ Icc (-(W k).totalCap P F μ ν) ((W k).totalCap P F μ ν)}
  have hc : IsCompact B := isCompact_pi_infinite fun _ =>
    isCompact_pi_infinite fun _ => isCompact_Icc
  have ht (k : ι) : 0 ≤ (W k).totalCap P F μ ν :=
    ((W k).cap_nonneg hP).trans (le_max_left _ _)
  have hb : B.Nonempty := ⟨fun _ _ => 0, fun k _ => ⟨by linarith [ht k], ht k⟩⟩
  obtain ⟨qmax, _, hmax⟩ := hc.exists_isMaxOn hb
    (maxCurvature_continuous Z₀ Z₁ Z₂).continuousOn
  refine ⟨(W k₀).totalCap P F μ ν, ht k₀, maxCurvature qmax Z₀ Z₁ Z₂,
    maxCurvature_nonneg qmax Z₀ Z₁ Z₂ h₀ h₂, ?_⟩
  intro D hW q hq
  have hcoord (k : ι) (i : Fin 7) :=
    local_coordinate_bound (W k) (hW k) hP hμ hν hne (hq.2 k) i
  exact ⟨(le_abs_self _).trans (hcoord k₀ 6),
    hmax (fun k i => abs_le.mp (hcoord k i))⟩

/-- Every family of sampled feasible designs with the fixed anchors has the
manuscript's O(h²) scaling loss, in particular the attained sampled optimizers. -/
theorem scaling_gap_isBigO {ι : Type*} [Fintype ι] [Nonempty ι]
    (k₀ : ι) (γ : ι → ℝ → ℝ × ℝ)
    (W : ∀ k, TwoStatisticAttainment.Anchors (γ k))
    (T : ℝ → ι → Finset ℝ) (q : ℝ → ι → Coordinates)
    (M : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ) (P : ℝ)
    (Z₀ Z₁ Z₂ : ι → ℝ) (hP : 0 < P)
    (hn : Operational.NonconstantOn M F)
    (h₀ : ∀ k, 0 ≤ Z₀ k) (h₂ : ∀ k, 0 ≤ Z₂ k)
    (hW : ∀ h > 0, ∀ k i, (W k).s i ∈ T h k)
    (hq : ∀ h > 0, Feasible γ (fun k => ↑(T h k)) M F P (q h)) :
    (fun h => q h k₀ 6 -
      (P / (P + maxCurvature (q h) Z₀ Z₁ Z₂ * h^2/8)) * q h k₀ 6)
      =O[𝓝[>] (0 : ℝ)] (fun h => h^2) := by
  obtain ⟨U, _, C, _, hcap⟩ := uniform_caps k₀ γ W M F P Z₀ Z₁ Z₂ hP.le hn h₀ h₂
  apply CertifiedGrid.scaling_gap_isBigO (fun h => q h k₀ 6)
    (fun h => maxCurvature (q h) Z₀ Z₁ Z₂) P U C hP
  · intro h hh; exact ((hq h hh).2 k₀).1
  · intro h hh; exact (hcap _ (hW h hh) _ (hq h hh)).1
  · intro h _; exact maxCurvature_nonneg _ _ _ _ h₀ h₂
  · intro h hh; exact (hcap _ (hW h hh) _ (hq h hh)).2

/-- A continuum-feasible point of this precise program yields actual
heterogeneous encoders with the certified operational robustness. -/
theorem feasible_operational_realization {K : ℕ} (hK : 0 < K)
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Icc (-1 : ℝ) 1))
    (hn : Operational.NonconstantOn (HeterogeneousScore.attainable γ) F)
    (P : ℝ) (q : Fin K → Coordinates)
    (hq : Feasible γ (fun _ => Icc (-1 : ℝ) 1) (HeterogeneousScore.attainable γ) F P q) :
    ∃ (e : Planar) (c : Fin K → ℝ × ℝ),
      (∀ k, ContinuousOn (HeterogeneousScore.encoder e c γ k) (Icc (-1 : ℝ) 1)) ∧
      (∀ k s, s ∈ Icc (-1 : ℝ) 1 →
        ArbitraryEncoder.squaredDistance (HeterogeneousScore.encoder e c γ k s) 0 ≤ P) ∧
      (K : ℝ)^2 * q ⟨0, hK⟩ 6 ≤ HeterogeneousScore.score γ F (HeterogeneousScore.encoder e c γ) := by
  let k₀ : Fin K := ⟨0, hK⟩
  have hpsd : ∀ k, PSD3 (q k 0) (q k 1) (q k 2) (q k₀ 3) (q k₀ 4) (q k₀ 5) := by
    intro k
    have hp := (hq.2 k).2.1
    rw [hq.1 k k₀ 3 (by decide), hq.1 k k₀ 4 (by decide), hq.1 k k₀ 5 (by decide)] at hp
    exact hp
  have hpeak : ∀ k s, s ∈ Icc (-1 : ℝ) 1 →
      form3 (q k 0) (q k 1) (q k 2) (q k₀ 3) (q k₀ 4) (q k₀ 5)
        1 (γ k s).1 (γ k s).2 ≤ P := by
    intro k s hs
    have hp := (hq.2 k).2.2.1 s hs
    change form3 (q k 0) (q k 1) (q k 2) (q k 3) (q k 4) (q k 5)
      1 (γ k s).1 (γ k s).2 ≤ P at hp
    rw [hq.1 k k₀ 3 (by decide), hq.1 k k₀ 4 (by decide), hq.1 k k₀ 5 (by decide)] at hp
    exact hp
  obtain ⟨e, c, _, _, _, hc, hp, hscore, _⟩ :=
    HeterogeneousSynthesis.feasible_operational_synthesis hK γ F hγ hn
      (fun k => q k 0) (fun k => q k 1) (fun k => q k 2)
      (q k₀ 3) (q k₀ 4) (q k₀ 5) P (q k₀ 6) hpsd hpeak ((hq.2 k₀).2.2.2)
  exact ⟨e, c, hc, hp, hscore⟩

/-- Full constructive discretization theorem for the actual heterogeneous
finite-input moment model. C² regularity supplies attained norm maxima;
fixed spanning samples supply both optimizers. The resulting encoder retains
all continuum peak constraints and the scaled operational score. -/
theorem certified_discretization {K : ℕ} [NeZero K]
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (W : ∀ k, TwoStatisticAttainment.Anchors (γ k)) (T : Fin K → Finset ℝ)
    (P h : ℝ) (hP : 0 < P) (hh : 0 ≤ h)
    (hn : Operational.NonconstantOn (HeterogeneousScore.attainable γ) F)
    (hW : ∀ k i, (W k).s i ∈ T k)
    (hTa : ∀ k, (-1 : ℝ) ∈ T k) (hTb : ∀ k, (1 : ℝ) ∈ T k)
    (hT : ∀ k t, t ∈ T k → t ∈ Icc (-1 : ℝ) 1)
    (hspacing : ∀ k l, l ∈ T k → ∀ r, r ∈ T k → l < r →
      (∀ t ∈ T k, l < t → t < r → False) → r-l ≤ h)
    (hγ : ∀ k, ContDiffOn ℝ 2 (γ k) (Icc (-1 : ℝ) 1)) :
    ∃ (Z₀ Z₁ Z₂ : Fin K → ℝ) (q qstar : Fin K → Coordinates),
      (∀ k, (0 ≤ Z₀ k ∧ 0 ≤ Z₁ k ∧ 0 ≤ Z₂ k) ∧
        (∀ s ∈ Icc (-1 : ℝ) 1, ‖euclideanFeature (γ k) s‖ ≤ Z₀ k) ∧
        (∀ s ∈ Icc (-1 : ℝ) 1, ‖firstFeature (γ k) s‖ ≤ Z₁ k) ∧
        (∀ s ∈ Icc (-1 : ℝ) 1, ‖secondFeature (γ k) s‖ ≤ Z₂ k) ∧
        (∃ s ∈ Icc (-1 : ℝ) 1, ‖euclideanFeature (γ k) s‖ = Z₀ k) ∧
        (∃ s ∈ Icc (-1 : ℝ) 1, ‖firstFeature (γ k) s‖ = Z₁ k) ∧
        (∃ s ∈ Icc (-1 : ℝ) 1, ‖secondFeature (γ k) s‖ = Z₂ k)) ∧
      Feasible γ (fun k => ↑(T k)) (HeterogeneousScore.attainable γ) F P q ∧
      (∀ r, Feasible γ (fun k => ↑(T k)) (HeterogeneousScore.attainable γ) F P r →
        r 0 6 ≤ q 0 6) ∧
      Feasible γ (fun _ => Icc (-1 : ℝ) 1) (HeterogeneousScore.attainable γ) F P qstar ∧
      (∀ r, Feasible γ (fun _ => Icc (-1 : ℝ) 1) (HeterogeneousScore.attainable γ) F P r →
        r 0 6 ≤ qstar 0 6) ∧
      (let ρ := P / (P + maxCurvature q Z₀ Z₁ Z₂ * h^2/8)
       Feasible γ (fun _ => Icc (-1 : ℝ) 1) (HeterogeneousScore.attainable γ) F P
         (fun k i => ρ * q k i) ∧
       ρ * q 0 6 ≤ qstar 0 6 ∧ qstar 0 6 ≤ q 0 6 ∧
       ∃ (e : Planar) (c : Fin K → ℝ × ℝ),
         (∀ k, ContinuousOn (HeterogeneousScore.encoder e c γ k) (Icc (-1 : ℝ) 1)) ∧
         (∀ k s, s ∈ Icc (-1 : ℝ) 1 →
           ArbitraryEncoder.squaredDistance (HeterogeneousScore.encoder e c γ k s) 0 ≤ P) ∧
         (K : ℝ)^2 * (ρ * q 0 6) ≤
           HeterogeneousScore.score γ F (HeterogeneousScore.encoder e c γ)) := by
  have hk : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  choose Z₀ Z₁ Z₂ h₀ h₁ h₂ hz₀ hz₁ hz₂ ha₀ ha₁ ha₂ using
    fun k => feature_norm_maxima (γ k) (hγ k)
  obtain ⟨q, qstar, hq, hqm, hs, hsm, hscale, hlo, hup⟩ :=
    c2_grid_certificate (0 : Fin K) γ W T (HeterogeneousScore.attainable γ) F P h
      Z₀ Z₁ Z₂ hP hh hn h₀ h₁ h₂ hW hTa hTb hT hspacing hγ hz₀ hz₁ hz₂
  refine ⟨Z₀, Z₁, Z₂, q, qstar,
    (fun k => ⟨⟨h₀ k, h₁ k, h₂ k⟩, hz₀ k, hz₁ k, hz₂ k, ha₀ k, ha₁ k, ha₂ k⟩),
    hq, hqm, hs, hsm, hscale, hlo, hup, ?_⟩
  exact feasible_operational_realization hk γ F (fun k => (hγ k).continuousOn) hn P _ hscale

end Analog.HeterogeneousGrid
