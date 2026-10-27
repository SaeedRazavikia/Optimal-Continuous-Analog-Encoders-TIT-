import Analog.GaussianDesignCompactness
import Analog.HeterogeneousCompletionDensity

/-!
# Compact actual moment images and public compact-source features

The moment set is the actual image of finite source tuples. Boundary moments
lie in the closed canonical coordinate intervals; no convexification,
closure replacement, or false containment in an open interval is used.
-/

noncomputable section
namespace Analog.HeterogeneousMomentCompactness
open Set HeterogeneousScore HeterogeneousAttainment HeterogeneousCompletionDensity
open scoped BigOperators

/-- Actual node features restricted to the compact source interval. -/
def compactFeatures {K : ℕ} (γ : Fin K → ℝ → ℝ × ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Icc (-1 : ℝ) 1)) :
    Fin K → C(Source, ℝ × ℝ) := fun k => ⟨fun s => γ k s, (hγ k).restrict⟩

@[simp] theorem compactFeatures_apply {K : ℕ} (γ : Fin K → ℝ → ℝ × ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Icc (-1 : ℝ) 1)) (k : Fin K) (s : Source) :
    compactFeatures γ hγ k s = γ k s := rfl

/-- Restricting to the source subtype preserves exactly the manuscript's
functional independence of the constant and two feature coordinates. -/
theorem independentFeatures {K : ℕ} (γ : Fin K → ℝ → ℝ × ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Icc (-1 : ℝ) 1))
    (hind : ∀ k, TwoStatisticAttainment.IndependentStatistics (γ k)) :
    GaussianDesignCompactness.IndependentFeatures (compactFeatures γ hγ) := by
  intro k c a b heq
  apply hind k c a b
  intro s hs
  exact heq ⟨s, hs⟩

/-- The canonical inclusion of compact-source tuples into physical tuples. -/
def sourceCoe {K : ℕ} (s : Fin K → Source) : Fin K → ℝ := fun k => s k

/-- Normalized actual moments vary continuously with compact-source tuples. -/
theorem meanStatistic_source_continuous {K : ℕ} (γ : Fin K → ℝ → ℝ × ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Icc (-1 : ℝ) 1)) :
    Continuous (fun s : Fin K → Source => meanStatistic γ (sourceCoe s)) := by
  have hc (k : Fin K) : Continuous (fun s : Fin K → Source => γ k (s k)) :=
    (compactFeatures γ hγ k).continuous.comp (continuous_apply k)
  exact ((continuous_finset_sum _ (fun k _ => (hc k).fst)).div_const (K : ℝ)).prodMk
    ((continuous_finset_sum _ (fun k _ => (hc k).snd)).div_const (K : ℝ))

/-- The physical attainable set is exactly the range on compact-source
tuples, with no enlargement of the image. -/
theorem attainable_eq_source_range {K : ℕ} (γ : Fin K → ℝ → ℝ × ℝ) :
    attainable γ = Set.range (fun s : Fin K → Source => meanStatistic γ (sourceCoe s)) := by
  ext μ
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨fun k => ⟨s k, hs k⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨sourceCoe s, fun k => (s k).property, rfl⟩

/-- Compactness is derived for the actual finite-node moment image. -/
theorem attainable_isCompact {K : ℕ} (γ : Fin K → ℝ → ℝ × ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Icc (-1 : ℝ) 1)) :
    IsCompact (attainable γ) := by
  rw [attainable_eq_source_range]
  exact isCompact_range (meanStatistic_source_continuous γ hγ)

/-- The zero source tuple witnesses nonemptiness for every node count. -/
theorem attainable_nonempty {K : ℕ} (γ : Fin K → ℝ → ℝ × ℝ) :
    (attainable γ).Nonempty := by
  refine ⟨meanStatistic γ (fun _ => 0), (fun _ => 0), ?_, rfl⟩
  intro k
  norm_num

/-- Closed canonical coordinate mean interval; this is definitionally the
same interval as `HeterogeneousFullRigidity.closedMeanDomain`. -/
def closedMeanDomain {K : ℕ} (φ : Fin K → ℝ → ℝ) : Set ℝ :=
  Icc ((∑ k, featureLower (φ k)) / (K : ℝ))
    ((∑ k, featureUpper (φ k)) / (K : ℝ))

/-- Both canonical feature extrema are attained by actual source values. -/
theorem feature_extrema_attained (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (Icc (-1 : ℝ) 1)) :
    (∃ s ∈ Icc (-1 : ℝ) 1, φ s = featureLower φ) ∧
    (∃ t ∈ Icc (-1 : ℝ) 1, φ t = featureUpper φ) := by
  have hc := isCompact_Icc.image_of_continuousOn hφ
  have hn : (φ '' Icc (-1 : ℝ) 1).Nonempty := ⟨φ 0, 0, by norm_num, rfl⟩
  exact ⟨hc.sInf_mem hn, hc.sSup_mem hn⟩

/-- The canonical scalar mean endpoints are also attained by physical
finite source tuples; no common maximizing source value across nodes is
assumed. -/
theorem scalar_mean_endpoints_attained {K : ℕ} (φ : Fin K → ℝ → ℝ)
    (hφ : ∀ k, ContinuousOn (φ k) (Icc (-1 : ℝ) 1)) :
    (∃ s ∈ ValidInput K,
      (∑ k, φ k (s k)) / (K : ℝ) = (∑ k, featureLower (φ k)) / (K : ℝ)) ∧
    (∃ t ∈ ValidInput K,
      (∑ k, φ k (t k)) / (K : ℝ) = (∑ k, featureUpper (φ k)) / (K : ℝ)) := by
  choose s hs hmin using fun k => (feature_extrema_attained (φ k) (hφ k)).1
  choose t ht hmax using fun k => (feature_extrema_attained (φ k) (hφ k)).2
  exact ⟨⟨s, hs, by simp_rw [hmin]⟩, ⟨t, ht, by simp_rw [hmax]⟩⟩

/-- Every continuous scalar feature value lies between its actual image
infimum and supremum, including boundary values. -/
theorem feature_mem_closed_range (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (Icc (-1 : ℝ) 1)) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    φ s ∈ Icc (featureLower φ) (featureUpper φ) := by
  have hc := isCompact_Icc.image_of_continuousOn hφ
  exact ⟨csInf_le hc.bddBelow ⟨s, hs, rfl⟩, le_csSup hc.bddAbove ⟨s, hs, rfl⟩⟩

/-- Every actual scalar mean is in the closed interval formed from the
exact nodewise extrema. The division uses the actual node count. -/
theorem scalar_mean_mem_closedMeanDomain {K : ℕ} (φ : Fin K → ℝ → ℝ)
    (hφ : ∀ k, ContinuousOn (φ k) (Icc (-1 : ℝ) 1))
    {s : Fin K → ℝ} (hs : s ∈ ValidInput K) :
    (∑ k, φ k (s k)) / (K : ℝ) ∈ closedMeanDomain φ := by
  constructor
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg K)
    exact Finset.sum_le_sum (fun k _ => (feature_mem_closed_range (φ k) (hφ k) (hs k)).1)
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg K)
    exact Finset.sum_le_sum (fun k _ => (feature_mem_closed_range (φ k) (hφ k) (hs k)).2)

/-- The actual moment image lies in the product of the two closed canonical
mean intervals. Open mean domains cannot contain its endpoint moments. -/
theorem attainable_subset_closedDomains {K : ℕ} (γ : Fin K → ℝ → ℝ × ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Icc (-1 : ℝ) 1)) :
    attainable γ ⊆ closedMeanDomain (fun k s => (γ k s).1) ×ˢ
      closedMeanDomain (fun k s => (γ k s).2) := by
  rintro μ ⟨s, hs, rfl⟩
  exact ⟨scalar_mean_mem_closedMeanDomain _ (fun k => (hγ k).fst) hs,
    scalar_mean_mem_closedMeanDomain _ (fun k => (hγ k).snd) hs⟩

/-- Actual heterogeneous continuity and functional independence derive the
compact coefficient closure used by the optimized Gaussian theorem. -/
theorem coefficientPeakSet_isCompact {K : ℕ} (hK : 0 < K)
    (γ : Fin K → ℝ → ℝ × ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Icc (-1 : ℝ) 1))
    (hind : ∀ k, TwoStatisticAttainment.IndependentStatistics (γ k))
    {P : ℝ} (hP : 0 ≤ P) :
    IsCompact (GaussianDesignCompactness.coefficientPeakSet (compactFeatures γ hγ) P) :=
  GaussianDesignCompactness.coefficientPeakSet_isCompact hK _
    (independentFeatures γ hγ hind) hP

end Analog.HeterogeneousMomentCompactness
