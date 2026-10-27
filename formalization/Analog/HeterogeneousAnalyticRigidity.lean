import Analog.HeterogeneousRegularity
import Analog.HeterogeneousSeparation

/-!
# Heterogeneous analytic rigidity from dense identifying charts

This module assembles actual inverse-function sections, convolution smoothing,
dense propagation, automatically selected cross-node anchors, common
coefficients, and endpoint integration. The remaining structural premises are
continuous local charts over an identifying set and density on the actual
regular image. Neither encoder differentiability nor determinant identities
are assumed. The subsequent `HeterogeneousFullRigidity` module derives both premises from
exact computation and the original receiver hypotheses, using proved planar
invariance of domain and physical completion separation.
-/

noncomputable section
open Set Filter Topology
namespace Analog.HeterogeneousAnalyticRigidity
open HeterogeneousRegularity

/-- All actual regular three-node moment sums are closure points of the
corresponding identifying set. No density outside attainable regular images
is required. -/
def DenseIdentification {K : ℕ} (φ₁ φ₂ : Fin K → ℝ → ℝ)
    (O : Fin K → Fin K → Fin K → Set Plane) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    ∀ x ∈ Ioo (-1 : ℝ) 1, ∀ y ∈ Ioo (-1 : ℝ) 1, ∀ z ∈ Ioo (-1 : ℝ) 1,
      deriv (φ₁ j) y * deriv (φ₂ k) z - deriv (φ₁ k) z * deriv (φ₂ j) y ≠ 0 →
      tripleStatistic (φ₁ i) (φ₁ j) (φ₁ k) (φ₂ i) (φ₂ j) (φ₂ k) (x, y, z) ∈
        closure (O i j k)

/-- Scalar factorizations only at regular triples above the identifying set. -/
def DenseScalarCharts {K : ℕ} (φ₁ φ₂ e : Fin K → ℝ → ℝ)
    (O : Fin K → Fin K → Fin K → Set Plane) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    ∀ x ∈ Ioo (-1 : ℝ) 1, ∀ y ∈ Ioo (-1 : ℝ) 1, ∀ z ∈ Ioo (-1 : ℝ) 1,
      deriv (φ₁ j) y * deriv (φ₂ k) z - deriv (φ₁ k) z * deriv (φ₂ j) y ≠ 0 →
      tripleStatistic (φ₁ i) (φ₁ j) (φ₁ k) (φ₂ i) (φ₂ j) (φ₂ k) (x, y, z) ∈ O i j k →
      ∃ X ∈ 𝓝 x, ∃ Y ∈ 𝓝 y, ∃ Z ∈ 𝓝 z,
      ∃ B ∈ 𝓝 (tripleStatistic (φ₁ i) (φ₁ j) (φ₁ k) (φ₂ i) (φ₂ j) (φ₂ k) (x, y, z)),
      ∃ H : Plane → ℝ, ContinuousOn H B ∧
        ∀ x' ∈ X, ∀ y' ∈ Y, ∀ z' ∈ Z,
          e i x' + e j y' + e k z' =
            H ((φ₁ i x', φ₂ i x') + (φ₁ j y', φ₂ j y') + (φ₁ k z', φ₂ k z'))

/-- Three or more nodes allow two reference nodes different from any selected
node. This is a finite index fact, not a feature-anchor assumption. -/
theorem exists_two_other_nodes {K : ℕ} (hK : 3 ≤ K) (i : Fin K) :
    ∃ j k : Fin K, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  let i₀ : Fin K := ⟨0, by omega⟩
  let i₁ : Fin K := ⟨1, by omega⟩
  let i₂ : Fin K := ⟨2, by omega⟩
  by_cases hi₀ : i = i₀
  · subst i
    exact ⟨i₁, i₂, by simp [i₀, i₁], by simp [i₀, i₂], by simp [i₁, i₂]⟩
  by_cases hi₁ : i = i₁
  · subst i
    exact ⟨i₀, i₂, by simp [i₀, i₁], by simp [i₁, i₂], by simp [i₀, i₂]⟩
  exact ⟨i₀, i₁, hi₀, hi₁, by simp [i₀, i₁]⟩

/-- Automatic C¹ regularity for every node, derived from dense charts and
per-node functional independence. -/
theorem contDiffOn_of_dense_scalar_charts {K : ℕ} (hK : 3 ≤ K)
    (φ₁ φ₂ e : Fin K → ℝ → ℝ) (O : Fin K → Fin K → Fin K → Set Plane)
    (h₁ : ∀ i, ContinuousOn (φ₁ i) (Icc (-1 : ℝ) 1))
    (h₂ : ∀ i, ContinuousOn (φ₂ i) (Icc (-1 : ℝ) 1))
    (hC₁ : ∀ i, ContDiffOn ℝ 1 (φ₁ i) (Ioo (-1 : ℝ) 1))
    (hC₂ : ∀ i, ContDiffOn ℝ 1 (φ₂ i) (Ioo (-1 : ℝ) 1))
    (hind : ∀ i, GeneralRigidity.NotInAffineLine (Icc (-1 : ℝ) 1) (φ₁ i) (φ₂ i))
    (hdense : DenseIdentification φ₁ φ₂ O) (hcharts : DenseScalarCharts φ₁ φ₂ e O) :
    ∀ i, ContDiffOn ℝ 1 (e i) (Ioo (-1 : ℝ) 1) := by
  intro i x hx
  obtain ⟨j, k, hij, hik, hjk⟩ := exists_two_other_nodes hK i
  obtain ⟨y, hy, z, hz, hd⟩ := HeterogeneousSeparation.independent_tangents_across_nodes
    (φ₁ j) (φ₂ j) (φ₁ k) (φ₂ k) (h₁ j) (h₂ j) (h₁ k) (h₂ k) (hC₁ j).differentiableOn_one
    (hC₂ j).differentiableOn_one (hC₁ k).differentiableOn_one
    (hC₂ k).differentiableOn_one (hind j) (hind k)
  have hγx : ContDiffAt ℝ 1 (fun s => (φ₁ i s, φ₂ i s)) x :=
    ((hC₁ i x hx).contDiffAt (Ioo_mem_nhds hx.1 hx.2)).prodMk
      ((hC₂ i x hx).contDiffAt (Ioo_mem_nhds hx.1 hx.2))
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_of_dense_triple_factorizations hγx (hC₁ j) (hC₁ k)
    (hC₂ j) (hC₂ k) hy hz hd (hdense i j k hij hik hjk x hx y hy z hz hd)
  intro q hq hqO
  exact hcharts i j k hij hik hjk x hx q.1 hq.1.1 q.2 hq.1.2 hq.2 hqO

/-- The complete heterogeneous scalar analytic chain: smoothness, dense
extension of derivative determinants, automatically selected independent
anchors, common coefficients, and both source endpoints. -/
theorem scalar_affine_of_dense_charts {K : ℕ} (hK : 4 ≤ K)
    (φ₁ φ₂ e : Fin K → ℝ → ℝ) (O : Fin K → Fin K → Fin K → Set Plane)
    (h₁ : ∀ i, ContinuousOn (φ₁ i) (Icc (-1 : ℝ) 1))
    (h₂ : ∀ i, ContinuousOn (φ₂ i) (Icc (-1 : ℝ) 1))
    (he : ∀ i, ContinuousOn (e i) (Icc (-1 : ℝ) 1))
    (hC₁ : ∀ i, ContDiffOn ℝ 1 (φ₁ i) (Ioo (-1 : ℝ) 1))
    (hC₂ : ∀ i, ContDiffOn ℝ 1 (φ₂ i) (Ioo (-1 : ℝ) 1))
    (hind : ∀ i, GeneralRigidity.NotInAffineLine (Icc (-1 : ℝ) 1) (φ₁ i) (φ₂ i))
    (hdense : DenseIdentification φ₁ φ₂ O) (hcharts : DenseScalarCharts φ₁ φ₂ e O) :
    ∃ α β : ℝ, ∃ c : Fin K → ℝ, ∀ i x, x ∈ Icc (-1 : ℝ) 1 →
      e i x = c i + α * φ₁ i x + β * φ₂ i x := by
  have hCe := contDiffOn_of_dense_scalar_charts (by omega) φ₁ φ₂ e O h₁ h₂ hC₁ hC₂ hind hdense hcharts
  apply HeterogeneousSeparation.affine_of_independence_and_triple_determinants hK φ₁ φ₂ e
    h₁ h₂ he (fun i => (hC₁ i).differentiableOn_one)
    (fun i => (hC₂ i).differentiableOn_one) (fun i => (hCe i).differentiableOn_one) hind
  intro i j k hij hik hjk x hx y hy z hz hd
  have hat (g : Fin K → ℝ → ℝ) (hCg : ∀ i, ContDiffOn ℝ 1 (g i) (Ioo (-1 : ℝ) 1))
      (i : Fin K) (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) : DifferentiableAt ℝ (g i) x :=
    ((hCg i).differentiableOn_one x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  apply determinant_of_dense_local_fibers (hat φ₁ hC₁ i x hx) (hat φ₂ hC₂ i x hx)
    (hat e hCe i x hx) (hC₁ j) (hC₁ k) (hC₂ j) (hC₂ k) (hCe j) (hCe k)
    hy hz hd (hdense i j k hij hik hjk x hx y hy z hz hd)
  intro q hq hqO
  obtain ⟨X, hX, Y, hY, Z, hZ, B, hB, H, hH, hfactor⟩ :=
    hcharts i j k hij hik hjk x hx q.1 hq.1.1 q.2 hq.1.2 hq.2 hqO
  refine ⟨X ×ˢ (Y ×ˢ Z), prod_mem_nhds hX (prod_mem_nhds hY hZ), ?_⟩
  intro p hp q' hq' hm
  change e i p.1 + e j p.2.1 + e k p.2.2 = e i q'.1 + e j q'.2.1 + e k q'.2.2
  rw [hfactor _ hp.1 _ hp.2.1 _ hp.2.2, hfactor _ hq'.1 _ hq'.2.1 _ hq'.2.2]
  apply congrArg H
  simpa [tripleStatistic, tripleSum, Prod.add_def, add_assoc] using hm

/-- Planar source-box charts with a merely continuous receiver. -/
def DensePlanarCharts {K : ℕ} (φ₁ φ₂ : Fin K → ℝ → ℝ)
    (E : Fin K → ℝ → Plane) (O : Fin K → Fin K → Fin K → Set Plane) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    ∀ x ∈ Ioo (-1 : ℝ) 1, ∀ y ∈ Ioo (-1 : ℝ) 1, ∀ z ∈ Ioo (-1 : ℝ) 1,
      deriv (φ₁ j) y * deriv (φ₂ k) z - deriv (φ₁ k) z * deriv (φ₂ j) y ≠ 0 →
      tripleStatistic (φ₁ i) (φ₁ j) (φ₁ k) (φ₂ i) (φ₂ j) (φ₂ k) (x, y, z) ∈ O i j k →
      ∃ X ∈ 𝓝 x, ∃ Y ∈ 𝓝 y, ∃ Z ∈ 𝓝 z,
      ∃ B ∈ 𝓝 (tripleStatistic (φ₁ i) (φ₁ j) (φ₁ k) (φ₂ i) (φ₂ j) (φ₂ k) (x, y, z)),
      ∃ H : Plane → Plane, ContinuousOn H B ∧
        ∀ x' ∈ X, ∀ y' ∈ Y, ∀ z' ∈ Z,
          E i x' + E j y' + E k z' =
            H ((φ₁ i x', φ₂ i x') + (φ₁ j y', φ₂ j y') + (φ₁ k z', φ₂ k z'))

/-- Heterogeneous planar affine representation from dense local charts.
The common feature vectors and separate offsets are constructed; regularity,
derivative identities, and independent reference inputs are all derived. -/
theorem planar_affine_of_dense_charts {K : ℕ} (hK : 4 ≤ K)
    (φ₁ φ₂ : Fin K → ℝ → ℝ) (E : Fin K → ℝ → Plane)
    (O : Fin K → Fin K → Fin K → Set Plane)
    (h₁ : ∀ i, ContinuousOn (φ₁ i) (Icc (-1 : ℝ) 1))
    (h₂ : ∀ i, ContinuousOn (φ₂ i) (Icc (-1 : ℝ) 1))
    (hE : ∀ i, ContinuousOn (E i) (Icc (-1 : ℝ) 1))
    (hC₁ : ∀ i, ContDiffOn ℝ 1 (φ₁ i) (Ioo (-1 : ℝ) 1))
    (hC₂ : ∀ i, ContDiffOn ℝ 1 (φ₂ i) (Ioo (-1 : ℝ) 1))
    (hind : ∀ i, GeneralRigidity.NotInAffineLine (Icc (-1 : ℝ) 1) (φ₁ i) (φ₂ i))
    (hdense : DenseIdentification φ₁ φ₂ O) (hcharts : DensePlanarCharts φ₁ φ₂ E O) :
    ∃ u v : Plane, ∃ c : Fin K → Plane, ∀ i x, x ∈ Icc (-1 : ℝ) 1 →
      E i x = c i + φ₁ i x • u + φ₂ i x • v := by
  have hfst : DenseScalarCharts φ₁ φ₂ (fun i x => (E i x).1) O := by
    intro i j k hij hik hjk x hx y hy z hz hd hp
    obtain ⟨X, hX, Y, hY, Z, hZ, B, hB, H, hH, hf⟩ :=
      hcharts i j k hij hik hjk x hx y hy z hz hd hp
    refine ⟨X, hX, Y, hY, Z, hZ, B, hB, fun p => (H p).1, hH.fst, ?_⟩
    intro x' hx' y' hy' z' hz'
    exact congrArg Prod.fst (hf x' hx' y' hy' z' hz')
  have hsnd : DenseScalarCharts φ₁ φ₂ (fun i x => (E i x).2) O := by
    intro i j k hij hik hjk x hx y hy z hz hd hp
    obtain ⟨X, hX, Y, hY, Z, hZ, B, hB, H, hH, hf⟩ :=
      hcharts i j k hij hik hjk x hx y hy z hz hd hp
    refine ⟨X, hX, Y, hY, Z, hZ, B, hB, fun p => (H p).2, hH.snd, ?_⟩
    intro x' hx' y' hy' z' hz'
    exact congrArg Prod.snd (hf x' hx' y' hy' z' hz')
  obtain ⟨ux, vx, cx, hx⟩ := scalar_affine_of_dense_charts hK φ₁ φ₂
    (fun i x => (E i x).1) O h₁ h₂ (fun i => (hE i).fst) hC₁ hC₂ hind hdense hfst
  obtain ⟨uy, vy, cy, hy⟩ := scalar_affine_of_dense_charts hK φ₁ φ₂
    (fun i x => (E i x).2) O h₁ h₂ (fun i => (hE i).snd) hC₁ hC₂ hind hdense hsnd
  refine ⟨(ux, uy), (vx, vy), (fun i => (cx i, cy i)), ?_⟩
  intro i x hxi
  apply Prod.ext
  · simpa [mul_comm] using hx i x hxi
  · simpa [mul_comm] using hy i x hxi

end Analog.HeterogeneousAnalyticRigidity
