import Analog.HeterogeneousCompletion

/-! # Strict interior moment ranges and actual completion-domain bounds -/

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Analog.HeterogeneousMomentRanges

/-- An interior input with nonzero derivative cannot attain either endpoint
of any valid scalar range bound. No differentiability premise is needed. -/
theorem strict_range_of_deriv_ne_zero (φ : ℝ → ℝ) {lo hi y : ℝ}
    (hbound : ∀ s ∈ Icc (-1 : ℝ) 1, φ s ∈ Icc lo hi)
    (hy : y ∈ Ioo (-1 : ℝ) 1) (hd : deriv φ y ≠ 0) :
    φ y ∈ Ioo lo hi := by
  have hy' := Ioo_subset_Icc_self hy
  constructor
  · apply lt_of_le_of_ne (hbound y hy').1
    intro heq
    have hmin : IsMinOn φ (Icc (-1 : ℝ) 1) y := by
      intro s hs
      rw [← heq]
      exact (hbound s hs).1
    exact hd (hmin.isLocalMin (Icc_mem_nhds hy.1 hy.2)).deriv_eq_zero
  · apply lt_of_le_of_ne (hbound y hy').2
    intro heq
    have hmax : IsMaxOn φ (Icc (-1 : ℝ) 1) y := by
      intro s hs
      rw [heq]
      exact (hbound s hs).2
    exact hd (hmax.isLocalMax (Icc_mem_nhds hy.1 hy.2)).deriv_eq_zero

/-- One nonzero derivative in the last two inputs makes the scalar triple
sum strictly interior to the sum of the three scalar range intervals. -/
theorem triple_sum_strict {κ : Type*} (φ : κ → ℝ → ℝ) (lo hi : κ → ℝ)
    (hbound : ∀ i s, s ∈ Icc (-1 : ℝ) 1 → φ i s ∈ Icc (lo i) (hi i))
    (i j k : κ) {x y z : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1)
    (hz : z ∈ Ioo (-1 : ℝ) 1)
    (hd : deriv (φ j) y ≠ 0 ∨ deriv (φ k) z ≠ 0) :
    φ i x + φ j y + φ k z ∈ Ioo (lo i + lo j + lo k) (hi i + hi j + hi k) := by
  have hix := hbound i x (Ioo_subset_Icc_self hx)
  have hjy := hbound j y (Ioo_subset_Icc_self hy)
  have hkz := hbound k z (Ioo_subset_Icc_self hz)
  rcases hd with hd | hd
  · have hs := strict_range_of_deriv_ne_zero (φ j) (hbound j) hy hd
    constructor <;> linarith [hs.1, hs.2, hix.1, hix.2, hkz.1, hkz.2]
  · have hs := strict_range_of_deriv_ne_zero (φ k) (hbound k) hz hd
    constructor <;> linarith [hs.1, hs.2, hix.1, hix.2, hjy.1, hjy.2]

/-- A regular last pair makes both partial moment coordinates strictly
interior to their exact sum-range rectangle. -/
theorem regular_triple_sum_strict {κ : Type*}
    (φ₁ φ₂ : κ → ℝ → ℝ) (lo₁ hi₁ lo₂ hi₂ : κ → ℝ)
    (hb₁ : ∀ i s, s ∈ Icc (-1 : ℝ) 1 → φ₁ i s ∈ Icc (lo₁ i) (hi₁ i))
    (hb₂ : ∀ i s, s ∈ Icc (-1 : ℝ) 1 → φ₂ i s ∈ Icc (lo₂ i) (hi₂ i))
    (i j k : κ) {x y z : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1)
    (hz : z ∈ Ioo (-1 : ℝ) 1)
    (hdet : deriv (φ₁ j) y * deriv (φ₂ k) z - deriv (φ₁ k) z * deriv (φ₂ j) y ≠ 0) :
    φ₁ i x + φ₁ j y + φ₁ k z ∈ Ioo (lo₁ i + lo₁ j + lo₁ k) (hi₁ i + hi₁ j + hi₁ k) ∧
    φ₂ i x + φ₂ j y + φ₂ k z ∈ Ioo (lo₂ i + lo₂ j + lo₂ k) (hi₂ i + hi₂ j + hi₂ k) := by
  constructor
  · apply triple_sum_strict φ₁ lo₁ hi₁ hb₁ i j k hx hy hz
    by_contra hh
    simp only [not_or, not_not] at hh
    exact hdet (by simp [hh.1, hh.2])
  · apply triple_sum_strict φ₂ lo₂ hi₂ hb₂ i j k hx hy hz
    by_contra hh
    simp only [not_or, not_not] at hh
    exact hdet (by simp [hh.1, hh.2])

/-- The background consists of exactly the nodes outside the four distinct
selected nodes. Its endpoint bounds follow from the actual full finite sum. -/
theorem background_bounds {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v lo hi : κ → ℝ) (hv : ∀ n, v n ∈ Icc (lo n) (hi n))
    (i j k l : κ) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (∑ n, lo n) ≤ lo i + lo j + lo k +
      ((∑ n, v n) - v i - v j - v k - v l) + lo l ∧
    hi i + hi j + hi k + ((∑ n, v n) - v i - v j - v k - v l) + hi l ≤
      (∑ n, hi n) := by
  let S : Finset κ := {i, j, k, l}
  have hsum (w : κ → ℝ) :
      (∑ n, w n) = w i + w j + w k + w l + ∑ n ∈ Finset.univ \ S, w n := by
    have hh := Finset.sum_sdiff (f := w) (Finset.subset_univ S)
    have hs : ∑ n ∈ S, w n = w i + w j + w k + w l := by
      simp [S, hij, hik, hil, hjk, hjl, hkl, add_assoc]
    rw [hs] at hh
    linarith
  have hlo : (∑ n ∈ Finset.univ \ S, lo n) ≤ ∑ n ∈ Finset.univ \ S, v n :=
    Finset.sum_le_sum (fun n _ => (hv n).1)
  have hhi : (∑ n ∈ Finset.univ \ S, v n) ≤ ∑ n ∈ Finset.univ \ S, hi n :=
    Finset.sum_le_sum (fun n _ => (hv n).2)
  rw [hsum lo, hsum v, hsum hi]
  constructor <;> linarith

/-- Bounds for the completed interval imply containment in the full
normalized receiver domain, preserving strict endpoints. -/
theorem normalized_completion_interval_subset {K a b β c d A B : ℝ}
    (hK : 0 < K) (hlo : A ≤ a + β + c) (hhi : b + β + d ≤ B) :
    Ioo ((a + β) / K + c / K) ((b + β) / K + d / K) ⊆ Ioo (A / K) (B / K) := by
  intro t ht
  constructor
  · have hh : A / K ≤ (a + β) / K + c / K := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hlo hK.le
    exact hh.trans_lt ht.1
  · have hh : (b + β) / K + d / K ≤ B / K := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hhi hK.le
    exact ht.2.trans_le hh

end Analog.HeterogeneousMomentRanges
