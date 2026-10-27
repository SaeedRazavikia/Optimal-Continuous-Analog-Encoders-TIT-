import Analog.TwoStatisticDesign
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Actual operational score for node-dependent preprocessing

This module treats the current manuscript's finite `Fin K` source tuples,
node-dependent feature curves and node-dependent offsets.  The two encoder
columns are shared.  All score identities include singular coefficient
matrices and use the actual attainable image, without convexification.

The four column coordinates of `Planar` are reused; its two offset fields
are ignored here, since the offsets are provided separately as `c`.
This module does not prove SDP attainment, singular Gram reconstruction,
or the converse classification of arbitrary continuous encoders.
-/

noncomputable section

namespace Analog.HeterogeneousScore

open GramSynthesis ArbitraryEncoder
open scoped BigOperators

/-- Admissible node-indexed inputs, with no identification of distinct nodes. -/
def ValidInput (K : ℕ) : Set (Fin K → ℝ) :=
  {s | ∀ k, s k ∈ Set.Icc (-1 : ℝ) 1}

/-- Node-dependent preprocessing, normalized by the actual node count. -/
def meanStatistic {K : ℕ} (γ : Fin K → ℝ → ℝ × ℝ)
    (s : Fin K → ℝ) : ℝ × ℝ :=
  ((∑ k, (γ k (s k)).1) / (K : ℝ),
   (∑ k, (γ k (s k)).2) / (K : ℝ))

/-- The finite-node attainable set, not a convex hull or a closure. -/
def attainable {K : ℕ} (γ : Fin K → ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  meanStatistic γ '' ValidInput K

/-- Each node has its own offset and preprocessing, and the columns are shared. -/
def encoder {K : ℕ} (e : Planar) (c : Fin K → ℝ × ℝ)
    (γ : Fin K → ℝ → ℝ × ℝ) (k : Fin K) (s : ℝ) : ℝ × ℝ :=
  ((c k).1 + e.ux * (γ k s).1 + e.vx * (γ k s).2,
   (c k).2 + e.uy * (γ k s).1 + e.vy * (γ k s).2)

/-- The actual two-coordinate multiple-access sum. -/
def received {K : ℕ} (E : Fin K → ℝ → ℝ × ℝ)
    (s : Fin K → ℝ) : ℝ × ℝ :=
  (∑ k, (E k (s k)).1, ∑ k, (E k (s k)).2)

/-- Operational squared separation for arbitrary node-dependent encoders. -/
def score {K : ℕ} (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (E : Fin K → ℝ → ℝ × ℝ) : ℝ :=
  Operational.score (ValidInput K) (F ∘ meanStatistic γ)
    (fun s t => squaredDistance (received E s) (received E t))

/-- Exact computation means that every valid received collision preserves F. -/
def ExactComputation {K : ℕ} (γ : Fin K → ℝ → ℝ × ℝ)
    (F : ℝ × ℝ → ℝ) (E : Fin K → ℝ → ℝ × ℝ) : Prop :=
  ∀ s ∈ ValidInput K, ∀ t ∈ ValidInput K,
    received E s = received E t → F (meanStatistic γ s) = F (meanStatistic γ t)

theorem meanStatistic_mem_attainable {K : ℕ}
    (γ : Fin K → ℝ → ℝ × ℝ) {s : Fin K → ℝ} (hs : s ∈ ValidInput K) :
    meanStatistic γ s ∈ attainable γ :=
  ⟨s, hs, rfl⟩

/-- The separate offsets sum, while the common columns commute with summation. -/
theorem received_encoder {K : ℕ} (e : Planar) (c : Fin K → ℝ × ℝ)
    (γ : Fin K → ℝ → ℝ × ℝ) (s : Fin K → ℝ) :
    received (encoder e c γ) s =
      ((∑ k, (c k).1) + e.ux * (∑ k, (γ k (s k)).1) +
          e.vx * (∑ k, (γ k (s k)).2),
       (∑ k, (c k).2) + e.uy * (∑ k, (γ k (s k)).1) +
          e.vy * (∑ k, (γ k (s k)).2)) := by
  simp only [received, encoder, Finset.sum_add_distrib, Finset.mul_sum]

/-- The current manuscript's aggregate formula, including distinct offsets. -/
theorem received_encoder_mean {K : ℕ} (hK : 0 < K)
    (e : Planar) (c : Fin K → ℝ × ℝ)
    (γ : Fin K → ℝ → ℝ × ℝ) (s : Fin K → ℝ) :
    received (encoder e c γ) s =
      ((∑ k, (c k).1) + (K : ℝ) *
          (e.ux * (meanStatistic γ s).1 + e.vx * (meanStatistic γ s).2),
       (∑ k, (c k).2) + (K : ℝ) *
          (e.uy * (meanStatistic γ s).1 + e.vy * (meanStatistic γ s).2)) := by
  have hk0 : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  rw [received_encoder]
  apply Prod.ext <;> dsimp [meanStatistic] <;> field_simp <;> ring

/-- Node-specific offsets cancel in every received-distance comparison. -/
theorem received_squaredDistance {K : ℕ} (hK : 0 < K)
    (e : Planar) (c : Fin K → ℝ × ℝ)
    (γ : Fin K → ℝ → ℝ × ℝ) (s t : Fin K → ℝ) :
    squaredDistance (received (encoder e c γ) s) (received (encoder e c γ) t) =
      (K : ℝ) ^ 2 * TwoStatisticDesign.gramCost e
        (meanStatistic γ s) (meanStatistic γ t) := by
  rw [received_encoder_mean hK, received_encoder_mean hK]
  dsimp [squaredDistance, TwoStatisticDesign.gramCost, form2,
    Planar.A, Planar.B, Planar.C]
  ring

/-- An invertible common encoder matrix preserves both node-dependent means. -/
theorem collision_preserves_mean {K : ℕ} (e : Planar) (c : Fin K → ℝ × ℝ)
    (γ : Fin K → ℝ → ℝ × ℝ) (hdet : e.ux * e.vy - e.uy * e.vx ≠ 0)
    (s t : Fin K → ℝ)
    (hcollision : received (encoder e c γ) s = received (encoder e c γ) t) :
    meanStatistic γ s = meanStatistic γ t := by
  rw [received_encoder, received_encoder] at hcollision
  have h₁ := congrArg Prod.fst hcollision
  have h₂ := congrArg Prod.snd hcollision
  dsimp only at h₁ h₂
  let x := (∑ k, (γ k (s k)).1) - (∑ k, (γ k (t k)).1)
  let y := (∑ k, (γ k (s k)).2) - (∑ k, (γ k (t k)).2)
  have hfirst : e.ux * x + e.vx * y = 0 := by
    dsimp [x, y]
    linarith only [h₁]
  have hsecond : e.uy * x + e.vy * y = 0 := by
    dsimp [x, y]
    linarith only [h₂]
  have hdx : (e.ux * e.vy - e.uy * e.vx) * x = 0 := by
    calc
      _ = e.vy * (e.ux * x + e.vx * y) - e.vx * (e.uy * x + e.vy * y) := by ring
      _ = 0 := by rw [hfirst, hsecond]; ring
  have hdy : (e.ux * e.vy - e.uy * e.vx) * y = 0 := by
    calc
      _ = e.ux * (e.uy * x + e.vy * y) - e.uy * (e.ux * x + e.vx * y) := by ring
      _ = 0 := by rw [hfirst, hsecond]; ring
  have hx0 := (mul_eq_zero.mp hdx).resolve_left hdet
  have hy0 := (mul_eq_zero.mp hdy).resolve_left hdet
  have hxsum : (∑ k, (γ k (s k)).1) = (∑ k, (γ k (t k)).1) := sub_eq_zero.mp hx0
  have hysum : (∑ k, (γ k (s k)).2) = (∑ k, (γ k (t k)).2) := sub_eq_zero.mp hy0
  apply Prod.ext <;> simp only [meanStatistic, hxsum, hysum]

/-- The sufficient direction of current heterogeneous encoding: no condition
on the readout beyond being a function of the two means is required. -/
theorem exact_computation_of_det {K : ℕ} (e : Planar) (c : Fin K → ℝ × ℝ)
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (hdet : e.ux * e.vy - e.uy * e.vx ≠ 0) :
    ExactComputation γ F (encoder e c γ) := by
  intro s _ t _ hcollision
  exact congrArg F (collision_preserves_mean e c γ hdet s t hcollision)

/-- Continuity of every local feature curve gives continuity of every encoder. -/
theorem encoder_continuousOn {K : ℕ} (e : Planar) (c : Fin K → ℝ × ℝ)
    (γ : Fin K → ℝ → ℝ × ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Set.Icc (-1 : ℝ) 1)) (k : Fin K) :
    ContinuousOn (encoder e c γ k) (Set.Icc (-1 : ℝ) 1) := by
  unfold encoder
  fun_prop

/-- Exact operational-to-Gram equality for heterogeneous nodes, including
singular common coefficient matrices and arbitrary postprocessing F. -/
theorem affine_operational_score {K : ℕ} (hK : 0 < K)
    (e : Planar) (c : Fin K → ℝ × ℝ)
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (hn : Operational.NonconstantOn (attainable γ) F) :
    score γ F (encoder e c γ) =
      (K : ℝ) ^ 2 * Operational.score (attainable γ) F
        (TwoStatisticDesign.gramCost e) := by
  unfold score
  calc
    _ = Operational.score (ValidInput K) (F ∘ meanStatistic γ)
        (fun s t => (K : ℝ) ^ 2 * TwoStatisticDesign.gramCost e
          (meanStatistic γ s) (meanStatistic γ t)) := by
      apply Operational.score_cost_congr_on
      intro s _ t _
      exact received_squaredDistance hK e c γ s t
    _ = _ := Operational.score_stat_image_user_count hn
      (fun μ _ ν _ => TwoStatisticDesign.gramCost_nonnegative e μ ν) hK

/-- The current program's attained-pair constraints are exactly score bounds. -/
theorem affine_score_bound_iff {K : ℕ} (hK : 0 < K)
    (e : Planar) (c : Fin K → ℝ × ℝ)
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (hn : Operational.NonconstantOn (attainable γ) F) (lam : ℝ) :
    (K : ℝ) ^ 2 * lam ≤ score γ F (encoder e c γ) ↔
      ∀ μ ∈ attainable γ, ∀ ν ∈ attainable γ,
        lam * (F μ - F ν) ^ 2 ≤ TwoStatisticDesign.gramCost e μ ν := by
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  rw [affine_operational_score hK e c γ F hn,
    mul_le_mul_iff_right₀ (sq_pos_of_pos hk)]
  exact Operational.le_score_iff hn
    (fun μ _ ν _ => TwoStatisticDesign.gramCost_nonnegative e μ ν) lam

/-- Positive actual score forces exact computation even before any affine
representation or invertibility of the common columns is assumed. -/
theorem positive_score_implies_exact {K : ℕ}
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (E : Fin K → ℝ → ℝ × ℝ)
    (hn : Operational.NonconstantOn (attainable γ) F)
    (hpos : 0 < score γ F E) : ExactComputation γ F E := by
  have hninput : Operational.NonconstantOn (ValidInput K) (F ∘ meanStatistic γ) :=
    (Operational.nonconstantOn_stat_image_iff (ValidInput K) (meanStatistic γ) F).mpr hn
  have hb := Operational.score_is_lowerBound hninput
    (fun s _ t _ => squaredDistance_nonnegative (received E s) (received E t))
  intro s hs t ht hcollision
  have hp := hb s hs t ht
  change score γ F E * (F (meanStatistic γ s) - F (meanStatistic γ t)) ^ 2 ≤ _ at hp
  simp only [hcollision, squaredDistance, sub_self,
    zero_pow (by decide : 2 ≠ 0), add_zero] at hp
  have hsquare : (F (meanStatistic γ s) - F (meanStatistic γ t)) ^ 2 ≤ 0 := by
    exact (mul_le_mul_iff_right₀ hpos).mp (by simpa only [mul_zero] using hp)
  nlinarith [sq_nonneg (F (meanStatistic γ s) - F (meanStatistic γ t))]

end Analog.HeterogeneousScore
