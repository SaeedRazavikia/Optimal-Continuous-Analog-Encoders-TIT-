import Analog.VarianceCollision
import Analog.GramSynthesis
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.FunProp

/-!
# Encoders for two arbitrary prescribed additive statistics

The observations and desired function are real-valued. A pair of preprocessing
functions is represented by `γ : ℝ → ℝ × ℝ`; its empirical mean is taken over
actual source lists of length `K`. The attainable set below is the image of
those lists, not the convex hull of the preprocessing curve.

This module checks the affine-encoder direction of the general extension:
the received-sum identity, its exact squared-distance normalization, exact
computation for every postprocessing function when the coefficient matrix is
invertible, and continuity. It makes no converse rigidity claim.
-/

noncomputable section

open Set
namespace Analog.AdditiveStatistics
open ArbitraryEncoder GramSynthesis

/-- The two unnormalized prescribed additive statistics. -/
def statisticSum (γ : ℝ → ℝ × ℝ) (xs : List ℝ) : ℝ × ℝ :=
  (xs.map γ).sum

/-- The empirical average of the two prescribed preprocessing functions. -/
def meanStatistic (K : ℕ) (γ : ℝ → ℝ × ℝ) (xs : List ℝ) : ℝ × ℝ :=
  ((statisticSum γ xs).1 / (K : ℝ), (statisticSum γ xs).2 / (K : ℝ))

/-- The exact finite-`K` attainable statistic set. -/
def attainable (K : ℕ) (γ : ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  meanStatistic K γ '' {xs | ValidInput K xs}

/-- The real-valued desired function of the prescribed empirical statistics. -/
def desiredFunction (K : ℕ) (γ : ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (xs : List ℝ) : ℝ :=
  F (meanStatistic K γ xs)

/-- A planar affine image of the prescribed preprocessing curve. -/
def encoder (e : Planar) (γ : ℝ → ℝ × ℝ) (s : ℝ) : ℝ × ℝ :=
  (e.cx + e.ux * (γ s).1 + e.vx * (γ s).2,
   e.cy + e.uy * (γ s).1 + e.vy * (γ s).2)

/-- Exact computation on every valid pair of real source tuples. -/
def ExactComputation (K : ℕ) (γ : ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (E : ℝ → ℝ × ℝ) : Prop :=
  ∀ xs ys : List ℝ, ValidInput K xs → ValidInput K ys →
    received E xs = received E ys →
      desiredFunction K γ F xs = desiredFunction K γ F ys

lemma encoder_energy (e : Planar) (γ : ℝ → ℝ × ℝ) (s : ℝ) :
    squaredDistance (encoder e γ s) 0 = e.energy 1 (γ s).1 (γ s).2 := by
  dsimp [squaredDistance, encoder, Planar.energy]
  ring

lemma meanStatistic_mem_attainable {K : ℕ} (γ : ℝ → ℝ × ℝ)
    (xs : List ℝ) (hx : ValidInput K xs) :
    meanStatistic K γ xs ∈ attainable K γ :=
  ⟨xs, hx, rfl⟩

lemma received_encoder (e : Planar) (γ : ℝ → ℝ × ℝ) (xs : List ℝ) :
    received (encoder e γ) xs =
      ((xs.length : ℝ) * e.cx + e.ux * (statisticSum γ xs).1 +
          e.vx * (statisticSum γ xs).2,
       (xs.length : ℝ) * e.cy + e.uy * (statisticSum γ xs).1 +
          e.vy * (statisticSum γ xs).2) := by
  induction xs with
  | nil => simp [received, statisticSum]; rfl
  | cons x xs ih =>
    simp only [received, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    apply Prod.ext <;>
      simp [encoder, statisticSum, Nat.cast_add, Nat.cast_one] <;> ring

/-- The noiseless multiple-access sum is `K` times the affine empirical
statistic, with the same translation at every valid input tuple. -/
theorem received_encoder_mean (e : Planar) {K : ℕ} (hK : 0 < K)
    (γ : ℝ → ℝ × ℝ) (xs : List ℝ) (hx : ValidInput K xs) :
    received (encoder e γ) xs =
      ((K : ℝ) * (e.cx + e.ux * (meanStatistic K γ xs).1 +
          e.vx * (meanStatistic K γ xs).2),
       (K : ℝ) * (e.cy + e.uy * (meanStatistic K γ xs).1 +
          e.vy * (meanStatistic K γ xs).2)) := by
  have hk0 : (K : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
  rw [received_encoder, hx.1]
  apply Prod.ext <;> dsimp [meanStatistic] <;> field_simp

/-- Received squared distance equals `K²` times the lower Gram form of the
difference of actual attainable empirical statistics. -/
theorem received_squaredDistance (e : Planar) {K : ℕ} (hK : 0 < K)
    (γ : ℝ → ℝ × ℝ) (xs ys : List ℝ)
    (hx : ValidInput K xs) (hy : ValidInput K ys) :
    squaredDistance (received (encoder e γ) xs) (received (encoder e γ) ys) =
      (K : ℝ) ^ 2 * form2 e.A e.B e.C
        ((meanStatistic K γ xs).1 - (meanStatistic K γ ys).1)
        ((meanStatistic K γ xs).2 - (meanStatistic K γ ys).2) := by
  rw [received_encoder_mean e hK γ xs hx, received_encoder_mean e hK γ ys hy]
  dsimp [squaredDistance, form2, Planar.A, Planar.B, Planar.C]
  ring

/-- An invertible coefficient matrix preserves both empirical statistics at
every collision of the received sums. -/
theorem collision_preserves_mean (e : Planar) {K : ℕ}
    (γ : ℝ → ℝ × ℝ) (hdet : e.ux * e.vy - e.uy * e.vx ≠ 0)
    (xs ys : List ℝ) (hx : ValidInput K xs) (hy : ValidInput K ys)
    (hcollision : received (encoder e γ) xs = received (encoder e γ) ys) :
    meanStatistic K γ xs = meanStatistic K γ ys := by
  rw [received_encoder, received_encoder, hx.1, hy.1] at hcollision
  have h₁ := congrArg Prod.fst hcollision
  have h₂ := congrArg Prod.snd hcollision
  dsimp only at h₁ h₂
  let x := (statisticSum γ xs).1 - (statisticSum γ ys).1
  let y := (statisticSum γ xs).2 - (statisticSum γ ys).2
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
  have hxs : (statisticSum γ xs).1 = (statisticSum γ ys).1 := sub_eq_zero.mp hx0
  have hys : (statisticSum γ xs).2 = (statisticSum γ ys).2 := sub_eq_zero.mp hy0
  apply Prod.ext <;> simp only [meanStatistic, hxs, hys]

/-- Every real-valued postprocessing function can be computed exactly from an
invertible affine embedding of its two prescribed statistics. -/
theorem exact_computation_of_det (e : Planar) (K : ℕ)
    (γ : ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (hdet : e.ux * e.vy - e.uy * e.vx ≠ 0) :
    ExactComputation K γ F (encoder e γ) := by
  intro xs ys hx hy hcollision
  exact congrArg F (collision_preserves_mean e γ hdet xs ys hx hy hcollision)

lemma coefficient_gram_det (e : Planar) :
    det e.A e.B e.C = (e.ux * e.vy - e.uy * e.vx) ^ 2 := by
  dsimp [det, Planar.A, Planar.B, Planar.C]
  ring

theorem exact_computation_of_gram (e : Planar) (K : ℕ)
    (γ : ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ) (hD : 0 < det e.A e.B e.C) :
    ExactComputation K γ F (encoder e γ) := by
  apply exact_computation_of_det e K γ F
  intro hzero
  rw [coefficient_gram_det, hzero] at hD
  norm_num at hD

theorem encoder_continuousOn (e : Planar) (γ : ℝ → ℝ × ℝ)
    (hγ : ContinuousOn γ (Icc (-1 : ℝ) 1)) :
    ContinuousOn (encoder e γ) (Icc (-1 : ℝ) 1) := by
  unfold encoder
  fun_prop

end Analog.AdditiveStatistics
