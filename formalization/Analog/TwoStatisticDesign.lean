import Analog.AdditiveStatistics
import Analog.AttainableScore

/-!
# Planar reconstruction for two arbitrary prescribed additive statistics

The source curve is γ(s) = (φ₁(s), φ₂(s)); neither coordinate is required
to be the identity. The positive definiteness of the lower Gram block is
an explicit hypothesis. Deriving it from common-completion identification,
and proving optimum attainment over all continuous encoders, are separate
obligations of the manuscript's unified extension.
-/

noncomputable section

namespace Analog.TwoStatisticDesign

open GramSynthesis ArbitraryEncoder AdditiveStatistics

/-- The actual squared-separation infimum for an arbitrary encoder. -/
def score (K : ℕ) (γ : ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (E : ℝ → ℝ × ℝ) : ℝ :=
  Operational.score {xs | ValidInput K xs} (desiredFunction K γ F)
    (fun xs ys => squaredDistance (received E xs) (received E ys))

/-- The lower Gram cost between two prescribed empirical statistics. -/
def gramCost (e : Planar) (μ ν : ℝ × ℝ) : ℝ :=
  form2 e.A e.B e.C (μ.1 - ν.1) (μ.2 - ν.2)

/-- A positive actual score forces exact computation for an arbitrary
encoder of the prescribed desired function. -/
theorem positive_score_implies_exact (K : ℕ) (γ : ℝ → ℝ × ℝ)
    (F : ℝ × ℝ → ℝ) (E : ℝ → ℝ × ℝ)
    (hn : Operational.NonconstantOn (attainable K γ) F)
    (hpos : 0 < score K γ F E) : ExactComputation K γ F E := by
  have hninput : Operational.NonconstantOn {xs | ValidInput K xs}
      (desiredFunction K γ F) :=
    (Operational.nonconstantOn_stat_image_iff {xs | ValidInput K xs}
      (meanStatistic K γ) F).mpr hn
  have hb := Operational.score_is_lowerBound hninput
    (fun xs _ ys _ => squaredDistance_nonnegative (received E xs) (received E ys))
  intro xs ys hxs hys hcollision
  have hp := hb xs hxs ys hys
  change score K γ F E * (desiredFunction K γ F xs - desiredFunction K γ F ys) ^ 2 ≤ _ at hp
  simp only [hcollision, squaredDistance, sub_self,
    zero_pow (by decide : 2 ≠ 0), add_zero] at hp
  have hs : (desiredFunction K γ F xs - desiredFunction K γ F ys) ^ 2 ≤ 0 := by
    exact (mul_le_mul_iff_right₀ hpos).mp (by simpa only [mul_zero] using hp)
  nlinarith [sq_nonneg (desiredFunction K γ F xs - desiredFunction K γ F ys)]

lemma gramCost_nonnegative (e : Planar) (μ ν : ℝ × ℝ) :
    0 ≤ gramCost e μ ν := by
  have he : gramCost e μ ν =
      (e.ux * (μ.1 - ν.1) + e.vx * (μ.2 - ν.2)) ^ 2 +
      (e.uy * (μ.1 - ν.1) + e.vy * (μ.2 - ν.2)) ^ 2 := by
    dsimp [gramCost, form2, Planar.A, Planar.B, Planar.C]
    ring
  rw [he]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The received-pair score is exactly K² times the attained-statistic Gram
score. This remains true for degenerate coefficient matrices. -/
theorem affine_operational_score (e : Planar) {K : ℕ} (hK : 0 < K)
    (γ : ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (hn : Operational.NonconstantOn (attainable K γ) F) :
    score K γ F (encoder e γ) =
      (K : ℝ) ^ 2 * Operational.score (attainable K γ) F (gramCost e) := by
  unfold score
  calc
    _ = Operational.score {xs | ValidInput K xs} (desiredFunction K γ F)
        (fun xs ys => (K : ℝ) ^ 2 *
          gramCost e (meanStatistic K γ xs) (meanStatistic K γ ys)) := by
      apply Operational.score_cost_congr_on
      intro xs hxs ys hys
      exact received_squaredDistance e hK γ xs ys hxs hys
    _ = _ := Operational.score_stat_image_user_count hn
      (fun μ _ ν _ => gramCost_nonnegative e μ ν) hK

/-- Exact pair constraints for the operational threshold, on the actual
finite-K image of valid input configurations. -/
theorem affine_score_bound_iff (e : Planar) {K : ℕ} (hK : 0 < K)
    (γ : ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (hn : Operational.NonconstantOn (attainable K γ) F) (lam : ℝ) :
    (K : ℝ) ^ 2 * lam ≤ score K γ F (encoder e γ) ↔
      ∀ μ ∈ attainable K γ, ∀ ν ∈ attainable K γ,
        lam * (F μ - F ν) ^ 2 ≤ gramCost e μ ν := by
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  rw [affine_operational_score e hK γ F hn,
    mul_le_mul_iff_right₀ (sq_pos_of_pos hk)]
  exact Operational.le_score_iff hn
    (fun μ _ ν _ => gramCost_nonnegative e μ ν) lam

/-- Schur reduction and planar realization preserve every pointwise power
constraint for an arbitrary prescribed planar preprocessing curve. -/
theorem planar_synthesis (γ : ℝ → ℝ × ℝ) (h l₁ l₂ A B C P : ℝ)
    (hA : 0 < A) (hD : 0 < det A B C) (hpsd : PSD3 h l₁ l₂ A B C)
    (hpeak : ∀ s ∈ Set.Icc (-1 : ℝ) 1,
      form3 h l₁ l₂ A B C 1 (γ s).1 (γ s).2 ≤ P) :
    ∀ s ∈ Set.Icc (-1 : ℝ) 1,
      (reconstruct A B C l₁ l₂).energy 1 (γ s).1 (γ s).2 ≤ P := by
  have hg := reconstruct_gram A B C l₁ l₂ hA hD
  intro s hs
  rw [Planar.energy_eq_form3, hg.1, hg.2.1, hg.2.2.1,
    hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2]
  exact ((schur_reduction h l₁ l₂ A B C hA hD hpsd).2
    1 (γ s).1 (γ s).2).trans (hpeak s hs)

/-- The same reconstruction retains every desired-function pair constraint
on the actual attainable set supplied as M. -/
theorem reconstruction_preserves_pairs (M : Set (ℝ × ℝ)) (F : ℝ × ℝ → ℝ)
    (A B C l₁ l₂ lam : ℝ) (hA : 0 < A) (hD : 0 < det A B C)
    (hpairs : ∀ μ ∈ M, ∀ ν ∈ M,
      lam * (F μ - F ν) ^ 2 ≤ form2 A B C (μ.1 - ν.1) (μ.2 - ν.2)) :
    ∀ μ ∈ M, ∀ ν ∈ M,
      lam * (F μ - F ν) ^ 2 ≤
        form2 (reconstruct A B C l₁ l₂).A
          (reconstruct A B C l₁ l₂).B (reconstruct A B C l₁ l₂).C
          (μ.1 - ν.1) (μ.2 - ν.2) := by
  have hg := reconstruct_lower_gram A B C l₁ l₂ hA hD
  simpa only [hg.1, hg.2.1, hg.2.2] using hpairs

/-- A feasible design with an explicitly positive-definite lower Gram block
produces a continuous exact encoder with every peak bound and the actual
operational separation guarantee. This is the constructive coefficient-class
part of the extension, not its continuous-encoder converse or attainment. -/
theorem positive_definite_operational_synthesis {K : ℕ} (hK : 0 < K)
    (γ : ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (hγ : ContinuousOn γ (Set.Icc (-1 : ℝ) 1))
    (hn : Operational.NonconstantOn (attainable K γ) F)
    (h l₁ l₂ A B C P lam : ℝ)
    (hA : 0 < A) (hD : 0 < det A B C) (hpsd : PSD3 h l₁ l₂ A B C)
    (hpeak : ∀ s ∈ Set.Icc (-1 : ℝ) 1,
      form3 h l₁ l₂ A B C 1 (γ s).1 (γ s).2 ≤ P)
    (hpairs : ∀ μ ∈ attainable K γ, ∀ ν ∈ attainable K γ,
      lam * (F μ - F ν) ^ 2 ≤ form2 A B C (μ.1 - ν.1) (μ.2 - ν.2)) :
    ∃ e : Planar, e.A = A ∧ e.B = B ∧ e.C = C ∧
      ContinuousOn (encoder e γ) (Set.Icc (-1 : ℝ) 1) ∧
      ExactComputation K γ F (encoder e γ) ∧
      (∀ s ∈ Set.Icc (-1 : ℝ) 1, squaredDistance (encoder e γ s) 0 ≤ P) ∧
      (K : ℝ) ^ 2 * lam ≤ score K γ F (encoder e γ) := by
  let e := reconstruct A B C l₁ l₂
  have hg := reconstruct_lower_gram A B C l₁ l₂ hA hD
  have heD : 0 < det e.A e.B e.C := by
    simpa only [e, hg.1, hg.2.1, hg.2.2] using hD
  refine ⟨e, hg.1, hg.2.1, hg.2.2, encoder_continuousOn e γ hγ,
    exact_computation_of_gram e K γ F heD, ?_, ?_⟩
  · intro s hs
    rw [encoder_energy]
    exact planar_synthesis γ h l₁ l₂ A B C P hA hD hpsd hpeak s hs
  · apply (affine_score_bound_iff e hK γ F hn lam).mpr
    exact reconstruction_preserves_pairs (attainable K γ) F
      A B C l₁ l₂ lam hA hD hpairs

end Analog.TwoStatisticDesign
