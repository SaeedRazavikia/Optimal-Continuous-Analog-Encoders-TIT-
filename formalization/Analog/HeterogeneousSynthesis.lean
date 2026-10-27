import Analog.HeterogeneousScore
import Analog.SingularGram

/-!
# Operational synthesis for heterogeneous nodes at every Gram rank

A feasible family of full PSD Gram forms with a common lower block yields
actual continuous node-indexed encoders, retaining all continuum peak bounds
and the actual finite-node operational score. The construction includes
singular Gram matrices and zero separation. This is the constructive SDP
bridge, not a compactness or optimizer-attainment theorem.
-/

noncomputable section
namespace Analog.HeterogeneousSynthesis
open GramSynthesis SingularGram HeterogeneousScore ArbitraryEncoder

/-- Each node retains its own translation after common-column reconstruction. -/
def reconstructedOffsets {K : ℕ} (A B C : ℝ) (l₁ l₂ : Fin K → ℝ) :
    Fin K → ℝ × ℝ := fun k =>
  ((reconstructPSD A B C (l₁ k) (l₂ k)).cx,
   (reconstructPSD A B C (l₁ k) (l₂ k)).cy)

/-- The actual complex-plane energy equals the corresponding reduced Gram form. -/
theorem reconstructed_encoder_energy {K : ℕ} (A B C q₁ q₂ : ℝ)
    (l₁ l₂ : Fin K → ℝ) (γ : Fin K → ℝ → ℝ × ℝ) (k : Fin K) (s : ℝ) :
    squaredDistance (encoder (reconstructPSD A B C q₁ q₂)
      (reconstructedOffsets A B C l₁ l₂) γ k s) 0 =
    (reconstructPSD A B C (l₁ k) (l₂ k)).energy 1 (γ k s).1 (γ k s).2 := by
  obtain ⟨hux, huy, hvx, hvy⟩ :=
    reconstructPSD_common_columns A B C q₁ q₂ (l₁ k) (l₂ k)
  dsimp [encoder, squaredDistance, reconstructedOffsets, Planar.energy]
  rw [hux, huy, hvx, hvy]
  ring

/-- Every feasible heterogeneous-node SDP point has an operational realization,
even when its common lower block is singular and the separation level is zero.
Exact computation follows when the separation level is positive. -/
theorem feasible_operational_synthesis {K : ℕ} (hK : 0 < K)
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Set.Icc (-1 : ℝ) 1))
    (hn : Operational.NonconstantOn (attainable γ) F)
    (h l₁ l₂ : Fin K → ℝ) (A B C P lam : ℝ)
    (hpsd : ∀ k, PSD3 (h k) (l₁ k) (l₂ k) A B C)
    (hpeak : ∀ k s, s ∈ Set.Icc (-1 : ℝ) 1 →
      form3 (h k) (l₁ k) (l₂ k) A B C 1 (γ k s).1 (γ k s).2 ≤ P)
    (hpairs : ∀ μ ∈ attainable γ, ∀ ν ∈ attainable γ,
      lam * (F μ - F ν) ^ 2 ≤ form2 A B C (μ.1 - ν.1) (μ.2 - ν.2)) :
    ∃ (e : Planar) (c : Fin K → ℝ × ℝ),
      e.A = A ∧ e.B = B ∧ e.C = C ∧
      (∀ k, ContinuousOn (encoder e c γ k) (Set.Icc (-1 : ℝ) 1)) ∧
      (∀ k s, s ∈ Set.Icc (-1 : ℝ) 1 → squaredDistance (encoder e c γ k s) 0 ≤ P) ∧
      (K : ℝ) ^ 2 * lam ≤ score γ F (encoder e c γ) ∧
      (0 < lam → ExactComputation γ F (encoder e c γ)) := by
  have hzero : PSD3 0 0 0 A B C := by
    intro t x y
    simpa [form3] using hpsd ⟨0, hK⟩ 0 x y
  let e := reconstructPSD A B C 0 0
  let c := reconstructedOffsets A B C l₁ l₂
  obtain ⟨_, _, _, hA, hB, hC⟩ := reconstructPSD_gram hzero
  have hscore : (K : ℝ) ^ 2 * lam ≤ score γ F (encoder e c γ) := by
    apply (affine_score_bound_iff hK e c γ F hn lam).mpr
    intro μ hμ ν hν
    have hp := hpairs μ hμ ν hν
    simpa only [TwoStatisticDesign.gramCost, e, hA, hB, hC] using hp
  refine ⟨e, c, hA, hB, hC, encoder_continuousOn e c γ hγ, ?_, hscore, ?_⟩
  · intro k s hs
    rw [reconstructed_encoder_energy]
    exact (reconstructPSD_energy_le (hpsd k) 1 (γ k s).1 (γ k s).2).trans
      (hpeak k s hs)
  · intro hlam
    apply positive_score_implies_exact γ F (encoder e c γ) hn
    have hk : 0 < (K : ℝ) := by exact_mod_cast hK
    exact lt_of_lt_of_le (mul_pos (sq_pos_of_pos hk) hlam) hscore

end Analog.HeterogeneousSynthesis
