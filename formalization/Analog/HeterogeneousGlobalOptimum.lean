import Analog.HeterogeneousFullRigidity
import Analog.HeterogeneousAttainment
import Analog.HeterogeneousGridFeasible

/-!
# The attained SDP optimum over all continuous peak-feasible encoders

Positive robustness implies exact computation. The proved full heterogeneous
rigidity theorem therefore transfers the coefficient-class optimum to every
continuous peak-feasible encoder, including encoders of zero robustness.
-/

noncomputable section
namespace Analog.HeterogeneousGlobalOptimum
open Set GramSynthesis HeterogeneousScore HeterogeneousAttainment
open HeterogeneousFullRigidity HeterogeneousRegularity
open ArbitraryEncoder (squaredDistance)
open scoped BigOperators

/-- Agreement on physical source intervals gives agreement of the actual
finite received sums. -/
theorem received_eq_of_source_eq {K : ℕ} (E E' : Fin K → ℝ → Plane)
    (heq : ∀ i x, x ∈ Icc (-1 : ℝ) 1 → E i x = E' i x)
    {s : Fin K → ℝ} (hs : s ∈ ValidInput K) : received E s = received E' s := by
  apply Prod.ext <;> simp only [received]
  · exact Finset.sum_congr rfl (fun i _ => congrArg Prod.fst (heq i (s i) (hs i)))
  · exact Finset.sum_congr rfl (fun i _ => congrArg Prod.snd (heq i (s i) (hs i)))

/-- The actual operational score only depends on encoder values on the
physical source intervals, including both endpoints. -/
theorem score_eq_of_source_eq {K : ℕ} (γ E E' : Fin K → ℝ → Plane) (F : Plane → ℝ)
    (heq : ∀ i x, x ∈ Icc (-1 : ℝ) 1 → E i x = E' i x) :
    score γ F E = score γ F E' := by
  unfold score Operational.score
  apply congrArg sInf
  ext q
  constructor
  · rintro ⟨s, hs, t, ht, hne, hq⟩
    refine ⟨s, hs, t, ht, hne, ?_⟩
    simpa only [received_eq_of_source_eq E E' heq hs,
      received_eq_of_source_eq E E' heq ht] using hq
  · rintro ⟨s, hs, t, ht, hne, hq⟩
    refine ⟨s, hs, t, ht, hne, ?_⟩
    simpa only [received_eq_of_source_eq E E' heq hs,
      received_eq_of_source_eq E E' heq ht] using hq

/-- A common-column formula supplies an actual `Planar` parameter with
identical node encoders on the physical source intervals. -/
theorem planar_parameter_of_affine {K : ℕ}
    (φ₁ φ₂ : Fin K → ℝ → ℝ) (E : Fin K → ℝ → Plane)
    (u v : Plane) (c : Fin K → Plane)
    (haff : ∀ i x, x ∈ Icc (-1 : ℝ) 1 → E i x = c i + φ₁ i x • u + φ₂ i x • v) :
    ∃ e : Planar, ∀ i x, x ∈ Icc (-1 : ℝ) 1 →
      E i x = encoder e c (featurePairs φ₁ φ₂) i x := by
  refine ⟨⟨0, 0, u.1, u.2, v.1, v.2⟩, ?_⟩
  intro i x hx
  rw [haff i x hx]
  ext <;> simp [encoder, featurePairs, mul_comm]

/-- The actual SDP point in the seven-coordinate representation used by
the grid theorem. -/
def pointCoordinates {K : ℕ} (q : SDPPoint K) (k : Fin K) : SynthesisAttainment.Coordinates :=
  ![q.h k, q.l₁ k, q.l₂ k, q.A, q.B, q.C, q.lam]

/-- No norm or attainment premise is needed to pass an actual feasible SDP
point into the continuum program used by grid certification. -/
theorem pointCoordinates_feasible {K : ℕ} (γ : Fin K → ℝ → Plane)
    (F : Plane → ℝ) (P : ℝ) (q : SDPPoint K) (hq : SDPFeasible γ F P q) :
    HeterogeneousGridFeasible.Feasible γ (fun _ => Icc (-1 : ℝ) 1)
      (attainable γ) F P (pointCoordinates q) := by
  constructor
  · intro k j i hi
    fin_cases i <;> simp_all [pointCoordinates]
  · intro k
    exact ⟨hq.1, hq.2.1 k, hq.2.2.1 k, hq.2.2.2⟩

/-- Every optimum of the continuum grid representation has the same global
upper-bound interpretation as the actual SDP optimum. Together with
`unrestricted_sdp_attained`, this supplies the unrestricted-encoder scope of
the certified grid bounds. -/
theorem grid_maximum_global_bound {K : ℕ} (k₀ : Fin K)
    (γ : Fin K → ℝ → Plane) (F : Plane → ℝ) (P : ℝ)
    (q : SDPPoint K) (hq : SDPFeasible γ F P q)
    (hglobal : ∀ E : Fin K → ℝ → Plane,
      (∀ k, ContinuousOn (E k) (Icc (-1 : ℝ) 1)) →
      (∀ k s, s ∈ Icc (-1 : ℝ) 1 → squaredDistance (E k s) 0 ≤ P) →
      score γ F E ≤ (K : ℝ)^2 * q.lam)
    (qstar : Fin K → SynthesisAttainment.Coordinates)
    (hmax : ∀ r, HeterogeneousGridFeasible.Feasible γ (fun _ => Icc (-1 : ℝ) 1)
      (attainable γ) F P r → r k₀ 6 ≤ qstar k₀ 6) :
    ∀ E : Fin K → ℝ → Plane,
      (∀ k, ContinuousOn (E k) (Icc (-1 : ℝ) 1)) →
      (∀ k s, s ∈ Icc (-1 : ℝ) 1 → squaredDistance (E k s) 0 ≤ P) →
      score γ F E ≤ (K : ℝ)^2 * qstar k₀ 6 := by
  intro E hE hp
  exact (hglobal E hE hp).trans (mul_le_mul_of_nonneg_left
    (hmax (pointCoordinates q) (pointCoordinates_feasible γ F P q hq)) (sq_nonneg _))

/-- Under the full rigidity receiver alternatives, the actual heterogeneous
SDP optimizer is also optimal among all continuous peak-feasible encoders.
No exact-computation premise is imposed on competing encoders. -/
theorem unrestricted_sdp_attained {K : ℕ} (hK : 4 ≤ K)
    (φ₁ φ₂ : Fin K → ℝ → ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (h₁ : ∀ i, ContinuousOn (φ₁ i) (Icc (-1 : ℝ) 1))
    (h₂ : ∀ i, ContinuousOn (φ₂ i) (Icc (-1 : ℝ) 1))
    (hC₁ : ∀ i, ContDiffOn ℝ 1 (φ₁ i) (Ioo (-1 : ℝ) 1))
    (hC₂ : ∀ i, ContDiffOn ℝ 1 (φ₂ i) (Ioo (-1 : ℝ) 1))
    (hind : ∀ i, GeneralRigidity.NotInAffineLine (Icc (-1 : ℝ) 1) (φ₁ i) (φ₂ i))
    (hψC₁ : ContDiffOn ℝ 1 ψ₁ (HeterogeneousCompletionDensity.meanDomain φ₁))
    (hψC₂ : ContDiffOn ℝ 1 ψ₂ (HeterogeneousCompletionDensity.meanDomain φ₂))
    (halt₁ : CompletionSeparation.ReceiverAlternative
      (HeterogeneousCompletionDensity.meanDomain φ₁) ψ₁)
    (halt₂ : CompletionSeparation.ReceiverAlternative
      (HeterogeneousCompletionDensity.meanDomain φ₂) ψ₂)
    (hna : CompletionSeparation.NoAffineInterval
      (HeterogeneousCompletionDensity.meanDomain φ₁) ψ₁ ∨
      CompletionSeparation.NoAffineInterval (HeterogeneousCompletionDensity.meanDomain φ₂) ψ₂)
    (hn : Operational.NonconstantOn (attainable (featurePairs φ₁ φ₂))
      (fun m => ψ₁ m.1 + ψ₂ m.2))
    {P : ℝ} (hP : 0 ≤ P) :
    ∃ (q : SDPPoint K) (e : Planar) (c : Fin K → Plane),
      SDPFeasible (featurePairs φ₁ φ₂) (fun m => ψ₁ m.1 + ψ₂ m.2) P q ∧
      (∀ q' : SDPPoint K,
        SDPFeasible (featurePairs φ₁ φ₂) (fun m => ψ₁ m.1 + ψ₂ m.2) P q' → q'.lam ≤ q.lam) ∧
      (∀ k s, s ∈ Icc (-1 : ℝ) 1 → squaredDistance (encoder e c (featurePairs φ₁ φ₂) k s) 0 ≤ P) ∧
      score (featurePairs φ₁ φ₂) (fun m => ψ₁ m.1 + ψ₂ m.2)
        (encoder e c (featurePairs φ₁ φ₂)) = (K : ℝ)^2 * q.lam ∧
      (∀ E : Fin K → ℝ → Plane,
        (∀ k, ContinuousOn (E k) (Icc (-1 : ℝ) 1)) →
        (∀ k s, s ∈ Icc (-1 : ℝ) 1 → squaredDistance (E k s) 0 ≤ P) →
        score (featurePairs φ₁ φ₂) (fun m => ψ₁ m.1 + ψ₂ m.2) E ≤ (K : ℝ)^2 * q.lam) := by
  obtain ⟨q, e, c, hq, hmaxq, hp, hscore, hmax⟩ := heterogeneous_sdp_attained
    (by omega) (featurePairs φ₁ φ₂) (fun m => ψ₁ m.1 + ψ₂ m.2)
    (fun i => (h₁ i).prodMk (h₂ i)) hn hP
  refine ⟨q, e, c, hq, hmaxq, hp, hscore, ?_⟩
  intro E hE hpeak
  by_cases hpos : 0 < score (featurePairs φ₁ φ₂) (fun m => ψ₁ m.1 + ψ₂ m.2) E
  · have hexact := positive_score_implies_exact _ _ E hn hpos
    obtain ⟨u, v, c', _, haff⟩ := nonsingular_affine_of_exact hK φ₁ φ₂ E ψ₁ ψ₂
      h₁ h₂ hE hC₁ hC₂ hind hψC₁ hψC₂ halt₁ halt₂ hna hexact
    obtain ⟨e', he'⟩ := planar_parameter_of_affine φ₁ φ₂ E u v c' haff
    have hpeak' : ∀ k s, s ∈ Icc (-1 : ℝ) 1 →
        squaredDistance (encoder e' c' (featurePairs φ₁ φ₂) k s) 0 ≤ P := by
      intro k s hs
      rw [← he' k s hs]
      exact hpeak k s hs
    rw [score_eq_of_source_eq _ E _ _ he']
    exact (hmax e' c' hpeak').trans_eq hscore
  · exact (le_of_not_gt hpos).trans (mul_nonneg (sq_nonneg _) hq.1)

end Analog.HeterogeneousGlobalOptimum
