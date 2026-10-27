import Analog.HeterogeneousFullRigidity
import Mathlib.Analysis.Convex.Function

/-! # Rigidity for the quadratic and quartic targets

The receiver and feature hypotheses of heterogeneous rigidity are derived
from the hypotheses of Proposition 4. Competing encoders are only continuous;
positive operational score supplies exact computation.
-/

noncomputable section
namespace Analog.PolynomialRigidity
open Set HeterogeneousScore HeterogeneousFullRigidity HeterogeneousRegularity
open HeterogeneousCompletionDensity CompletionSeparation
open scoped BigOperators

theorem nonconstant_of_positive_score {X : Type*} (D : Set X) (f : X → ℝ)
    (cost : X → X → ℝ) (h : 0 < Operational.score D f cost) :
    Operational.NonconstantOn D f := by
  by_contra hn
  have he : Operational.Quotients D f cost = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro q ⟨x, hx, y, hy, hne, _⟩
    exact hn ⟨x, hx, y, hy, hne⟩
  simp [Operational.score, he] at h

theorem strict_shape_noAffineInterval (ψ : ℝ → ℝ)
    (hshape : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ) :
    NoAffineInterval (Ioo (-1 : ℝ) 1) ψ := by
  intro l r hlr hsub
  rintro ⟨α, β, haff⟩
  let x := (3 * l + r) / 4
  let y := (l + 3 * r) / 4
  have hx : x ∈ Ioo l r := by dsimp [x]; constructor <;> linarith
  have hy : y ∈ Ioo l r := by dsimp [y]; constructor <;> linarith
  have hxy : x ≠ y := by dsimp [x, y]; intro he; linarith
  have hm : (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y ∈ Ioo l r := by
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hxs : x ∈ Icc (-1 : ℝ) 1 := ⟨(hsub hx).1.le, (hsub hx).2.le⟩
  have hys : y ∈ Icc (-1 : ℝ) 1 := ⟨(hsub hy).1.le, (hsub hy).2.le⟩
  rcases hshape with hc | hc
  · have hstrict := hc.2
    have hh := hstrict hxs hys hxy (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hh
    rw [haff _ hm, haff _ hx, haff _ hy] at hh
    linarith
  · have hstrict := hc.2
    have hh := hstrict hxs hys hxy (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hh
    rw [haff _ hm, haff _ hx, haff _ hy] at hh
    linarith

theorem meanDomain_identity {K : ℕ} (hK : 0 < K) :
    meanDomain (fun (_ : Fin K) (s : ℝ) => s) = Ioo (-1 : ℝ) 1 := by
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  simp [meanDomain, featureLower, featureUpper, csInf_Icc, csSup_Icc,
    show (-1 : ℝ) ≤ 1 by norm_num, hk]

theorem polynomial_independent (p : ℕ) (hp : p = 2 ∨ p = 4) :
    GeneralRigidity.NotInAffineLine (Icc (-1 : ℝ) 1) (fun s => s)
      (fun s => s ^ p) := by
  rintro ⟨A, B, C, hnon, hrel⟩
  have hm := hrel (-1) (by norm_num)
  have hz := hrel 0 (by norm_num)
  have hp' := hrel 1 (by norm_num)
  rcases hp with rfl | rfl <;> norm_num at hm hz hp' <;>
    rcases hnon with hA | hB <;> apply_assumption <;> linarith

/-- The complete positive-score necessity used by Proposition 4, for both
polynomial features and either strict receiver curvature. -/
theorem polynomial_positive_score_rigidity {K : ℕ} (hK : 4 ≤ K)
    (p : ℕ) (hp : p = 2 ∨ p = 4) (ψ : ℝ → ℝ)
    (hψ : ContDiffOn ℝ 1 ψ (Icc (-1 : ℝ) 1))
    (hshape : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (E : Fin K → ℝ → Plane)
    (hE : ∀ i, ContinuousOn (E i) (Icc (-1 : ℝ) 1))
    (hpos : 0 < score (fun _ s => (s, s ^ p)) (fun m => m.2 - ψ m.1) E) :
    ∃ u v : Plane, ∃ c : Fin K → Plane, u.1 * v.2 - v.1 * u.2 ≠ 0 ∧
      ∀ i s, s ∈ Icc (-1 : ℝ) 1 → E i s = c i + s • u + s ^ p • v := by
  have hninput := nonconstant_of_positive_score _ _ _ hpos
  have hn := (Operational.nonconstantOn_stat_image_iff (ValidInput K)
    (meanStatistic (fun _ s => (s, s ^ p))) (fun m => m.2 - ψ m.1)).mp hninput
  have he := positive_score_implies_exact _ _ E hn hpos
  have hmd := meanDomain_identity (K := K) (by omega)
  have hna : NoAffineInterval (meanDomain (fun (_ : Fin K) (s : ℝ) => s))
      (fun s => -ψ s) := by
    rw [hmd]
    apply strict_shape_noAffineInterval
    rcases hshape with hc | hc
    · exact Or.inr hc.neg
    · exact Or.inl hc.neg
  have hψneg : ContDiffOn ℝ 1 (fun s => -ψ s)
      (meanDomain (fun (_ : Fin K) (s : ℝ) => s)) := by
    rw [hmd]
    exact hψ.neg.mono Ioo_subset_Icc_self
  have haltid : ReceiverAlternative
      (meanDomain (fun (_ : Fin K) (s : ℝ) => s ^ p)) (fun s => s) :=
    Or.inl ⟨0, 1, one_ne_zero, fun _ _ => by ring⟩
  have hexact : ExactComputation
      (featurePairs (fun (_ : Fin K) (s : ℝ) => s) (fun _ s => s ^ p))
      (fun m => -ψ m.1 + m.2) E := by
    simpa only [featurePairs, sub_eq_neg_add] using he
  exact nonsingular_affine_of_exact hK (fun _ s => s) (fun _ s => s ^ p) E
    (fun s => -ψ s) (fun s => s) (fun _ => continuousOn_id)
    (fun _ => continuousOn_id.pow p) hE (fun _ => contDiffOn_id)
    (fun _ => contDiffOn_id.pow p) (fun _ => polynomial_independent p hp)
    hψneg contDiffOn_id (Or.inr hna) haltid (Or.inl hna) hexact

end Analog.PolynomialRigidity
