import Analog.GeneralCollision
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuous recovery on compact source spaces

Exactness is a statement about collisions. On a compact source space it
also supplies a continuous receiver on the actual received range. For the
original moment family, the fourth-input collision theorem additionally
makes the individual continuous encoder a closed embedding.

These results do not assert that a continuous injection on an open planar
set has open image. They therefore do not establish the reverse local
factorization used in the continuous-encoder rigidity proof.
-/

noncomputable section
open Set Topology

namespace Analog
namespace PlanarTopology

/-- Collision preservation gives a continuous recovery map on the actual
received range, without any supplied decoder or decoder regularity. -/
theorem continuous_recovery_of_compact
    {X Y Z : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z]
    (r : X → Y) (f : X → Z) (hr : Continuous r) (hf : Continuous f)
    (hcollision : ∀ x y, r x = r y → f x = f y) :
    ∃ D : Set.range r → Z, Continuous D ∧
      ∀ x, D (Set.rangeFactorization r x) = f x := by
  let D : Set.range r → Z := fun y => f (Classical.choose y.property)
  have hD : ∀ x, D (Set.rangeFactorization r x) = f x := by
    intro x
    exact hcollision _ x (Classical.choose_spec (Set.rangeFactorization r x).property)
  refine ⟨D, ?_, hD⟩
  have hq : IsQuotientMap (Set.rangeFactorization r) :=
    IsQuotientMap.of_surjective_continuous
      Set.rangeFactorization_surjective hr.rangeFactorization
  apply hq.continuous_iff.mpr
  have heq : D ∘ Set.rangeFactorization r = f := funext hD
  rw [heq]
  exact hf

/-- The original moment-family exactness condition already implies that
the individual encoder is injective on the closed source interval. -/
theorem exact_encoder_injOn {K : ℕ} (hK : 4 ≤ K)
    (φ ψ : ℝ → ℝ) (E : ℝ → ℝ × ℝ)
    (hshape : StrictConvexOn ℝ (Ioo (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Ioo (-1 : ℝ) 1) ψ)
    (hexact : GeneralCollision.ExactTarget K φ ψ E) :
    Set.InjOn E (Icc (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  have hxv : ArbitraryEncoder.ValidInput 3 [x, 0, 0] := by
    simp [ArbitraryEncoder.ValidInput, ArbitraryEncoder.InSource, hx.1, hx.2]
  have hyv : ArbitraryEncoder.ValidInput 3 [y, 0, 0] := by
    simp [ArbitraryEncoder.ValidInput, ArbitraryEncoder.InSource, hy.1, hy.2]
  have hr : ArbitraryEncoder.received E [x, 0, 0] =
      ArbitraryEncoder.received E [y, 0, 0] := by
    simp [ArbitraryEncoder.received, hxy]
  have hm := GeneralCollision.triple_collision_preserves_moments
    hK φ ψ E hshape hexact [x, 0, 0] [y, 0, 0] hxv hyv hr
  simpa [ArbitraryEncoder.firstMoment] using hm.1

/-- Under continuity, the source curve is a closed topological embedding.
This conclusion includes both source endpoints. -/
theorem exact_encoder_closedEmbedding {K : ℕ} (hK : 4 ≤ K)
    (φ ψ : ℝ → ℝ) (E : ℝ → ℝ × ℝ)
    (hshape : StrictConvexOn ℝ (Ioo (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Ioo (-1 : ℝ) 1) ψ)
    (hexact : GeneralCollision.ExactTarget K φ ψ E)
    (hE : ContinuousOn E (Icc (-1 : ℝ) 1)) :
    IsClosedEmbedding (fun x : Icc (-1 : ℝ) 1 => E x) := by
  apply hE.restrict.isClosedEmbedding
  intro x y hxy
  apply Subtype.ext
  exact exact_encoder_injOn hK φ ψ E hshape hexact x.property y.property hxy

/-- Three observations from the closed source interval. -/
abbrev SourceTriple := Icc (-1 : ℝ) 1 × Icc (-1 : ℝ) 1 × Icc (-1 : ℝ) 1

def tripleReceived (E : ℝ → ℝ × ℝ) (p : SourceTriple) : ℝ × ℝ :=
  E p.1 + E p.2.1 + E p.2.2

def tripleStatistics (φ : ℝ → ℝ) (p : SourceTriple) : ℝ × ℝ :=
  (p.1.val + p.2.1.val + p.2.2.val, φ p.1 + φ p.2.1 + φ p.2.2)

/-- Exact computation by at least four transmitters gives continuous
recovery of both triple statistics on the entire compact triple range.
This is the recovery direction, not local constancy on moment fibers. -/
theorem continuous_triple_moment_recovery {K : ℕ} (hK : 4 ≤ K)
    (φ ψ : ℝ → ℝ) (E : ℝ → ℝ × ℝ)
    (hshape : StrictConvexOn ℝ (Ioo (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Ioo (-1 : ℝ) 1) ψ)
    (hexact : GeneralCollision.ExactTarget K φ ψ E)
    (hE : ContinuousOn E (Icc (-1 : ℝ) 1))
    (hφ : ContinuousOn φ (Icc (-1 : ℝ) 1)) :
    ∃ D : Set.range (tripleReceived E) → ℝ × ℝ, Continuous D ∧
      ∀ p, D (Set.rangeFactorization (tripleReceived E) p) = tripleStatistics φ p := by
  have h1 : Continuous (fun p : SourceTriple => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous (fun p : SourceTriple => p.2.1.val) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have h3 : Continuous (fun p : SourceTriple => p.2.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hr : Continuous (tripleReceived E) :=
    ((hE.restrict.comp continuous_fst).add
      (hE.restrict.comp (continuous_fst.comp continuous_snd))).add
        (hE.restrict.comp (continuous_snd.comp continuous_snd))
  have hm : Continuous (tripleStatistics φ) :=
    ((h1.add h2).add h3).prodMk
      (((hφ.restrict.comp continuous_fst).add
        (hφ.restrict.comp (continuous_fst.comp continuous_snd))).add
          (hφ.restrict.comp (continuous_snd.comp continuous_snd)))
  apply continuous_recovery_of_compact (tripleReceived E) (tripleStatistics φ) hr hm
  intro p q hpq
  have valid (p : SourceTriple) :
      ArbitraryEncoder.ValidInput 3 [p.1.val, p.2.1.val, p.2.2.val] := by
    have hp1 := p.1.property
    have hp2 := p.2.1.property
    have hp3 := p.2.2.property
    simp [ArbitraryEncoder.ValidInput, ArbitraryEncoder.InSource,
      hp1.1, hp1.2, hp2.1, hp2.2, hp3.1, hp3.2]
  have hc : ArbitraryEncoder.received E [p.1.val, p.2.1.val, p.2.2.val] =
      ArbitraryEncoder.received E [q.1.val, q.2.1.val, q.2.2.val] := by
    simpa [ArbitraryEncoder.received, tripleReceived, add_assoc] using hpq
  have hstats := GeneralCollision.triple_collision_preserves_moments hK φ ψ E
    hshape hexact _ _ (valid p) (valid q) hc
  apply Prod.ext
  · simpa [tripleStatistics, ArbitraryEncoder.firstMoment, add_assoc] using hstats.1
  · simpa [tripleStatistics, GeneralCollision.featureMoment, add_assoc] using hstats.2

end PlanarTopology
end Analog
