import Analog.GeneralScore
import Analog.HeterogeneousScore
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# The endpoint score formula for the actual finite-node model

This module assembles Lemma 1 (`prop:score`). It identifies the operational
quotient set for `Fin K` inputs and arbitrary node offsets with the previously
proved shared-feature list model. Thus the exact endpoint formula and arbitrarily
short sharp pairs refer to the actual finite-node channel. Endpoint derivatives
are one-sided derivatives within the closed source interval.
-/

noncomputable section
open Set
open scoped BigOperators
namespace Analog.FiniteNodeScore
open GramSynthesis ArbitraryEncoder

/-- Common features, retaining the actual node indexing. -/
def sharedFeatures {K : ℕ} (φ : ℝ → ℝ) : Fin K → ℝ → ℝ × ℝ :=
  fun _ s => (s, φ s)

/-- The scalar two-moment readout. -/
def readout (ψ : ℝ → ℝ) (m : ℝ × ℝ) : ℝ := m.2 - ψ m.1

/-- The same common columns in the legacy list representation. -/
def asCurve (e : Planar) : Curve :=
  ⟨e.cx, e.cy, e.ux, e.uy, e.vx, e.vy⟩

lemma ofFn_valid {K : ℕ} {s : Fin K → ℝ}
    (hs : s ∈ HeterogeneousScore.ValidInput K) :
    ArbitraryEncoder.ValidInput K (List.ofFn s) := by
  refine ⟨List.length_ofFn, ?_⟩
  intro x hx
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  exact hs k

lemma exists_ofFn_of_valid {K : ℕ} {xs : List ℝ}
    (hx : ArbitraryEncoder.ValidInput K xs) :
    ∃ s : Fin K → ℝ, s ∈ HeterogeneousScore.ValidInput K ∧ List.ofFn s = xs := by
  obtain ⟨hlen, hvals⟩ := hx
  subst K
  exact ⟨xs.get, (fun k => hvals _ (List.get_mem xs k)), List.ofFn_get xs⟩

lemma target_ofFn {K : ℕ} (φ ψ : ℝ → ℝ) (s : Fin K → ℝ) :
    GeneralCollision.target K φ ψ (List.ofFn s) =
      readout ψ (HeterogeneousScore.meanStatistic (sharedFeatures φ) s) := by
  simp [GeneralCollision.target, GeneralCollision.featureMoment,
    firstMoment, List.map_ofFn, List.sum_ofFn, readout,
    HeterogeneousScore.meanStatistic, sharedFeatures, Function.comp_def]

/-- Distinct node offsets cancel, including when their average is nonzero. -/
lemma squaredDistance_ofFn {K : ℕ} (e : Planar) (c : Fin K → ℝ × ℝ)
    (φ : ℝ → ℝ) (s t : Fin K → ℝ) :
    squaredDistance
      (HeterogeneousScore.received (HeterogeneousScore.encoder e c (sharedFeatures φ)) s)
      (HeterogeneousScore.received (HeterogeneousScore.encoder e c (sharedFeatures φ)) t) =
    squaredDistance
      (received (GeneralScore.encoder (asCurve e) φ) (List.ofFn s))
      (received (GeneralScore.encoder (asCurve e) φ) (List.ofFn t)) := by
  rw [HeterogeneousScore.received_encoder, HeterogeneousScore.received_encoder,
    GeneralScore.received_encoder, GeneralScore.received_encoder]
  simp only [List.length_ofFn, firstMoment, GeneralCollision.featureMoment,
    List.map_ofFn, List.sum_ofFn, Function.comp_def, sharedFeatures]
  dsimp [squaredDistance, asCurve]
  ring

/-- The quotient sets, and hence their infima, are unchanged by switching from
lists to node-indexed inputs and by allowing arbitrary separate offsets. -/
theorem score_eq_shared_list {K : ℕ} (e : Planar) (c : Fin K → ℝ × ℝ)
    (φ ψ : ℝ → ℝ) :
    HeterogeneousScore.score (sharedFeatures φ) (readout ψ)
      (HeterogeneousScore.encoder e c (sharedFeatures φ)) =
      GeneralScore.score K φ ψ (asCurve e) := by
  unfold HeterogeneousScore.score GeneralScore.score Operational.score
  congr 1
  ext q
  constructor
  · rintro ⟨s, hs, t, ht, hne, hq⟩
    refine ⟨List.ofFn s, ofFn_valid hs, List.ofFn t, ofFn_valid ht, ?_, ?_⟩
    · simpa only [target_ofFn, Function.comp_apply] using hne
    · simpa only [target_ofFn, ← squaredDistance_ofFn e c φ s t,
        Function.comp_apply] using hq
  · rintro ⟨xs, hxs, ys, hys, hne, hq⟩
    obtain ⟨s, hs, rfl⟩ := exists_ofFn_of_valid hxs
    obtain ⟨t, ht, rfl⟩ := exists_ofFn_of_valid hys
    refine ⟨s, hs, t, ht, ?_, ?_⟩
    · simpa only [target_ofFn, Function.comp_apply] using hne
    · simpa only [target_ofFn, ← squaredDistance_ofFn e c φ s t,
        Function.comp_apply] using hq

/-- Strict feature curvature makes the actual finite-node target nonconstant. -/
theorem finite_target_nonconstant {K : ℕ} (hK : 2 ≤ K) (φ ψ : ℝ → ℝ)
    (hφ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ) :
    Operational.NonconstantOn (HeterogeneousScore.ValidInput K)
      (readout ψ ∘ HeterogeneousScore.meanStatistic (sharedFeatures φ)) := by
  obtain ⟨xs, hxs, ys, hys, hne⟩ :=
    GeneralScore.target_nonconstant_of_strict_feature hK φ ψ hφ
  obtain ⟨s, hs, rfl⟩ := exists_ofFn_of_valid hxs
  obtain ⟨t, ht, rfl⟩ := exists_ofFn_of_valid hys
  exact ⟨s, hs, t, ht, by simpa only [target_ofFn, Function.comp_apply] using hne⟩

/-- The same nonconstancy on the actual attainable image. -/
theorem attainable_target_nonconstant {K : ℕ} (hK : 2 ≤ K) (φ ψ : ℝ → ℝ)
    (hφ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ) :
    Operational.NonconstantOn (HeterogeneousScore.attainable (sharedFeatures (K := K) φ))
      (readout ψ) :=
  (Operational.nonconstantOn_stat_image_iff _ _ _).mp
    (finite_target_nonconstant hK φ ψ hφ)

/-- Lemma 1's endpoint-dual formula for the actual finite-node channel.
The result is stronger than the paper's `4 ≤ K` assumption. -/
theorem finite_node_operational_score {K : ℕ} (hK : 2 ≤ K)
    (e : Planar) (c : Fin K → ℝ × ℝ) (φ ψ : ℝ → ℝ)
    (hD : 0 < det e.A e.B e.C)
    (hφ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ)
    (hdφ : ∀ z ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ φ z)
    (hψ : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (hdψ : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hcψ : ContinuousOn (GeneralScore.readoutSlope ψ) (Icc (-1 : ℝ) 1)) :
    HeterogeneousScore.score (sharedFeatures φ) (readout ψ)
      (HeterogeneousScore.encoder e c (sharedFeatures φ)) =
      (K : ℝ) ^ 2 / max
        (dual e.A e.B e.C (-GeneralScore.readoutSlope ψ (-1)) 1)
        (dual e.A e.B e.C (-GeneralScore.readoutSlope ψ 1) 1) := by
  rw [score_eq_shared_list]
  exact GeneralScore.general_operational_score (asCurve e) hK φ ψ hD hφ hdφ
    hψ hdψ hcψ

/-- Arbitrarily short actual finite-node received pairs approach the score.
The pairs may have any prescribed positive bound on their received distance. -/
theorem finite_node_small_distance_sharpness {K : ℕ} (hK : 2 ≤ K)
    (e : Planar) (c : Fin K → ℝ × ℝ) (φ ψ : ℝ → ℝ)
    (hD : 0 < det e.A e.B e.C)
    (hφ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ)
    (hdφ : ∀ z ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ φ z)
    (hψ : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (hdψ : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hcψ : ContinuousOn (GeneralScore.readoutSlope ψ) (Icc (-1 : ℝ) 1))
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ s t : Fin K → ℝ,
      s ∈ HeterogeneousScore.ValidInput K ∧ t ∈ HeterogeneousScore.ValidInput K ∧
      readout ψ (HeterogeneousScore.meanStatistic (sharedFeatures φ) s) ≠
        readout ψ (HeterogeneousScore.meanStatistic (sharedFeatures φ) t) ∧
      squaredDistance
        (HeterogeneousScore.received (HeterogeneousScore.encoder e c (sharedFeatures φ)) s)
        (HeterogeneousScore.received (HeterogeneousScore.encoder e c (sharedFeatures φ)) t) < δ ^ 2 ∧
      squaredDistance
        (HeterogeneousScore.received (HeterogeneousScore.encoder e c (sharedFeatures φ)) s)
        (HeterogeneousScore.received (HeterogeneousScore.encoder e c (sharedFeatures φ)) t) /
        (readout ψ (HeterogeneousScore.meanStatistic (sharedFeatures φ) s) -
          readout ψ (HeterogeneousScore.meanStatistic (sharedFeatures φ) t)) ^ 2 <
        HeterogeneousScore.score (sharedFeatures φ) (readout ψ)
          (HeterogeneousScore.encoder e c (sharedFeatures φ)) + ε := by
  obtain ⟨xs, ys, hxs, hys, hne, hdist, hquot⟩ :=
    GeneralScore.general_score_small_distance_sharpness (asCurve e) hK φ ψ hD
      hφ hdφ hψ hdψ hcψ ε δ hε hδ
  obtain ⟨s, hs, rfl⟩ := exists_ofFn_of_valid hxs
  obtain ⟨t, ht, rfl⟩ := exists_ofFn_of_valid hys
  refine ⟨s, t, hs, ht, ?_, ?_, ?_⟩
  · simpa only [target_ofFn] using hne
  · simpa only [squaredDistance_ofFn] using hdist
  · simpa only [squaredDistance_ofFn, score_eq_shared_list, target_ofFn] using hquot

/-- The manuscript's closed-interval C¹ readout assumption implies both the
within-derivative and endpoint-continuity premises of the endpoint formula. -/
lemma c1_readout_regular (ψ : ℝ → ℝ)
    (hψ : ContDiffOn ℝ 1 ψ (Icc (-1 : ℝ) 1)) :
    DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1) ∧
      ContinuousOn (GeneralScore.readoutSlope ψ) (Icc (-1 : ℝ) 1) :=
  ⟨hψ.differentiableOn le_rfl,
    hψ.continuousOn_derivWithin (uniqueDiffOn_Icc (by norm_num)) le_rfl⟩

/-- Lemma 1 (`prop:score`), under its manuscript C¹ and strict-curvature
hypotheses, for arbitrary node offsets and the exact `Fin K` operational score.
The continuity of the feature at the endpoints, also assumed in the paper,
is not needed for this score identity. -/
theorem lemma_one_score {K : ℕ} (hK : 4 ≤ K)
    (e : Planar) (c : Fin K → ℝ × ℝ) (φ ψ : ℝ → ℝ)
    (hD : 0 < det e.A e.B e.C)
    (hφ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ)
    (hdφ : ContDiffOn ℝ 1 φ (Ioo (-1 : ℝ) 1))
    (hψ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (hdψ : ContDiffOn ℝ 1 ψ (Icc (-1 : ℝ) 1)) :
    HeterogeneousScore.score (sharedFeatures φ) (readout ψ)
      (HeterogeneousScore.encoder e c (sharedFeatures φ)) =
      (K : ℝ) ^ 2 / max
        (dual e.A e.B e.C (-GeneralScore.readoutSlope ψ (-1)) 1)
        (dual e.A e.B e.C (-GeneralScore.readoutSlope ψ 1) 1) := by
  apply finite_node_operational_score (by omega) e c φ ψ hD hφ
  · intro z hz
    exact (hdφ.differentiableOn le_rfl z hz).differentiableAt (isOpen_Ioo.mem_nhds hz)
  · exact hψ.imp StrictConvexOn.convexOn StrictConcaveOn.concaveOn
  · exact (c1_readout_regular ψ hdψ).1
  · exact (c1_readout_regular ψ hdψ).2

/-- Lemma 1's sharpness conclusion under the same manuscript assumptions.
For every accuracy and every received-distance threshold there are actual
admissible, unequal-target node tuples realizing both bounds. -/
theorem lemma_one_sharpness {K : ℕ} (hK : 4 ≤ K)
    (e : Planar) (c : Fin K → ℝ × ℝ) (φ ψ : ℝ → ℝ)
    (hD : 0 < det e.A e.B e.C)
    (hφ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ)
    (hdφ : ContDiffOn ℝ 1 φ (Ioo (-1 : ℝ) 1))
    (hψ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (hdψ : ContDiffOn ℝ 1 ψ (Icc (-1 : ℝ) 1))
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ s t : Fin K → ℝ,
      s ∈ HeterogeneousScore.ValidInput K ∧ t ∈ HeterogeneousScore.ValidInput K ∧
      readout ψ (HeterogeneousScore.meanStatistic (sharedFeatures φ) s) ≠
        readout ψ (HeterogeneousScore.meanStatistic (sharedFeatures φ) t) ∧
      squaredDistance
        (HeterogeneousScore.received (HeterogeneousScore.encoder e c (sharedFeatures φ)) s)
        (HeterogeneousScore.received (HeterogeneousScore.encoder e c (sharedFeatures φ)) t) < δ ^ 2 ∧
      squaredDistance
        (HeterogeneousScore.received (HeterogeneousScore.encoder e c (sharedFeatures φ)) s)
        (HeterogeneousScore.received (HeterogeneousScore.encoder e c (sharedFeatures φ)) t) /
        (readout ψ (HeterogeneousScore.meanStatistic (sharedFeatures φ) s) -
          readout ψ (HeterogeneousScore.meanStatistic (sharedFeatures φ) t)) ^ 2 <
        HeterogeneousScore.score (sharedFeatures φ) (readout ψ)
          (HeterogeneousScore.encoder e c (sharedFeatures φ)) + ε := by
  apply finite_node_small_distance_sharpness (by omega) e c φ ψ hD hφ
    (fun z hz => (hdφ.differentiableOn le_rfl z hz).differentiableAt
      (isOpen_Ioo.mem_nhds hz))
    (hψ.imp StrictConvexOn.convexOn StrictConcaveOn.concaveOn)
    (c1_readout_regular ψ hdψ).1 (c1_readout_regular ψ hdψ).2 ε δ hε hδ

end Analog.FiniteNodeScore
