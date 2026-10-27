import Analog.HeterogeneousLocalCharts
import Analog.HeterogeneousCompletion
import Analog.HeterogeneousNonsingularity
import Analog.HeterogeneousCompletionDensity

/-!
# Heterogeneous rigidity from exact computation

The local topology bridge is discharged here using actual physical
completion collisions and the proved planar invariance-of-domain theorem.
-/

noncomputable section
namespace Analog.HeterogeneousFullRigidity
open Set Filter Topology HeterogeneousRegularity HeterogeneousAnalyticRigidity
open HeterogeneousCompletion HeterogeneousScore
open scoped BigOperators

/-- Actual feature pairs, retaining the manuscript's two separately indexed
families. -/
def featurePairs {K : ℕ} (φ₁ φ₂ : Fin K → ℝ → ℝ) : Fin K → ℝ → Plane :=
  fun i x => (φ₁ i x, φ₂ i x)

/-- Exact computation gives the continuous planar source-box charts needed
by automatic regularity, at every actual identifying regular triple. -/
theorem dense_planar_charts_of_exact {K : ℕ}
    (φ₁ φ₂ : Fin K → ℝ → ℝ) (E : Fin K → ℝ → Plane) (ψ₁ ψ₂ : ℝ → ℝ)
    (h₁ : ∀ i, ContinuousOn (φ₁ i) (Icc (-1 : ℝ) 1))
    (h₂ : ∀ i, ContinuousOn (φ₂ i) (Icc (-1 : ℝ) 1))
    (hE : ∀ i, ContinuousOn (E i) (Icc (-1 : ℝ) 1))
    (hC₁ : ∀ i, ContDiffOn ℝ 1 (φ₁ i) (Ioo (-1 : ℝ) 1))
    (hC₂ : ∀ i, ContDiffOn ℝ 1 (φ₂ i) (Ioo (-1 : ℝ) 1))
    (hexact : ExactComputation (featurePairs φ₁ φ₂)
      (fun m => ψ₁ m.1 + ψ₂ m.2) E) :
    DensePlanarCharts φ₁ φ₂ E (localIdentifyingSet (featurePairs φ₁ φ₂) ψ₁ ψ₂) := by
  intro i j k hij hik hjk x hx y hy z hz hd hp
  obtain ⟨B, hB, hrecover⟩ := identifying_collision_neighborhood
    (featurePairs φ₁ φ₂) E ψ₁ ψ₂ hexact i j k hij hik hjk hp
  have hC (i : Fin K) (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 1) :
      ContDiffAt ℝ 1 (fun t => (φ₁ i t, φ₂ i t)) s :=
    ((hC₁ i s hs).contDiffAt (Ioo_mem_nhds hs.1 hs.2)).prodMk
      ((hC₂ i s hs).contDiffAt (Ioo_mem_nhds hs.1 hs.2))
  exact HeterogeneousLocalCharts.heterogeneous_local_chart
    (φ₁ i) (φ₁ j) (φ₁ k) (φ₂ i) (φ₂ j) (φ₂ k) (E i) (E j) (E k)
    ((h₁ i).prodMk (h₂ i)) ((h₁ j).prodMk (h₂ j)) ((h₁ k).prodMk (h₂ k))
    (hE i) (hE j) (hE k) hx hy hz (hC i x hx) (hC j y hy) (hC k z hz) hd hB hrecover

/-- The analytic and topological chains together: density of the actual
two-completion identifying locus and exact computation imply common affine
columns, with individual node offsets and both source endpoints included. -/
theorem affine_of_exact_and_dense_identification {K : ℕ} (hK : 4 ≤ K)
    (φ₁ φ₂ : Fin K → ℝ → ℝ) (E : Fin K → ℝ → Plane) (ψ₁ ψ₂ : ℝ → ℝ)
    (h₁ : ∀ i, ContinuousOn (φ₁ i) (Icc (-1 : ℝ) 1))
    (h₂ : ∀ i, ContinuousOn (φ₂ i) (Icc (-1 : ℝ) 1))
    (hE : ∀ i, ContinuousOn (E i) (Icc (-1 : ℝ) 1))
    (hC₁ : ∀ i, ContDiffOn ℝ 1 (φ₁ i) (Ioo (-1 : ℝ) 1))
    (hC₂ : ∀ i, ContDiffOn ℝ 1 (φ₂ i) (Ioo (-1 : ℝ) 1))
    (hind : ∀ i, GeneralRigidity.NotInAffineLine (Icc (-1 : ℝ) 1) (φ₁ i) (φ₂ i))
    (hexact : ExactComputation (featurePairs φ₁ φ₂)
      (fun m => ψ₁ m.1 + ψ₂ m.2) E)
    (hdense : DenseIdentification φ₁ φ₂
      (localIdentifyingSet (featurePairs φ₁ φ₂) ψ₁ ψ₂)) :
    ∃ u v : Plane, ∃ c : Fin K → Plane, ∀ i x, x ∈ Icc (-1 : ℝ) 1 →
      E i x = c i + φ₁ i x • u + φ₂ i x • v := by
  exact planar_affine_of_dense_charts hK φ₁ φ₂ E _ h₁ h₂ hE hC₁ hC₂ hind hdense
    (dense_planar_charts_of_exact φ₁ φ₂ E ψ₁ ψ₂ h₁ h₂ hE hC₁ hC₂ hexact)

/-- Local exact recovery at one regular identifying triple excludes singular
common affine columns. The needed open moment slice is constructed from the
actual source-coordinate inverse. -/
theorem nonsingular_at_identifying_triple {K : ℕ}
    (φ₁ φ₂ : Fin K → ℝ → ℝ) (E : Fin K → ℝ → Plane) (ψ₁ ψ₂ : ℝ → ℝ)
    (h₁ : ∀ i, ContinuousOn (φ₁ i) (Icc (-1 : ℝ) 1))
    (h₂ : ∀ i, ContinuousOn (φ₂ i) (Icc (-1 : ℝ) 1))
    (hC₁ : ∀ i, ContDiffOn ℝ 1 (φ₁ i) (Ioo (-1 : ℝ) 1))
    (hC₂ : ∀ i, ContDiffOn ℝ 1 (φ₂ i) (Ioo (-1 : ℝ) 1))
    (hexact : ExactComputation (featurePairs φ₁ φ₂)
      (fun m => ψ₁ m.1 + ψ₂ m.2) E)
    (u v : Plane) (c : Fin K → Plane)
    (haffine : ∀ i x, x ∈ Icc (-1 : ℝ) 1 → E i x = c i + φ₁ i x • u + φ₂ i x • v)
    (i j k : Fin K) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x y z : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hy : y ∈ Ioo (-1 : ℝ) 1) (hz : z ∈ Ioo (-1 : ℝ) 1)
    (hd : deriv (φ₁ j) y * deriv (φ₂ k) z - deriv (φ₁ k) z * deriv (φ₂ j) y ≠ 0)
    (hp : tripleStatistic (φ₁ i) (φ₁ j) (φ₁ k) (φ₂ i) (φ₂ j) (φ₂ k) (x, y, z) ∈
      localIdentifyingSet (featurePairs φ₁ φ₂) ψ₁ ψ₂ i j k) :
    u.1 * v.2 - v.1 * u.2 ≠ 0 := by
  let M := tripleStatistic (φ₁ i) (φ₁ j) (φ₁ k) (φ₂ i) (φ₂ j) (φ₂ k)
  let R : RigidityAnalysis.Triple → Plane := fun p => E i p.1 + E j p.2.1 + E k p.2.2
  have hC (n : Fin K) (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 1) :
      ContDiffAt ℝ 1 (fun t => (φ₁ n t, φ₂ n t)) s :=
    ((hC₁ n s hs).contDiffAt (Ioo_mem_nhds hs.1 hs.2)).prodMk
      ((hC₂ n s hs).contDiffAt (Ioo_mem_nhds hs.1 hs.2))
  obtain ⟨L, hL, hLs⟩ := HeterogeneousCoordinates.coordinates_localHomeomorph
    (hC i x hx) (hC j y hy) (hC k z hz) hd
  obtain ⟨B, hB, hrecover⟩ := identifying_collision_neighborhood
    (featurePairs φ₁ φ₂) E ψ₁ ψ₂ hexact i j k hij hik hjk hp
  obtain ⟨B', hB'B, hB'open, hmB'⟩ := mem_nhds_iff.mp hB
  have hM : ContinuousOn M HeterogeneousLocalCharts.sourceTriples := by
    simpa only [M, tripleStatistic, tripleSum, Prod.add_def] using
      HeterogeneousLocalCharts.continuousOn_sum _ _ _
        ((h₁ i).prodMk (h₂ i)) ((h₁ j).prodMk (h₂ j)) ((h₁ k).prodMk (h₂ k))
  let N := HeterogeneousLocalCharts.interiorTriples ∩ M ⁻¹' B'
  have hNopen : IsOpen N :=
    (hM.mono HeterogeneousLocalCharts.interiorTriples_subset).isOpen_inter_preimage
      HeterogeneousLocalCharts.isOpen_interiorTriples hB'open
  let e := L.restr N
  have hesource : e.source = L.source ∩ N := L.restr_source' N hNopen
  have hevalid : e.source ⊆ HeterogeneousLocalCharts.sourceTriples := by
    intro p hp
    rw [hesource] at hp
    exact HeterogeneousLocalCharts.interiorTriples_subset hp.2.1
  apply HeterogeneousNonsingularity.determinant_ne_zero_of_local_recovery
    e M R u v (c i + c j + c k) (fun p => congrFun hL p) ?_ ?_ (x, y, z) ?_
  · intro p hp
    have hv := hevalid hp
    change E i p.1 + E j p.2.1 + E k p.2.2 = _
    rw [haffine i p.1 hv.1, haffine j p.2.1 hv.2.1, haffine k p.2.2 hv.2.2]
    dsimp [M, tripleStatistic, tripleSum]
    simp only [add_smul]
    abel
  · intro p hp q hq heq
    have hp' := hp
    have hq' := hq
    rw [hesource] at hp' hq'
    exact hrecover p (hevalid hp) q (hevalid hq) (hB'B hp'.2.2) (hB'B hq'.2.2) heq
  · rw [hesource]
    exact ⟨hLs, ⟨hx, hy, hz⟩, hmB'⟩

/-- Full common-affine necessity, including nonsingularity, once density of
the actual physical-completion identifying locus is available. -/
theorem nonsingular_affine_of_exact_and_dense_identification {K : ℕ} (hK : 4 ≤ K)
    (φ₁ φ₂ : Fin K → ℝ → ℝ) (E : Fin K → ℝ → Plane) (ψ₁ ψ₂ : ℝ → ℝ)
    (h₁ : ∀ i, ContinuousOn (φ₁ i) (Icc (-1 : ℝ) 1))
    (h₂ : ∀ i, ContinuousOn (φ₂ i) (Icc (-1 : ℝ) 1))
    (hE : ∀ i, ContinuousOn (E i) (Icc (-1 : ℝ) 1))
    (hC₁ : ∀ i, ContDiffOn ℝ 1 (φ₁ i) (Ioo (-1 : ℝ) 1))
    (hC₂ : ∀ i, ContDiffOn ℝ 1 (φ₂ i) (Ioo (-1 : ℝ) 1))
    (hind : ∀ i, GeneralRigidity.NotInAffineLine (Icc (-1 : ℝ) 1) (φ₁ i) (φ₂ i))
    (hexact : ExactComputation (featurePairs φ₁ φ₂)
      (fun m => ψ₁ m.1 + ψ₂ m.2) E)
    (hdense : DenseIdentification φ₁ φ₂
      (localIdentifyingSet (featurePairs φ₁ φ₂) ψ₁ ψ₂)) :
    ∃ u v : Plane, ∃ c : Fin K → Plane, u.1 * v.2 - v.1 * u.2 ≠ 0 ∧
      ∀ i x, x ∈ Icc (-1 : ℝ) 1 → E i x = c i + φ₁ i x • u + φ₂ i x • v := by
  obtain ⟨u, v, c, haff⟩ := affine_of_exact_and_dense_identification hK φ₁ φ₂ E ψ₁ ψ₂
    h₁ h₂ hE hC₁ hC₂ hind hexact hdense
  refine ⟨u, v, c, ?_, haff⟩
  let i : Fin K := ⟨0, by omega⟩
  obtain ⟨j, k, hij, hik, hjk⟩ := exists_two_other_nodes (by omega) i
  obtain ⟨y, hy, z, hz, hd⟩ := HeterogeneousSeparation.independent_tangents_across_nodes
    (φ₁ j) (φ₂ j) (φ₁ k) (φ₂ k) (h₁ j) (h₂ j) (h₁ k) (h₂ k)
    (hC₁ j).differentiableOn_one (hC₂ j).differentiableOn_one
    (hC₁ k).differentiableOn_one (hC₂ k).differentiableOn_one (hind j) (hind k)
  have hzero : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  have hcl := regular_pair_identifying_closure (a := φ₁ i) (d := φ₂ i)
    (hC₁ j) (hC₁ k) (hC₂ j) (hC₂ k) hy hz hd
    (hdense i j k hij hik hjk 0 hzero y hy z hz hd)
  obtain ⟨q, _, hq, hqO⟩ := mem_closure_iff_nhds.mp hcl univ Filter.univ_mem
  exact nonsingular_at_identifying_triple φ₁ φ₂ E ψ₁ ψ₂ h₁ h₂ hC₁ hC₂ hexact u v c haff
    i j k hij hik hjk hzero hq.1.1 hq.1.2 hq.2 hqO

/-- The sufficient direction holds for arbitrary scalar readouts: invertible
common columns recover the actual two normalized statistics. The encoder
formula is only required on the physical source interval. -/
theorem exact_of_nonsingular_affine {K : ℕ}
    (φ₁ φ₂ : Fin K → ℝ → ℝ) (E : Fin K → ℝ → Plane) (F : Plane → ℝ)
    (u v : Plane) (c : Fin K → Plane) (hdet : u.1 * v.2 - v.1 * u.2 ≠ 0)
    (haffine : ∀ i x, x ∈ Icc (-1 : ℝ) 1 → E i x = c i + φ₁ i x • u + φ₂ i x • v) :
    ExactComputation (featurePairs φ₁ φ₂) F E := by
  let e : GramSynthesis.Planar := ⟨0, 0, u.1, u.2, v.1, v.2⟩
  have heq (i : Fin K) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
      E i x = encoder e c (featurePairs φ₁ φ₂) i x := by
    rw [haffine i x hx]
    ext <;> simp [encoder, featurePairs, e, mul_comm]
  have hreceived (s : Fin K → ℝ) (hs : s ∈ ValidInput K) :
      received E s = received (encoder e c (featurePairs φ₁ φ₂)) s := by
    apply Prod.ext
    · simp only [received]
      exact Finset.sum_congr rfl (fun i _ => congrArg Prod.fst (heq i (s i) (hs i)))
    · simp only [received]
      exact Finset.sum_congr rfl (fun i _ => congrArg Prod.snd (heq i (s i) (hs i)))
  have hex := exact_computation_of_det e c (featurePairs φ₁ φ₂) F
    (by simpa [e, mul_comm] using hdet)
  intro s hs t ht hst
  apply hex s hs t ht
  rw [← hreceived s hs, ← hreceived t ht]
  exact hst

/-- The manuscript's receiver alternative on a closed mean interval,
combined with nonconstancy there, gives exactly the open-domain receiver
alternative used by the analytic completion proof. -/
theorem receiver_alternative_of_closed {l r : ℝ} (ψ : ℝ → ℝ)
    (hn : Operational.NonconstantOn (Icc l r) ψ)
    (halt : (∃ α β : ℝ, ∀ z ∈ Icc l r, ψ z = α + β * z) ∨
      CompletionSeparation.NoAffineInterval (Ioo l r) ψ) :
    CompletionSeparation.ReceiverAlternative (Ioo l r) ψ := by
  rcases halt with ⟨α, β, haff⟩ | hna
  · left
    refine ⟨α, β, ?_, fun z hz => haff z ⟨hz.1.le, hz.2.le⟩⟩
    intro hb
    obtain ⟨s, hs, t, ht, hst⟩ := hn
    apply hst
    rw [haff s hs, haff t ht, hb]
    simp
  · exact Or.inr hna

/-- Under the stated alternatives, a receiver that is not affine on the
closed mean interval is nowhere affine on its interior. -/
theorem noAffineInterval_of_closed_nonaffine {l r : ℝ} (ψ : ℝ → ℝ)
    (halt : (∃ α β : ℝ, ∀ z ∈ Icc l r, ψ z = α + β * z) ∨
      CompletionSeparation.NoAffineInterval (Ioo l r) ψ)
    (hna : ¬ ∃ α β : ℝ, ∀ z ∈ Icc l r, ψ z = α + β * z) :
    CompletionSeparation.NoAffineInterval (Ioo l r) ψ :=
  halt.resolve_left hna

/-- Necessity from exact computation and the receiver alternatives alone:
completion separation, actual moment-domain density, local topology,
automatic regularity, common columns, and nonsingularity are all proved. -/
theorem nonsingular_affine_of_exact {K : ℕ} (hK : 4 ≤ K)
    (φ₁ φ₂ : Fin K → ℝ → ℝ) (E : Fin K → ℝ → Plane) (ψ₁ ψ₂ : ℝ → ℝ)
    (h₁ : ∀ i, ContinuousOn (φ₁ i) (Icc (-1 : ℝ) 1))
    (h₂ : ∀ i, ContinuousOn (φ₂ i) (Icc (-1 : ℝ) 1))
    (hE : ∀ i, ContinuousOn (E i) (Icc (-1 : ℝ) 1))
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
    (hexact : ExactComputation (featurePairs φ₁ φ₂)
      (fun m => ψ₁ m.1 + ψ₂ m.2) E) :
    ∃ u v : Plane, ∃ c : Fin K → Plane, u.1 * v.2 - v.1 * u.2 ≠ 0 ∧
      ∀ i x, x ∈ Icc (-1 : ℝ) 1 → E i x = c i + φ₁ i x • u + φ₂ i x • v := by
  exact nonsingular_affine_of_exact_and_dense_identification hK φ₁ φ₂ E ψ₁ ψ₂
    h₁ h₂ hE hC₁ hC₂ hind hexact
    (HeterogeneousCompletionDensity.dense_identification hK φ₁ φ₂ ψ₁ ψ₂ h₁ h₂ hind
      hψC₁ hψC₂ halt₁ halt₂ hna)

/-- The manuscript's closed scalar mean interval, defined using the exact
per-node feature image extrema. -/
def closedMeanDomain {K : ℕ} (φ : Fin K → ℝ → ℝ) : Set ℝ :=
  Icc ((∑ i, HeterogeneousCompletionDensity.featureLower (φ i)) / (K : ℝ))
    ((∑ i, HeterogeneousCompletionDensity.featureUpper (φ i)) / (K : ℝ))

/-- Affineness on the actual closed mean interval. -/
def AffineOnMean {K : ℕ} (φ : Fin K → ℝ → ℝ) (ψ : ℝ → ℝ) : Prop :=
  ∃ α β : ℝ, ∀ z ∈ closedMeanDomain φ, ψ z = α + β * z

/-- The original receiver assumption: affine on the full closed mean
interval, or nonaffine on every nonempty open interval in its interior. -/
def ReceiverAdmissible {K : ℕ} (φ : Fin K → ℝ → ℝ) (ψ : ℝ → ℝ) : Prop :=
  AffineOnMean φ ψ ∨
    CompletionSeparation.NoAffineInterval (HeterogeneousCompletionDensity.meanDomain φ) ψ

/-- The full current heterogeneous rigidity theorem under its original
closed-domain hypotheses, in both directions. There are no supplied local
charts, derivative identities, independent tangent anchors, topology axioms,
or density assumptions. The two real common columns are nonsingular. -/
theorem heterogeneous_rigidity {K : ℕ} (hK : 4 ≤ K)
    (φ₁ φ₂ : Fin K → ℝ → ℝ) (E : Fin K → ℝ → Plane) (ψ₁ ψ₂ : ℝ → ℝ)
    (h₁ : ∀ i, ContinuousOn (φ₁ i) (Icc (-1 : ℝ) 1))
    (h₂ : ∀ i, ContinuousOn (φ₂ i) (Icc (-1 : ℝ) 1))
    (hE : ∀ i, ContinuousOn (E i) (Icc (-1 : ℝ) 1))
    (hC₁ : ∀ i, ContDiffOn ℝ 1 (φ₁ i) (Ioo (-1 : ℝ) 1))
    (hC₂ : ∀ i, ContDiffOn ℝ 1 (φ₂ i) (Ioo (-1 : ℝ) 1))
    (hind : ∀ i, GeneralRigidity.NotInAffineLine (Icc (-1 : ℝ) 1) (φ₁ i) (φ₂ i))
    (_hψ₁ : ContinuousOn ψ₁ (closedMeanDomain φ₁))
    (_hψ₂ : ContinuousOn ψ₂ (closedMeanDomain φ₂))
    (hψC₁ : ContDiffOn ℝ 1 ψ₁ (HeterogeneousCompletionDensity.meanDomain φ₁))
    (hψC₂ : ContDiffOn ℝ 1 ψ₂ (HeterogeneousCompletionDensity.meanDomain φ₂))
    (halt₁ : ReceiverAdmissible φ₁ ψ₁) (halt₂ : ReceiverAdmissible φ₂ ψ₂)
    (hn₁ : Operational.NonconstantOn (closedMeanDomain φ₁) ψ₁)
    (hn₂ : Operational.NonconstantOn (closedMeanDomain φ₂) ψ₂)
    (hna : ¬ AffineOnMean φ₁ ψ₁ ∨ ¬ AffineOnMean φ₂ ψ₂) :
    ExactComputation (featurePairs φ₁ φ₂) (fun m => ψ₁ m.1 + ψ₂ m.2) E ↔
      ∃ u v : Plane, ∃ c : Fin K → Plane, u.1 * v.2 - v.1 * u.2 ≠ 0 ∧
        ∀ i x, x ∈ Icc (-1 : ℝ) 1 → E i x = c i + φ₁ i x • u + φ₂ i x • v := by
  constructor
  · intro hexact
    have ha₁ : CompletionSeparation.ReceiverAlternative
        (HeterogeneousCompletionDensity.meanDomain φ₁) ψ₁ :=
      receiver_alternative_of_closed ψ₁ hn₁ halt₁
    have ha₂ : CompletionSeparation.ReceiverAlternative
        (HeterogeneousCompletionDensity.meanDomain φ₂) ψ₂ :=
      receiver_alternative_of_closed ψ₂ hn₂ halt₂
    have hna' : CompletionSeparation.NoAffineInterval
        (HeterogeneousCompletionDensity.meanDomain φ₁) ψ₁ ∨
        CompletionSeparation.NoAffineInterval (HeterogeneousCompletionDensity.meanDomain φ₂) ψ₂ :=
      hna.imp (noAffineInterval_of_closed_nonaffine ψ₁ halt₁)
        (noAffineInterval_of_closed_nonaffine ψ₂ halt₂)
    exact nonsingular_affine_of_exact hK φ₁ φ₂ E ψ₁ ψ₂ h₁ h₂ hE hC₁ hC₂ hind
      hψC₁ hψC₂ ha₁ ha₂ hna' hexact
  · rintro ⟨u, v, c, hdet, haffine⟩
    exact exact_of_nonsingular_affine φ₁ φ₂ E _ u v c hdet haffine

end Analog.HeterogeneousFullRigidity
