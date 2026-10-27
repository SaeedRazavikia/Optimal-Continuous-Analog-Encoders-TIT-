import Analog.PlanarInvariance
import Analog.HeterogeneousCoordinates

/-!
# Continuous local heterogeneous charts from actual moment recovery

The reverse local dependence is proved using planar invariance of domain and
the actual inverse-function chart retaining the first source coordinate.
Encoder differentiability and continuous moment recovery are not hypotheses.
-/

noncomputable section
namespace Analog.HeterogeneousLocalCharts
open Set Filter Topology HeterogeneousRegularity
open RigidityAnalysis (Triple)

def sourceTriples : Set Triple :=
  Icc (-1 : ℝ) 1 ×ˢ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)

def interiorTriples : Set Triple :=
  Ioo (-1 : ℝ) 1 ×ˢ (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1)

theorem interiorTriples_subset : interiorTriples ⊆ sourceTriples := by
  intro p hp
  exact ⟨⟨hp.1.1.le, hp.1.2.le⟩,
    ⟨hp.2.1.1.le, hp.2.1.2.le⟩, ⟨hp.2.2.1.le, hp.2.2.2.le⟩⟩

theorem isOpen_interiorTriples : IsOpen interiorTriples :=
  isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)

/-- On three actual source intervals, moment recovery near a regular triple
implies a continuous reverse factorization on an actual source box. -/
theorem local_chart_of_recovery
    (R M : Triple → Plane) (hR : ContinuousOn R sourceTriples)
    (hM : ContinuousOn M sourceTriples)
    (L : OpenPartialHomeomorph Triple Triple)
    (hL : (L : Triple → Triple) = fun p => (p.1, M p))
    {x y z : ℝ} (hxyz : (x, y, z) ∈ interiorTriples)
    (hsource : (x, y, z) ∈ L.source)
    {B : Set Plane} (hB : B ∈ 𝓝 (M (x, y, z)))
    (hcollision : ∀ p ∈ sourceTriples, ∀ q ∈ sourceTriples,
      M p ∈ B → M q ∈ B → R p = R q → M p = M q) :
    ∃ X ∈ 𝓝 x, ∃ Y ∈ 𝓝 y, ∃ Z ∈ 𝓝 z,
      ∃ V ∈ 𝓝 (M (x, y, z)), ∃ H : Plane → Plane,
        ContinuousOn H V ∧ ∀ x' ∈ X, ∀ y' ∈ Y, ∀ z' ∈ Z,
          R (x', y', z') = H (M (x', y', z')) := by
  obtain ⟨B', hB'B, hB'open, hmB'⟩ := mem_nhds_iff.mp hB
  let N := interiorTriples ∩ M ⁻¹' B'
  have hNopen : IsOpen N :=
    (hM.mono interiorTriples_subset).isOpen_inter_preimage isOpen_interiorTriples hB'open
  let e := L.restr N
  have hesource : e.source = L.source ∩ N := L.restr_source' N hNopen
  have hxs : (x, y, z) ∈ e.source := by
    rw [hesource]
    exact ⟨hsource, hxyz, hmB'⟩
  have hevalid : e.source ⊆ sourceTriples := by
    intro p hp
    rw [hesource] at hp
    exact interiorTriples_subset hp.2.1
  have hecoord : ∀ p ∈ e.source, (e p).2 = M p := by
    intro p _
    change (L p).2 = M p
    rw [hL]
  obtain ⟨T, hT, V, hV, H, hH, hf⟩ :=
    PlanarInvariance.local_factorization_of_coordinates R M e (x, y, z) hxs
      (hR.mono hevalid) hecoord (by
        intro p hp q hq heq
        have hp' := hp
        have hq' := hq
        rw [hesource] at hp' hq'
        exact hcollision p (hevalid hp) q (hevalid hq)
          (hB'B hp'.2.2) (hB'B hq'.2.2) heq)
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hT
  obtain ⟨X, hX, W, hW, hXW⟩ := hT
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hW
  obtain ⟨Y, hY, Z, hZ, hYZ⟩ := hW
  exact ⟨X, hX, Y, hY, Z, hZ, V, hV, H, hH,
    fun x' hx' y' hy' z' hz' => hf _ (hXW ⟨hx', hYZ ⟨hy', hz'⟩⟩)⟩

/-- A sum of three continuous node functions is continuous on the actual
closed source cube. -/
theorem continuousOn_sum (e₁ e₂ e₃ : ℝ → Plane)
    (h₁ : ContinuousOn e₁ (Icc (-1 : ℝ) 1))
    (h₂ : ContinuousOn e₂ (Icc (-1 : ℝ) 1))
    (h₃ : ContinuousOn e₃ (Icc (-1 : ℝ) 1)) :
    ContinuousOn (fun p : Triple => e₁ p.1 + e₂ p.2.1 + e₃ p.2.2) sourceTriples := by
  exact ((h₁.comp continuous_fst.continuousOn (fun _ hp => hp.1)).add
    (h₂.comp (continuous_fst.comp continuous_snd).continuousOn (fun _ hp => hp.2.1))).add
    (h₃.comp (continuous_snd.comp continuous_snd).continuousOn (fun _ hp => hp.2.2))

/-- The actual C¹ feature and continuous encoder assumptions suffice for the
local chart, once local scalar-completion recovery of moments is established. -/
theorem heterogeneous_local_chart
    (a b c d e f : ℝ → ℝ) (E₁ E₂ E₃ : ℝ → Plane)
    (h₁ : ContinuousOn (fun s => (a s, d s)) (Icc (-1 : ℝ) 1))
    (h₂ : ContinuousOn (fun s => (b s, e s)) (Icc (-1 : ℝ) 1))
    (h₃ : ContinuousOn (fun s => (c s, f s)) (Icc (-1 : ℝ) 1))
    (hE₁ : ContinuousOn E₁ (Icc (-1 : ℝ) 1))
    (hE₂ : ContinuousOn E₂ (Icc (-1 : ℝ) 1))
    (hE₃ : ContinuousOn E₃ (Icc (-1 : ℝ) 1))
    {x y z : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hy : y ∈ Ioo (-1 : ℝ) 1) (hz : z ∈ Ioo (-1 : ℝ) 1)
    (hCx : ContDiffAt ℝ 1 (fun s => (a s, d s)) x)
    (hCy : ContDiffAt ℝ 1 (fun s => (b s, e s)) y)
    (hCz : ContDiffAt ℝ 1 (fun s => (c s, f s)) z)
    (hdet : deriv b y * deriv f z - deriv c z * deriv e y ≠ 0)
    {B : Set Plane} (hB : B ∈ 𝓝 (tripleStatistic a b c d e f (x, y, z)))
    (hcollision : ∀ p ∈ sourceTriples, ∀ q ∈ sourceTriples,
      tripleStatistic a b c d e f p ∈ B → tripleStatistic a b c d e f q ∈ B →
      E₁ p.1 + E₂ p.2.1 + E₃ p.2.2 = E₁ q.1 + E₂ q.2.1 + E₃ q.2.2 →
      tripleStatistic a b c d e f p = tripleStatistic a b c d e f q) :
    ∃ X ∈ 𝓝 x, ∃ Y ∈ 𝓝 y, ∃ Z ∈ 𝓝 z,
      ∃ V ∈ 𝓝 (tripleStatistic a b c d e f (x, y, z)), ∃ H : Plane → Plane,
        ContinuousOn H V ∧ ∀ x' ∈ X, ∀ y' ∈ Y, ∀ z' ∈ Z,
          E₁ x' + E₂ y' + E₃ z' =
            H ((a x', d x') + (b y', e y') + (c z', f z')) := by
  obtain ⟨L, hL, hLs⟩ := HeterogeneousCoordinates.coordinates_localHomeomorph hCx hCy hCz hdet
  have hM : ContinuousOn (tripleStatistic a b c d e f) sourceTriples := by
    simpa only [tripleStatistic, tripleSum, Prod.add_def] using
      continuousOn_sum _ _ _ h₁ h₂ h₃
  exact local_chart_of_recovery _ _ (continuousOn_sum E₁ E₂ E₃ hE₁ hE₂ hE₃)
    hM L hL ⟨hx, hy, hz⟩ hLs hB hcollision

end Analog.HeterogeneousLocalCharts
