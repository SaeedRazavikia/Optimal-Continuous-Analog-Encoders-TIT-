import Analog.GeneralRigidity
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.TietzeExtension

/-!
# Smoothing a local additive-statistic factorization

The smoothing step differentiates a convolution kernel, not the original
continuous receiver. The lemmas below state explicitly the local translation
identity used by that step. They do not assert that exactness alone supplies
this identity; that is the separate topological/local-chart obligation.
-/

noncomputable section
open Set Filter Topology MeasureTheory ContinuousLinearMap
open scoped Convolution ContDiff
namespace Analog.EncoderRegularity

abbrev Plane := ℝ × ℝ
local notation "μ" => (MeasureTheory.Measure.addHaar : Measure Plane)

/-- A smooth compactly supported averaging kernel of any positive radius. -/
theorem normalized_kernel (D : ℝ) (hD : 0 < D) :
    ∃ ρ : Plane → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      Function.support ρ = Metric.ball 0 D ∧ ∫ w, ρ w ∂μ = 1 := by
  refine ⟨ExistsContDiffBumpBase.w D, ?_,
    ExistsContDiffBumpBase.w_compact_support Plane hD,
    ExistsContDiffBumpBase.w_support Plane hD,
    ExistsContDiffBumpBase.w_integral Plane hD⟩
  rw [ExistsContDiffBumpBase.w_def]
  exact ((ExistsContDiffBumpBase.u_smooth Plane).comp
    (contDiff_id.const_smul D⁻¹)).const_smul _

/-- A continuous factorization with locally constant translation differences
forces regularity of the encoder. This is the manuscript's averaging argument:
the convolution is smooth before it is composed with the preprocessing curve. -/
theorem contDiffAt_of_shift_difference {γ : ℝ → Plane} {e : ℝ → ℝ}
    {H : Plane → ℝ} {x₀ D : ℝ} {U : Set ℝ}
    (hH : Continuous H) (hD : 0 < D) (hU : U ∈ 𝓝 x₀)
    (hγ : ContDiffAt ℝ 1 γ x₀)
    (hshift : ∀ x ∈ U, ∀ w ∈ Metric.ball (0 : Plane) D,
      e x - e x₀ = H (γ x - w) - H (γ x₀ - w)) :
    ContDiffAt ℝ 1 e x₀ := by
  obtain ⟨ρ, hρsmooth, hρsupport, hρball, hρone⟩ := normalized_kernel D hD
  let B : Plane → ℝ := ρ ⋆[lsmul ℝ ℝ, μ] H
  have hB : ContDiff ℝ 1 B :=
    hρsupport.contDiff_convolution_left (lsmul ℝ ℝ)
      (hρsmooth.of_le (by norm_num)) hH.locallyIntegrable
  have hint : ∀ p : Plane, Integrable (fun w => ρ w * H (p - w)) μ := by
    intro p
    exact hρsupport.convolutionExists_left (lsmul ℝ ℝ)
      hρsmooth.continuous hH.locallyIntegrable p
  have heq : e =ᶠ[𝓝 x₀] fun x => B (γ x) - B (γ x₀) + e x₀ := by
    filter_upwards [hU] with x hx
    have hi : (∫ w, ρ w * (e x - e x₀) ∂μ) =
        ∫ w, ρ w * H (γ x - w) - ρ w * H (γ x₀ - w) ∂μ := by
      apply integral_congr_ae
      filter_upwards with w
      by_cases hw : w ∈ Function.support ρ
      · rw [hshift x hx w (hρball ▸ hw)]
        ring
      · have hz : ρ w = 0 := by simpa [Function.mem_support] using hw
        simp [hz]
    rw [integral_mul_const, hρone, one_mul,
      integral_sub (hint (γ x)) (hint (γ x₀))] at hi
    change e x - e x₀ = B (γ x) - B (γ x₀) at hi
    linarith
  exact ContDiffAt.congr_of_eventuallyEq
    (((hB.contDiffAt.comp x₀ hγ).sub contDiffAt_const).add contDiffAt_const) heq

/-- A local factorization over a neighborhood of pair-statistic translations
implies the difference identity needed for smoothing. The offset function C
is not differentiated and need not be measurable. -/
theorem contDiffAt_of_local_factorization {γ : ℝ → Plane} {e : ℝ → ℝ}
    {H C : Plane → ℝ} {x₀ D : ℝ} {U : Set ℝ}
    (hH : Continuous H) (hD : 0 < D) (hU : U ∈ 𝓝 x₀)
    (hx₀ : x₀ ∈ U) (hγ : ContDiffAt ℝ 1 γ x₀)
    (hfactor : ∀ x ∈ U, ∀ w ∈ Metric.ball (0 : Plane) D,
      e x + C w = H (γ x - w)) :
    ContDiffAt ℝ 1 e x₀ := by
  apply contDiffAt_of_shift_difference hH hD hU hγ
  intro x hx w hw
  have h₁ := hfactor x hx w hw
  have h₂ := hfactor x₀ hx₀ w hw
  linarith



/-- Automatic regularity from a receiver defined only on its local open chart.
We construct a continuous extension on a smaller closed ball using Tietze,
choose an actual compact averaging kernel, and apply the convolution proof.
Thus no smooth receiver, global receiver, or averaging identity is assumed. -/
theorem contDiffAt_of_local_chart {γ : ℝ → Plane} {e : ℝ → ℝ}
    {H C : Plane → ℝ} {x₀ : ℝ} {w₀ : Plane}
    {U : Set ℝ} {V B : Set Plane}
    (hU : U ∈ 𝓝 x₀) (hV : V ∈ 𝓝 w₀)
    (hB : B ∈ 𝓝 (γ x₀ + w₀)) (hH : ContinuousOn H B)
    (hγ : ContDiffAt ℝ 1 γ x₀)
    (hfactor : ∀ x ∈ U, ∀ w ∈ V, e x + C w = H (γ x + w)) :
    ContDiffAt ℝ 1 e x₀ := by
  obtain ⟨r, hr, hrB⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hB
  obtain ⟨v, hv, hvV⟩ := Metric.mem_nhds_iff.mp hV
  let S : Set Plane := Metric.closedBall (γ x₀ + w₀) r
  let f : C(S, ℝ) := ⟨fun p => H p, (hH.mono hrB).restrict⟩
  obtain ⟨H', hH'⟩ := f.exists_restrict_eq (show IsClosed S from Metric.isClosed_closedBall)
  have hext : ∀ p ∈ S, H' p = H p := by
    intro p hp
    exact congrArg (fun g : C(S, ℝ) => g ⟨p, hp⟩) hH'
  let D := min (r / 2) v
  have hD : 0 < D := lt_min (by positivity) hv
  let U' : Set ℝ := U ∩ γ ⁻¹' Metric.ball (γ x₀) (r / 2)
  have hU' : U' ∈ 𝓝 x₀ :=
    inter_mem hU (hγ.continuousAt (Metric.ball_mem_nhds _ (by positivity)))
  have hargs : ∀ x ∈ U', ∀ w ∈ Metric.ball (0 : Plane) D,
      γ x + w₀ - w ∈ S := by
    intro x hx w hw
    have hx' : ‖γ x - γ x₀‖ < r / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx.2
    have hw' : ‖w‖ < D := by simpa [Metric.mem_ball] using hw
    change dist (γ x + w₀ - w) (γ x₀ + w₀) ≤ r
    rw [dist_eq_norm]
    have heq : γ x + w₀ - w - (γ x₀ + w₀) = (γ x - γ x₀) - w := by abel
    rw [heq]
    exact (norm_sub_le _ _).trans (by have := min_le_left (r / 2) v; dsimp [D] at hw'; linarith)
  have hwV : ∀ w ∈ Metric.ball (0 : Plane) D, w₀ - w ∈ V := by
    intro w hw
    apply hvV
    have hw' : ‖w‖ < D := by simpa [Metric.mem_ball] using hw
    change dist (w₀ - w) w₀ < v
    rw [dist_eq_norm]
    have heq : w₀ - w - w₀ = -w := by abel
    rw [heq, norm_neg]
    exact lt_of_lt_of_le hw' (min_le_right _ _)
  apply contDiffAt_of_local_factorization (γ := fun x => γ x + w₀)
    (H := H') (C := fun w => C (w₀ - w)) H'.continuous hD hU'
    (mem_of_mem_nhds hU') (hγ.add contDiffAt_const)
  intro x hx w hw
  rw [hext _ (hargs x hx w hw)]
  convert hfactor x hx.1 (w₀ - w) (hwV w hw) using 1
  abel_nf



/-- A genuine local pair-statistic inverse converts a source-box triple
factorization into the translation identity. Combined with the preceding
result, this proves automatic C1 regularity at the first transmitter input. -/
theorem contDiffAt_of_triple_factorization {φ₁ φ₂ e : ℝ → ℝ}
    {H : Plane → ℝ} {x₀ y₀ z₀ : ℝ}
    {X Y Z : Set ℝ} {B : Set Plane}
    (hX : X ∈ 𝓝 x₀) (hY : Y ∈ 𝓝 y₀) (hZ : Z ∈ 𝓝 z₀)
    (hB : B ∈ 𝓝 ((φ₁ x₀, φ₂ x₀) + (φ₁ y₀, φ₂ y₀) + (φ₁ z₀, φ₂ z₀)))
    (hH : ContinuousOn H B)
    (hγx : ContDiffAt ℝ 1 (fun s => (φ₁ s, φ₂ s)) x₀)
    (hγy : ContDiffAt ℝ 1 (fun s => (φ₁ s, φ₂ s)) y₀)
    (hγz : ContDiffAt ℝ 1 (fun s => (φ₁ s, φ₂ s)) z₀)
    (hdet : GeneralRigidity.tangentDet φ₁ φ₂ y₀ z₀ ≠ 0)
    (hfactor : ∀ x ∈ X, ∀ y ∈ Y, ∀ z ∈ Z,
      e x + e y + e z = H ((φ₁ x, φ₂ x) + (φ₁ y, φ₂ y) + (φ₁ z, φ₂ z))) :
    ContDiffAt ℝ 1 e x₀ := by
  obtain ⟨g, hg, hgp, hgr⟩ := GeneralRigidity.pairStatistic_local_section
    (hγy.fst.hasStrictDerivAt le_rfl) (hγz.fst.hasStrictDerivAt le_rfl)
    (hγy.snd.hasStrictDerivAt le_rfl) (hγz.snd.hasStrictDerivAt le_rfl) hdet
  let w₀ := GeneralRigidity.pairStatistic φ₁ φ₂ (y₀, z₀)
  have hgc : Tendsto g (𝓝 w₀) (𝓝 (y₀, z₀)) := by
    simpa only [ContinuousAt, hgp] using hg.continuousAt
  let V : Set Plane := {w | GeneralRigidity.pairStatistic φ₁ φ₂ (g w) = w} ∩
    g ⁻¹' (Y ×ˢ Z)
  have hV : V ∈ 𝓝 w₀ := inter_mem hgr (hgc (prod_mem_nhds hY hZ))
  apply contDiffAt_of_local_chart (γ := fun s => (φ₁ s, φ₂ s))
    (C := fun w => e (g w).1 + e (g w).2) hX hV
    (show B ∈ 𝓝 ((φ₁ x₀, φ₂ x₀) + w₀) from by
      simpa [w₀, GeneralRigidity.pairStatistic, Prod.add_def, add_assoc] using hB) hH hγx
  intro x hx w hw
  have hsum : (φ₁ (g w).1, φ₂ (g w).1) + (φ₁ (g w).2, φ₂ (g w).2) = w := hw.1
  calc
    e x + (e (g w).1 + e (g w).2) = e x + e (g w).1 + e (g w).2 := by ring
    _ = H ((φ₁ x, φ₂ x) + (φ₁ (g w).1, φ₂ (g w).1) +
        (φ₁ (g w).2, φ₂ (g w).2)) := hfactor x hx _ hw.2.1 _ hw.2.2
    _ = H ((φ₁ x, φ₂ x) + w) := by rw [add_assoc, hsum]



/-- The local continuous planar factorizations produced by the topological
part of rigidity, stated on source boxes at regular triples. -/
def LocalPlanarCharts (domain : Set ℝ) (φ₁ φ₂ : ℝ → ℝ) (E : ℝ → Plane) : Prop :=
  ∀ x ∈ domain, ∀ y ∈ domain, ∀ z ∈ domain,
    GeneralRigidity.tangentDet φ₁ φ₂ y z ≠ 0 →
    ∃ X ∈ 𝓝 x, ∃ Y ∈ 𝓝 y, ∃ Z ∈ 𝓝 z,
    ∃ B ∈ 𝓝 ((φ₁ x, φ₂ x) + (φ₁ y, φ₂ y) + (φ₁ z, φ₂ z)),
    ∃ H : Plane → Plane, ContinuousOn H B ∧
      ∀ x' ∈ X, ∀ y' ∈ Y, ∀ z' ∈ Z,
        E x' + E y' + E z' =
          H ((φ₁ x', φ₂ x') + (φ₁ y', φ₂ y') + (φ₁ z', φ₂ z'))

/-- Actual source-box factorizations give the local statistic-fiber hypothesis
of the general differential rigidity theorem. -/
theorem local_fibers_of_charts {domain : Set ℝ} {φ₁ φ₂ : ℝ → ℝ} {E : ℝ → Plane}
    (hf : LocalPlanarCharts domain φ₁ φ₂ E) :
    GeneralRigidity.LocalPlanarStatisticFibers domain φ₁ φ₂ E := by
  intro x hx y hy z hz hd
  obtain ⟨X, hX, Y, hY, Z, hZ, B, hB, H, hH, hfactor⟩ := hf x hx y hy z hz hd
  refine ⟨X ×ˢ (Y ×ˢ Z), prod_mem_nhds hX (prod_mem_nhds hY hZ), ?_⟩
  intro p hp q hq hm
  rw [hfactor _ hp.1 _ hp.2.1 _ hp.2.2, hfactor _ hq.1 _ hq.2.1 _ hq.2.2]
  exact congrArg H hm

/-- The automatic regularity conclusion on the interval interior. A merely
continuous chart receiver suffices; no derivative of the encoder is assumed. -/
theorem contDiffOn_of_local_charts {a b : ℝ} {φ₁ φ₂ : ℝ → ℝ} {E : ℝ → Plane}
    (h₁ : ContinuousOn φ₁ (Icc a b)) (h₂ : ContinuousOn φ₂ (Icc a b))
    (hC₁ : ContDiffOn ℝ 1 φ₁ (Ioo a b)) (hC₂ : ContDiffOn ℝ 1 φ₂ (Ioo a b))
    (hind : GeneralRigidity.NotInAffineLine (Icc a b) φ₁ φ₂)
    (hf : LocalPlanarCharts (Ioo a b) φ₁ φ₂ E) :
    ContDiffOn ℝ 1 E (Ioo a b) := by
  obtain ⟨y, hy, z, hz, hd⟩ := GeneralRigidity.independent_tangents h₁ h₂
    hC₁.differentiableOn_one hC₂.differentiableOn_one hind
  have hγ : ∀ s ∈ Ioo a b, ContDiffAt ℝ 1 (fun t => (φ₁ t, φ₂ t)) s := by
    intro s hs
    exact ((hC₁ s hs).contDiffAt (Ioo_mem_nhds hs.1 hs.2)).prodMk
      ((hC₂ s hs).contDiffAt (Ioo_mem_nhds hs.1 hs.2))
  intro x hx
  obtain ⟨X, hX, Y, hY, Z, hZ, B, hB, H, hH, hfactor⟩ := hf x hx y hy z hz hd
  have hfst : ContDiffAt ℝ 1 (fun s => (E s).1) x := by
    apply contDiffAt_of_triple_factorization hX hY hZ hB hH.fst
      (hγ x hx) (hγ y hy) (hγ z hz) hd
    intro x' hx' y' hy' z' hz'
    exact congrArg Prod.fst (hfactor x' hx' y' hy' z' hz')
  have hsnd : ContDiffAt ℝ 1 (fun s => (E s).2) x := by
    apply contDiffAt_of_triple_factorization hX hY hZ hB hH.snd
      (hγ x hx) (hγ y hy) (hγ z hz) hd
    intro x' hx' y' hy' z' hz'
    exact congrArg Prod.snd (hfactor x' hx' y' hy' z' hz')
  exact (hfst.prodMk hsnd).contDiffWithinAt

/-- The full analytic chain from continuous local factorizations to an affine
representation: localization, convolution smoothing, inverse-function charts,
differential kernels, integration, and endpoint extension. Only the preceding
topological production of the stated charts is left as a hypothesis. -/
theorem planar_affine_of_local_charts {a b : ℝ} {φ₁ φ₂ : ℝ → ℝ} {E : ℝ → Plane}
    (h₁ : ContinuousOn φ₁ (Icc a b)) (h₂ : ContinuousOn φ₂ (Icc a b))
    (hE : ContinuousOn E (Icc a b))
    (hC₁ : ContDiffOn ℝ 1 φ₁ (Ioo a b)) (hC₂ : ContDiffOn ℝ 1 φ₂ (Ioo a b))
    (hind : GeneralRigidity.NotInAffineLine (Icc a b) φ₁ φ₂)
    (hf : LocalPlanarCharts (Ioo a b) φ₁ φ₂ E) :
    ∃ c u v : Plane, ∀ x ∈ Icc a b, E x = c + φ₁ x • u + φ₂ x • v := by
  exact GeneralRigidity.planar_affine_of_local_fibers h₁ h₂ hE hC₁ hC₂
    (contDiffOn_of_local_charts h₁ h₂ hC₁ hC₂ hind hf).differentiableOn_one
    hind (local_fibers_of_charts hf)



/-- Scalar chart factorizations are required only at regular triples whose
statistic lies in the identifying subset O. -/
def DenseScalarCharts (φ₁ φ₂ e : ℝ → ℝ) (O : Set Plane) : Prop :=
  ∀ x ∈ Ioo (-1 : ℝ) 1, ∀ y ∈ Ioo (-1 : ℝ) 1, ∀ z ∈ Ioo (-1 : ℝ) 1,
    GeneralRigidity.tangentDet φ₁ φ₂ y z ≠ 0 →
    GeneralRigidity.tripleStatistic φ₁ φ₂ (x, y, z) ∈ O →
    ∃ X ∈ 𝓝 x, ∃ Y ∈ 𝓝 y, ∃ Z ∈ 𝓝 z,
    ∃ B ∈ 𝓝 ((φ₁ x, φ₂ x) + (φ₁ y, φ₂ y) + (φ₁ z, φ₂ z)),
    ∃ H : Plane → ℝ, ContinuousOn H B ∧
      ∀ x' ∈ X, ∀ y' ∈ Y, ∀ z' ∈ Z,
        e x' + e y' + e z' =
          H ((φ₁ x', φ₂ x') + (φ₁ y', φ₂ y') + (φ₁ z', φ₂ z'))

/-- Dense identification is enough for automatic regularity at every input:
for each first input, the pair submersion supplies nearby identifying anchors. -/
theorem contDiffOn_of_dense_scalar_charts {φ₁ φ₂ e : ℝ → ℝ} {O : Set Plane}
    (h₁ : ContinuousOn φ₁ (Icc (-1 : ℝ) 1))
    (h₂ : ContinuousOn φ₂ (Icc (-1 : ℝ) 1))
    (hC₁ : ContDiffOn ℝ 1 φ₁ (Ioo (-1 : ℝ) 1))
    (hC₂ : ContDiffOn ℝ 1 φ₂ (Ioo (-1 : ℝ) 1))
    (hind : GeneralRigidity.NotInAffineLine (Icc (-1 : ℝ) 1) φ₁ φ₂)
    (hdense : GeneralRigidity.regularTripleImage φ₁ φ₂ ⊆ closure O)
    (hf : DenseScalarCharts φ₁ φ₂ e O) : ContDiffOn ℝ 1 e (Ioo (-1 : ℝ) 1) := by
  obtain ⟨y, hy, z, hz, hd⟩ := GeneralRigidity.independent_tangents h₁ h₂
    hC₁.differentiableOn_one hC₂.differentiableOn_one hind
  have hγ : ∀ s ∈ Ioo (-1 : ℝ) 1, ContDiffAt ℝ 1 (fun t => (φ₁ t, φ₂ t)) s := by
    intro s hs
    exact ((hC₁ s hs).contDiffAt (Ioo_mem_nhds hs.1 hs.2)).prodMk
      ((hC₂ s hs).contDiffAt (Ioo_mem_nhds hs.1 hs.2))
  intro x hx
  have hcl := GeneralRigidity.regular_pair_identifying_closure hC₁ hC₂ hx hy hz hd hdense
  obtain ⟨q, _, hq⟩ := mem_closure_iff_nhds.mp hcl Set.univ Filter.univ_mem
  obtain ⟨X, hX, Y, hY, Z, hZ, B, hB, H, hH, hfactor⟩ :=
    hf x hx q.1 hq.1.1.1 q.2 hq.1.1.2 hq.1.2 hq.2
  exact (contDiffAt_of_triple_factorization hX hY hZ hB hH (hγ x hx)
    (hγ q.1 hq.1.1.1) (hγ q.2 hq.1.1.2) hq.1.2 hfactor).contDiffWithinAt

/-- The entire scalar analytic rigidity proof with the manuscript's dense
identifying set. The only remaining condition is the topologically obtained
local continuous factorization, and it is assumed only at identifying points. -/
theorem scalar_affine_of_dense_charts {φ₁ φ₂ e : ℝ → ℝ} {O : Set Plane}
    (h₁ : ContinuousOn φ₁ (Icc (-1 : ℝ) 1))
    (h₂ : ContinuousOn φ₂ (Icc (-1 : ℝ) 1))
    (he : ContinuousOn e (Icc (-1 : ℝ) 1))
    (hC₁ : ContDiffOn ℝ 1 φ₁ (Ioo (-1 : ℝ) 1))
    (hC₂ : ContDiffOn ℝ 1 φ₂ (Ioo (-1 : ℝ) 1))
    (hind : GeneralRigidity.NotInAffineLine (Icc (-1 : ℝ) 1) φ₁ φ₂)
    (hdense : GeneralRigidity.regularTripleImage φ₁ φ₂ ⊆ closure O)
    (hf : DenseScalarCharts φ₁ φ₂ e O) :
    ∃ c α β : ℝ, ∀ x ∈ Icc (-1 : ℝ) 1, e x = c + α * φ₁ x + β * φ₂ x := by
  have hCe := contDiffOn_of_dense_scalar_charts h₁ h₂ hC₁ hC₂ hind hdense hf
  have hs₁ : ∀ t ∈ Ioo (-1 : ℝ) 1, HasStrictDerivAt φ₁ (deriv φ₁ t) t := by
    intro t ht
    exact ((hC₁ t ht).contDiffAt (Ioo_mem_nhds ht.1 ht.2)).hasStrictDerivAt le_rfl
  have hs₂ : ∀ t ∈ Ioo (-1 : ℝ) 1, HasStrictDerivAt φ₂ (deriv φ₂ t) t := by
    intro t ht
    exact ((hC₂ t ht).contDiffAt (Ioo_mem_nhds ht.1 ht.2)).hasStrictDerivAt le_rfl
  have hde : ∀ t ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ e t := by
    intro t ht
    exact (hCe.differentiableOn_one t ht).differentiableAt (Ioo_mem_nhds ht.1 ht.2)
  apply GeneralRigidity.scalar_affine_of_dense_determinants h₁ h₂ he hC₁ hC₂ hCe hind hdense
  intro x hx y hy z hz hd hp
  obtain ⟨X, hX, Y, hY, Z, hZ, B, hB, H, hH, hfactor⟩ := hf x hx y hy z hz hd hp
  apply GeneralRigidity.determinant_of_local_fibers
    (hs₁ x hx).hasDerivAt.differentiableAt (hs₂ x hx).hasDerivAt.differentiableAt
    (hs₁ y hy) (hs₁ z hz) (hs₂ y hy) (hs₂ z hz)
    (hde x hx) (hde y hy) (hde z hz) hd
    (U := X ×ˢ (Y ×ˢ Z)) (prod_mem_nhds hX (prod_mem_nhds hY hZ))
  intro p hp q hq hm
  change e p.1 + e p.2.1 + e p.2.2 = e q.1 + e q.2.1 + e q.2.2
  rw [hfactor _ hp.1 _ hp.2.1 _ hp.2.2, hfactor _ hq.1 _ hq.2.1 _ hq.2.2]
  exact congrArg H hm

/-- Planar chart factorizations only at identifying regular triples. -/
def DensePlanarCharts (φ₁ φ₂ : ℝ → ℝ) (E : ℝ → Plane) (O : Set Plane) : Prop :=
  ∀ x ∈ Ioo (-1 : ℝ) 1, ∀ y ∈ Ioo (-1 : ℝ) 1, ∀ z ∈ Ioo (-1 : ℝ) 1,
    GeneralRigidity.tangentDet φ₁ φ₂ y z ≠ 0 →
    GeneralRigidity.tripleStatistic φ₁ φ₂ (x, y, z) ∈ O →
    ∃ X ∈ 𝓝 x, ∃ Y ∈ 𝓝 y, ∃ Z ∈ 𝓝 z,
    ∃ B ∈ 𝓝 ((φ₁ x, φ₂ x) + (φ₁ y, φ₂ y) + (φ₁ z, φ₂ z)),
    ∃ H : Plane → Plane, ContinuousOn H B ∧
      ∀ x' ∈ X, ∀ y' ∈ Y, ∀ z' ∈ Z,
        E x' + E y' + E z' =
          H ((φ₁ x', φ₂ x') + (φ₁ y', φ₂ y') + (φ₁ z', φ₂ z'))

/-- General planar affine rigidity from charts on a dense identifying set.
This removes the stronger all-regular-triples premise of LocalPlanarCharts.
Automatic regularity and dense propagation are both derived. -/
theorem planar_affine_of_dense_charts {φ₁ φ₂ : ℝ → ℝ} {E : ℝ → Plane} {O : Set Plane}
    (h₁ : ContinuousOn φ₁ (Icc (-1 : ℝ) 1))
    (h₂ : ContinuousOn φ₂ (Icc (-1 : ℝ) 1))
    (hE : ContinuousOn E (Icc (-1 : ℝ) 1))
    (hC₁ : ContDiffOn ℝ 1 φ₁ (Ioo (-1 : ℝ) 1))
    (hC₂ : ContDiffOn ℝ 1 φ₂ (Ioo (-1 : ℝ) 1))
    (hind : GeneralRigidity.NotInAffineLine (Icc (-1 : ℝ) 1) φ₁ φ₂)
    (hdense : GeneralRigidity.regularTripleImage φ₁ φ₂ ⊆ closure O)
    (hf : DensePlanarCharts φ₁ φ₂ E O) :
    ∃ c u v : Plane, ∀ x ∈ Icc (-1 : ℝ) 1, E x = c + φ₁ x • u + φ₂ x • v := by
  have hfx : DenseScalarCharts φ₁ φ₂ (fun s => (E s).1) O := by
    intro x hx y hy z hz hd hp
    obtain ⟨X, hX, Y, hY, Z, hZ, B, hB, H, hH, hfactor⟩ := hf x hx y hy z hz hd hp
    refine ⟨X, hX, Y, hY, Z, hZ, B, hB, fun p => (H p).1, hH.fst, ?_⟩
    intro x' hx' y' hy' z' hz'
    exact congrArg Prod.fst (hfactor x' hx' y' hy' z' hz')
  have hfy : DenseScalarCharts φ₁ φ₂ (fun s => (E s).2) O := by
    intro x hx y hy z hz hd hp
    obtain ⟨X, hX, Y, hY, Z, hZ, B, hB, H, hH, hfactor⟩ := hf x hx y hy z hz hd hp
    refine ⟨X, hX, Y, hY, Z, hZ, B, hB, fun p => (H p).2, hH.snd, ?_⟩
    intro x' hx' y' hy' z' hz'
    exact congrArg Prod.snd (hfactor x' hx' y' hy' z' hz')
  obtain ⟨cx, ux, vx, hx⟩ := scalar_affine_of_dense_charts h₁ h₂ hE.fst hC₁ hC₂ hind hdense hfx
  obtain ⟨cy, uy, vy, hy⟩ := scalar_affine_of_dense_charts h₁ h₂ hE.snd hC₁ hC₂ hind hdense hfy
  refine ⟨(cx, cy), (ux, uy), (vx, vy), ?_⟩
  intro x hxi
  apply Prod.ext
  · simpa [mul_comm] using hx x hxi
  · simpa [mul_comm] using hy x hxi

end Analog.EncoderRegularity
