import Analog.EncoderRegularity
import Analog.HeterogeneousRigidity

/-!
# Local regularity for distinct transmitter feature curves

The pair inverse and convolution regularization below allow three different
feature curves and three different continuous encoders. The local continuous
factorization is an explicit hypothesis in this analytic layer. The subsequent
`HeterogeneousLocalCharts` and `HeterogeneousFullRigidity` modules derive it
from exact computation using the separately proved planar topology.
No differentiability of the factorizing receiver or encoders is assumed by
the smoothing theorem.
-/

noncomputable section
open Set Filter Topology
namespace Analog.HeterogeneousRegularity
open GeneralRigidity RigidityAnalysis

abbrev Plane := ℝ × ℝ

/-- Two different nodes' unnormalized feature sums. -/
def pairStatistic (a b c d : ℝ → ℝ) (p : Plane) : Plane :=
  (a p.1 + b p.2, c p.1 + d p.2)

/-- The derivative of the actual heterogeneous pair map. -/
theorem pairStatistic_hasStrictFDerivAt {a b c d : ℝ → ℝ}
    {y z ay bz cy dz : ℝ}
    (ha : HasStrictDerivAt a ay y) (hb : HasStrictDerivAt b bz z)
    (hc : HasStrictDerivAt c cy y) (hd : HasStrictDerivAt d dz z) :
    HasStrictFDerivAt (pairStatistic a b c d) (pairDerivative ay bz cy dz) (y, z) := by
  have hfst : HasStrictFDerivAt (fun p : Plane => p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (y, z) := hasStrictFDerivAt_fst
  have hsnd : HasStrictFDerivAt (fun p : Plane => p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (y, z) := hasStrictFDerivAt_snd
  have h₁ := (ha.hasStrictFDerivAt.comp (y, z) hfst).add
    (hb.hasStrictFDerivAt.comp (y, z) hsnd)
  have h₂ := (hc.hasStrictFDerivAt.comp (y, z) hfst).add
    (hd.hasStrictFDerivAt.comp (y, z) hsnd)
  convert h₁.prodMk h₂ using 1
  ext <;> simp [pairDerivative, ContinuousLinearMap.comp_apply]

/-- The genuine inverse-function theorem for different feature curves. -/
theorem pairStatistic_local_section {a b c d : ℝ → ℝ}
    {y z ay bz cy dz : ℝ}
    (ha : HasStrictDerivAt a ay y) (hb : HasStrictDerivAt b bz z)
    (hc : HasStrictDerivAt c cy y) (hd : HasStrictDerivAt d dz z)
    (hdet : ay * dz - bz * cy ≠ 0) :
    ∃ g : Plane → Plane,
      DifferentiableAt ℝ g (pairStatistic a b c d (y, z)) ∧
      g (pairStatistic a b c d (y, z)) = (y, z) ∧
      ∀ᶠ p in 𝓝 (pairStatistic a b c d (y, z)), pairStatistic a b c d (g p) = p := by
  have hd' : HasStrictFDerivAt (pairStatistic a b c d)
      (pairDerivativeEquiv ay bz cy dz hdet : Plane →L[ℝ] Plane) (y, z) := by
    simpa only [pairDerivativeEquiv_coe] using pairStatistic_hasStrictFDerivAt ha hb hc hd
  exact ⟨hd'.localInverse (pairStatistic a b c d)
      (pairDerivativeEquiv ay bz cy dz hdet) (y, z),
    hd'.to_localInverse.hasFDerivAt.differentiableAt,
    hd'.localInverse_apply_image, hd'.eventually_right_inverse⟩

/-- Three distinct encoders factorizing through three distinct C¹ curves
force automatic C¹ regularity at the first transmitter input. -/
theorem contDiffAt_of_triple_factorization
    {φ₁x φ₂x φ₁y φ₂y φ₁z φ₂z ex ey ez : ℝ → ℝ}
    {H : Plane → ℝ} {x₀ y₀ z₀ : ℝ}
    {X Y Z : Set ℝ} {B : Set Plane}
    (hX : X ∈ 𝓝 x₀) (hY : Y ∈ 𝓝 y₀) (hZ : Z ∈ 𝓝 z₀)
    (hB : B ∈ 𝓝 ((φ₁x x₀, φ₂x x₀) + (φ₁y y₀, φ₂y y₀) + (φ₁z z₀, φ₂z z₀)))
    (hH : ContinuousOn H B)
    (hγx : ContDiffAt ℝ 1 (fun s => (φ₁x s, φ₂x s)) x₀)
    (hγy : ContDiffAt ℝ 1 (fun s => (φ₁y s, φ₂y s)) y₀)
    (hγz : ContDiffAt ℝ 1 (fun s => (φ₁z s, φ₂z s)) z₀)
    (hdet : deriv φ₁y y₀ * deriv φ₂z z₀ - deriv φ₁z z₀ * deriv φ₂y y₀ ≠ 0)
    (hfactor : ∀ x ∈ X, ∀ y ∈ Y, ∀ z ∈ Z,
      ex x + ey y + ez z = H ((φ₁x x, φ₂x x) + (φ₁y y, φ₂y y) + (φ₁z z, φ₂z z))) :
    ContDiffAt ℝ 1 ex x₀ := by
  obtain ⟨g, hg, hgp, hgr⟩ := pairStatistic_local_section
    (hγy.fst.hasStrictDerivAt le_rfl) (hγz.fst.hasStrictDerivAt le_rfl)
    (hγy.snd.hasStrictDerivAt le_rfl) (hγz.snd.hasStrictDerivAt le_rfl) hdet
  let w₀ := pairStatistic φ₁y φ₁z φ₂y φ₂z (y₀, z₀)
  have hgc : Tendsto g (𝓝 w₀) (𝓝 (y₀, z₀)) := by
    simpa only [ContinuousAt, hgp] using hg.continuousAt
  let V : Set Plane := {w | pairStatistic φ₁y φ₁z φ₂y φ₂z (g w) = w} ∩
    g ⁻¹' (Y ×ˢ Z)
  have hV : V ∈ 𝓝 w₀ := inter_mem hgr (hgc (prod_mem_nhds hY hZ))
  apply EncoderRegularity.contDiffAt_of_local_chart (γ := fun x => (φ₁x x, φ₂x x))
    (C := fun w => ey (g w).1 + ez (g w).2) hX hV
    (show B ∈ 𝓝 ((φ₁x x₀, φ₂x x₀) + w₀) from by
      simpa [w₀, pairStatistic, Prod.add_def, add_assoc] using hB) hH hγx
  intro x hx w hw
  have hsum : (φ₁y (g w).1, φ₂y (g w).1) + (φ₁z (g w).2, φ₂z (g w).2) = w := hw.1
  calc
    ex x + (ey (g w).1 + ez (g w).2) = ex x + ey (g w).1 + ez (g w).2 := by ring
    _ = H ((φ₁x x, φ₂x x) + (φ₁y (g w).1, φ₂y (g w).1) +
        (φ₁z (g w).2, φ₂z (g w).2)) := hfactor x hx _ hw.2.1 _ hw.2.2
    _ = H ((φ₁x x, φ₂x x) + w) := by rw [add_assoc, hsum]

/-- Sum of three potentially different scalar functions. -/
def tripleSum (f g h : ℝ → ℝ) (p : Triple) : ℝ :=
  f p.1 + g p.2.1 + h p.2.2

/-- Both heterogeneous partial statistics on the actual source triple. -/
def tripleStatistic (a b c d e f : ℝ → ℝ) (p : Triple) : Plane :=
  (tripleSum a b c p, tripleSum d e f p)

/-- Derivative of the heterogeneous scalar triple sum. -/
theorem tripleSum_hasFDerivAt {f g h : ℝ → ℝ} {x y z dx dy dz : ℝ}
    (hx : HasDerivAt f dx x) (hy : HasDerivAt g dy y) (hz : HasDerivAt h dz z) :
    HasFDerivAt (tripleSum f g h) (slopeRow dx dy dz) (x, y, z) := by
  have h1 := hx.comp_hasFDerivAt (𝕜 := ℝ) (x, y, z) hasFDerivAt_fst
  have h2 := hy.comp_hasFDerivAt (𝕜 := ℝ) (x, y, z)
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, y, z))).fst
  have h3 := hz.comp_hasFDerivAt (𝕜 := ℝ) (x, y, z)
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, y, z))).snd
  exact (h1.add h2).add h3

/-- A pair inverse supplies a triple right section with first input fixed. -/
theorem triple_section_of_pair {a b c d e f : ℝ → ℝ} {x y z : ℝ}
    {g : Plane → Plane}
    (hg : DifferentiableAt ℝ g (pairStatistic b c e f (y, z)))
    (hgp : g (pairStatistic b c e f (y, z)) = (y, z))
    (hgr : ∀ᶠ p in 𝓝 (pairStatistic b c e f (y, z)), pairStatistic b c e f (g p) = p) :
    ∃ r : Plane → Triple,
      DifferentiableAt ℝ r (tripleStatistic a b c d e f (x, y, z)) ∧
      r (tripleStatistic a b c d e f (x, y, z)) = (x, y, z) ∧
      ∀ᶠ p in 𝓝 (tripleStatistic a b c d e f (x, y, z)),
        tripleStatistic a b c d e f (r p) = p := by
  let shift : Plane → Plane := fun p => (p.1 - a x, p.2 - d x)
  have hdshift : Differentiable ℝ shift :=
    (differentiable_fst.sub_const (a x)).prodMk (differentiable_snd.sub_const (d x))
  have hshift : shift (tripleStatistic a b c d e f (x, y, z)) =
      pairStatistic b c e f (y, z) := by
    apply Prod.ext <;> dsimp [shift, tripleStatistic, tripleSum, pairStatistic] <;> ring
  have hdcomp := (hshift.symm ▸ hg).comp _ hdshift.differentiableAt
  refine ⟨fun p => (x, g (shift p)), (differentiableAt_const x).prodMk hdcomp, ?_, ?_⟩
  · simp [hshift, hgp]
  · have hc : Tendsto shift (𝓝 (tripleStatistic a b c d e f (x, y, z)))
        (𝓝 (pairStatistic b c e f (y, z))) := by
      simpa only [ContinuousAt, hshift] using
        (hdshift (tripleStatistic a b c d e f (x, y, z))).continuousAt
    filter_upwards [hc hgr] with p hp
    have h₁ := congrArg Prod.fst hp
    have h₂ := congrArg Prod.snd hp
    apply Prod.ext
    · dsimp [pairStatistic, shift] at h₁
      dsimp [tripleStatistic, tripleSum]
      linarith
    · dsimp [pairStatistic, shift] at h₂
      dsimp [tripleStatistic, tripleSum]
      linarith

/-- Derivative-kernel annihilation from actual heterogeneous statistic fibers,
using a genuine local right section, without differentiating the readout. -/
theorem triple_kernel_of_section {a b c d e f ex ey ez : ℝ → ℝ} {x y z : ℝ}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b y)
    (hc : DifferentiableAt ℝ c z) (hd : DifferentiableAt ℝ d x)
    (he : DifferentiableAt ℝ e y) (hf : DifferentiableAt ℝ f z)
    (hex : DifferentiableAt ℝ ex x) (hey : DifferentiableAt ℝ ey y)
    (hez : DifferentiableAt ℝ ez z)
    {r : Plane → Triple} {U : Set Triple}
    (hr : DifferentiableAt ℝ r (tripleStatistic a b c d e f (x, y, z)))
    (hrp : r (tripleStatistic a b c d e f (x, y, z)) = (x, y, z))
    (hrr : ∀ᶠ p in 𝓝 (tripleStatistic a b c d e f (x, y, z)),
      tripleStatistic a b c d e f (r p) = p)
    (hU : U ∈ 𝓝 ((x, y, z) : Triple))
    (hfiber : ∀ p ∈ U, ∀ q ∈ U,
      tripleStatistic a b c d e f p = tripleStatistic a b c d e f q →
      tripleSum ex ey ez p = tripleSum ex ey ez q)
    {u v w : ℝ}
    (hk₁ : deriv a x * u + deriv b y * v + deriv c z * w = 0)
    (hk₂ : deriv d x * u + deriv e y * v + deriv f z * w = 0) :
    deriv ex x * u + deriv ey y * v + deriv ez z * w = 0 := by
  have hm := (tripleSum_hasFDerivAt ha.hasDerivAt hb.hasDerivAt hc.hasDerivAt).prodMk
    (tripleSum_hasFDerivAt hd.hasDerivAt he.hasDerivAt hf.hasDerivAt)
  have henc := tripleSum_hasFDerivAt hex.hasDerivAt hey.hasDerivAt hez.hasDerivAt
  change HasFDerivAt (tripleStatistic a b c d e f) _ _ at hm
  have hv : fderiv ℝ (tripleStatistic a b c d e f) (x, y, z) (u, v, w) = 0 := by
    rw [hm.fderiv]
    apply Prod.ext
    · simpa [slopeRow_apply] using hk₁
    · simpa [slopeRow_apply] using hk₂
  have hh := fderiv_annihilates_of_local_section
    hm.differentiableAt henc.differentiableAt hr hrp hrr hU hfiber hv
  simpa [henc.fderiv, slopeRow_apply] using hh

/-- The actual three-node determinant vanishes at every regular local fiber,
with no identical-node assumption. -/
theorem determinant_of_local_fibers {a b c d e f ex ey ez : ℝ → ℝ} {x y z : ℝ}
    (ha : DifferentiableAt ℝ a x) (hd : DifferentiableAt ℝ d x)
    (hb : HasStrictDerivAt b (deriv b y) y)
    (hc : HasStrictDerivAt c (deriv c z) z)
    (he : HasStrictDerivAt e (deriv e y) y)
    (hf : HasStrictDerivAt f (deriv f z) z)
    (hex : DifferentiableAt ℝ ex x) (hey : DifferentiableAt ℝ ey y)
    (hez : DifferentiableAt ℝ ez z)
    (hdet : deriv b y * deriv f z - deriv c z * deriv e y ≠ 0)
    {U : Set Triple} (hU : U ∈ 𝓝 ((x, y, z) : Triple))
    (hfiber : ∀ p ∈ U, ∀ q ∈ U,
      tripleStatistic a b c d e f p = tripleStatistic a b c d e f q →
      tripleSum ex ey ez p = tripleSum ex ey ez q) :
    deriv ex x * (deriv b y * deriv f z - deriv c z * deriv e y) +
      deriv ey y * (deriv c z * deriv d x - deriv a x * deriv f z) +
      deriv ez z * (deriv a x * deriv e y - deriv b y * deriv d x) = 0 := by
  obtain ⟨g, hg, hgp, hgr⟩ := pairStatistic_local_section hb hc he hf hdet
  obtain ⟨r, hr, hrp, hrr⟩ := triple_section_of_pair (a := a) (d := d) (x := x) hg hgp hgr
  apply kernel_determinant
  intro u v w hu hv
  exact triple_kernel_of_section ha hb.hasDerivAt.differentiableAt
    hc.hasDerivAt.differentiableAt hd he.hasDerivAt.differentiableAt
    hf.hasDerivAt.differentiableAt hex hey hez hr hrp hrr hU hfiber hu hv

/-- Regular source pairs from two different nodes. -/
def regularPairs (b c e f : ℝ → ℝ) : Set Plane :=
  ((Ioo (-1 : ℝ) 1) ×ˢ (Ioo (-1 : ℝ) 1)) ∩
    {p | deriv b p.1 * deriv f p.2 - deriv c p.2 * deriv e p.1 ≠ 0}

/-- Interior C¹ preprocessing makes the set of regular pairs a neighborhood
of every one of its points. -/
theorem regularPairs_mem_nhds {b c e f : ℝ → ℝ} {y z : ℝ}
    (hCb : ContDiffOn ℝ 1 b (Ioo (-1 : ℝ) 1))
    (hCc : ContDiffOn ℝ 1 c (Ioo (-1 : ℝ) 1))
    (hCe : ContDiffOn ℝ 1 e (Ioo (-1 : ℝ) 1))
    (hCf : ContDiffOn ℝ 1 f (Ioo (-1 : ℝ) 1))
    (hy : y ∈ Ioo (-1 : ℝ) 1) (hz : z ∈ Ioo (-1 : ℝ) 1)
    (hd : deriv b y * deriv f z - deriv c z * deriv e y ≠ 0) :
    regularPairs b c e f ∈ 𝓝 (y, z) := by
  have hby := ((hCb.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl) y hy).continuousAt
    (Ioo_mem_nhds hy.1 hy.2)
  have hcz := ((hCc.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl) z hz).continuousAt
    (Ioo_mem_nhds hz.1 hz.2)
  have hey := ((hCe.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl) y hy).continuousAt
    (Ioo_mem_nhds hy.1 hy.2)
  have hfz := ((hCf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl) z hz).continuousAt
    (Ioo_mem_nhds hz.1 hz.2)
  have hdet : ContinuousAt (fun p : Plane =>
      deriv b p.1 * deriv f p.2 - deriv c p.2 * deriv e p.1) (y, z) := by fun_prop
  exact inter_mem (prod_mem_nhds (Ioo_mem_nhds hy.1 hy.2) (Ioo_mem_nhds hz.1 hz.2))
    (hdet.eventually_ne hd)

/-- An actual heterogeneous pair submersion pulls a closure point of the
identifying moment set back to nearby regular pairs. -/
theorem regular_pair_identifying_closure {a b c d e f : ℝ → ℝ} {x y z : ℝ}
    {O : Set Plane}
    (hCb : ContDiffOn ℝ 1 b (Ioo (-1 : ℝ) 1))
    (hCc : ContDiffOn ℝ 1 c (Ioo (-1 : ℝ) 1))
    (hCe : ContDiffOn ℝ 1 e (Ioo (-1 : ℝ) 1))
    (hCf : ContDiffOn ℝ 1 f (Ioo (-1 : ℝ) 1))
    (hy : y ∈ Ioo (-1 : ℝ) 1) (hz : z ∈ Ioo (-1 : ℝ) 1)
    (hd : deriv b y * deriv f z - deriv c z * deriv e y ≠ 0)
    (hpoint : tripleStatistic a b c d e f (x, y, z) ∈ closure O) :
    (y, z) ∈ closure (regularPairs b c e f ∩
      (fun p : Plane => tripleStatistic a b c d e f (x, p.1, p.2)) ⁻¹' O) := by
  have hb := ((hCb y hy).contDiffAt (Ioo_mem_nhds hy.1 hy.2)).hasStrictDerivAt le_rfl
  have hc := ((hCc z hz).contDiffAt (Ioo_mem_nhds hz.1 hz.2)).hasStrictDerivAt le_rfl
  have he := ((hCe y hy).contDiffAt (Ioo_mem_nhds hy.1 hy.2)).hasStrictDerivAt le_rfl
  have hf := ((hCf z hz).contDiffAt (Ioo_mem_nhds hz.1 hz.2)).hasStrictDerivAt le_rfl
  have hp := pairStatistic_hasStrictFDerivAt hb hc he hf
  have hmap : HasStrictFDerivAt
      (fun p : Plane => tripleStatistic a b c d e f (x, p.1, p.2))
      (pairDerivative (deriv b y) (deriv c z) (deriv e y) (deriv f z)) (y, z) := by
    convert hp.const_add (a x, d x) using 1
    ext p <;> simp [tripleStatistic, tripleSum, pairStatistic, add_assoc]
  exact closure_preimage_of_map_nhds
    (hmap.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr (pairDerivative_surjective hd)))
    hpoint (regularPairs_mem_nhds hCb hCc hCe hCf hy hz hd)

/-- Automatic regularity needs charts only over the dense identifying set,
not over every regular triple. The inverse-function and averaging steps are
derived for the three different feature curves and encoders. -/
theorem contDiffAt_of_dense_triple_factorizations
    {a b c d e f ex ey ez : ℝ → ℝ} {x y z : ℝ} {O : Set Plane}
    (hγx : ContDiffAt ℝ 1 (fun s => (a s, d s)) x)
    (hCb : ContDiffOn ℝ 1 b (Ioo (-1 : ℝ) 1))
    (hCc : ContDiffOn ℝ 1 c (Ioo (-1 : ℝ) 1))
    (hCe : ContDiffOn ℝ 1 e (Ioo (-1 : ℝ) 1))
    (hCf : ContDiffOn ℝ 1 f (Ioo (-1 : ℝ) 1))
    (hy : y ∈ Ioo (-1 : ℝ) 1) (hz : z ∈ Ioo (-1 : ℝ) 1)
    (hd : deriv b y * deriv f z - deriv c z * deriv e y ≠ 0)
    (hpoint : tripleStatistic a b c d e f (x, y, z) ∈ closure O)
    (hcharts : ∀ q ∈ regularPairs b c e f,
      tripleStatistic a b c d e f (x, q.1, q.2) ∈ O →
      ∃ X ∈ 𝓝 x, ∃ Y ∈ 𝓝 q.1, ∃ Z ∈ 𝓝 q.2,
      ∃ B ∈ 𝓝 (tripleStatistic a b c d e f (x, q.1, q.2)),
      ∃ H : Plane → ℝ, ContinuousOn H B ∧
        ∀ x' ∈ X, ∀ y' ∈ Y, ∀ z' ∈ Z,
          ex x' + ey y' + ez z' =
            H ((a x', d x') + (b y', e y') + (c z', f z'))) :
    ContDiffAt ℝ 1 ex x := by
  have hcl := regular_pair_identifying_closure hCb hCc hCe hCf hy hz hd hpoint
  obtain ⟨q, _, hq, hp⟩ := mem_closure_iff_nhds.mp hcl Set.univ Filter.univ_mem
  obtain ⟨X, hX, Y, hY, Z, hZ, B, hB, H, hH, hfactor⟩ := hcharts q hq hp
  have hγy : ContDiffAt ℝ 1 (fun s => (b s, e s)) q.1 :=
    ((hCb q.1 hq.1.1).contDiffAt (Ioo_mem_nhds hq.1.1.1 hq.1.1.2)).prodMk
      ((hCe q.1 hq.1.1).contDiffAt (Ioo_mem_nhds hq.1.1.1 hq.1.1.2))
  have hγz : ContDiffAt ℝ 1 (fun s => (c s, f s)) q.2 :=
    ((hCc q.2 hq.1.2).contDiffAt (Ioo_mem_nhds hq.1.2.1 hq.1.2.2)).prodMk
      ((hCf q.2 hq.1.2).contDiffAt (Ioo_mem_nhds hq.1.2.1 hq.1.2.2))
  apply contDiffAt_of_triple_factorization hX hY hZ ?_ hH hγx hγy hγz hq.2 hfactor
  simpa [tripleStatistic, tripleSum, Prod.add_def, add_assoc] using hB

/-- Extend a three-node determinant from the dense identifying set to every
regular source triple. The encoder regularity premise is supplied by the
preceding averaging theorem, not by any readout derivative. -/
theorem determinant_of_dense_local_fibers
    {a b c d e f ex ey ez : ℝ → ℝ} {x y z : ℝ} {O : Set Plane}
    (ha : DifferentiableAt ℝ a x) (hd' : DifferentiableAt ℝ d x)
    (hex : DifferentiableAt ℝ ex x)
    (hCb : ContDiffOn ℝ 1 b (Ioo (-1 : ℝ) 1))
    (hCc : ContDiffOn ℝ 1 c (Ioo (-1 : ℝ) 1))
    (hCe : ContDiffOn ℝ 1 e (Ioo (-1 : ℝ) 1))
    (hCf : ContDiffOn ℝ 1 f (Ioo (-1 : ℝ) 1))
    (hCey : ContDiffOn ℝ 1 ey (Ioo (-1 : ℝ) 1))
    (hCez : ContDiffOn ℝ 1 ez (Ioo (-1 : ℝ) 1))
    (hy : y ∈ Ioo (-1 : ℝ) 1) (hz : z ∈ Ioo (-1 : ℝ) 1)
    (hd : deriv b y * deriv f z - deriv c z * deriv e y ≠ 0)
    (hpoint : tripleStatistic a b c d e f (x, y, z) ∈ closure O)
    (hfibers : ∀ q ∈ regularPairs b c e f,
      tripleStatistic a b c d e f (x, q.1, q.2) ∈ O →
      ∃ U ∈ 𝓝 ((x, q.1, q.2) : Triple),
        ∀ p ∈ U, ∀ q' ∈ U,
          tripleStatistic a b c d e f p = tripleStatistic a b c d e f q' →
          tripleSum ex ey ez p = tripleSum ex ey ez q') :
    deriv ex x * (deriv b y * deriv f z - deriv c z * deriv e y) +
      deriv ey y * (deriv c z * deriv d x - deriv a x * deriv f z) +
      deriv ez z * (deriv a x * deriv e y - deriv b y * deriv d x) = 0 := by
  let detfun : Plane → ℝ := fun p =>
    deriv ex x * (deriv b p.1 * deriv f p.2 - deriv c p.2 * deriv e p.1) +
      deriv ey p.1 * (deriv c p.2 * deriv d x - deriv a x * deriv f p.2) +
      deriv ez p.2 * (deriv a x * deriv e p.1 - deriv b p.1 * deriv d x)
  have continuous_derivative_at : ∀ (g : ℝ → ℝ), ContDiffOn ℝ 1 g (Ioo (-1 : ℝ) 1) →
      ∀ t ∈ Ioo (-1 : ℝ) 1, ContinuousAt (deriv g) t := by
    intro g hg t ht
    exact ((hg.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl) t ht).continuousAt
      (Ioo_mem_nhds ht.1 ht.2)
  have hby := continuous_derivative_at b hCb y hy
  have hcz := continuous_derivative_at c hCc z hz
  have hey := continuous_derivative_at e hCe y hy
  have hfz := continuous_derivative_at f hCf z hz
  have heyy := continuous_derivative_at ey hCey y hy
  have hezz := continuous_derivative_at ez hCez z hz
  have hcont : ContinuousAt detfun (y, z) := by dsimp [detfun]; fun_prop
  apply zero_at_closure hcont (regular_pair_identifying_closure hCb hCc hCe hCf hy hz hd hpoint)
  intro p hp
  obtain ⟨U, hU, hfiber⟩ := hfibers p hp.1 hp.2
  exact determinant_of_local_fibers ha hd'
    (((hCb p.1 hp.1.1.1).contDiffAt (Ioo_mem_nhds hp.1.1.1.1 hp.1.1.1.2)).hasStrictDerivAt le_rfl)
    (((hCc p.2 hp.1.1.2).contDiffAt (Ioo_mem_nhds hp.1.1.2.1 hp.1.1.2.2)).hasStrictDerivAt le_rfl)
    (((hCe p.1 hp.1.1.1).contDiffAt (Ioo_mem_nhds hp.1.1.1.1 hp.1.1.1.2)).hasStrictDerivAt le_rfl)
    (((hCf p.2 hp.1.1.2).contDiffAt (Ioo_mem_nhds hp.1.1.2.1 hp.1.1.2.2)).hasStrictDerivAt le_rfl)
    hex ((hCey.differentiableOn_one p.1 hp.1.1.1).differentiableAt
      (Ioo_mem_nhds hp.1.1.1.1 hp.1.1.1.2))
    ((hCez.differentiableOn_one p.2 hp.1.1.2).differentiableAt
      (Ioo_mem_nhds hp.1.1.2.1 hp.1.1.2.2)) hp.1.2 hU hfiber

end Analog.HeterogeneousRegularity
