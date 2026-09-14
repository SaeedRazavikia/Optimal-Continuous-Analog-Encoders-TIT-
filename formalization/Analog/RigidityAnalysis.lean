import Analog.DifferentialRigidity
import Analog.RigidityCompletion
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Differential kernels from local moment fibers

The geometric hypothesis here is local constancy of the encoded sum on moment
fibers, together with a differentiable local right section of the moment map.
The encoded sum is assumed differentiable. No differentiability of the
factorizing readout is assumed: its derivative is obtained by composing the
encoded sum with the local section. The automatic differentiability and
topological steps for arbitrary continuous encoders remain separate.
-/

open Filter Topology

namespace Analog.RigidityAnalysis

/-- A differentiable function constant on the local fibers of a differentiable
map has derivative factoring through that map whenever a differentiable local
right section through the base point exists. This derives the differential
factorization instead of assuming a differentiable factorizing readout. -/
theorem fderiv_factors_of_local_section
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {moment : E → F} {encoded : E → G} {rightSection : F → E}
    {x : E} {U : Set E}
    (hm : DifferentiableAt ℝ moment x)
    (he : DifferentiableAt ℝ encoded x)
    (hs : DifferentiableAt ℝ rightSection (moment x))
    (hsx : rightSection (moment x) = x)
    (hsright : ∀ᶠ p in 𝓝 (moment x), moment (rightSection p) = p)
    (hU : U ∈ 𝓝 x)
    (hfiber : ∀ p ∈ U, ∀ q ∈ U, moment p = moment q → encoded p = encoded q) :
    fderiv ℝ encoded x =
      (fderiv ℝ encoded x).comp
        ((fderiv ℝ rightSection (moment x)).comp (fderiv ℝ moment x)) := by
  have hscont : Tendsto rightSection (𝓝 (moment x)) (𝓝 x) := by
    simpa only [ContinuousAt, hsx] using hs.continuousAt
  have heq : encoded =ᶠ[𝓝 x] fun p => encoded (rightSection (moment p)) := by
    filter_upwards [hU, hm.continuousAt (hscont hU),
      hm.continuousAt hsright] with p hp hsp hright
    exact hfiber p hp (rightSection (moment p)) hsp hright.symm
  have he' : HasFDerivAt encoded (fderiv ℝ encoded x) (rightSection (moment x)) := by
    simpa [hsx] using he.hasFDerivAt
  have hcomp := he'.comp x (hs.hasFDerivAt.comp x hm.hasFDerivAt)
  exact he.hasFDerivAt.unique (hcomp.congr_of_eventuallyEq heq)

/-- The tangent-kernel conclusion follows from actual local fiber constancy
and a local section. -/
theorem fderiv_annihilates_of_local_section
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {moment : E → F} {encoded : E → G} {rightSection : F → E}
    {x : E} {U : Set E}
    (hm : DifferentiableAt ℝ moment x)
    (he : DifferentiableAt ℝ encoded x)
    (hs : DifferentiableAt ℝ rightSection (moment x))
    (hsx : rightSection (moment x) = x)
    (hsright : ∀ᶠ p in 𝓝 (moment x), moment (rightSection p) = p)
    (hU : U ∈ 𝓝 x)
    (hfiber : ∀ p ∈ U, ∀ q ∈ U, moment p = moment q → encoded p = encoded q)
    {v : E} (hv : fderiv ℝ moment x v = 0) :
    fderiv ℝ encoded x v = 0 := by
  rw [fderiv_factors_of_local_section hm he hs hsx hsright hU hfiber]
  simp [hv]

/-- Three real transmitter inputs. -/
abbrev Triple := ℝ × (ℝ × ℝ)

/-- The sum of a scalar feature over three inputs. -/
def tripleSum (f : ℝ → ℝ) (p : Triple) : ℝ :=
  f p.1 + f p.2.1 + f p.2.2

/-- The two unnormalized moment sums. -/
def tripleMoment (φ : ℝ → ℝ) (p : Triple) : ℝ × ℝ :=
  (tripleSum id p, tripleSum φ p)

/-- A differential row on the three source coordinates. -/
noncomputable def slopeRow (dx dy dz : ℝ) : Triple →L[ℝ] ℝ :=
  dx • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) +
    dy • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
    dz • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

theorem slopeRow_apply (dx dy dz : ℝ) (v : Triple) :
    slopeRow dx dy dz v = dx * v.1 + dy * v.2.1 + dz * v.2.2 := by
  simp [slopeRow]

/-- The encoded or feature triple sum has the expected differential row. -/
theorem tripleSum_hasFDerivAt {f : ℝ → ℝ} {x y z dx dy dz : ℝ}
    (hx : HasDerivAt f dx x) (hy : HasDerivAt f dy y)
    (hz : HasDerivAt f dz z) :
    HasFDerivAt (tripleSum f) (slopeRow dx dy dz) (x, y, z) := by
  have h1 := hx.comp_hasFDerivAt (𝕜 := ℝ) (x, y, z) hasFDerivAt_fst
  have h2 := hy.comp_hasFDerivAt (𝕜 := ℝ) (x, y, z)
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, y, z))).fst
  have h3 := hz.comp_hasFDerivAt (𝕜 := ℝ) (x, y, z)
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, y, z))).snd
  exact (h1.add h2).add h3

/-- Local constancy on actual moment fibers implies annihilation of the two
moment differential kernels. The local right section is the object supplied
by an inverse-function chart; no tangent-space theorem is assumed. -/
theorem triple_kernel_of_local_section
    {φ e : ℝ → ℝ} {x y z : ℝ}
    (hφx : DifferentiableAt ℝ φ x) (hφy : DifferentiableAt ℝ φ y)
    (hφz : DifferentiableAt ℝ φ z)
    (hex : DifferentiableAt ℝ e x) (hey : DifferentiableAt ℝ e y)
    (hez : DifferentiableAt ℝ e z)
    {rightSection : (ℝ × ℝ) → Triple} {U : Set Triple}
    (hs : DifferentiableAt ℝ rightSection (tripleMoment φ (x, y, z)))
    (hsx : rightSection (tripleMoment φ (x, y, z)) = (x, y, z))
    (hsright : ∀ᶠ p in 𝓝 (tripleMoment φ (x, y, z)),
      tripleMoment φ (rightSection p) = p)
    (hU : U ∈ 𝓝 (x, y, z))
    (hfiber : ∀ p ∈ U, ∀ q ∈ U, tripleMoment φ p = tripleMoment φ q →
      tripleSum e p = tripleSum e q)
    {a b c : ℝ} (hfirst : a + b + c = 0)
    (hsecond : deriv φ x * a + deriv φ y * b + deriv φ z * c = 0) :
    deriv e x * a + deriv e y * b + deriv e z * c = 0 := by
  have hm := (tripleSum_hasFDerivAt (hasDerivAt_id x)
    (hasDerivAt_id y) (hasDerivAt_id z)).prodMk
      (tripleSum_hasFDerivAt hφx.hasDerivAt hφy.hasDerivAt hφz.hasDerivAt)
  have he := tripleSum_hasFDerivAt hex.hasDerivAt hey.hasDerivAt hez.hasDerivAt
  change HasFDerivAt (tripleMoment φ) _ _ at hm
  have hv : fderiv ℝ (tripleMoment φ) (x, y, z) (a, b, c) = 0 := by
    rw [hm.fderiv]
    apply Prod.ext
    · simpa [slopeRow_apply] using hfirst
    · simpa [slopeRow_apply] using hsecond
  have hk := fderiv_annihilates_of_local_section
    hm.differentiableAt he.differentiableAt hs hsx hsright hU hfiber hv
  simpa [he.fderiv, slopeRow_apply] using hk

/-- A local right inverse for the two-input moment map gives a local right
section for the three-input moment map, keeping the first input fixed. -/
theorem triple_section_of_pair
    {φ : ℝ → ℝ} {x y z : ℝ} {g : (ℝ × ℝ) → (ℝ × ℝ)}
    (hg : DifferentiableAt ℝ g (y + z, φ y + φ z))
    (hgpoint : g (y + z, φ y + φ z) = (y, z))
    (hgright : ∀ᶠ p in 𝓝 (y + z, φ y + φ z),
      ((g p).1 + (g p).2, φ (g p).1 + φ (g p).2) = p) :
    ∃ r : (ℝ × ℝ) → Triple,
      DifferentiableAt ℝ r (tripleMoment φ (x, y, z)) ∧
      r (tripleMoment φ (x, y, z)) = (x, y, z) ∧
      ∀ᶠ p in 𝓝 (tripleMoment φ (x, y, z)), tripleMoment φ (r p) = p := by
  let shift : (ℝ × ℝ) → (ℝ × ℝ) := fun p => (p.1 - x, p.2 - φ x)
  have hshift : Differentiable ℝ shift :=
    (differentiable_fst.sub_const x).prodMk (differentiable_snd.sub_const (φ x))
  have hshiftpoint : shift (tripleMoment φ (x, y, z)) = (y + z, φ y + φ z) := by
    simp [shift, tripleMoment, tripleSum]
    constructor <;> ring
  have hcomp : DifferentiableAt ℝ (fun p => g (shift p))
      (tripleMoment φ (x, y, z)) :=
    (hshiftpoint.symm ▸ hg).comp _ hshift.differentiableAt
  refine ⟨fun p => (x, g (shift p)), (differentiableAt_const x).prodMk hcomp, ?_, ?_⟩
  · simp [hshiftpoint, hgpoint]
  · have hcont : Tendsto shift (𝓝 (tripleMoment φ (x, y, z)))
        (𝓝 (y + z, φ y + φ z)) := by
      simpa only [ContinuousAt, hshiftpoint] using
        (hshift (tripleMoment φ (x, y, z))).continuousAt
    filter_upwards [hcont hgright] with p hp
    have h1 := congrArg Prod.fst hp
    have h2 := congrArg Prod.snd hp
    apply Prod.ext
    · change x + (g (shift p)).1 + (g (shift p)).2 = p.1
      dsimp [shift] at h1
      linarith
    · change φ x + φ (g (shift p)).1 + φ (g (shift p)).2 = p.2
      dsimp [shift] at h2
      linarith

/-- At distinct strict feature slopes, the differentiable section is supplied
by the actual inverse function theorem. Only differentiability of the encoder
and constancy on local moment fibers remain as analytic hypotheses. -/
theorem triple_kernel_of_local_fibers
    {φ e : ℝ → ℝ} {x y z : ℝ}
    (hφx : DifferentiableAt ℝ φ x)
    (hφy : HasStrictDerivAt φ (deriv φ y) y)
    (hφz : HasStrictDerivAt φ (deriv φ z) z)
    (hanchor : deriv φ y ≠ deriv φ z)
    (hex : DifferentiableAt ℝ e x) (hey : DifferentiableAt ℝ e y)
    (hez : DifferentiableAt ℝ e z)
    {U : Set Triple} (hU : U ∈ 𝓝 (x, y, z))
    (hfiber : ∀ p ∈ U, ∀ q ∈ U, tripleMoment φ p = tripleMoment φ q →
      tripleSum e p = tripleSum e q)
    {a b c : ℝ} (hfirst : a + b + c = 0)
    (hsecond : deriv φ x * a + deriv φ y * b + deriv φ z * c = 0) :
    deriv e x * a + deriv e y * b + deriv e z * c = 0 := by
  obtain ⟨g, hg, hgp, hgr⟩ :=
    RigidityCompletion.pairMoment_local_section hφy hφz hanchor
  obtain ⟨r, hr, hrp, hrr⟩ := triple_section_of_pair (x := x) hg hgp hgr
  exact triple_kernel_of_local_section hφx
    hφy.hasDerivAt.differentiableAt hφz.hasDerivAt.differentiableAt
    hex hey hez hr hrp hrr hU hfiber hfirst hsecond

/-- Local moment-fiber constancy for a scalar encoder on an open source
interval. No differentiable or continuous factorizing receiver is assumed. -/
def LocalMomentFibers (domain : Set ℝ) (φ e : ℝ → ℝ) : Prop :=
  ∀ x ∈ domain, ∀ y ∈ domain, ∀ z ∈ domain,
    ∃ U ∈ 𝓝 ((x, y, z) : Triple),
      ∀ p ∈ U, ∀ q ∈ U, tripleMoment φ p = tripleMoment φ q →
        tripleSum e p = tripleSum e q

/-- The complete differential part of scalar rigidity, including endpoint
extension. Compared with the earlier differential-kernel theorem, the kernel
condition is now proved from local moment fibers using a constructed inverse
function chart. Automatic differentiability of a merely continuous encoder
and the derivation of fiber constancy from exactness are not assumed proved. -/
theorem affine_representation_of_local_fibers
    {a b : ℝ} (hab : a < b) {φ e : ℝ → ℝ}
    (hφ : ContinuousOn φ (Set.Icc a b))
    (he : ContinuousOn e (Set.Icc a b))
    (hφstrict : ∀ x ∈ Set.Ioo a b, HasStrictDerivAt φ (deriv φ x) x)
    (hediff : DifferentiableOn ℝ e (Set.Ioo a b))
    (hnonaffine : ¬ ∃ c α : ℝ, ∀ x ∈ Set.Icc a b, φ x = c + α * x)
    (hfibers : LocalMomentFibers (Set.Ioo a b) φ e) :
    ∃ c α β : ℝ, ∀ x ∈ Set.Icc a b, e x = c + α * x + β * φ x := by
  have hφdiff : DifferentiableOn ℝ φ (Set.Ioo a b) :=
    fun x hx => (hφstrict x hx).hasDerivAt.differentiableAt.differentiableWithinAt
  obtain ⟨y, hy, z, hz, hanchor⟩ :=
    DifferentialRigidity.nonaffine_has_distinct_interior_slopes hab hφ hφdiff hnonaffine
  let β := (deriv e y - deriv e z) / (deriv φ y - deriv φ z)
  let α := deriv e y - β * deriv φ y
  have hslopes : ∀ x ∈ Set.Ioo a b, deriv e x = α + β * deriv φ x := by
    intro x hx
    obtain ⟨U, hU, hf⟩ := hfibers x hx y hy z hz
    have hexd := (hediff x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
    have heyd := (hediff y hy).differentiableAt (Ioo_mem_nhds hy.1 hy.2)
    have hezd := (hediff z hz).differentiableAt (Ioo_mem_nhds hz.1 hz.2)
    apply DifferentialRigidity.affine_slope_from_kernel _ _ _ _ _ _ hanchor
    intro a' b' c' hfirst hsecond
    exact triple_kernel_of_local_fibers
      (hφstrict x hx).hasDerivAt.differentiableAt
      (hφstrict y hy) (hφstrict z hz) hanchor hexd heyd hezd
      hU hf hfirst hsecond
  obtain ⟨c, hc⟩ := DifferentialRigidity.affine_representation_of_derivative_relation
    hφ he hφdiff hediff hslopes
  exact ⟨c, α, β, hc⟩

/-- Local constancy of the physical planar triple sum on the moment fibers. -/
def LocalPlanarMomentFibers (domain : Set ℝ) (φ : ℝ → ℝ)
    (E : ℝ → ℝ × ℝ) : Prop :=
  ∀ x ∈ domain, ∀ y ∈ domain, ∀ z ∈ domain,
    ∃ U ∈ 𝓝 ((x, y, z) : Triple),
      ∀ p ∈ U, ∀ q ∈ U, tripleMoment φ p = tripleMoment φ q →
        E p.1 + E p.2.1 + E p.2.2 = E q.1 + E q.2.1 + E q.2.2

/-- Planar rigidity from the hypotheses available after the manuscript's
topological factorization and regularization steps. The feature uses the
original `C¹` assumption; the encoder needs only interior differentiability.
Both the local chart and the derivative-kernel argument are now proved. -/
theorem planar_affine_representation_of_local_fibers
    {a b : ℝ} (hab : a < b) {φ : ℝ → ℝ} {E : ℝ → ℝ × ℝ}
    (hφ : ContinuousOn φ (Set.Icc a b))
    (hE : ContinuousOn E (Set.Icc a b))
    (hφc1 : ContDiffOn ℝ 1 φ (Set.Ioo a b))
    (hEdiff : DifferentiableOn ℝ E (Set.Ioo a b))
    (hnonaffine : ¬ ∃ c α : ℝ, ∀ x ∈ Set.Icc a b, φ x = c + α * x)
    (hfibers : LocalPlanarMomentFibers (Set.Ioo a b) φ E) :
    ∃ c u v : ℝ × ℝ, ∀ x ∈ Set.Icc a b,
      E x = c + x • u + φ x • v := by
  have hφstrict : ∀ x ∈ Set.Ioo a b, HasStrictDerivAt φ (deriv φ x) x := by
    intro x hx
    exact ((hφc1 x hx).contDiffAt (Ioo_mem_nhds hx.1 hx.2)).hasStrictDerivAt le_rfl
  have hfx : LocalMomentFibers (Set.Ioo a b) φ (fun x => (E x).1) := by
    intro x hx y hy z hz
    obtain ⟨U, hU, hf⟩ := hfibers x hx y hy z hz
    refine ⟨U, hU, ?_⟩
    intro p hp q hq hm
    simpa only [tripleSum, Prod.fst_add] using congrArg Prod.fst (hf p hp q hq hm)
  have hfy : LocalMomentFibers (Set.Ioo a b) φ (fun x => (E x).2) := by
    intro x hx y hy z hz
    obtain ⟨U, hU, hf⟩ := hfibers x hx y hy z hz
    refine ⟨U, hU, ?_⟩
    intro p hp q hq hm
    simpa only [tripleSum, Prod.snd_add] using congrArg Prod.snd (hf p hp q hq hm)
  obtain ⟨cx, ux, vx, hx⟩ := affine_representation_of_local_fibers
    hab hφ hE.fst hφstrict hEdiff.fst hnonaffine hfx
  obtain ⟨cy, uy, vy, hy⟩ := affine_representation_of_local_fibers
    hab hφ hE.snd hφstrict hEdiff.snd hnonaffine hfy
  refine ⟨(cx, cy), (ux, uy), (vx, vy), ?_⟩
  intro x hxi
  apply Prod.ext
  · simpa [mul_comm] using hx x hxi
  · simpa [mul_comm] using hy x hxi

/-- A local factorization through the two moments supplies fiber constancy.
The map `H` can be completely arbitrary; no regularity is added to the
manuscript's continuous factorization in this conversion. -/
theorem local_fibers_of_factorization
    {domain : Set ℝ} {φ : ℝ → ℝ} {E : ℝ → ℝ × ℝ}
    (hfactor : ∀ x ∈ domain, ∀ y ∈ domain, ∀ z ∈ domain,
      ∃ U ∈ 𝓝 ((x, y, z) : Triple), ∃ H : (ℝ × ℝ) → (ℝ × ℝ),
        ∀ p ∈ U, E p.1 + E p.2.1 + E p.2.2 = H (tripleMoment φ p)) :
    LocalPlanarMomentFibers domain φ E := by
  intro x hx y hy z hz
  obtain ⟨U, hU, H, hH⟩ := hfactor x hx y hy z hz
  refine ⟨U, hU, ?_⟩
  intro p hp q hq hm
  rw [hH p hp, hH q hq, hm]

/-- Exact computation gives an independent affine-feature representation once
local moment-fiber constancy and actual interior differentiability of the
encoder have been established. This joins the inverse-function chart, the
tangent-kernel argument, integration, endpoint continuity, and independence
to the project's actual channel and general target definitions. The two
remaining continuous-encoder hypotheses are explicit. -/
theorem rigid_representation_of_local_fibers
    {K : ℕ} (hK : 4 ≤ K) {φ ψ : ℝ → ℝ} {E : ℝ → ℝ × ℝ}
    (hφ : ContinuousOn φ (Set.Icc (-1 : ℝ) 1))
    (hC1φ : ContDiffOn ℝ 1 φ (Set.Ioo (-1 : ℝ) 1))
    (hE : ContinuousOn E (Set.Icc (-1 : ℝ) 1))
    (hdE : DifferentiableOn ℝ E (Set.Ioo (-1 : ℝ) 1))
    (hnonaffine : ¬ ∃ c a : ℝ, ∀ s ∈ Set.Icc (-1 : ℝ) 1, φ s = c + a * s)
    (hshape : StrictConvexOn ℝ (Set.Ioo (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Set.Ioo (-1 : ℝ) 1) ψ)
    (hexact : GeneralCollision.ExactTarget K φ ψ E)
    (hfibers : LocalPlanarMomentFibers (Set.Ioo (-1 : ℝ) 1) φ E) :
    ∃ e : RigidityCompletion.FeatureEncoder,
      e.det ≠ 0 ∧ ∀ s ∈ Set.Icc (-1 : ℝ) 1, E s = e.encoder φ s := by
  obtain ⟨c, u, v, he⟩ := planar_affine_representation_of_local_fibers
    (by norm_num : (-1 : ℝ) < 1) hφ hE hC1φ hdE hnonaffine hfibers
  let e : RigidityCompletion.FeatureEncoder := ⟨c, u, v⟩
  have hrep : ∀ s, ArbitraryEncoder.InSource s → E s = e.encoder φ s := he
  have hexact' : GeneralCollision.ExactTarget K φ ψ (e.encoder φ) :=
    (RigidityCompletion.exactTarget_congr_on_source hrep).mp hexact
  exact ⟨e, (e.exact_iff_det_ne_zero_of_nonaffine hK hφ hC1φ hnonaffine hshape).mp
    hexact', he⟩

end Analog.RigidityAnalysis
