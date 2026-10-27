import Analog.PlanarInvarianceCore
import Analog.PlanarBrouwer
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Planar invariance of domain and reverse factorization

The topology step in continuous-encoder rigidity: if equal received values
determine a planar moment parameter, continuous variation in a connected
fiber cannot change the received value. No continuity of the recovery map
is required.
-/

noncomputable section
namespace Analog.PlanarInvariance
open Set Filter Topology

abbrev Plane := ℝ × ℝ
abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

instance : PlanarInvarianceCore.BrouwerFixedPoint EuclideanPlane where
  brouwer_fixed_point := PlanarBrouwer.brouwer_fixed_point_planeClosedUnitBall

/-- The ordinary product plane has invariance of domain, transported from
the Euclidean norm through its standard homeomorphism. -/
theorem isOpen_image (f : Plane → Plane) (U : Set Plane) (hU : IsOpen U)
    (hf : ContinuousOn f U) (hinj : InjOn f U) : IsOpen (f '' U) := by
  let e : EuclideanPlane ≃ₜ Plane :=
    (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).trans (Homeomorph.finTwoArrow (X := ℝ))
  have hpre : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have hcont : ContinuousOn (fun x => e.symm (f (e x))) (e ⁻¹' U) :=
    e.symm.continuous.comp_continuousOn
      (hf.comp e.continuous.continuousOn (fun _ hx => hx))
  have hi : InjOn (fun x => e.symm (f (e x))) (e ⁻¹' U) := by
    intro x hx y hy hxy
    exact e.injective (hinj hx hy (e.symm.injective hxy))
  have hopen := PlanarInvarianceCore.invariance_of_domain_open_map
    (fun x => e.symm (f (e x))) (e ⁻¹' U) hpre hcont hi
  have heq : e '' ((fun x => e.symm (f (e x))) '' (e ⁻¹' U)) = f '' U := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨e x, hx, e.apply_symm_apply _⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨e.symm (f x), ⟨e.symm x, ?_, ?_⟩, e.apply_symm_apply _⟩
      · simpa using hx
      · simp
  rw [← heq]
  exact e.isOpenMap _ hopen

/-- Invariance of domain turns continuous injective slices and collision
recovery of the planar parameter into constancy along every connected fiber.
The recovery function itself is neither supplied nor assumed continuous. -/
theorem fiber_constant_of_collision_recovery {T : Type*}
    [TopologicalSpace T] [PreconnectedSpace T]
    (R : Plane → T → Plane) (U : Set Plane) (hU : IsOpen U)
    (hslice : ∀ t, ContinuousOn (fun p => R p t) U)
    (hfiber : ∀ p ∈ U, Continuous (R p))
    (hcollision : ∀ p ∈ U, ∀ q ∈ U, ∀ s t, R p s = R q t → p = q) :
    ∀ p ∈ U, ∀ s t, R p s = R p t := by
  intro p hp
  have hlocal : IsLocallyConstant (R p) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro t
    have hinj : InjOn (fun q => R q t) U := by
      intro q hq q' hq' heq
      exact hcollision q hq q' hq' t t heq
    have hopen := isOpen_image (fun q => R q t) U hU (hslice t) hinj
    have hmem : R p t ∈ (fun q => R q t) '' U := ⟨p, hp, rfl⟩
    have hev := (hfiber p hp).continuousAt.eventually_mem (hopen.mem_nhds hmem)
    filter_upwards [hev] with t' ht'
    obtain ⟨q, hq, heq⟩ := ht'
    have hpq : p = q := hcollision p hp q hq t' t heq.symm
    simpa [← hpq] using heq.symm
  exact hlocal.apply_eq_of_preconnectedSpace

/-- A genuine local coordinate homeomorphism, with one real fiber coordinate
and two moment coordinates, turns local recovery of the moments into a
continuous reverse factorization. -/
theorem local_factorization_of_coordinates {X : Type*} [TopologicalSpace X]
    (R M : X → Plane) (e : OpenPartialHomeomorph X (ℝ × Plane))
    (x₀ : X) (hx₀ : x₀ ∈ e.source) (hR : ContinuousOn R e.source)
    (hcoord : ∀ x ∈ e.source, (e x).2 = M x)
    (hcollision : ∀ x ∈ e.source, ∀ y ∈ e.source, R x = R y → M x = M y) :
    ∃ N ∈ 𝓝 x₀, ∃ B ∈ 𝓝 (M x₀), ∃ H : Plane → Plane,
      ContinuousOn H B ∧ ∀ x ∈ N, R x = H (M x) := by
  have he₀ := e.map_source hx₀
  have htarget := e.open_target.mem_nhds he₀
  rw [nhds_prod_eq, Filter.mem_prod_iff] at htarget
  obtain ⟨I, hI, V, hV, hIV⟩ := htarget
  obtain ⟨a, b, hab, hsubI⟩ := mem_nhds_iff_exists_Ioo_subset.mp hI
  obtain ⟨U, hUV, hUopen, hpU⟩ := mem_nhds_iff.mp hV
  have hrect : Ioo a b ×ˢ U ⊆ e.target := by
    intro z hz
    exact hIV ⟨hsubI hz.1, hUV hz.2⟩
  let t₀ : Ioo a b := ⟨(e x₀).1, hab⟩
  let S : Plane → Ioo a b → Plane := fun p t => R (e.symm (t, p))
  have hslice : ∀ t, ContinuousOn (fun p => S p t) U := by
    intro t
    have hmap : MapsTo (fun p : Plane => ((t : ℝ), p)) U e.target :=
      fun p hp => hrect ⟨t.property, hp⟩
    exact hR.comp (e.continuousOn_symm.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap)
      (fun p hp => e.map_target (hmap hp))
  have hfiber : ∀ p ∈ U, Continuous (S p) := by
    intro p hp
    have hmap : MapsTo (fun t : Ioo a b => ((t : ℝ), p)) univ e.target :=
      fun t _ => hrect ⟨t.property, hp⟩
    apply continuousOn_univ.mp
    exact hR.comp (e.continuousOn_symm.comp
      (continuous_subtype_val.prodMk continuous_const).continuousOn hmap)
      (fun t ht => e.map_target (hmap ht))
  have hrecover : ∀ p ∈ U, ∀ q ∈ U, ∀ s t, S p s = S q t → p = q := by
    intro p hp q hq s t heq
    have hsp : ((s : ℝ), p) ∈ e.target := hrect ⟨s.property, hp⟩
    have htq : ((t : ℝ), q) ∈ e.target := hrect ⟨t.property, hq⟩
    have hm := hcollision _ (e.map_target hsp) _ (e.map_target htq) heq
    rw [← hcoord _ (e.map_target hsp), ← hcoord _ (e.map_target htq),
      e.right_inv hsp, e.right_inv htq] at hm
    exact hm
  letI : PreconnectedSpace (Ioo a b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have hconstant := fiber_constant_of_collision_recovery S U hUopen hslice hfiber hrecover
  let H : Plane → Plane := fun p => S p t₀
  have hB : U ∈ 𝓝 (M x₀) := by
    rw [← hcoord x₀ hx₀]
    exact hUopen.mem_nhds hpU
  let N := e.source ∩ e ⁻¹' (Ioo a b ×ˢ U)
  have hN : N ∈ 𝓝 x₀ := by
    apply inter_mem (e.open_source.mem_nhds hx₀)
    exact (e.continuousAt hx₀).preimage_mem_nhds
      (prod_mem_nhds (Ioo_mem_nhds hab.1 hab.2) (hUopen.mem_nhds hpU))
  refine ⟨N, hN, U, hB, H, hslice t₀, ?_⟩
  intro x hx
  let t : Ioo a b := ⟨(e x).1, hx.2.1⟩
  have hcx := hconstant (e x).2 hx.2.2 t t₀
  change R (e.symm ((e x).1, (e x).2)) = H (e x).2 at hcx
  rw [Prod.mk.eta, e.left_inv hx.1, hcoord x hx.1] at hcx
  exact hcx

end Analog.PlanarInvariance
