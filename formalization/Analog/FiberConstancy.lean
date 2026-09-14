import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Maps.Basic

/-!
# Constancy of fibers for open slices

This file verifies the topological constancy argument used in the manuscript's
rigidity proof, with the openness of every fixed-parameter slice stated as an
explicit hypothesis. It does not establish invariance of domain, nor does it
establish the continuous-encoder rigidity theorem.

The recovery map `q` need not be continuous. Joint continuity of `R` is enough
to make each parameter fiber locally constant; preconnectedness of the
parameter space then makes that fiber constant.
-/

namespace Analog

open Set

variable {B T Y : Type*}
  [TopologicalSpace B] [TopologicalSpace T] [TopologicalSpace Y]

/-- With open fixed-parameter slices and a recovery map for the first coordinate,
each fixed-first-coordinate fiber is locally constant. -/
theorem open_slice_fiber_locally_constant
    (R : B × T → Y) (q : Y → B)
    (hR : Continuous R)
    (hopen : ∀ t, IsOpenMap fun p => R (p, t))
    (hq : ∀ p t, q (R (p, t)) = p)
    (p : B) (t : T) :
    ∃ U : Set T, IsOpen U ∧ t ∈ U ∧ ∀ u ∈ U, R (p, u) = R (p, t) := by
  let U : Set T := (fun u => R (p, u)) ⁻¹' Set.range (fun b => R (b, t))
  have hcont : Continuous fun u => R (p, u) :=
    hR.comp (continuous_const.prodMk continuous_id)
  refine ⟨U, hcont.isOpen_preimage _ (hopen t).isOpen_range, ?_, ?_⟩
  · exact ⟨p, rfl⟩
  · intro u hu
    obtain ⟨b, hb⟩ := hu
    have hbp : b = p := by
      calc
        b = q (R (b, t)) := (hq b t).symm
        _ = q (R (p, u)) := congrArg q hb
        _ = p := hq p u
    calc
      R (p, u) = R (b, t) := hb.symm
      _ = R (p, t) := by rw [hbp]

/-- Every set has open preimage along a parameter fiber. This formulation of
local constancy does not impose a separation axiom on the received space. -/
theorem open_slice_fiber_preimage_isOpen
    (R : B × T → Y) (q : Y → B)
    (hR : Continuous R)
    (hopen : ∀ t, IsOpenMap fun p => R (p, t))
    (hq : ∀ p t, q (R (p, t)) = p)
    (p : B) (S : Set Y) :
    IsOpen ((fun t => R (p, t)) ⁻¹' S) := by
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro t ht
  obtain ⟨U, hU, htU, hconst⟩ :=
    open_slice_fiber_locally_constant R q hR hopen hq p t
  refine ⟨U, ?_, hU, htU⟩
  intro u hu
  change R (p, u) ∈ S
  rw [hconst u hu]
  exact ht

/-- On a preconnected parameter space, open slices and recovery of the first
coordinate force the received value to be independent of the parameter.

The open-map hypothesis is explicit and essential to this formalized result.
Applying this theorem to continuous injections from planar open sets requires
a separate invariance-of-domain theorem, which this file does not prove. -/
theorem open_slice_fiber_constancy [PreconnectedSpace T]
    (R : B × T → Y) (q : Y → B)
    (hR : Continuous R)
    (hopen : ∀ t, IsOpenMap fun p => R (p, t))
    (hq : ∀ p t, q (R (p, t)) = p)
    (p : B) (t u : T) : R (p, t) = R (p, u) := by
  classical
  let U : Set T := (fun v => R (p, v)) ⁻¹' {R (p, u)}
  have hU : IsOpen U :=
    open_slice_fiber_preimage_isOpen R q hR hopen hq p {R (p, u)}
  have hUc : IsOpen Uᶜ :=
    open_slice_fiber_preimage_isOpen R q hR hopen hq p {R (p, u)}ᶜ
  suffices ht : t ∉ Uᶜ from Classical.not_not.mp ht
  intro ht
  have h := isPreconnected_univ U Uᶜ hU hUc
    (by simp only [union_compl_self, subset_univ])
    ⟨u, ⟨Set.mem_univ _, rfl⟩⟩ ⟨t, ⟨Set.mem_univ _, ht⟩⟩
  simp only [inter_compl_self, inter_empty, Set.not_nonempty_empty] at h

end Analog
