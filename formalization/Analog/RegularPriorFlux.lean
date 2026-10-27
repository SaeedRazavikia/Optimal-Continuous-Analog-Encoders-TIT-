import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-!
# Compact test fluxes for locally regular prior densities

A prior density need only be C¹ and positive on its open full-mass region.
Multiplication by an interior compact test function gives a globally C¹ flux.
The apparent divisions by the prior in its weighted energy and information
term extend continuously by zero, with compact support and finite integrals.
No regularity is imposed on the density outside the open region.
-/

noncomputable section
namespace Analog.RegularPriorFlux
open Set MeasureTheory
open scoped Topology

abbrev Plane := ℝ × ℝ

/-- Compactly supported multiplication localizes C¹ prior regularity. -/
theorem flux_contDiff {Ω : Set Plane} (hΩ : IsOpen Ω)
    {p η : Plane → ℝ} (hp : ContDiffOn ℝ 1 p Ω)
    (hη : ContDiff ℝ 1 η) (hs : tsupport η ⊆ Ω) :
    ContDiff ℝ 1 (fun m => p m * η m) := by
  rw [contDiff_iff_contDiffAt]
  intro m
  by_cases hm : m ∈ Ω
  · exact (hp.contDiffAt (hΩ.mem_nhds hm)).mul hη.contDiffAt
  · have hn : m ∉ tsupport (fun x => p x * η x) := by
      intro hx
      exact hm (hs (tsupport_mul_subset_right hx))
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hn)

/-- The flux has support inside the original compact test support. -/
theorem flux_support_subset (p η : Plane → ℝ) :
    tsupport (fun m => p m * η m) ⊆ tsupport η := tsupport_mul_subset_right

theorem flux_hasCompactSupport {p η : Plane → ℝ} (hη : HasCompactSupport η) :
    HasCompactSupport (fun m => p m * η m) := hη.mul_left

/-- Directional differentiation does not enlarge the test support. -/
theorem flux_derivative_support_subset (p η : Plane → ℝ) (z : Plane) :
    tsupport (fun m => fderiv ℝ (fun x => p x * η x) m z) ⊆ tsupport η := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro m hm
  by_contra hnot
  have ha : m ∉ tsupport (fun x => p x * η x) :=
    fun h => hnot (flux_support_subset p η h)
  have hd := fderiv_of_notMem_tsupport ℝ ha
  exact hm (by dsimp only; rw [hd]; rfl)

/-- When the prior vanishes, an interior test flux and every directional
flux derivative vanish; this justifies cancellation with the joint density. -/
theorem flux_zero_of_prior_zero {Ω : Set Plane} {p η : Plane → ℝ}
    (hp : ∀ m ∈ Ω, 0 < p m) (hs : tsupport η ⊆ Ω)
    {m : Plane} (hm : p m = 0) (z : Plane) :
    p m * η m = 0 ∧ fderiv ℝ (fun x => p x * η x) m z = 0 := by
  have hn : m ∉ tsupport η := by
    intro h
    have hh := hp m (hs h)
    rw [hm] at hh
    exact lt_irrefl 0 hh
  have ha : m ∉ tsupport (fun x => p x * η x) :=
    fun h => hn (flux_support_subset p η h)
  constructor
  · simp [hm]
  · rw [fderiv_of_notMem_tsupport ℝ ha]
    rfl

private theorem quotient_support_subset (g p : Plane → ℝ) :
    tsupport (fun m => g m / p m) ⊆ tsupport g := by
  apply closure_mono
  intro m hm hg
  exact hm (by simp [hg])

/-- Division by a locally positive prior is continuous when the numerator
is continuously supported in the prior's regular open region. -/
theorem localized_division {Ω : Set Plane} (hΩ : IsOpen Ω)
    {p g : Plane → ℝ} (hp : ContinuousOn p Ω)
    (hpos : ∀ m ∈ Ω, 0 < p m)
    (hg : Continuous g) (hgs : HasCompactSupport g) (hs : tsupport g ⊆ Ω) :
    Continuous (fun m => g m / p m) ∧
      HasCompactSupport (fun m => g m / p m) ∧
      Integrable (fun m => g m / p m) := by
  have hc : Continuous (fun m => g m / p m) :=
    (hg.continuousOn.div hp (fun m hm => ne_of_gt (hpos m hm))).continuous_of_tsupport_subset
      hΩ ((quotient_support_subset g p).trans hs)
  have hcomp : HasCompactSupport (fun m => g m / p m) :=
    hgs.mono (by intro m hm hgzero; exact hm (by simp [hgzero]))
  exact ⟨hc, hcomp, hc.integrable_of_hasCompactSupport hcomp⟩

private theorem square_support_subset (g : Plane → ℝ) :
    tsupport (fun m => g m ^ 2) ⊆ tsupport g := by
  apply closure_mono
  intro m hm hgzero
  exact hm (by simp [hgzero])

/-- Finite weighted flux energy follows from the manuscript's local prior
regularity and the compact interior test support. -/
theorem flux_energy_regular {Ω : Set Plane} (hΩ : IsOpen Ω)
    {p η : Plane → ℝ} (hp : ContDiffOn ℝ 1 p Ω)
    (hpos : ∀ m ∈ Ω, 0 < p m) (hη : ContDiff ℝ 1 η)
    (hηs : HasCompactSupport η) (hs : tsupport η ⊆ Ω) :
    Continuous (fun m => (p m * η m)^2 / p m) ∧
      HasCompactSupport (fun m => (p m * η m)^2 / p m) ∧
      Integrable (fun m => (p m * η m)^2 / p m) := by
  have ha := flux_contDiff hΩ hp hη hs
  have has := flux_hasCompactSupport (p := p) hηs
  apply localized_division hΩ hp.continuousOn hpos (ha.continuous.pow 2)
  · exact has.comp_left (g := fun x : ℝ => x^2) (by norm_num)
  · exact (square_support_subset _).trans ((flux_support_subset p η).trans hs)

/-- Finite prior-score energy: no finite global Fisher information is assumed. -/
theorem flux_information_regular {Ω : Set Plane} (hΩ : IsOpen Ω)
    {p η : Plane → ℝ} (hp : ContDiffOn ℝ 1 p Ω)
    (hpos : ∀ m ∈ Ω, 0 < p m) (hη : ContDiff ℝ 1 η)
    (hηs : HasCompactSupport η) (hs : tsupport η ⊆ Ω) (z : Plane) :
    Continuous (fun m => (fderiv ℝ (fun x => p x * η x) m z)^2 / p m) ∧
      HasCompactSupport (fun m => (fderiv ℝ (fun x => p x * η x) m z)^2 / p m) ∧
      Integrable (fun m => (fderiv ℝ (fun x => p x * η x) m z)^2 / p m) := by
  have ha := flux_contDiff hΩ hp hη hs
  have has := flux_hasCompactSupport (p := p) hηs
  have hd : Continuous (fun m => fderiv ℝ (fun x => p x * η x) m z) :=
    (ha.continuous_fderiv le_rfl).clm_apply continuous_const
  apply localized_division hΩ hp.continuousOn hpos (hd.pow 2)
  · exact (has.fderiv_apply ℝ z).comp_left (g := fun x : ℝ => x^2) (by norm_num)
  · exact (square_support_subset _).trans ((flux_derivative_support_subset p η z).trans hs)


private theorem two_test_quotient_regular {Ω : Set Plane} (hΩ : IsOpen Ω)
    {p η₁ η₂ g : Plane → ℝ} (hp : ContinuousOn p Ω)
    (hpos : ∀ m ∈ Ω, 0 < p m) (hg : Continuous g)
    (h₁ : HasCompactSupport η₁) (h₂ : HasCompactSupport η₂)
    (hs₁ : tsupport η₁ ⊆ Ω) (hs₂ : tsupport η₂ ⊆ Ω)
    (hz : ∀ m, m ∉ tsupport η₁ → m ∉ tsupport η₂ → g m = 0) :
    Continuous (fun m => g m / p m) ∧ HasCompactSupport (fun m => g m / p m) ∧
      Integrable (fun m => g m / p m) := by
  let S := tsupport η₁ ∪ tsupport η₂
  have hsub : Function.support g ⊆ S := by
    intro m hm
    by_contra hn
    have h₁m : m ∉ tsupport η₁ := fun h => hn (Or.inl h)
    have h₂m : m ∉ tsupport η₂ := fun h => hn (Or.inr h)
    exact hm (hz m h₁m h₂m)
  have ht : tsupport g ⊆ S :=
    closure_minimal hsub ((isClosed_tsupport η₁).union (isClosed_tsupport η₂))
  have hgs : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact (h₁.isCompact.union h₂.isCompact) hsub
  exact localized_division hΩ hp hpos hg hgs (ht.trans (union_subset hs₁ hs₂))

/-- The full two-component flux divergence has a finite prior-information
term under the original locally regular prior assumptions. -/
theorem vector_flux_information_regular {Ω : Set Plane} (hΩ : IsOpen Ω)
    {p η₁ η₂ : Plane → ℝ} (hp : ContDiffOn ℝ 1 p Ω)
    (hpos : ∀ m ∈ Ω, 0 < p m)
    (hc₁ : ContDiff ℝ 1 η₁) (hc₂ : ContDiff ℝ 1 η₂)
    (h₁ : HasCompactSupport η₁) (h₂ : HasCompactSupport η₂)
    (hs₁ : tsupport η₁ ⊆ Ω) (hs₂ : tsupport η₂ ⊆ Ω) (z₁ z₂ : Plane) :
    let b := fun m => fderiv ℝ (fun x => p x * η₁ x) m z₁ +
      fderiv ℝ (fun x => p x * η₂ x) m z₂
    Continuous (fun m => b m ^ 2 / p m) ∧
      HasCompactSupport (fun m => b m ^ 2 / p m) ∧
      Integrable (fun m => b m ^ 2 / p m) := by
  dsimp only
  have ha₁ := flux_contDiff hΩ hp hc₁ hs₁
  have ha₂ := flux_contDiff hΩ hp hc₂ hs₂
  have hd₁ : Continuous (fun m => fderiv ℝ (fun x => p x * η₁ x) m z₁) :=
    (ha₁.continuous_fderiv le_rfl).clm_apply continuous_const
  have hd₂ : Continuous (fun m => fderiv ℝ (fun x => p x * η₂ x) m z₂) :=
    (ha₂.continuous_fderiv le_rfl).clm_apply continuous_const
  apply two_test_quotient_regular hΩ hp.continuousOn hpos ((hd₁.add hd₂).pow 2)
    h₁ h₂ hs₁ hs₂
  intro m hm₁ hm₂
  have hd₁zero : fderiv ℝ (fun x => p x * η₁ x) m z₁ = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun m => fderiv ℝ (fun x => p x * η₁ x) m z₁)
      (fun h => hm₁ (flux_derivative_support_subset p η₁ z₁ h))
  have hd₂zero : fderiv ℝ (fun x => p x * η₂ x) m z₂ = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun m => fderiv ℝ (fun x => p x * η₂ x) m z₂)
      (fun h => hm₂ (flux_derivative_support_subset p η₂ z₂ h))
  simp [hd₁zero, hd₂zero]

/-- The Gaussian mean-score energy of a full two-component compact flux is
finite for arbitrary linear mean maps, including singular mean matrices. -/
theorem vector_flux_energy_regular {Ω : Set Plane} (hΩ : IsOpen Ω)
    {p η₁ η₂ : Plane → ℝ} (hp : ContDiffOn ℝ 1 p Ω)
    (hpos : ∀ m ∈ Ω, 0 < p m)
    (hc₁ : ContDiff ℝ 1 η₁) (hc₂ : ContDiff ℝ 1 η₂)
    (h₁ : HasCompactSupport η₁) (h₂ : HasCompactSupport η₂)
    (hs₁ : tsupport η₁ ⊆ Ω) (hs₂ : tsupport η₂ ⊆ Ω) (z₁ z₂ : Plane)
    (r₁ r₂ : Plane →L[ℝ] ℝ) :
    let A := fun m => (p m * η₁ m) • z₁ + (p m * η₂ m) • z₂
    Continuous (fun m => ((r₁ (A m))^2 + (r₂ (A m))^2) / p m) ∧
      HasCompactSupport (fun m => ((r₁ (A m))^2 + (r₂ (A m))^2) / p m) ∧
      Integrable (fun m => ((r₁ (A m))^2 + (r₂ (A m))^2) / p m) := by
  dsimp only
  have ha₁ := flux_contDiff hΩ hp hc₁ hs₁
  have ha₂ := flux_contDiff hΩ hp hc₂ hs₂
  have hA : Continuous (fun m => (p m * η₁ m) • z₁ + (p m * η₂ m) • z₂) :=
    (ha₁.continuous.smul continuous_const).add (ha₂.continuous.smul continuous_const)
  apply two_test_quotient_regular hΩ hp.continuousOn hpos
    (((r₁.continuous.comp hA).pow 2).add ((r₂.continuous.comp hA).pow 2)) h₁ h₂ hs₁ hs₂
  intro m hm₁ hm₂
  have he₁ : η₁ m = 0 := image_eq_zero_of_notMem_tsupport hm₁
  have he₂ : η₂ m = 0 := image_eq_zero_of_notMem_tsupport hm₂
  simp [he₁, he₂]

end Analog.RegularPriorFlux
