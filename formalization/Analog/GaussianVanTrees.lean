import Analog.GaussianScoreIdentity
import Analog.RegularPriorFlux
import Analog.BorelRisk

/-!
# A model-level Gaussian van Trees inequality for regular priors

The prior is only C¹ and positive on an open set containing the compact test
supports; it need not be regular elsewhere or have finite global Fisher
information. The theorem constructs the actual Gaussian joint law, derives
its score covariance and information, and clips arbitrary Borel estimators
before transferring the bound to their genuine nonnegative (possibly infinite)
risk. No information inequality, covariance identity, or score-integrability
conclusion is assumed.
-/

noncomputable section
namespace Analog.GaussianVanTrees
open MeasureTheory Set GaussianScoreIdentity RegularPriorFlux
open scoped Topology NNReal ENNReal

abbrev Plane := ℝ × ℝ

def sensitivity (p f η₁ η₂ : Plane → ℝ) (z w : Plane) : ℝ :=
  (∫ m, fderiv ℝ f m z * (p m * η₁ m)) +
    (∫ m, fderiv ℝ f m w * (p m * η₂ m))

def priorInformation (p η₁ η₂ : Plane → ℝ) (z w : Plane) : ℝ :=
  ∫ m, (fderiv ℝ (fun x => p x * η₁ x) m z +
    fderiv ℝ (fun x => p x * η₂ x) m w)^2 / p m

def channelInformation (p η₁ η₂ : Plane → ℝ) (z w : Plane)
    (r₁ r₂ : Plane →L[ℝ] ℝ) : ℝ :=
  ∫ m, ((r₁ ((p m * η₁ m) • z + (p m * η₂ m) • w))^2 +
    (r₂ ((p m * η₁ m) • z + (p m * η₂ m) • w))^2) / p m

/-- All regular compact tests have finite actual Gaussian score information,
with the exact prior-plus-channel decomposition. -/
theorem regular_score_information {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (η₁ η₂ : Plane → ℝ) (hη₁ : ContDiff ℝ 1 η₁) (hη₂ : ContDiff ℝ 1 η₂)
    (hc₁ : HasCompactSupport η₁) (hc₂ : HasCompactSupport η₂)
    (hs₁ : tsupport η₁ ⊆ Ω) (hs₂ : tsupport η₂ ⊆ Ω)
    (z w : Plane) (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane)
    {v : ℝ≥0} (hv : v ≠ 0) :
    let S := twoFluxScore p (fun m => p m * η₁ m) (fun m => p m * η₂ m)
      z w r₁ r₂ c v
    MemLp S 2 (jointLaw p r₁ r₂ c v) ∧
      (∫ q, S q ^ 2 ∂jointLaw p r₁ r₂ c v) =
        priorInformation p η₁ η₂ z w + channelInformation p η₁ η₂ z w r₁ r₂ / (v : ℝ) := by
  dsimp only
  have ha := flux_contDiff hΩ hpC hη₁ hs₁
  have hb := flux_contDiff hΩ hpC hη₂ hs₂
  have hia := (flux_information_regular hΩ hpC hpPos hη₁ hc₁ hs₁ z).2.2
  have hEa := (flux_energy_regular hΩ hpC hpPos hη₁ hc₁ hs₁).2.2
  have hib := (flux_information_regular hΩ hpC hpPos hη₂ hc₂ hs₂ w).2.2
  have hEb := (flux_energy_regular hΩ hpC hpPos hη₂ hc₂ hs₂).2.2
  have hsa := fluxScore_memLp p hp hp0 _ ha z r₁ r₂ c hv hia hEa
  have hsb := fluxScore_memLp p hp hp0 _ hb w r₁ r₂ c hv hib hEb
  refine ⟨hsa.add hsb, ?_⟩
  rw [jointLaw_twoFlux_information p hp hp0 _ _ z w r₁ r₂ c hv hsa hsb]
  have hI := (vector_flux_information_regular hΩ hpC hpPos hη₁ hη₂ hc₁ hc₂ hs₁ hs₂ z w).2.2
  have hE := (vector_flux_energy_regular hΩ hpC hpPos hη₁ hη₂ hc₁ hc₂ hs₁ hs₂ z w r₁ r₂).2.2
  rw [integral_add hI (hE.div_const (v : ℝ)), integral_div]
  rfl

/-- Finite-risk form of the regular-prior Gaussian van Trees bound. Every
score regularity and integrability premise is derived from compact interior
tests and the actual locally regular prior. -/
theorem regular_information_bound {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (f η₁ η₂ : Plane → ℝ) (hf : ContDiff ℝ 1 f)
    (hη₁ : ContDiff ℝ 1 η₁) (hη₂ : ContDiff ℝ 1 η₂)
    (hc₁ : HasCompactSupport η₁) (hc₂ : HasCompactSupport η₂)
    (hs₁ : tsupport η₁ ⊆ Ω) (hs₂ : tsupport η₂ ⊆ Ω)
    (z w : Plane) (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane)
    {v : ℝ≥0} (hv : v ≠ 0) (D : Plane → ℝ)
    (he : MemLp (fun q : Plane × Plane => D q.2 - f q.1) 2 (jointLaw p r₁ r₂ c v))
    (hden : 0 < priorInformation p η₁ η₂ z w + channelInformation p η₁ η₂ z w r₁ r₂ / (v : ℝ)) :
    sensitivity p f η₁ η₂ z w ^ 2 /
      (priorInformation p η₁ η₂ z w + channelInformation p η₁ η₂ z w r₁ r₂ / (v : ℝ)) ≤
        ∫ q, (D q.2 - f q.1)^2 ∂jointLaw p r₁ r₂ c v := by
  have ha := flux_contDiff hΩ hpC hη₁ hs₁
  have hb := flux_contDiff hΩ hpC hη₂ hs₂
  have has := flux_hasCompactSupport (p := p) hc₁
  have hbs := flux_hasCompactSupport (p := p) hc₂
  have hia := (flux_information_regular hΩ hpC hpPos hη₁ hc₁ hs₁ z).2.2
  have hEa := (flux_energy_regular hΩ hpC hpPos hη₁ hc₁ hs₁).2.2
  have hib := (flux_information_regular hΩ hpC hpPos hη₂ hc₂ hs₂ w).2.2
  have hEb := (flux_energy_regular hΩ hpC hpPos hη₂ hc₂ hs₂).2.2
  have hsa := fluxScore_memLp p hp hp0 _ ha z r₁ r₂ c hv hia hEa
  have hsb := fluxScore_memLp p hp hp0 _ hb w r₁ r₂ c hv hib hEb
  have hcov := jointLaw_twoFlux_covariance p hp hp0 r₁ r₂ c hv f _ _ D z w
    hf ha hb has hbs
    (fun _ hm => flux_zero_of_prior_zero hpPos hs₁ hm z)
    (fun _ hm => flux_zero_of_prior_zero hpPos hs₂ hm w) he hsa hsb
  obtain ⟨hS, hinfo⟩ := regular_score_information hΩ p hp hp0 hpC hpPos η₁ η₂ hη₁ hη₂
    hc₁ hc₂ hs₁ hs₂ z w r₁ r₂ c hv
  have hpos : 0 < ∫ q, twoFluxScore p (fun m => p m*η₁ m) (fun m => p m*η₂ m)
      z w r₁ r₂ c v q ^ 2 ∂jointLaw p r₁ r₂ c v := by rwa [hinfo]
  have hbnd := information_bound_of_covariance (jointLaw p r₁ r₂ c v)
    (fun q => D q.2-f q.1) _ he hS hpos
  rw [hcov, hinfo] at hbnd
  exact hbnd

/-- Model-level van Trees bound for every Borel decoder, including decoders
of infinite risk. The prior needs no finite global Fisher information and
no regularity outside the test-support region. -/
theorem regular_prior_vanTrees {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (f η₁ η₂ : Plane → ℝ) (hf : ContDiff ℝ 1 f)
    (hη₁ : ContDiff ℝ 1 η₁) (hη₂ : ContDiff ℝ 1 η₂)
    (hc₁ : HasCompactSupport η₁) (hc₂ : HasCompactSupport η₂)
    (hs₁ : tsupport η₁ ⊆ Ω) (hs₂ : tsupport η₂ ⊆ Ω)
    (z w : Plane) (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane)
    {v : ℝ≥0} (hv : v ≠ 0) (D : Plane → ℝ) (hD : Measurable D)
    (lo hi : ℝ) (hlohi : lo ≤ hi)
    (htarget : ∀ᵐ q ∂jointLaw p r₁ r₂ c v, lo ≤ f q.1 ∧ f q.1 ≤ hi)
    (hden : 0 < priorInformation p η₁ η₂ z w + channelInformation p η₁ η₂ z w r₁ r₂ / (v : ℝ)) :
    ENNReal.ofReal (sensitivity p f η₁ η₂ z w ^ 2 /
      (priorInformation p η₁ η₂ z w + channelInformation p η₁ η₂ z w r₁ r₂ / (v : ℝ))) ≤
        BorelRisk.squareRisk (jointLaw p r₁ r₂ c v) (fun q => f q.1) (fun q => D q.2) := by
  letI := jointLaw_isProbability p hp0 hpi hpn r₁ r₂ c hv
  have ht : Measurable (fun q : Plane × Plane => f q.1) := hf.continuous.measurable.comp measurable_fst
  have hdec : Measurable (fun q : Plane × Plane => D q.2) := hD.comp measurable_snd
  have he := BorelRisk.clipped_error_memLp ht hdec hlohi htarget
  apply BorelRisk.lower_bound_of_clipped_risk ht hdec hlohi htarget
  exact regular_information_bound hΩ p hp hp0 hpC hpPos f η₁ η₂ hf hη₁ hη₂ hc₁ hc₂
    hs₁ hs₂ z w r₁ r₂ c hv (fun y => Decoder.clip lo hi (D y)) he hden

/-- Both explicit information contributions are nonnegative for a density. -/
theorem priorInformation_nonnegative (p η₁ η₂ : Plane → ℝ) (hp0 : ∀ m, 0 ≤ p m)
    (z w : Plane) : 0 ≤ priorInformation p η₁ η₂ z w :=
  integral_nonneg fun m => div_nonneg (sq_nonneg _) (hp0 m)

theorem channelInformation_nonnegative (p η₁ η₂ : Plane → ℝ) (hp0 : ∀ m, 0 ≤ p m)
    (z w : Plane) (r₁ r₂ : Plane →L[ℝ] ℝ) :
    0 ≤ channelInformation p η₁ η₂ z w r₁ r₂ :=
  integral_nonneg fun m => div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (hp0 m)

/-- The moment-prior bounded-target assumption suffices for the all-Borel
model-level inequality; no joint-law marginal assumption is required. -/
theorem regular_prior_vanTrees_of_prior {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (f η₁ η₂ : Plane → ℝ) (hf : ContDiff ℝ 1 f)
    (hη₁ : ContDiff ℝ 1 η₁) (hη₂ : ContDiff ℝ 1 η₂)
    (hc₁ : HasCompactSupport η₁) (hc₂ : HasCompactSupport η₂)
    (hs₁ : tsupport η₁ ⊆ Ω) (hs₂ : tsupport η₂ ⊆ Ω)
    (z w : Plane) (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane)
    {v : ℝ≥0} (hv : v ≠ 0) (D : Plane → ℝ) (hD : Measurable D)
    (lo hi : ℝ) (hlohi : lo ≤ hi)
    (htarget : ∀ᵐ m ∂priorLaw p, lo ≤ f m ∧ f m ≤ hi)
    (hden : 0 < priorInformation p η₁ η₂ z w + channelInformation p η₁ η₂ z w r₁ r₂ / (v : ℝ)) :
    ENNReal.ofReal (sensitivity p f η₁ η₂ z w ^ 2 /
      (priorInformation p η₁ η₂ z w + channelInformation p η₁ η₂ z w r₁ r₂ / (v : ℝ))) ≤
        BorelRisk.squareRisk (jointLaw p r₁ r₂ c v) (fun q => f q.1) (fun q => D q.2) := by
  have ht : ∀ᵐ q ∂jointLaw p r₁ r₂ c v, lo ≤ f q.1 ∧ f q.1 ≤ hi :=
    jointLaw_ae_of_priorLaw p hp hp0 r₁ r₂ c v (P := fun m => lo ≤ f m ∧ f m ≤ hi) htarget
  exact regular_prior_vanTrees hΩ p hp hp0 hpi hpn hpC hpPos f η₁ η₂ hf hη₁ hη₂ hc₁ hc₂
    hs₁ hs₂ z w r₁ r₂ c hv D hD lo hi hlohi ht hden

end Analog.GaussianVanTrees
