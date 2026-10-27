import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

/-!
# A global C¹ extension from a closed interval

We extend the prescribed derivative by clamping its argument to the source
interval, and integrate that continuous extension. The resulting function
agrees with the original function throughout the closed interval, is globally
C¹, and has a bounded uniformly continuous derivative. Only continuity on the
closed interval and the derivative identity on its interior are assumed.
-/

noncomputable section
namespace Analog.EndpointExtension
open Set MeasureTheory
open scoped Topology

/-- Constant endpoint continuation of the prescribed derivative. -/
def clippedDerivative (a b : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  g (max a (min b x))

/-- Extension obtained by integrating the clamped derivative. -/
def extension (a b : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  f a + ∫ t in a..x, clippedDerivative a b g t

/-- Clamping does not change an argument in the original interval. -/
theorem clippedDerivative_eq {a b x : ℝ} (g : ℝ → ℝ) (hx : x ∈ Icc a b) :
    clippedDerivative a b g x = g x := by
  simp [clippedDerivative, min_eq_right hx.2, max_eq_right hx.1]

/-- The clamped derivative is globally continuous. -/
theorem clippedDerivative_continuous {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) : Continuous (clippedDerivative a b g) := by
  exact hg.restrict.comp (LipschitzWith.projIcc hab).continuous

/-- Compactness of the interval bounds the derivative at every real argument. -/
theorem clippedDerivative_bounded {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |clippedDerivative a b g x| ≤ M := by
  have hc : IsCompact (Set.range (fun x : Icc a b => |g x|)) :=
    isCompact_range hg.restrict.abs
  obtain ⟨M, hM⟩ := hc.bddAbove
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro x
  exact (hM (Set.mem_range_self (Set.projIcc a b hab x))).trans (le_max_left _ _)

/-- Heine-Cantor on the interval and nonexpansive clamping give global
uniform continuity of the extended derivative. -/
theorem clippedDerivative_uniformContinuous {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) : UniformContinuous (clippedDerivative a b g) := by
  have hu : UniformContinuous (fun x : Icc a b => g x) :=
    CompactSpace.uniformContinuous_of_continuous hg.restrict
  exact hu.comp (LipschitzWith.projIcc hab).uniformContinuous

/-- The fundamental theorem gives the derivative globally, including at both
original endpoints and outside the original interval. -/
theorem extension_hasDerivAt {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) (x : ℝ) :
    HasDerivAt (extension a b f g) (clippedDerivative a b g x) x := by
  have hc := clippedDerivative_continuous hab hg
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add (f a)

/-- Closed-interval agreement needs derivatives only in the open interior. -/
theorem extension_eq_on {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) :
    EqOn (extension a b f g) f (Icc a b) := by
  intro x hx
  have hc := clippedDerivative_continuous hab hg
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
    (hf.mono (fun t ht => ⟨ht.1, ht.2.trans hx.2⟩))
    (f' := clippedDerivative a b g)
    (fun t ht => by
      have ht' : t ∈ Ioo a b := ⟨ht.1, ht.2.trans_le hx.2⟩
      simpa only [clippedDerivative_eq g ⟨ht'.1.le, ht'.2.le⟩] using hderiv t ht')
    (hc.intervalIntegrable a x)
  unfold extension
  rw [hint]
  ring

/-- The actual constructed extension is globally C¹. -/
theorem extension_contDiff {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) : ContDiff ℝ 1 (extension a b f g) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (extension_hasDerivAt hab f hg x).differentiableAt, ?_⟩
  have he : deriv (extension a b f g) = clippedDerivative a b g :=
    funext (fun x => (extension_hasDerivAt hab f hg x).deriv)
  rw [he]
  exact clippedDerivative_continuous hab hg

/-- Existence form for downstream statistical arguments: all global regularity
and derivative bounds are obtained from the original closed-interval data. -/
theorem exists_global_extension {a b : ℝ} (hab : a < b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) :
    ∃ fbar gbar : ℝ → ℝ, ContDiff ℝ 1 fbar ∧ EqOn fbar f (Icc a b) ∧
      (∀ x, HasDerivAt fbar (gbar x) x) ∧ UniformContinuous gbar ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ x, |gbar x| ≤ M) ∧ EqOn gbar g (Icc a b) := by
  refine ⟨extension a b f g, clippedDerivative a b g,
    extension_contDiff hab.le f hg, extension_eq_on hab.le hf hg hderiv,
    extension_hasDerivAt hab.le f hg, clippedDerivative_uniformContinuous hab.le hg,
    clippedDerivative_bounded hab.le hg, ?_⟩
  intro x hx
  exact clippedDerivative_eq g hx

end Analog.EndpointExtension
