import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Support-preserving smooth approximation for statistical test fields

The approximation here is constructed by convolution with a normalized smooth
bump. It preserves compact support inside a prescribed open set, so it can be
used for the compactly supported test fields in weighted van Trees arguments.
-/

noncomputable section

namespace Analog.WeightedVariational

open Set Function Metric MeasureTheory ContinuousLinearMap
open scoped Topology Convolution ContDiff Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Every continuous compactly supported field can be approximated uniformly
by a smooth field whose compact support remains in the same prescribed open
set. The approximating function is built using a normalized convolution. -/
theorem smooth_compact_approximation {f : E → F} {Ω : Set E}
    (hf : Continuous f) (hc : HasCompactSupport f) (hΩ : IsOpen Ω)
    (hs : tsupport f ⊆ Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ Ω ∧ ∀ x, dist (g x) (f x) ≤ ε := by
  borelize E
  let μ : Measure E := Measure.addHaar
  obtain ⟨δs, hδs, hthick⟩ := hc.isCompact.exists_cthickening_subset_open hΩ hs
  obtain ⟨δu, hδu, hu⟩ := Metric.uniformContinuous_iff.mp
    (hc.uniformContinuous_of_continuous hf) ε hε
  let δ := min δs δu
  have hδ : 0 < δ := lt_min hδs hδu
  let φ : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let g : E → F := φ.normed μ ⋆[lsmul ℝ ℝ, μ] f
  have hgc : HasCompactSupport g := φ.hasCompactSupport_normed.convolution _ hc
  refine ⟨g, φ.hasCompactSupport_normed.contDiff_convolution_left _
      φ.contDiff_normed hf.locallyIntegrable, hgc, ?_, ?_⟩
  · apply subset_trans ?_ hthick
    apply closure_minimal ?_ isClosed_cthickening
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := support_convolution_subset_swap (lsmul ℝ ℝ) hx
    apply mem_cthickening_of_dist_le (y + z) y δs (tsupport f)
      (subset_tsupport f hy)
    have hz' : ‖z‖ < δ := by
      rw [φ.support_normed_eq] at hz
      simpa [φ, mem_ball] using hz
    have he : dist (y + z) y = ‖z‖ := by simp [dist_eq_norm]
    rw [he]
    exact hz'.le.trans (min_le_left _ _)
  · intro x
    apply φ.dist_normed_convolution_le hf.aestronglyMeasurable
    intro y hy
    apply le_of_lt
    apply hu
    exact (show dist y x < δ from hy).trans_le (min_le_right _ _)

/-- A compact set inside an open set has a continuous cutoff, with compact
support still strictly inside the open set. -/
theorem compact_cutoff {K Ω : Set E} (hK : IsCompact K) (hΩ : IsOpen Ω)
    (hsub : K ⊆ Ω) :
    ∃ χ : E → ℝ, Continuous χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨L, hL, hLc, hKL, hLΩ⟩ := exists_compact_closed_between hK hΩ hsub
  obtain ⟨χ, hχK, hχL, hχc, hχrange⟩ :=
    exists_continuous_one_zero_of_isCompact hK isOpen_interior.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hKL)
  refine ⟨χ, χ.continuous, hχc, ?_, hχrange, hχK⟩
  apply subset_trans ?_ hLΩ
  apply closure_minimal ?_ hLc
  intro x hx
  by_contra hn
  have hzero := hχL (show x ∈ (interior L)ᶜ from fun h => hn (interior_subset h))
  exact hx hzero

/-- A sequence of interior compact cutoffs is eventually one at every point
of the open set. This uses an actual compact exhaustion, not an approximation
hypothesis on the desired field. -/
theorem compact_cutoff_sequence {Ω : Set E} (hΩ : IsOpen Ω) :
    ∃ χ : ℕ → E → ℝ,
      (∀ n, Continuous (χ n) ∧ HasCompactSupport (χ n) ∧ tsupport (χ n) ⊆ Ω ∧
        ∀ x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧
      ∀ x ∈ Ω, ∀ᶠ n in Filter.atTop, χ n x = 1 := by
  letI : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let K : ℕ → Set E := fun n => Subtype.val '' compactCovering Ω n
  have hK : ∀ n, IsCompact (K n) := fun n =>
    (isCompact_compactCovering Ω n).image continuous_subtype_val
  have hsub : ∀ n, K n ⊆ Ω := fun n => Subtype.coe_image_subset _ _
  choose χ hχc hχk hχs hχb hχ1 using fun n => compact_cutoff (hK n) hΩ (hsub n)
  refine ⟨χ, fun n => ⟨hχc n, hχk n, hχs n, hχb n⟩, ?_⟩
  intro x hx
  obtain ⟨N, hN⟩ := exists_mem_compactCovering (⟨x, hx⟩ : Ω)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  apply hχ1 n
  exact ⟨⟨x, hx⟩, compactCovering_subset Ω hn hN, rfl⟩

section FinitePrior

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

/-- Support-preserving smoothing has an explicit squared-L² error under
any probability measure, including a nonuniform prior density. -/
theorem smooth_compact_approximation_L2 {f : E → F} {Ω : Set E}
    (hf : Continuous f) (hc : HasCompactSupport f) (hΩ : IsOpen Ω)
    (hs : tsupport f ⊆ Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ Ω ∧ Integrable (fun x => ‖g x - f x‖ ^ 2) μ ∧
      (∫ x, ‖g x - f x‖ ^ 2 ∂μ) ≤ ε ^ 2 := by
  obtain ⟨g, hg, hgc, hgs, hdist⟩ := smooth_compact_approximation hf hc hΩ hs hε
  refine ⟨g, hg, hgc, hgs, ?_, ?_⟩
  · exact ((hg.continuous.sub hf).norm.pow 2).integrable_of_hasCompactSupport
      ((hgc.sub hc).comp_left (g := fun a : F => ‖a‖ ^ 2) (by simp))
  have hbound : ∀ x, ‖g x - f x‖ ^ 2 ≤ ε ^ 2 := by
    intro x
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa [dist_eq_norm] using hdist x) 2
  have hint := integral_mono_of_nonneg (μ := μ)
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖g x - f x‖))
    (integrable_const (ε ^ 2)) (Filter.Eventually.of_forall hbound)
  simpa using hint

omit [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure μ] in
/-- Construct smooth interior test fields converging pointwise, with an
explicit norm-error dominator. No prior measure is needed for this construction. -/
theorem smooth_test_field_approximation {f : E → F} {Ω : Set E}
    (hf : Continuous f) (hΩ : IsOpen Ω) :
    ∃ g : ℕ → E → F,
      (∀ n, ContDiff ℝ ∞ (g n) ∧ HasCompactSupport (g n) ∧ tsupport (g n) ⊆ Ω) ∧
      (∀ n x, ‖g n x - f x‖ ≤ 1 + ‖f x‖) ∧
      ∀ x ∈ Ω, Filter.Tendsto (fun n => g n x) Filter.atTop (𝓝 (f x)) := by
  obtain ⟨χ, hχ, hχ1⟩ := compact_cutoff_sequence hΩ
  let u : ℕ → E → F := fun n x => χ n x • f x
  have hu : ∀ n, Continuous (u n) := fun n => (hχ n).1.smul hf
  have huk : ∀ n, HasCompactSupport (u n) := fun n => (hχ n).2.1.smul_right
  have hus : ∀ n, tsupport (u n) ⊆ Ω := fun n =>
    (tsupport_smul_subset_left (χ n) f).trans (hχ n).2.2.1
  have hpos : ∀ n : ℕ, 0 < (1 / ((n : ℝ) + 1)) := fun n => by positivity
  choose g hg hgk hgs hdist using fun n =>
    smooth_compact_approximation (hu n) (huk n) hΩ (hus n) (hpos n)
  have huerr : ∀ n x, ‖u n x - f x‖ ≤ ‖f x‖ := by
    intro n x
    have hb := (hχ n).2.2.2 x
    have he : u n x - f x = (χ n x - 1) • f x := by simp [u, sub_smul]
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith : χ n x - 1 ≤ 0)]
    nlinarith [norm_nonneg (f x)]
  have hgerr : ∀ n x, ‖g n x - f x‖ ≤ 1 + ‖f x‖ := by
    intro n x
    have hδ : (1 / ((n : ℝ) + 1)) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have ht := dist_triangle (g n x) (u n x) (f x)
    simp only [dist_eq_norm] at ht
    have hd : ‖g n x - u n x‖ ≤ 1 / ((n : ℝ) + 1) := by
      simpa only [dist_eq_norm] using hdist n x
    linarith [huerr n x]
  have hpt : ∀ x ∈ Ω, Filter.Tendsto (fun n => g n x) Filter.atTop (𝓝 (f x)) := by
    intro x hx
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero' (Filter.Eventually.of_forall (fun n => dist_nonneg)) ?_
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hχ1 x hx] with n hn
    have he : u n x = f x := by simp [u, hn]
    simpa only [he] using hdist n x
  exact ⟨g, fun n => ⟨hg n, hgk n, hgs n⟩, hgerr, hpt⟩

/-- Every continuous square-integrable field can be approximated in the
actual prior L² norm by smooth compactly supported fields inside a full-measure
open set. The cutoff and mollification sequences are constructed, not assumed. -/
theorem smooth_test_field_L2_density {f : E → F} {Ω : Set E}
    (hf : Continuous f) (hΩ : IsOpen Ω) (hfull : ∀ᵐ x ∂μ, x ∈ Ω)
    (hL2 : Integrable (fun x => ‖f x‖ ^ 2) μ) :
    ∃ g : ℕ → E → F,
      (∀ n, ContDiff ℝ ∞ (g n) ∧ HasCompactSupport (g n) ∧ tsupport (g n) ⊆ Ω) ∧
      Filter.Tendsto (fun n => ∫ x, ‖g n x - f x‖ ^ 2 ∂μ)
        Filter.atTop (𝓝 0) := by
  obtain ⟨g, hg, hgerr, hpt⟩ := smooth_test_field_approximation hf hΩ
  refine ⟨g, hg, ?_⟩
  have hi := tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun n x => ‖g n x - f x‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun x => 2 + 2 * ‖f x‖ ^ 2)
    (fun n => (((hg n).1.continuous.sub hf).norm.pow 2).aestronglyMeasurable)
    ((integrable_const 2).add (hL2.const_mul 2))
    (fun n => Filter.Eventually.of_forall (fun x => ?_))
    (hfull.mono (fun x hx => ?_))
  · simpa using hi
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := hgerr n x
    nlinarith [sq_nonneg (‖f x‖ - 1), norm_nonneg (g n x - f x), norm_nonneg (f x)]
  · simpa using (((hpt x hx).sub (tendsto_const_nhds (x := f x))).norm.pow 2)

end FinitePrior

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace H] [BorelSpace E] in
/-- Identify the genuine L² inner product with the integral of the supplied
representatives; the representatives need only be square integrable. -/
theorem inner_toLp_eq_integral {f g : E → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace H] [BorelSpace E] in
/-- The integrated Cauchy--Schwarz inequality used in the variational
statistical converse. All moments are actual integrals, not formal variables. -/
theorem integral_inner_square_le {f g : E → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, inner ℝ (f x) (g x) ∂μ) ^ 2 ≤
      (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [inner_toLp_eq_integral hf hg, inner_toLp_eq_integral hf hf,
    inner_toLp_eq_integral hg hg] at h
  simpa only [real_inner_self_eq_norm_sq, pow_two] using h

variable [IsProbabilityMeasure μ]

/-- Smooth interior fields approximate both quadratic moments in the
variational Cauchy--Schwarz bound. The approximating fields are constructed. -/
theorem smooth_test_moments {f : E → H} {Ω : Set E}
    (hf : Continuous f) (hΩ : IsOpen Ω) (hfull : ∀ᵐ x ∂μ, x ∈ Ω)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C) :
    ∃ g : ℕ → E → H,
      (∀ n, ContDiff ℝ ∞ (g n) ∧ HasCompactSupport (g n) ∧ tsupport (g n) ⊆ Ω) ∧
      Filter.Tendsto (fun n => ∫ x, inner ℝ (g n x) (f x) ∂μ)
        Filter.atTop (𝓝 (∫ x, ‖f x‖ ^ 2 ∂μ)) ∧
      Filter.Tendsto (fun n => ∫ x, ‖g n x‖ ^ 2 ∂μ)
        Filter.atTop (𝓝 (∫ x, ‖f x‖ ^ 2 ∂μ)) := by
  obtain ⟨g, hg, herr, hpt⟩ := smooth_test_field_approximation hf hΩ
  have hgb : ∀ n x, ‖g n x‖ ≤ 1 + 2 * C := by
    intro n x
    have h := norm_add_le (g n x - f x) (f x)
    rw [sub_add_cancel] at h
    linarith [herr n x, hbound x]
  refine ⟨g, hg, ?_, ?_⟩
  · have hi := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => inner ℝ (g n x) (f x)) (f := fun x => ‖f x‖ ^ 2)
      (fun _ => (1 + 2 * C) * C)
      (fun n => ((hg n).1.continuous.inner hf).aestronglyMeasurable)
      (integrable_const _) (fun n => Filter.Eventually.of_forall (fun x => ?_))
      (hfull.mono (fun x hx => ?_))
    · exact hi
    · exact (norm_inner_le_norm _ _).trans
        (mul_le_mul (hgb n x) (hbound x) (norm_nonneg _) (by positivity))
    · simpa only [real_inner_self_eq_norm_sq] using
        (hpt x hx).inner (𝕜 := ℝ) (tendsto_const_nhds (x := f x))
  · apply tendsto_integral_of_dominated_convergence (fun _ => (1 + 2 * C) ^ 2)
    · intro n
      exact ((hg n).1.continuous.norm.pow 2).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      apply Filter.Eventually.of_forall
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hgb n x) 2
    · exact hfull.mono (fun x hx => (hpt x hx).norm.pow 2)

/-- Values of the actual variational quotient on smooth compact interior
fields. A zero-energy field contributes zero under real total division. -/
def smoothVariationalValues (f : E → H) (Ω : Set E) (μ : Measure E) : Set ℝ :=
  {q | ∃ g : E → H, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ω ∧
    q = (∫ x, inner ℝ (g x) (f x) ∂μ) ^ 2 / (∫ x, ‖g x‖ ^ 2 ∂μ)}

/-- The smooth-test variational supremum equals the true squared L² norm.
This derives the lower bound from constructed interior cutoffs and smoothing;
no variational equality or approximating sequence is assumed. -/
theorem smooth_variational_supremum {f : E → H} {Ω : Set E}
    (hf : Continuous f) (hΩ : IsOpen Ω) (hfull : ∀ᵐ x ∂μ, x ∈ Ω)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C) :
    sSup (smoothVariationalValues f Ω μ) = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  let T : ℝ := ∫ x, ‖f x‖ ^ 2 ∂μ
  have hT : 0 ≤ T := integral_nonneg (fun _ => sq_nonneg _)
  have hf2 : MemLp f 2 μ := MemLp.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall hbound)
  have hzero : 0 ∈ smoothVariationalValues f Ω μ := by
    refine ⟨fun _ => 0, contDiff_const, ?_, ?_, ?_⟩
    · exact HasCompactSupport.zero
    · change tsupport (0 : E → H) ⊆ Ω
      simp [tsupport]
    · simp
  have hb : ∀ q ∈ smoothVariationalValues f Ω μ, q ≤ T := by
    rintro q ⟨g, hg, hgk, _, rfl⟩
    have hg2 : MemLp g 2 μ := (memLp_two_iff_integrable_sq_norm hg.continuous.aestronglyMeasurable).mpr
      ((hg.continuous.norm.pow 2).integrable_of_hasCompactSupport
        (hgk.comp_left (g := fun a : H => ‖a‖ ^ 2) (by simp)))
    have hB : 0 ≤ ∫ x, ‖g x‖ ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
    by_cases hz : (∫ x, ‖g x‖ ^ 2 ∂μ) = 0
    · simpa only [hz, div_zero] using hT
    · exact (div_le_iff₀ (lt_of_le_of_ne hB (Ne.symm hz))).mpr
        (by simpa only [T, mul_comm] using integral_inner_square_le hg2 hf2)
  have hbd : BddAbove (smoothVariationalValues f Ω μ) := ⟨T, hb⟩
  apply le_antisymm (csSup_le ⟨0, hzero⟩ hb)
  by_cases hT0 : T = 0
  · simpa only [hT0] using le_csSup hbd hzero
  · obtain ⟨g, hg, hA, hB⟩ := smooth_test_moments hf hΩ hfull hC hbound
    have hq := (hA.pow 2).div hB hT0
    have he : T ^ 2 / T = T := by field_simp
    change Filter.Tendsto
      (fun n => (∫ x, inner ℝ (g n x) (f x) ∂μ) ^ 2 / (∫ x, ‖g n x‖ ^ 2 ∂μ))
      Filter.atTop (𝓝 (T ^ 2 / T)) at hq
    rw [he] at hq
    apply le_of_tendsto' hq
    intro n
    exact le_csSup hbd ⟨g n, (hg n).1, (hg n).2.1, (hg n).2.2, rfl⟩

/-- A positive variational value is approached by actual positive-energy
smooth interior tests. This excludes any reliance on real division at zero
when the test is used in a statistical information denominator. -/
theorem positive_energy_test_approaches_supremum {f : E → H} {Ω : Set E}
    (hf : Continuous f) (hΩ : IsOpen Ω) (hfull : ∀ᵐ x ∂μ, x ∈ Ω)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C)
    (hT : 0 < ∫ x, ‖f x‖ ^ 2 ∂μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → H, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ω ∧
      0 < (∫ x, ‖g x‖ ^ 2 ∂μ) ∧
      (∫ x, ‖f x‖ ^ 2 ∂μ) - ε <
        (∫ x, inner ℝ (g x) (f x) ∂μ) ^ 2 / (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  obtain ⟨g, hg, hA, hB⟩ := smooth_test_moments hf hΩ hfull hC hbound
  let T := ∫ x, ‖f x‖ ^ 2 ∂μ
  have hq := (hA.pow 2).div hB (ne_of_gt hT)
  have he : T ^ 2 / T = T := by dsimp [T]; field_simp
  change Filter.Tendsto
    (fun n => (∫ x, inner ℝ (g n x) (f x) ∂μ) ^ 2 / (∫ x, ‖g n x‖ ^ 2 ∂μ))
    Filter.atTop (𝓝 (T ^ 2 / T)) at hq
  rw [he] at hq
  have heB := (tendsto_order.mp hB).1 0 hT
  have heq := (tendsto_order.mp hq).1 (T - ε) (sub_lt_self T hε)
  obtain ⟨n, hnB, hnq⟩ := (heB.and heq).exists
  exact ⟨g n, (hg n).1, (hg n).2.1, (hg n).2.2, hnB, hnq⟩

/-- Weighted smooth-test values after an actual invertible linear change
of coordinates. For a Gram factor S, the denominator is the Gram energy. -/
def weightedSmoothVariationalValues (S : H ≃L[ℝ] H) (f : E → H)
    (Ω : Set E) (μ : Measure E) : Set ℝ :=
  {q | ∃ g : E → H, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ω ∧
    q = (∫ x, inner ℝ (S (g x)) (f x) ∂μ) ^ 2 / (∫ x, ‖S (g x)‖ ^ 2 ∂μ)}

omit [FiniteDimensional ℝ E] [CompleteSpace H] [BorelSpace E] [IsProbabilityMeasure μ] in
/-- An invertible linear transformation preserves the class of smooth
compact interior fields, so the weighted variational set is exact. -/
theorem weighted_variational_values_eq (S : H ≃L[ℝ] H) (f : E → H)
    (Ω : Set E) (μ : Measure E) :
    weightedSmoothVariationalValues S f Ω μ = smoothVariationalValues f Ω μ := by
  have hsupp : ∀ (L : H →L[ℝ] H) (g : E → H), tsupport (fun x => L (g x)) ⊆ tsupport g := by
    intro L g
    apply closure_mono
    intro x hx hz
    apply hx
    simp only [hz, map_zero]
  ext q
  constructor
  · rintro ⟨g, hg, hgk, hgs, rfl⟩
    exact ⟨fun x => S (g x), S.contDiff.comp hg, hgk.comp_left (map_zero S),
      (hsupp S.toContinuousLinearMap g).trans hgs, rfl⟩
  · rintro ⟨g, hg, hgk, hgs, rfl⟩
    refine ⟨fun x => S.symm (g x), S.symm.contDiff.comp hg,
      hgk.comp_left (map_zero S.symm), (hsupp S.symm.toContinuousLinearMap g).trans hgs, ?_⟩
    simp only [S.apply_symm_apply]

/-- Weighted variational identity, with the Gram geometry represented by
an actual invertible linear factor rather than an assumed optimal quotient. -/
theorem weighted_smooth_variational_supremum (S : H ≃L[ℝ] H)
    {f : E → H} {Ω : Set E} (hf : Continuous f) (hΩ : IsOpen Ω)
    (hfull : ∀ᵐ x ∂μ, x ∈ Ω) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C) :
    sSup (weightedSmoothVariationalValues S f Ω μ) = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [weighted_variational_values_eq]
  exact smooth_variational_supremum hf hΩ hfull hC hbound

/-- The actual Gram-weighted quotient, with untransformed gradient field. -/
def gramVariationalValues (S : H ≃L[ℝ] H) (w : E → H)
    (Ω : Set E) (μ : Measure E) : Set ℝ :=
  {q | ∃ g : E → H, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ω ∧
    q = (∫ x, inner ℝ (g x) (w x) ∂μ) ^ 2 / (∫ x, ‖S (g x)‖ ^ 2 ∂μ)}

/-- The Gram-weighted variational supremum equals the actual inverse-Gram
energy. For a matrix S with G=SᵀS, the integrand is wᵀG⁻¹w. All test fields and
moments are genuine functions and integrals under the supplied prior. -/
theorem inverse_gram_variational_supremum (S : H ≃L[ℝ] H)
    {w : E → H} {Ω : Set E} (hw : Continuous w) (hΩ : IsOpen Ω)
    (hfull : ∀ᵐ x ∂μ, x ∈ Ω) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖w x‖ ≤ C) :
    sSup (gramVariationalValues S w Ω μ) =
      ∫ x, ‖S.symm.toContinuousLinearMap.adjoint (w x)‖ ^ 2 ∂μ := by
  let B : H →L[ℝ] H := S.symm.toContinuousLinearMap.adjoint
  have hp : ∀ a b : H, inner ℝ (S a) (B b) = inner ℝ a b := by
    intro a b
    dsimp only [B]
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp only [ContinuousLinearEquiv.coe_coe, S.symm_apply_apply]
  have he : gramVariationalValues S w Ω μ =
      weightedSmoothVariationalValues S (fun x => B (w x)) Ω μ := by
    ext q
    simp only [gramVariationalValues, weightedSmoothVariationalValues, mem_setOf_eq, hp]
  rw [he]
  apply weighted_smooth_variational_supremum S (B.continuous.comp hw) hΩ hfull
    (mul_nonneg (norm_nonneg B) hC)
  intro x
  exact (B.le_opNorm (w x)).trans (mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg B))

/-- A nonzero continuous bounded scalar projection admits an actual smooth
compact interior test with strictly positive correlation. This supplies the
nonvanishing test required to exclude a singular Gram limit. -/
theorem exists_positive_scalar_test {f : E → ℝ} {Ω : Set E}
    (hf : Continuous f) (hΩ : IsOpen Ω) (hfull : ∀ᵐ x ∂μ, x ∈ Ω)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C)
    (hpositive : 0 < ∫ x, f x ^ 2 ∂μ) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
      0 < ∫ x, χ x * f x ∂μ := by
  obtain ⟨g, hg, hA, _⟩ := smooth_test_moments hf hΩ hfull hC hbound
  have hpos : 0 < ∫ x, ‖f x‖ ^ 2 ∂μ := by simpa using hpositive
  have hev := (tendsto_order.mp hA).1 0 hpos
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨g n, (hg n).1, (hg n).2.1, (hg n).2.2, ?_⟩
  simpa only [real_inner_comm, RCLike.inner_apply, conj_trivial, mul_comm] using hn

end Hilbert

end Analog.WeightedVariational
