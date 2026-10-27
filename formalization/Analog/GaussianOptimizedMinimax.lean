import Analog.GaussianParameterChannel
import Analog.FixedPriorGaussianLimit
import Analog.GaussianMovingGram
import Analog.CompactRiskOptimization
import Analog.GaussianMinimaxConverse
import Analog.GaussianMinimaxUpper
import Analog.HeterogeneousMomentCompactness

/-!
# Optimization of the actual Gaussian minimax risk

This file assembles attained coefficient minimization, actual Gaussian
converses at regular and singular limits, and one fixed achieving decoder.
-/

noncomputable section
namespace Analog.GaussianOptimizedMinimax
open Set Filter MeasureTheory HeterogeneousAttainment GaussianDesignAttainment
open GaussianDesignCompactness GaussianParameterChannel GaussianBayesConverse
open GeneralTargetGaussianAchievability FixedPriorGaussianLimit
open GaussianWorstCase GaussianMinimaxConverse
open scoped Topology NNReal

abbrev Plane := ℝ × ℝ

def gradientCoordinates (f : Plane → ℝ) (m : Plane) : Plane :=
  ((gradient f m).re, (gradient f m).im)

theorem directional_derivative_coordinates (f : Plane → ℝ) (m z : Plane) :
    fderiv ℝ f m z = (gradientCoordinates f m).1*z.1 + (gradientCoordinates f m).2*z.2 := by
  have hz : z = z.1 • firstDirection + z.2 • secondDirection := by
    ext <;> simp [firstDirection, secondDirection]
  conv_lhs => rw [hz, map_add, map_smul, map_smul]
  simp only [gradientCoordinates, GaussianBayesConverse.gradient, smul_eq_mul]
  ring

/-- A singular two-column receiver has an actual nonzero real direction
annihilated by both rows. -/
theorem singular_kernel {K : ℕ} (p : Parameters K) (hp : coefficientDet p = 0) :
    ∃ z : Plane, z ≠ 0 ∧ firstRow p z = 0 ∧ secondRow p z = 0 := by
  by_cases hrow : p.2.1.1 = 0 ∧ p.2.2.1 = 0
  · by_cases hrow' : p.2.1.2 = 0 ∧ p.2.2.2 = 0
    · refine ⟨(1,0), by simp, ?_, ?_⟩ <;>
        simp [firstRow_apply, secondRow_apply, hrow.1, hrow.2, hrow'.1, hrow'.2]
    · refine ⟨(-p.2.2.2,p.2.1.2), ?_, ?_, ?_⟩
      · intro hz
        have h₁ := congrArg Prod.fst hz
        have h₂ := congrArg Prod.snd hz
        exact hrow' ⟨h₂, neg_eq_zero.mp h₁⟩
      · simp [firstRow_apply, hrow.1, hrow.2]
      · rw [secondRow_apply]
        simp only
        ring
  · refine ⟨(-p.2.2.1,p.2.1.1), ?_, ?_, ?_⟩
    · intro hz
      have h₁ := congrArg Prod.fst hz
      have h₂ := congrArg Prod.snd hz
      exact hrow ⟨h₂, neg_eq_zero.mp h₁⟩
    · rw [firstRow_apply]
      simp only
      ring
    · rw [secondRow_apply]
      have he : p.2.1.2 * (-p.2.2.1) + p.2.2.2 * p.2.1.1 = coefficientDet p := by
        unfold coefficientDet
        ring
      simp only
      rw [he, hp, mul_zero]

/-- Gradient spanning on a set whose interior is dense detects every nonzero
direction at an actual interior moment, where a local regular prior exists. -/
theorem interior_direction_witness {M : Set Plane}
    (hdense : M ⊆ closure (interior M)) (f : Plane → ℝ) (hf : ContDiff ℝ 1 f)
    (hspan : GradientSpans M (gradientCoordinates f)) {z : Plane} (hz : z ≠ 0) :
    ∃ m ∈ interior M, fderiv ℝ f m z ≠ 0 := by
  by_contra hn
  have hinside : interior M ⊆ {m | fderiv ℝ f m z = 0} := by
    intro m hm
    by_contra hne
    exact hn ⟨m, hm, hne⟩
  have hcont : Continuous (fun m => fderiv ℝ f m z) :=
    (hf.continuous_fderiv le_rfl).clm_apply continuous_const
  have hclosure : closure (interior M) ⊆ {m | fderiv ℝ f m z = 0} :=
    closure_minimal hinside (isClosed_eq hcont continuous_const)
  have hzero := hspan z.1 z.2 (fun m hm => by
    rw [← directional_derivative_coordinates]
    exact hclosure (hdense hm))
  exact hz (Prod.ext hzero.1 hzero.2)

theorem directional_derivative_bounded (f : Plane → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hgrad : ∀ m, ‖gradient f m‖ ≤ C) (z : Plane) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m, |fderiv ℝ f m z| ≤ B := by
  refine ⟨‖ArbitraryEncoder.asComplex z‖ * C, mul_nonneg (norm_nonneg _) hC, fun m => ?_⟩
  have he : fderiv ℝ f m z = inner ℝ (ArbitraryEncoder.asComplex z) (gradient f m) := by
    rw [directional_derivative_coordinates, complex_inner_coordinates]
    dsimp [gradientCoordinates, ArbitraryEncoder.asComplex]
    ring
  rw [he]
  exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
    (mul_le_mul_of_nonneg_left (hgrad m) (norm_nonneg _))

def normalizedDesignRisk {K : ℕ} (M : Set Plane) (f : Plane → ℝ)
    (p : Parameters K) (v : ℝ≥0) : ℝ :=
  minimaxRisk M f (firstRow p) (secondRow p) (totalOffset p) v / (2 * (v : ℝ))

def coefficientMaximum {K : ℕ} (M : Set Plane) (f : Plane → ℝ) (p : Parameters K) : ℝ :=
  sSup ((fun m => inverseCoefficient p (gradientCoordinates f) m / (2 * (K : ℝ)^2)) '' M)

theorem localCoefficient_parameter {K : ℕ} (hK : 0 < K) (f : Plane → ℝ)
    (p : Parameters K) (hp : coefficientDet p ≠ 0) (m : Plane) :
    localCoefficient f (channelEquiv hK p hp) m =
      inverseCoefficient p (gradientCoordinates f) m / (2 * (K : ℝ)^2) := by
  rw [localCoefficient, parameter_inverse_energy]
  dsimp only [inverseCoefficient, gradientCoordinates]
  ring

theorem maxCoefficient_parameter {K : ℕ} (hK : 0 < K) (M : Set Plane) (f : Plane → ℝ)
    (p : Parameters K) (hp : coefficientDet p ≠ 0) :
    maxCoefficient M f (channelEquiv hK p hp) = coefficientMaximum M f p := by
  unfold maxCoefficient coefficientMaximum
  simp only [localCoefficient_parameter hK f p hp]

/-- The actual coefficient-parameter receiver satisfies the full moving-design
minimax converse at every nonsingular parameter limit. -/
theorem parameter_regular_converse {K : ℕ} (hK : 0 < K)
    (M : Set Plane) (hne : M.Nonempty) (hregular : M ⊆ closure (interior M))
    (f : Plane → ℝ) (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hC : 0 ≤ C) (hgrad : ∀ m, ‖GaussianBayesConverse.gradient f m‖ ≤ C)
    (p : ℕ → Parameters K) (p₀ : Parameters K)
    (hp : ∀ n, coefficientDet (p n) ≠ 0) (hp₀ : coefficientDet p₀ ≠ 0)
    (hconv : Tendsto p atTop (𝓝 p₀))
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0))
    (lo hi : ℝ) (hlohi : lo ≤ hi) (hbound : ∀ m ∈ M, lo ≤ f m ∧ f m ≤ hi) :
    GaussianConverseLimits.LowerAsymptotic (fun n => normalizedDesignRisk M f (p n) (v n))
      (coefficientMaximum M f p₀) := by
  let S := fun n => channelEquiv hK (p n) (hp n)
  let S₀ := channelEquiv hK p₀ hp₀
  have hA : Tendsto (fun n => GaussianGramCoefficient.gramA (S n)) atTop
      (𝓝 (GaussianGramCoefficient.gramA S₀)) := by
    simp only [S, S₀, parameter_gramA]
    exact ((show Continuous (fun q : Parameters K => (K : ℝ)^2*(parameterPlanar q).A) by
      unfold parameterPlanar GramSynthesis.Planar.A; fun_prop).tendsto p₀).comp hconv
  have hB : Tendsto (fun n => GaussianGramCoefficient.gramB (S n)) atTop
      (𝓝 (GaussianGramCoefficient.gramB S₀)) := by
    simp only [S, S₀, parameter_gramB]
    exact ((show Continuous (fun q : Parameters K => (K : ℝ)^2*(parameterPlanar q).B) by
      unfold parameterPlanar GramSynthesis.Planar.B; fun_prop).tendsto p₀).comp hconv
  have hCross : Tendsto (fun n => GaussianGramCoefficient.gramC (S n)) atTop
      (𝓝 (GaussianGramCoefficient.gramC S₀)) := by
    simp only [S, S₀, parameter_gramC]
    exact ((show Continuous (fun q : Parameters K => (K : ℝ)^2*(parameterPlanar q).C) by
      unfold parameterPlanar GramSynthesis.Planar.C; fun_prop).tendsto p₀).comp hconv
  have h := moving_minimax_converse M hne hregular f hf hC hgrad S S₀ hA hB hCross
    (fun n => totalOffset (p n)) v hv hlim lo hi hlohi hbound
  simpa only [S, S₀, receiverFirst_eq, receiverSecond_eq, maxCoefficient_parameter,
    normalizedDesignRisk] using h

/-- Every singular parameter limit is excluded by an actual interior target
derivative and the likelihood-based divergent minimax risk. -/
theorem parameter_singular_converse {K : ℕ} (hK : 0 < K)
    (M : Set Plane) (hregular : M ⊆ closure (interior M))
    (f : Plane → ℝ) (hf : ContDiff ℝ 1 f)
    (hspan : GradientSpans M (gradientCoordinates f))
    {C : ℝ} (hC : 0 ≤ C) (hgrad : ∀ m, ‖GaussianBayesConverse.gradient f m‖ ≤ C)
    (p : ℕ → Parameters K) (p₀ : Parameters K)
    (hp : ∀ n, coefficientDet (p n) ≠ 0) (hp₀ : coefficientDet p₀ = 0)
    (hconv : Tendsto p atTop (𝓝 p₀))
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0))
    (lo hi : ℝ) (hlohi : lo ≤ hi) (hbound : ∀ m ∈ M, lo ≤ f m ∧ f m ≤ hi) :
    Tendsto (fun n => normalizedDesignRisk M f (p n) (v n)) atTop atTop := by
  obtain ⟨z, hz, hr, hi'⟩ := singular_kernel p₀ hp₀
  obtain ⟨x, hx, hdetect⟩ := interior_direction_witness hregular f hf hspan hz
  obtain ⟨B, hB, hb⟩ := directional_derivative_bounded f hC hgrad z
  have hElim : Tendsto (fun n => (firstRow (p n) z)^2+(secondRow (p n) z)^2) atTop (𝓝 0) := by
    simpa only [hr, hi', zero_pow (by norm_num : 2 ≠ 0), add_zero] using
      ((direction_energy_continuous z).tendsto p₀).comp hconv
  exact localized_singular_minimax_diverges M f hf z hx hdetect B hB hb
    (fun n => firstRow (p n)) (fun n => secondRow (p n)) (fun n => totalOffset (p n))
    v hv hlim lo hi hlohi hbound
    (fun n => direction_energy_positive hK (p n) (hp n) z hz) hElim

def prescribedCoordinates (r₁ r₂ : IntervalReadout) (m : Plane) : Plane :=
  (r₁.slope m.1, r₂.slope m.2)

def prescribedMaximum {K : ℕ} (M : Set Plane) (r₁ r₂ : IntervalReadout)
    (p : Parameters K) : ℝ :=
  sSup ((fun m => inverseCoefficient p (prescribedCoordinates r₁ r₂) m / (2 * (K : ℝ)^2)) '' M)

def optimizedRisk {K : ℕ} {X : Type*} [TopologicalSpace X]
    (γ : Fin K → C(X, Plane)) (P : ℝ) (M : Set Plane) (f : Plane → ℝ) (v : ℝ≥0) : ℝ :=
  sInf ((fun p => normalizedDesignRisk M f p v) ''
    {p : Parameters K | p ∈ coefficientPeakSet γ P ∧ coefficientDet p ≠ 0})

/-- The unnormalized actual risk infimum, before division by total noise. -/
def rawOptimizedRisk {K : ℕ} {X : Type*} [TopologicalSpace X]
    (γ : Fin K → C(X, Plane)) (P : ℝ) (M : Set Plane) (f : Plane → ℝ) (v : ℝ≥0) : ℝ :=
  sInf ((fun p : Parameters K => minimaxRisk M f (firstRow p) (secondRow p) (totalOffset p) v) ''
    {p : Parameters K | p ∈ coefficientPeakSet γ P ∧ coefficientDet p ≠ 0})

/-- Positive-noise normalization commutes with the actual design infimum.
This is an algebraic identity, not an exchange of optimization and limit. -/
theorem optimizedRisk_eq_infimum_div {K : ℕ} {X : Type*} [TopologicalSpace X]
    (γ : Fin K → C(X, Plane)) (P : ℝ) (M : Set Plane) (f : Plane → ℝ)
    (hne : {p : Parameters K | p ∈ coefficientPeakSet γ P ∧ coefficientDet p ≠ 0}.Nonempty)
    {v : ℝ≥0} (hv : 0 < v) :
    optimizedRisk γ P M f v = rawOptimizedRisk γ P M f v / (2 * (v : ℝ)) := by
  let Q := {p : Parameters K | p ∈ coefficientPeakSet γ P ∧ coefficientDet p ≠ 0}
  let R := fun p : Parameters K => minimaxRisk M f (firstRow p) (secondRow p) (totalOffset p) v
  let N : ℝ := 2 * (v : ℝ)
  have hN : 0 < N := mul_pos (by norm_num) (NNReal.coe_pos.mpr hv)
  have hR : ∀ p, 0 ≤ R p := fun p => minimaxRisk_nonnegative M f _ _ _ _
  have hnorm : BddBelow ((fun p => R p / N) '' Q) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, _, rfl⟩
    exact div_nonneg (hR p) hN.le
  have hraw : BddBelow (R '' Q) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, _, rfl⟩
    exact hR p
  change sInf ((fun p => R p / N) '' Q) = sInf (R '' Q) / N
  apply le_antisymm
  · apply (le_div_iff₀ hN).mpr
    apply le_csInf (hne.image R)
    rintro _ ⟨p, hp, rfl⟩
    exact (le_div_iff₀ hN).mp (csInf_le hnorm (mem_image_of_mem _ hp))
  · apply le_csInf (hne.image (fun p => R p / N))
    rintro _ ⟨p, hp, rfl⟩
    exact div_le_div_of_nonneg_right (csInf_le hraw (mem_image_of_mem _ hp)) hN.le

theorem gradientCoordinates_readout (r₁ r₂ : IntervalReadout) {m : Plane}
    (hm : Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂) :
    gradientCoordinates (planeExtension r₁ r₂) m = prescribedCoordinates r₁ r₂ m := by
  rw [gradientCoordinates, planeExtension_gradient]
  have hm₁ : m.1 ∈ Icc r₁.lower r₁.upper := hm.1
  have hm₂ : m.2 ∈ Icc r₂.lower r₂.upper := hm.2
  simp [prescribedCoordinates, extendedSlope, EndpointExtension.clippedDerivative_eq _ hm₁,
    EndpointExtension.clippedDerivative_eq _ hm₂]

theorem coefficientMaximum_prescribed {K : ℕ} (M : Set Plane) (r₁ r₂ : IntervalReadout)
    (hrect : ∀ m ∈ M, Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂) (p : Parameters K) :
    coefficientMaximum M (planeExtension r₁ r₂) p = prescribedMaximum M r₁ r₂ p := by
  unfold coefficientMaximum prescribedMaximum
  congr 1
  apply Set.image_congr
  intro m hm
  simp only [inverseCoefficient, gradientCoordinates_readout r₁ r₂ (hrect m hm)]

/-- The actual minimax risk optimized over all peak-feasible identifiable
heterogeneous coefficient designs converges to the attained inverse-Gram
minimum. The target and coefficient use the original prescribed readouts.
All statistical converse, compactness, singular exclusion, and achievable
upper bounds are derived from the displayed structural hypotheses. -/
theorem optimized_minimax_sequential_limit {K : ℕ} (hK : 0 < K)
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (γ : Fin K → C(X, Plane)) (hind : IndependentFeatures γ)
    {P : ℝ} (hP : 0 < P)
    (M : Set Plane) (hM : IsCompact M) (hne : M.Nonempty)
    (hregular : M ⊆ closure (interior M))
    (r₁ r₂ : IntervalReadout)
    (hrect : ∀ m ∈ M, Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂)
    (hspan : GradientSpans M (prescribedCoordinates r₁ r₂))
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0)) :
    ∃ pstar : Parameters K, pstar ∈ coefficientPeakSet γ P ∧ coefficientDet pstar ≠ 0 ∧
      (∀ p ∈ coefficientPeakSet γ P, coefficientDet p ≠ 0 →
        prescribedMaximum M r₁ r₂ pstar ≤ prescribedMaximum M r₁ r₂ p) ∧
      Tendsto (fun n => optimizedRisk γ P M (planeTarget r₁ r₂) (v n)) atTop
        (𝓝 (prescribedMaximum M r₁ r₂ pstar)) := by
  let f := planeExtension r₁ r₂
  have hf : ContDiff ℝ 1 f := planeExtension_contDiff r₁ r₂
  have hspan' : GradientSpans M (gradientCoordinates f) := by
    intro a b hab
    apply hspan a b
    intro m hm
    rw [← gradientCoordinates_readout r₁ r₂ (hrect m hm)]
    exact hab m hm
  have hw : Continuous (gradientCoordinates f) :=
    (Complex.continuous_re.comp (gradient_continuous hf)).prodMk
      (Complex.continuous_im.comp (gradient_continuous hf))
  obtain ⟨pstar, hpstar, hdstar, mstar, hmstar, hmax, hminimal⟩ :=
    inverse_gram_design_minimum hK γ hind hP M hM hne (gradientCoordinates f) hw.continuousOn hspan'
  have hd : 0 < 2 * (K : ℝ)^2 := by positivity
  have hstar : coefficientMaximum M f pstar =
      inverseCoefficient pstar (gradientCoordinates f) mstar / (2 * (K : ℝ)^2) := by
    apply IsGreatest.csSup_eq
    refine ⟨mem_image_of_mem _ hmstar, ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    exact div_le_div_of_nonneg_right (hmax m hm) hd.le
  have hmin : ∀ p ∈ coefficientPeakSet γ P, coefficientDet p ≠ 0 →
      coefficientMaximum M f pstar ≤ coefficientMaximum M f p := by
    intro p hp hdet
    obtain ⟨m, hm, hle⟩ := hminimal p hp hdet
    rw [hstar]
    apply (div_le_div_of_nonneg_right hle hd.le).trans
    apply le_csSup
    · exact hM.bddAbove_image ((inverseCoefficient_continuousOn p hw.continuousOn).div_const _)
    · exact mem_image_of_mem _ hm
  obtain ⟨C, hC, hgrad⟩ := planeExtension_gradient_bounded r₁ r₂
  obtain ⟨B, hB, hb⟩ := target_bounded r₁ r₂
  have hbound : ∀ m ∈ M, -B ≤ f m ∧ f m ≤ B := by
    intro m hm
    change -B ≤ extendedTarget r₁ r₂ (Complex.equivRealProdCLM.symm m) ∧
      extendedTarget r₁ r₂ (Complex.equivRealProdCLM.symm m) ≤ B
    rw [(extension_agrees r₁ r₂ (hrect m hm)).1]
    exact abs_le.mp (hb _ (hrect m hm))
  let A := coefficientPeakSet γ P
  letI : CompactSpace A := isCompact_iff_compactSpace.mp (coefficientPeakSet_isCompact hK γ hind hP.le)
  let risk := fun q : A => fun n => normalizedDesignRisk M f q.1 (v n)
  let good := fun q : A => coefficientDet q.1 ≠ 0
  let J := fun q : A => coefficientMaximum M f q.1
  let qstar : A := ⟨pstar, hpstar⟩
  have hu : ∀ b > coefficientMaximum M f pstar, ∀ᶠ n in atTop, risk qstar n < b := by
    have hh := GaussianMinimaxUpper.fixed_minimax_upper M hM hne r₁ r₂
      (channelEquiv hK pstar hdstar) (totalOffset pstar) v hv hlim
    have hcoef : sSup (GaussianMinimaxUpper.channelEnergy r₁ r₂
        (channelEquiv hK pstar hdstar) '' M) = coefficientMaximum M f pstar :=
      maxCoefficient_parameter hK M f pstar hdstar
    rw [hcoef] at hh
    simpa only [risk, qstar, normalizedDesignRisk, receiverFirst_eq, receiverSecond_eq, f] using hh
  have hout := CompactRiskOptimization.admissible_outer_infimum_tendsto_of_eventual_upper
    risk good J (coefficientMaximum M f pstar)
    (fun q _ n => div_nonneg (minimaxRisk_nonnegative M f _ _ _ _) (by positivity))
    (fun q hq => hmin q.1 q.2 hq) qstar hdstar hu
    (by
      intro q q₀ idx hq hidx hconv hq₀
      have hconv' : Tendsto (fun n => (q n).1) atTop (𝓝 q₀.1) :=
        continuous_subtype_val.continuousAt.tendsto.comp hconv
      exact parameter_regular_converse hK M hne hregular f hf hC hgrad
        (fun n => (q n).1) q₀.1 hq hq₀ hconv' (fun n => v (idx n))
        (fun n => hv (idx n)) (hlim.comp hidx.tendsto_atTop) (-B) B (by linarith) hbound)
    (by
      intro q q₀ idx hq hidx hconv hq₀
      have hconv' : Tendsto (fun n => (q n).1) atTop (𝓝 q₀.1) :=
        continuous_subtype_val.continuousAt.tendsto.comp hconv
      exact parameter_singular_converse hK M hregular f hf hspan' hC hgrad
        (fun n => (q n).1) q₀.1 hq (not_not.mp hq₀) hconv' (fun n => v (idx n))
        (fun n => hv (idx n)) (hlim.comp hidx.tendsto_atTop) (-B) B (by linarith) hbound)
  have hfg : EqOn (planeTarget r₁ r₂) f M := by
    intro m hm
    exact (extension_agrees r₁ r₂ (hrect m hm)).1.symm
  have hriskeq (p : Parameters K) (n : ℕ) :
      normalizedDesignRisk M (planeTarget r₁ r₂) p (v n) = normalizedDesignRisk M f p (v n) := by
    unfold normalizedDesignRisk
    rw [GaussianMinimaxUpper.minimaxRisk_congr_target M (planeTarget r₁ r₂) f hfg]
  have heq : ∀ n, CompactRiskOptimization.admissibleInfRisk risk good n =
      optimizedRisk γ P M (planeTarget r₁ r₂) (v n) := by
    intro n
    unfold CompactRiskOptimization.admissibleInfRisk optimizedRisk
    congr 1
    ext a
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q.1, ⟨q.2, hq⟩, ?_⟩
      exact hriskeq q.1 n
    · rintro ⟨p, ⟨hp, hdet⟩, rfl⟩
      refine ⟨⟨p, hp⟩, hdet, ?_⟩
      exact (hriskeq p n).symm
  have heqfun : CompactRiskOptimization.admissibleInfRisk risk good =
      fun n => optimizedRisk γ P M (planeTarget r₁ r₂) (v n) := funext heq
  rw [heqfun] at hout
  refine ⟨pstar, hpstar, hdstar, ?_, ?_⟩
  · intro p hp hdet
    simpa only [f, coefficientMaximum_prescribed M r₁ r₂ hrect] using hmin p hp hdet
  · simpa only [f, coefficientMaximum_prescribed M r₁ r₂ hrect] using hout

/-- The one-sided small-noise minimax limit, with a single attained design
chosen independently of the noise level. -/
theorem optimized_minimax_limit {K : ℕ} (hK : 0 < K)
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (γ : Fin K → C(X, Plane)) (hind : IndependentFeatures γ)
    {P : ℝ} (hP : 0 < P)
    (M : Set Plane) (hM : IsCompact M) (hne : M.Nonempty)
    (hregular : M ⊆ closure (interior M))
    (r₁ r₂ : IntervalReadout)
    (hrect : ∀ m ∈ M, Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂)
    (hspan : GradientSpans M (prescribedCoordinates r₁ r₂)) :
    ∃ pstar : Parameters K, pstar ∈ coefficientPeakSet γ P ∧ coefficientDet pstar ≠ 0 ∧
      (∀ p ∈ coefficientPeakSet γ P, coefficientDet p ≠ 0 →
        prescribedMaximum M r₁ r₂ pstar ≤ prescribedMaximum M r₁ r₂ p) ∧
      Tendsto (fun v : ℝ≥0 => optimizedRisk γ P M (planeTarget r₁ r₂) v)
        (𝓝[>] (0 : ℝ≥0)) (𝓝 (prescribedMaximum M r₁ r₂ pstar)) := by
  let u : ℕ → ℝ≥0 := fun n => ⟨1 / ((n : ℝ) + 1), by positivity⟩
  have hu : ∀ n, u n ≠ 0 := by
    intro n
    apply ne_of_gt
    change 0 < 1 / ((n : ℝ) + 1)
    positivity
  have hulim : Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨pstar, hpstar, hdstar, hmin, _⟩ := optimized_minimax_sequential_limit hK γ hind hP
    M hM hne hregular r₁ r₂ hrect hspan u hu hulim
  refine ⟨pstar, hpstar, hdstar, hmin, ?_⟩
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro v hv
  have hvpos : ∀ᶠ n in atTop, 0 < v n := hv.eventually self_mem_nhdsWithin
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hvpos
  apply (Filter.tendsto_add_atTop_iff_nat n₀).mp
  have hv' : ∀ n, v (n+n₀) ≠ 0 := fun n => ne_of_gt (hn₀ _ (Nat.le_add_left _ _))
  have hvl : Tendsto (fun n => (v (n+n₀) : ℝ)) atTop (𝓝 0) :=
    NNReal.tendsto_coe.mpr ((tendsto_nhds_of_tendsto_nhdsWithin hv).comp
      (Filter.tendsto_add_atTop_nat n₀))
  obtain ⟨qstar, hqstar, hdq, hqmin, hqresult⟩ := optimized_minimax_sequential_limit hK γ hind hP
    M hM hne hregular r₁ r₂ hrect hspan (fun n => v (n+n₀)) hv' hvl
  have heq : prescribedMaximum M r₁ r₂ qstar = prescribedMaximum M r₁ r₂ pstar :=
    le_antisymm (hqmin pstar hpstar hdstar) (hmin qstar hqstar hdq)
  rwa [heq] at hqresult

/-- The coefficient-minimizing fixed receiver has a single explicit global
decoder whose actual worst-case Gaussian risk attains its coefficient. -/
theorem constructed_decoder_attains {K : ℕ} (hK : 0 < K)
    (M : Set Plane) (hM : IsCompact M) (hne : M.Nonempty)
    (r₁ r₂ : IntervalReadout)
    (hrect : ∀ m ∈ M, Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂)
    (p : Parameters K) (hp : coefficientDet p ≠ 0) :
    Tendsto (fun N : ℝ => sSup
      (GeneralTargetGaussianAchievability.normalizedRisk r₁ r₂ (channelEquiv hK p hp)
        (Complex.equivRealProdCLM.symm (totalOffset p)) N ''
          (Complex.equivRealProdCLM.symm '' M)))
      (𝓝[>] (0 : ℝ)) (𝓝 (prescribedMaximum M r₁ r₂ p)) := by
  let T := channelEquiv hK p hp
  let MC := Complex.equivRealProdCLM.symm '' M
  have hMC : IsCompact MC := hM.image Complex.equivRealProdCLM.symm.continuous
  have hMCne : MC.Nonempty := hne.image _
  have hMCrect : MC ⊆ rectangle r₁ r₂ := by
    rintro _ ⟨m, hm, rfl⟩
    exact hrect m hm
  obtain ⟨mstar, hmstar, hmax, hlim⟩ := worst_case_limit r₁ r₂ T
    (Complex.equivRealProdCLM.symm (totalOffset p)) MC hMC hMCne hMCrect
  have hsup : sSup (coefficient r₁ r₂ T '' MC) = coefficient r₁ r₂ T mstar := by
    apply IsGreatest.csSup_eq
    exact ⟨mem_image_of_mem _ hmstar, by rintro _ ⟨m, hm, rfl⟩; exact hmax m hm⟩
  have himage : coefficient r₁ r₂ T '' MC =
      (fun m => inverseCoefficient p (prescribedCoordinates r₁ r₂) m / (2*(K : ℝ)^2)) '' M := by
    rw [show MC = Complex.equivRealProdCLM.symm '' M from rfl, Set.image_image]
    apply Set.image_congr
    intro m hm
    change planeCoefficient r₁ r₂ T m = _
    rw [coefficient_eq_inverse_energy r₁ r₂ T (hrect m hm)]
    change localCoefficient (planeExtension r₁ r₂) T m = _
    rw [localCoefficient_parameter]
    simp only [inverseCoefficient, gradientCoordinates_readout r₁ r₂ (hrect m hm)]
  rw [← hsup, himage] at hlim
  exact hlim

/-- The actual finite-node attainable moment image supplies compactness and
nonemptiness automatically. This is the one-sided optimized theorem for the
original source features, without an assumed compact moment domain. -/
theorem heterogeneous_optimized_minimax_limit {K : ℕ} (hK : 0 < K)
    (γ : Fin K → ℝ → Plane)
    (hγ : ∀ k, ContinuousOn (γ k) (Icc (-1 : ℝ) 1))
    (hind : ∀ k, TwoStatisticAttainment.IndependentStatistics (γ k))
    {P : ℝ} (hP : 0 < P)
    (hregular : HeterogeneousScore.attainable γ ⊆ closure (interior (HeterogeneousScore.attainable γ)))
    (r₁ r₂ : IntervalReadout)
    (hrect : ∀ m ∈ HeterogeneousScore.attainable γ,
      Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂)
    (hspan : GradientSpans (HeterogeneousScore.attainable γ) (prescribedCoordinates r₁ r₂)) :
    ∃ pstar : Parameters K,
      pstar ∈ coefficientPeakSet (HeterogeneousMomentCompactness.compactFeatures γ hγ) P ∧
      coefficientDet pstar ≠ 0 ∧
      (∀ p ∈ coefficientPeakSet (HeterogeneousMomentCompactness.compactFeatures γ hγ) P,
        coefficientDet p ≠ 0 →
          prescribedMaximum (HeterogeneousScore.attainable γ) r₁ r₂ pstar ≤
            prescribedMaximum (HeterogeneousScore.attainable γ) r₁ r₂ p) ∧
      Tendsto (fun v : ℝ≥0 => optimizedRisk (HeterogeneousMomentCompactness.compactFeatures γ hγ) P
        (HeterogeneousScore.attainable γ) (planeTarget r₁ r₂) v)
        (𝓝[>] (0 : ℝ≥0))
        (𝓝 (prescribedMaximum (HeterogeneousScore.attainable γ) r₁ r₂ pstar)) :=
  optimized_minimax_limit hK (HeterogeneousMomentCompactness.compactFeatures γ hγ)
    (HeterogeneousMomentCompactness.independentFeatures γ hγ hind) hP
    (HeterogeneousScore.attainable γ) (HeterogeneousMomentCompactness.attainable_isCompact γ hγ)
    (HeterogeneousMomentCompactness.attainable_nonempty γ) hregular r₁ r₂ hrect hspan

/-- The paper's ratio-of-infimum form, with an attained noise-independent
receiver and a single explicit decoder attaining exactly the same value. -/
theorem optimized_minimax_achieved {K : ℕ} (hK : 0 < K)
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (γ : Fin K → C(X, Plane)) (hind : IndependentFeatures γ)
    {P : ℝ} (hP : 0 < P)
    (M : Set Plane) (hM : IsCompact M) (hne : M.Nonempty)
    (hregular : M ⊆ closure (interior M))
    (r₁ r₂ : IntervalReadout)
    (hrect : ∀ m ∈ M, Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂)
    (hspan : GradientSpans M (prescribedCoordinates r₁ r₂)) :
    ∃ pstar : Parameters K, ∃ hdet : coefficientDet pstar ≠ 0,
      pstar ∈ coefficientPeakSet γ P ∧
      (∀ p ∈ coefficientPeakSet γ P, coefficientDet p ≠ 0 →
        prescribedMaximum M r₁ r₂ pstar ≤ prescribedMaximum M r₁ r₂ p) ∧
      Tendsto (fun v : ℝ≥0 => rawOptimizedRisk γ P M (planeTarget r₁ r₂) v / (2 * (v : ℝ)))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 (prescribedMaximum M r₁ r₂ pstar)) ∧
      Tendsto (fun N : ℝ => sSup
        (GeneralTargetGaussianAchievability.normalizedRisk r₁ r₂ (channelEquiv hK pstar hdet)
          (Complex.equivRealProdCLM.symm (totalOffset pstar)) N ''
            (Complex.equivRealProdCLM.symm '' M)))
        (𝓝[>] (0 : ℝ)) (𝓝 (prescribedMaximum M r₁ r₂ pstar)) := by
  obtain ⟨pstar, hpstar, hdstar, hmin, hlim⟩ := optimized_minimax_limit hK γ hind hP
    M hM hne hregular r₁ r₂ hrect hspan
  refine ⟨pstar, hdstar, hpstar, hmin, ?_, constructed_decoder_attains hK M hM hne r₁ r₂ hrect pstar hdstar⟩
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact optimizedRisk_eq_infimum_div γ P M (planeTarget r₁ r₂) ⟨pstar, hpstar, hdstar⟩ hv

/-- Complete finite-source version: compactness and nonemptiness concern the
actual attainable image and are derived from the feature assumptions. -/
theorem heterogeneous_optimized_minimax_achieved {K : ℕ} (hK : 0 < K)
    (γ : Fin K → ℝ → Plane)
    (hγ : ∀ k, ContinuousOn (γ k) (Icc (-1 : ℝ) 1))
    (hind : ∀ k, TwoStatisticAttainment.IndependentStatistics (γ k))
    {P : ℝ} (hP : 0 < P)
    (hregular : HeterogeneousScore.attainable γ ⊆ closure (interior (HeterogeneousScore.attainable γ)))
    (r₁ r₂ : IntervalReadout)
    (hrect : ∀ m ∈ HeterogeneousScore.attainable γ,
      Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂)
    (hspan : GradientSpans (HeterogeneousScore.attainable γ) (prescribedCoordinates r₁ r₂)) :
    ∃ pstar : Parameters K, ∃ hdet : coefficientDet pstar ≠ 0,
      pstar ∈ coefficientPeakSet (HeterogeneousMomentCompactness.compactFeatures γ hγ) P ∧
      (∀ p ∈ coefficientPeakSet (HeterogeneousMomentCompactness.compactFeatures γ hγ) P,
        coefficientDet p ≠ 0 →
          prescribedMaximum (HeterogeneousScore.attainable γ) r₁ r₂ pstar ≤
            prescribedMaximum (HeterogeneousScore.attainable γ) r₁ r₂ p) ∧
      Tendsto (fun v : ℝ≥0 => rawOptimizedRisk (HeterogeneousMomentCompactness.compactFeatures γ hγ) P
        (HeterogeneousScore.attainable γ) (planeTarget r₁ r₂) v / (2 * (v : ℝ)))
        (𝓝[>] (0 : ℝ≥0))
        (𝓝 (prescribedMaximum (HeterogeneousScore.attainable γ) r₁ r₂ pstar)) ∧
      Tendsto (fun N : ℝ => sSup
        (GeneralTargetGaussianAchievability.normalizedRisk r₁ r₂ (channelEquiv hK pstar hdet)
          (Complex.equivRealProdCLM.symm (totalOffset pstar)) N ''
            (Complex.equivRealProdCLM.symm '' HeterogeneousScore.attainable γ)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (prescribedMaximum (HeterogeneousScore.attainable γ) r₁ r₂ pstar)) :=
  optimized_minimax_achieved hK (HeterogeneousMomentCompactness.compactFeatures γ hγ)
    (HeterogeneousMomentCompactness.independentFeatures γ hγ hind) hP
    (HeterogeneousScore.attainable γ) (HeterogeneousMomentCompactness.attainable_isCompact γ hγ)
    (HeterogeneousMomentCompactness.attainable_nonempty γ) hregular r₁ r₂ hrect hspan

end Analog.GaussianOptimizedMinimax
