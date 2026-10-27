import Analog.CompactMinimumDecoder
import Analog.FixedPriorGaussianLimit
import Analog.GaussianParameterChannel

/-!
# The compact-minimum decoder attains the fixed-prior Gaussian limit

This closes the representation issue in Proposition 3: the particular
minimum-formula decoder displayed in Theorem 3, with its sharp uniform
constant, attains the same inverse-Gram coefficient as the optimum over
all Borel decoders.  It is one fixed decoder, independent of the prior and
of the noise level.  The final specialization uses the actual finite-node
moment image and the channel `K U`, retaining the sum of all node offsets.
-/

noncomputable section
namespace Analog.MinimumDecoderGaussianLimit
open Set Filter MeasureTheory
open GeneralTargetGaussianAchievability FixedPriorGaussianLimit
open GaussianScoreIdentity GaussianBayesConverse CompactMinimumDecoder
open scoped Topology NNReal ENNReal

abbrev Plane := ℝ × ℝ

/-- The exact moment-coordinate sharp uniform constant. -/
def momentConstant (M : Set ℂ) (r₁ r₂ : IntervalReadout)
    (T : ℂ ≃L[ℝ] ℂ) (c : ℂ) : ℝ≥0 :=
  Decoder.sharpConstant (fun m : M => c + T m) (fun m : M => target r₁ r₂ m)

/-- The decoder displayed in the paper, not an unspecified extension. -/
def minimumDecoder (M : Set ℂ) (r₁ r₂ : IntervalReadout)
    (T : ℂ ≃L[ℝ] ℂ) (c : ℂ) : ℂ → ℝ :=
  compactMinimum M (fun m => c + T m) (target r₁ r₂) (momentConstant M r₁ r₂ T c)

/-- The prescribed target is continuous on every moment subset of its
closed coordinate rectangle. -/
theorem target_continuousOn (M : Set ℂ) (r₁ r₂ : IntervalReadout)
    (hrect : M ⊆ rectangle r₁ r₂) : ContinuousOn (target r₁ r₂) M := by
  exact (r₁.value_continuous.comp Complex.continuous_re.continuousOn
    (fun m hm => (hrect hm).1)).add
      (r₂.value_continuous.comp Complex.continuous_im.continuousOn
        (fun m hm => (hrect hm).2))

/-- Every nonconstant readout on an identifiable channel has positive
score, derived from the already constructed Lipschitz exact extension. -/
theorem moment_score_positive (M : Set ℂ) (r₁ r₂ : IntervalReadout)
    (hrect : M ⊆ rectangle r₁ r₂) (T : ℂ ≃L[ℝ] ℂ) (c : ℂ)
    (hn : Operational.NonconstantOn M (target r₁ r₂)) :
    0 < Decoder.metricScore (fun m : M => c + T m) (fun m : M => target r₁ r₂ m) := by
  have hn' : Operational.NonconstantOn Set.univ (fun m : M => target r₁ r₂ m) := by
    obtain ⟨m, hm, n, hnm, hne⟩ := hn
    exact ⟨⟨m, hm⟩, trivial, ⟨n, hnm⟩, trivial, hne⟩
  obtain ⟨_, _, L, _, _, hL⟩ := decoder_regularity r₁ r₂ T c
  exact Decoder.uniform_implies_positive_score hn'
    (Decoder.lipschitz_exact_uniform hL
      (fun m : M => decoder_exact r₁ r₂ T c (hrect m.property)))

/-- Exactness and global sharp Lipschitz regularity of the particular
minimum decoder are derived; neither is an additional assumption. -/
theorem minimumDecoder_regular (M : Set ℂ) (hM : IsCompact M)
    (hne : M.Nonempty) (r₁ r₂ : IntervalReadout) (hrect : M ⊆ rectangle r₁ r₂)
    (T : ℂ ≃L[ℝ] ℂ) (c : ℂ) (hn : Operational.NonconstantOn M (target r₁ r₂)) :
    LipschitzWith (momentConstant M r₁ r₂ T c) (minimumDecoder M r₁ r₂ T c) ∧
      (∀ m ∈ M, minimumDecoder M r₁ r₂ T c (c + T m) = target r₁ r₂ m) := by
  have hr : ContinuousOn (fun m => c + T m) M :=
    (continuous_const.add T.continuous).continuousOn
  have hf := target_continuousOn M r₁ r₂ hrect
  have hn' : Operational.NonconstantOn Set.univ (fun m : M => target r₁ r₂ m) := by
    obtain ⟨m, hm, n, hnm, hne⟩ := hn
    exact ⟨⟨m, hm⟩, trivial, ⟨n, hnm⟩, trivial, hne⟩
  have hp := Decoder.sharpConstant_pairwise (fun m : M => c + T m)
    (fun m : M => target r₁ r₂ m) hn'
    (moment_score_positive M r₁ r₂ hrect T c hn)
  refine ⟨compactMinimum_lipschitz hM hne hr hf _, ?_⟩
  intro m hm
  exact compactMinimum_exact hM hr hf _
    (fun x hx z hz => hp ⟨x, hx⟩ ⟨z, hz⟩) hm

/-- The minimum-formula decoder attains the leading average coefficient
for every interior-supported probability law, without depending on it. -/
theorem minimum_decoder_prior_limit {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Set ℂ) (hM : IsCompact M) (hne : M.Nonempty)
    (r₁ r₂ : IntervalReadout) (hrect : M ⊆ rectangle r₁ r₂)
    (T : ℂ ≃L[ℝ] ℂ) (c : ℂ) (hn : Operational.NonconstantOn M (target r₁ r₂))
    (m : Ω → ℂ) (hm : Measurable m) (hinterior : ∀ᵐ ω ∂μ, m ω ∈ interior M) :
    Tendsto (fun N : ℝ =>
      (∫ q : Ω × ℂ, (minimumDecoder M r₁ r₂ T c
        (c + T (m q.1) + Real.sqrt N • q.2) - target r₁ r₂ (m q.1))^2
        ∂μ.prod GaussianNoise.standardComplexGaussian) / N)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ ω, coefficient r₁ r₂ T (m ω) ∂μ)) := by
  obtain ⟨hL, he⟩ := minimumDecoder_regular M hM hne r₁ r₂ hrect T c hn
  exact exact_decoder_prior_limit r₁ r₂ T c M hrect _ hL he m hm hinterior


/-- The actual prior-averaged risk of the displayed minimum decoder, with
`N` equal to total complex Gaussian noise power. -/
def minimumRisk (p : Plane → ℝ) (M : Set ℂ) (r₁ r₂ : IntervalReadout)
    (T : ℂ ≃L[ℝ] ℂ) (c : Plane) (N : ℝ) : ℝ :=
  ∫ q : Plane × ℂ,
    (minimumDecoder M r₁ r₂ T (Complex.equivRealProdCLM.symm c)
      (Complex.equivRealProdCLM.symm c + T (Complex.equivRealProdCLM.symm q.1) +
        Real.sqrt N • q.2) - planeTarget r₁ r₂ q.1)^2
    ∂(priorLaw p).prod GaussianNoise.standardComplexGaussian

/-- Proposition 3 in its inverse-Gram trace form: the infimum over all
Borel decoders and the one explicit minimum-formula decoder have exactly
the same limit.  `2v` is total complex noise power in the likelihood law. -/
theorem fixed_prior_minimum_inverse_trace {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (hfull : ∀ᵐ m ∂priorLaw p, m ∈ Ω)
    (M : Set ℂ) (hM : IsCompact M) (hne : M.Nonempty)
    (hΩM : ∀ m ∈ Ω, Complex.equivRealProdCLM.symm m ∈ interior M)
    (r₁ r₂ : IntervalReadout) (hrect : M ⊆ rectangle r₁ r₂)
    (T : ℂ ≃L[ℝ] ℂ) (c : Plane) (hn : Operational.NonconstantOn M (target r₁ r₂)) :
    let J := Matrix.trace (GaussianGramCoefficient.gradientSecondMoment (priorLaw p)
      (prescribedGradient r₁ r₂) * (GaussianGramCoefficient.gramMatrix T)⁻¹) / 2
    Tendsto (fun v : ℝ≥0 => optimalRisk p (planeTarget r₁ r₂) T c v / (2*(v : ℝ)))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 J) ∧
    Tendsto (fun N : ℝ => minimumRisk p M r₁ r₂ T c N / N)
      (𝓝[>] (0 : ℝ)) (𝓝 J) := by
  letI := priorLaw_isProbability p hp0 hpi hpn
  have hi : ∀ᵐ m ∂priorLaw p, Complex.equivRealProdCLM.symm m ∈ interior M :=
    hfull.mono (fun m hm => hΩM m hm)
  have hr : ∀ᵐ m ∂priorLaw p, Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂ :=
    hi.mono (fun _ hm => hrect (interior_subset hm))
  constructor
  · exact fixed_prior_limit_inverse_trace hΩ p hp hp0 hpi hpn hpC hpPos hfull r₁ r₂ T c hr
  · have hlim := minimum_decoder_prior_limit (μ := priorLaw p) M hM hne r₁ r₂ hrect T
      (Complex.equivRealProdCLM.symm c) hn
      (fun m : Plane => Complex.equivRealProdCLM.symm m)
      Complex.equivRealProdCLM.symm.continuous.measurable hi
    change Tendsto (fun N : ℝ => minimumRisk p M r₁ r₂ T c N / N)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ m, planeCoefficient r₁ r₂ T m ∂priorLaw p)) at hlim
    rwa [coefficient_integral_eq_trace p hp0 hpi hpn r₁ r₂ T hr] at hlim

/-- The prescribed local coefficient explicitly retains the physical
`1/(2 K²)` factor for a finite-node coefficient encoder. -/
theorem parameter_coefficient {K : ℕ} (hK : 0 < K)
    (a : HeterogeneousAttainment.Parameters K)
    (ha : GaussianDesignAttainment.coefficientDet a ≠ 0)
    (r₁ r₂ : IntervalReadout) {m : Plane}
    (hm : Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂) :
    planeCoefficient r₁ r₂ (GaussianParameterChannel.channelEquiv hK a ha) m =
      GaussianDesignAttainment.inverseCoefficient a
        (fun z : Plane => (r₁.slope z.1, r₂.slope z.2)) m / (2*(K : ℝ)^2) := by
  rw [coefficient_eq_inverse_energy r₁ r₂ _ hm,
    GaussianParameterChannel.parameter_inverse_energy]
  have hm₁ : m.1 ∈ Icc r₁.lower r₁.upper := hm.1
  have hm₂ : m.2 ∈ Icc r₂.lower r₂.upper := hm.2
  rw [planeExtension_gradient]
  simp only [extendedSlope, EndpointExtension.clippedDerivative_eq _ hm₁,
    EndpointExtension.clippedDerivative_eq _ hm₂]
  unfold GaussianDesignAttainment.inverseCoefficient
  dsimp
  ring

/-- The actual compact finite-node moment set, without convexification. -/
def complexMoments {K : ℕ} (γ : Fin K → ℝ → Plane) : Set ℂ :=
  Complex.equivRealProdCLM.symm '' HeterogeneousScore.attainable γ

/-- Proposition 3 for the physical heterogeneous affine encoder.  The
minimum is over the actual finite-node moment image; the channel includes
`K` and the sum of the arbitrary node offsets.  Compactness and
nonemptiness are derived from the source features. -/
theorem heterogeneous_fixed_prior_minimum {K : ℕ} (hK : 0 < K)
    (γ : Fin K → ℝ → Plane)
    (hγ : ∀ k, ContinuousOn (γ k) (Icc (-1 : ℝ) 1))
    (a : HeterogeneousAttainment.Parameters K)
    (ha : GaussianDesignAttainment.coefficientDet a ≠ 0)
    {Ω : Set Plane} (hΩ : IsOpen Ω) (hΩM : Ω ⊆ interior (HeterogeneousScore.attainable γ))
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (hfull : ∀ᵐ m ∂priorLaw p, m ∈ Ω)
    (r₁ r₂ : IntervalReadout)
    (hrect : ∀ m ∈ HeterogeneousScore.attainable γ,
      Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂)
    (hn : Operational.NonconstantOn (HeterogeneousScore.attainable γ) (planeTarget r₁ r₂)) :
    let T := GaussianParameterChannel.channelEquiv hK a ha
    let c := GaussianParameterChannel.totalOffset a
    let J := (∫ m, GaussianDesignAttainment.inverseCoefficient a
      (fun z : Plane => (r₁.slope z.1, r₂.slope z.2)) m ∂priorLaw p) / (2*(K : ℝ)^2)
    Tendsto (fun v : ℝ≥0 => optimalRisk p (planeTarget r₁ r₂) T c v / (2*(v : ℝ)))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 J) ∧
    Tendsto (fun N : ℝ => minimumRisk p (complexMoments γ) r₁ r₂ T c N / N)
      (𝓝[>] (0 : ℝ)) (𝓝 J) := by
  let M := HeterogeneousScore.attainable γ
  let MC := complexMoments γ
  let T := GaussianParameterChannel.channelEquiv hK a ha
  let c := GaussianParameterChannel.totalOffset a
  have hMC : IsCompact MC :=
    (HeterogeneousMomentCompactness.attainable_isCompact γ hγ).image
      Complex.equivRealProdCLM.symm.continuous
  have hMCne : MC.Nonempty := (HeterogeneousMomentCompactness.attainable_nonempty γ).image _
  have hMCrect : MC ⊆ rectangle r₁ r₂ := by
    rintro _ ⟨m, hm, rfl⟩
    exact hrect m hm
  have hΩMC : ∀ m ∈ Ω, Complex.equivRealProdCLM.symm m ∈ interior MC := by
    intro m hm
    exact Complex.equivRealProdCLM.symm.toHomeomorph.isOpenMap.image_interior_subset M
      ⟨m, hΩM hm, rfl⟩
  have hnC : Operational.NonconstantOn MC (target r₁ r₂) := by
    obtain ⟨m, hm, n, hnm, hne⟩ := hn
    exact ⟨_, ⟨m, hm, rfl⟩, _, ⟨n, hnm, rfl⟩, hne⟩
  have hi : ∀ᵐ m ∂priorLaw p, Complex.equivRealProdCLM.symm m ∈ interior MC :=
    hfull.mono (fun m hm => hΩMC m hm)
  have hr : ∀ᵐ m ∂priorLaw p, Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂ :=
    hi.mono (fun _ hm => hMCrect (interior_subset hm))
  have hJ : Matrix.trace (GaussianGramCoefficient.gradientSecondMoment (priorLaw p)
      (prescribedGradient r₁ r₂) * (GaussianGramCoefficient.gramMatrix T)⁻¹) / 2 =
      (∫ m, GaussianDesignAttainment.inverseCoefficient a
        (fun z : Plane => (r₁.slope z.1, r₂.slope z.2)) m ∂priorLaw p) / (2*(K : ℝ)^2) := by
    rw [← coefficient_integral_eq_trace p hp0 hpi hpn r₁ r₂ T hr, ← integral_div]
    apply integral_congr_ae
    filter_upwards [hr] with m hm
    exact parameter_coefficient hK a ha r₁ r₂ hm
  have hlim := fixed_prior_minimum_inverse_trace hΩ p hp hp0 hpi hpn hpC hpPos hfull
    MC hMC hMCne hΩMC r₁ r₂ hMCrect T c hnC
  dsimp only at hlim
  rw [hJ] at hlim
  exact hlim


/-- The two coordinate descriptions have exactly the same physical
received point, including all individual offsets. -/
theorem parameter_received_eq {K : ℕ} (hK : 0 < K)
    (a : HeterogeneousAttainment.Parameters K)
    (ha : GaussianDesignAttainment.coefficientDet a ≠ 0) (m : Plane) :
    CompactMinimumDecoder.momentReceived (HeterogeneousAttainment.parameterPlanar a) a.1 m =
      Complex.equivRealProdCLM.symm (GaussianParameterChannel.totalOffset a) +
        GaussianParameterChannel.channelEquiv hK a ha (Complex.equivRealProdCLM.symm m) := by
  apply Complex.ext <;>
    simp [CompactMinimumDecoder.momentReceived, ArbitraryEncoder.asComplex,
      GaussianParameterChannel.totalOffset, GaussianParameterChannel.channelEquiv_apply,
      GaussianParameterChannel.channelMap_apply, HeterogeneousAttainment.parameterPlanar]

/-- Passing between real-pair moments and their complex representation
preserves the whole quotient set, hence the sharp score. -/
theorem complex_moment_metricScore_eq {K : ℕ} (hK : 0 < K)
    (a : HeterogeneousAttainment.Parameters K)
    (ha : GaussianDesignAttainment.coefficientDet a ≠ 0)
    (γ : Fin K → ℝ → Plane) (r₁ r₂ : IntervalReadout) :
    Decoder.metricScore
      (fun m : complexMoments γ =>
        Complex.equivRealProdCLM.symm (GaussianParameterChannel.totalOffset a) +
          GaussianParameterChannel.channelEquiv hK a ha m)
      (fun m : complexMoments γ => target r₁ r₂ m) =
    Decoder.metricScore
      (fun m : HeterogeneousScore.attainable γ =>
        CompactMinimumDecoder.momentReceived (HeterogeneousAttainment.parameterPlanar a) a.1 m)
      (fun m : HeterogeneousScore.attainable γ => planeTarget r₁ r₂ m) := by
  unfold Decoder.metricScore Operational.score
  congr 1
  ext q
  constructor
  · rintro ⟨⟨_, ⟨m, hm, rfl⟩⟩, _, ⟨_, ⟨n, hnm, rfl⟩⟩, _, hne, hq⟩
    refine ⟨⟨m, hm⟩, trivial, ⟨n, hnm⟩, trivial, hne, ?_⟩
    simpa only [parameter_received_eq hK a ha, planeTarget] using hq
  · rintro ⟨m, _, n, _, hne, hq⟩
    refine ⟨⟨Complex.equivRealProdCLM.symm m, ⟨m, m.property, rfl⟩⟩, trivial,
      ⟨Complex.equivRealProdCLM.symm n, ⟨n, n.property, rfl⟩⟩, trivial, hne, ?_⟩
    simpa only [parameter_received_eq hK a ha, planeTarget] using hq

/-- The sharp coefficient of the statistical decoder equals the exact
physical coefficient used in Theorem 3. -/
theorem minimum_constant_eq_paper {K : ℕ} (hK : 0 < K)
    (a : HeterogeneousAttainment.Parameters K)
    (ha : GaussianDesignAttainment.coefficientDet a ≠ 0)
    (γ : Fin K → ℝ → Plane) (r₁ r₂ : IntervalReadout) :
    momentConstant (complexMoments γ) r₁ r₂
      (GaussianParameterChannel.channelEquiv hK a ha)
      (Complex.equivRealProdCLM.symm (GaussianParameterChannel.totalOffset a)) =
    CompactMinimumDecoder.momentConstant (HeterogeneousAttainment.parameterPlanar a) a.1 γ
      (planeTarget r₁ r₂) := by
  apply NNReal.eq
  simp only [momentConstant, CompactMinimumDecoder.momentConstant,
    CompactMinimumDecoder.sharpOn, Decoder.sharpConstant, NNReal.coe_mk,
    complex_moment_metricScore_eq hK a ha]

/-- Pointwise equality with the very decoder used in the formalization
of Theorem 3.  This is a reindexing of the same attained minimum. -/
theorem minimumDecoder_eq_paper_decoder {K : ℕ} (hK : 0 < K)
    (a : HeterogeneousAttainment.Parameters K)
    (ha : GaussianDesignAttainment.coefficientDet a ≠ 0)
    (γ : Fin K → ℝ → Plane) (r₁ r₂ : IntervalReadout) :
    minimumDecoder (complexMoments γ) r₁ r₂
      (GaussianParameterChannel.channelEquiv hK a ha)
      (Complex.equivRealProdCLM.symm (GaussianParameterChannel.totalOffset a)) =
    CompactMinimumDecoder.momentDecoder (HeterogeneousAttainment.parameterPlanar a) a.1 γ
      (planeTarget r₁ r₂) := by
  funext y
  simp only [minimumDecoder]
  rw [minimum_constant_eq_paper hK a ha]
  simp only [CompactMinimumDecoder.momentDecoder, compactMinimum, complexMoments, Set.image_image]
  congr 1
  apply Set.image_congr
  intro m hm
  rw [parameter_received_eq hK a ha]
  rfl

end Analog.MinimumDecoderGaussianLimit
