import Analog.GaussianBayesConverse
import Analog.GaussianSequentialConverse

/-!
# Genuine worst-case Gaussian risks and localization

Nonnegative integrals retain infinite-risk Borel estimators. Tonelli connects
conditional observation risks to the regular-prior joint law, so averaging
produces a lower bound on the actual worst-case risk and its decoder optimum.
-/

noncomputable section
namespace Analog.GaussianWorstCase
open MeasureTheory Set Filter GaussianScoreIdentity GaussianSequentialConverse
open scoped Topology NNReal ENNReal

abbrev Plane := ℝ × ℝ

def observationLaw (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0) (m : Plane) : Measure Plane :=
  volume.withDensity (fun y => ENNReal.ofReal (likelihood r₁ r₂ c v m y))

def pointRisk (f D : Plane → ℝ) (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0)
    (m : Plane) : ℝ≥0∞ := BorelRisk.squareRisk (observationLaw r₁ r₂ c v m) (fun _ => f m) D

def worstRisk (M : Set Plane) (f D : Plane → ℝ) (r₁ r₂ : Plane →L[ℝ] ℝ)
    (c : Plane) (v : ℝ≥0) : ℝ≥0∞ := ⨆ m : M, pointRisk f D r₁ r₂ c v m

def minimaxRisk (M : Set Plane) (f : Plane → ℝ) (r₁ r₂ : Plane →L[ℝ] ℝ)
    (c : Plane) (v : ℝ≥0) : ℝ :=
  (⨅ D : BorelRisk.BorelDecoder Plane, worstRisk M f D.1 r₁ r₂ c v).toReal

theorem observationLaw_isProbability (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane)
    {v : ℝ≥0} (hv : v ≠ 0) (m : Plane) : IsProbabilityMeasure (observationLaw r₁ r₂ c v m) := by
  constructor
  rw [observationLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (likelihood_integrable r₁ r₂ c v m)
      (Eventually.of_forall (fun y => (likelihood_pos r₁ r₂ c hv m y).le)),
    likelihood_integral r₁ r₂ c hv m]
  norm_num

theorem pointRisk_eq_lintegral (f D : Plane → ℝ) (hD : Measurable D)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0) (m : Plane) :
    pointRisk f D r₁ r₂ c v m = ∫⁻ y, ENNReal.ofReal (likelihood r₁ r₂ c v m y) *
      ENNReal.ofReal ((D y - f m)^2) := by
  have hq : Measurable (fun y => ENNReal.ofReal (likelihood r₁ r₂ c v m y)) :=
    ((likelihood_joint_continuous r₁ r₂ c v).comp
      ((continuous_const : Continuous (fun _ : Plane => m)).prodMk continuous_id)).measurable.ennreal_ofReal
  exact lintegral_withDensity_eq_lintegral_mul volume hq ((hD.sub measurable_const).pow_const 2).ennreal_ofReal

theorem pointRisk_measurable (f D : Plane → ℝ) (hf : Measurable f) (hD : Measurable D)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0) :
    Measurable (pointRisk f D r₁ r₂ c v) := by
  have heq : pointRisk f D r₁ r₂ c v = fun m => ∫⁻ y, ENNReal.ofReal (likelihood r₁ r₂ c v m y) *
      ENNReal.ofReal ((D y - f m)^2) := funext (pointRisk_eq_lintegral f D hD r₁ r₂ c v)
  rw [heq]
  apply Measurable.lintegral_prod_right
  exact (likelihood_joint_continuous r₁ r₂ c v).measurable.ennreal_ofReal.mul
    (((hD.comp measurable_snd).sub (hf.comp measurable_fst)).pow_const 2).ennreal_ofReal

/-- Tonelli identifies Bayes squared risk with the prior average of the actual
conditional Gaussian risk, even for unbounded Borel decoders. -/
theorem jointRisk_eq_average (p f D : Plane → ℝ) (hp : Measurable p)
    (hp0 : ∀ m, 0 ≤ p m) (hf : Measurable f) (hD : Measurable D)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0) :
    BorelRisk.squareRisk (jointLaw p r₁ r₂ c v) (fun q => f q.1) (fun q => D q.2) =
      ∫⁻ m, pointRisk f D r₁ r₂ c v m ∂priorLaw p := by
  have hq := (likelihood_joint_continuous r₁ r₂ c v).measurable.ennreal_ofReal
  have he : Measurable (fun q : Plane × Plane => ENNReal.ofReal ((D q.2-f q.1)^2)) :=
    (((hD.comp measurable_snd).sub (hf.comp measurable_fst)).pow_const 2).ennreal_ofReal
  have hd : Measurable (fun q : Plane × Plane => ENNReal.ofReal (p q.1 * likelihood r₁ r₂ c v q.1 q.2)) :=
    ((hp.comp measurable_fst).mul
      (likelihood_joint_continuous r₁ r₂ c v).measurable).ennreal_ofReal
  rw [BorelRisk.squareRisk, jointLaw, lintegral_withDensity_eq_lintegral_mul volume hd he]
  simp_rw [Pi.mul_apply, ENNReal.ofReal_mul (hp0 _), mul_assoc]
  change (∫⁻ q : Plane × Plane, ENNReal.ofReal (p q.1) *
    (ENNReal.ofReal (likelihood r₁ r₂ c v q.1 q.2) *
      ENNReal.ofReal ((D q.2 - f q.1)^2)) ∂volume.prod volume) = _
  have hh : Measurable (fun q : Plane × Plane => ENNReal.ofReal (p q.1) *
    (ENNReal.ofReal (likelihood r₁ r₂ c v q.1 q.2) * ENNReal.ofReal ((D q.2 - f q.1)^2))) :=
    ((hp.comp measurable_fst).ennreal_ofReal).mul (hq.mul he)
  rw [lintegral_prod _ hh.aemeasurable]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [priorLaw, lintegral_withDensity_eq_lintegral_mul volume hp.ennreal_ofReal
    (pointRisk_measurable f D hf hD r₁ r₂ c v)]
  simp_rw [Pi.mul_apply, pointRisk_eq_lintegral f D hD]

/-- Averaging any supported prior cannot exceed the worst-case squared risk. -/
theorem jointRisk_le_worstRisk (M : Set Plane) (p f D : Plane → ℝ)
    (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m) (hpi : Integrable p)
    (hpn : (∫ m, p m) = 1) (hf : Measurable f) (hD : Measurable D)
    (hM : ∀ᵐ m ∂priorLaw p, m ∈ M)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0) :
    BorelRisk.squareRisk (jointLaw p r₁ r₂ c v) (fun q => f q.1) (fun q => D q.2) ≤
      worstRisk M f D r₁ r₂ c v := by
  letI := priorLaw_isProbability p hp0 hpi hpn
  rw [jointRisk_eq_average p f D hp hp0 hf hD]
  calc
    (∫⁻ m, pointRisk f D r₁ r₂ c v m ∂priorLaw p) ≤
        ∫⁻ _m, worstRisk M f D r₁ r₂ c v ∂priorLaw p := by
      apply lintegral_mono_ae
      filter_upwards [hM] with m hm
      exact le_iSup_of_le ⟨m, hm⟩ le_rfl
    _ = worstRisk M f D r₁ r₂ c v := by simp

/-- A constant decoder bounds the unrestricted worst-case optimum. -/
theorem worstRisk_const_le (M : Set Plane) (f : Plane → ℝ)
    (lo hi : ℝ) (hlohi : lo ≤ hi) (hbound : ∀ m ∈ M, lo ≤ f m ∧ f m ≤ hi)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0) :
    worstRisk M f (fun _ => lo) r₁ r₂ c v ≤ ENNReal.ofReal ((hi-lo)^2) := by
  apply iSup_le
  intro m
  letI := observationLaw_isProbability r₁ r₂ c hv m.1
  calc
    pointRisk f (fun _ => lo) r₁ r₂ c v m.1 ≤
        ∫⁻ _y, ENNReal.ofReal ((hi-lo)^2) ∂observationLaw r₁ r₂ c v m.1 := by
      apply lintegral_mono
      intro y
      apply ENNReal.ofReal_le_ofReal
      have h := BorelRisk.interval_error_bound ⟨le_rfl, hlohi⟩ (hbound m.1 m.2)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (sub_nonneg.mpr hlohi)).mpr h
    _ = ENNReal.ofReal ((hi-lo)^2) := by simp

/-- Worst-case optimization is finite and converting its nonnegative infimum
to a real number is therefore legitimate. -/
theorem minimaxRisk_finite (M : Set Plane) (f : Plane → ℝ)
    (lo hi : ℝ) (hlohi : lo ≤ hi) (hbound : ∀ m ∈ M, lo ≤ f m ∧ f m ≤ hi)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0) :
    (⨅ D : BorelRisk.BorelDecoder Plane, worstRisk M f D.1 r₁ r₂ c v) ≠ ⊤ := by
  apply ne_of_lt
  apply lt_of_le_of_lt (iInf_le _ ⟨fun _ => lo, measurable_const⟩)
  exact (worstRisk_const_le M f lo hi hlohi hbound r₁ r₂ c hv).trans_lt ENNReal.ofReal_lt_top

/-- The genuine all-Borel Bayes optimum is bounded by the genuine all-Borel
worst-case optimum. -/
theorem rowOptimalRisk_le_minimaxRisk (M : Set Plane) (p f : Plane → ℝ)
    (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m) (hpi : Integrable p)
    (hpn : (∫ m, p m) = 1) (hf : Measurable f) (hM : ∀ᵐ m ∂priorLaw p, m ∈ M)
    (lo hi : ℝ) (hlohi : lo ≤ hi) (hbound : ∀ m ∈ M, lo ≤ f m ∧ f m ≤ hi)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0) :
    rowOptimalRisk p f r₁ r₂ c v ≤ minimaxRisk M f r₁ r₂ c v := by
  apply ENNReal.toReal_mono (minimaxRisk_finite M f lo hi hlohi hbound r₁ r₂ c hv)
  apply iInf_mono
  intro D
  exact jointRisk_le_worstRisk M p f D.1 hp hp0 hpi hpn hf D.2 hM r₁ r₂ c v

/-- Every regular supported prior gives an actual worst-case converse. The
Bayes optimum and the worst-case optimum both range over all Borel decoders. -/
theorem regular_prior_minimax_converse {Ω : Set Plane} (hΩ : IsOpen Ω)
    (M : Set Plane) (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (hfull : ∀ᵐ m ∂priorLaw p, m ∈ Ω) (hM : ∀ᵐ m ∂priorLaw p, m ∈ M)
    (f : Plane → ℝ) (hf : ContDiff ℝ 1 f) (S : ℂ ≃L[ℝ] ℂ) (c : Plane)
    {C : ℝ} (hC : 0 ≤ C) (hgrad : ∀ m, ‖GaussianBayesConverse.gradient f m‖ ≤ C)
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0))
    (lo hi : ℝ) (hlohi : lo ≤ hi)
    (hbound : ∀ m ∈ M, lo ≤ f m ∧ f m ≤ hi) :
    GaussianConverseLimits.LowerAsymptotic
      (fun n => minimaxRisk M f (GaussianBayesConverse.receiverFirst S)
        (GaussianBayesConverse.receiverSecond S) c (v n) / (2 * (v n : ℝ)))
      ((∫ m, ‖S.symm.toContinuousLinearMap.adjoint (GaussianBayesConverse.gradient f m)‖ ^ 2
        ∂priorLaw p) / 2) := by
  have ht : ∀ᵐ m ∂priorLaw p, lo ≤ f m ∧ f m ≤ hi := hM.mono fun m hm => hbound m hm
  have h := GaussianBayesConverse.regular_prior_bayes_converse_total_noise hΩ p hp hp0
    hpi hpn hpC hpPos hfull f hf S c hC hgrad v hv hlim lo hi hlohi ht
  intro a ha
  filter_upwards [h a ha] with n hn
  exact hn.trans (div_le_div_of_nonneg_right
    (rowOptimalRisk_le_minimaxRisk M p f hp hp0 hpi hpn hf.continuous.measurable hM
      lo hi hlohi hbound _ _ c (hv n)) (by positivity))

/-- Continuity extends all pointwise lower asymptotic bounds from the interior
to its closure; no interchange of a supremum and a limit is used. -/
theorem lowerAsymptotic_at_closure {M : Set Plane} {risk : ℕ → ℝ} {g : Plane → ℝ}
    (hg : Continuous g)
    (hinside : ∀ m ∈ interior M, GaussianConverseLimits.LowerAsymptotic risk (g m))
    {m : Plane} (hm : m ∈ closure (interior M)) :
    GaussianConverseLimits.LowerAsymptotic risk (g m) := by
  intro a ha
  have hex : ∃ x ∈ interior M, a < g x := by
    by_contra! hnone
    have hs : interior M ⊆ {x | g x ≤ a} := hnone
    have hc : closure (interior M) ⊆ {x | g x ≤ a} :=
      closure_minimal hs (isClosed_le hg continuous_const)
    exact (not_le_of_gt ha) (hc hm)
  obtain ⟨x, hx, hax⟩ := hex
  exact hinside x hx a hax

theorem minimaxRisk_nonnegative (M : Set Plane) (f : Plane → ℝ)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0) :
    0 ≤ minimaxRisk M f r₁ r₂ c v := ENNReal.toReal_nonneg

/-- A uniform conditional-risk bound for one actual Borel decoder bounds the
unrestricted minimax risk. This can be used with the constructed achieving
decoder without interchanging any optimization and limit. -/
theorem minimaxRisk_le_of_uniform_bound (M : Set Plane) (f : Plane → ℝ)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0)
    (D : BorelRisk.BorelDecoder Plane) {b : ℝ} (hb : 0 ≤ b)
    (hpoint : ∀ m ∈ M, pointRisk f D.1 r₁ r₂ c v m ≤ ENNReal.ofReal b) :
    minimaxRisk M f r₁ r₂ c v ≤ b := by
  have h : (⨅ D : BorelRisk.BorelDecoder Plane, worstRisk M f D.1 r₁ r₂ c v) ≤ ENNReal.ofReal b := by
    apply (iInf_le _ D).trans
    apply iSup_le
    intro m
    exact hpoint m.1 m.2
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal hb)

end Analog.GaussianWorstCase
