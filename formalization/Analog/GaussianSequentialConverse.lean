import Analog.GaussianVanTrees
import Analog.GaussianConverseLimits
import Analog.WeightedVariational

/-!
# Moving-channel Gaussian converses

The channel rows and offsets may change at every noise level. The risk is the
actual infimum over every Borel decoder, with its nonnegative integral (possibly
infinite), converted to a real number only after clipping proves finiteness.
Fixed compact interior tests give normalized lower bounds and exclude singular
channel limits whenever a test detects a nonzero target derivative.
-/

noncomputable section
namespace Analog.GaussianSequentialConverse
open MeasureTheory Set Filter GaussianScoreIdentity GaussianVanTrees GaussianConverseLimits
open scoped Topology NNReal ENNReal

abbrev Plane := ℝ × ℝ

def rowOptimalRisk (p f : Plane → ℝ) (r₁ r₂ : Plane →L[ℝ] ℝ)
    (c : Plane) (v : ℝ≥0) : ℝ :=
  (⨅ D : BorelRisk.BorelDecoder Plane,
    BorelRisk.bayesRisk (jointLaw p r₁ r₂ c v) (fun q => f q.1) (fun q => q.2) D).toReal

/-- Model-level Bayes information bound, optimized over all Borel decoders. -/
theorem rowOptimalRisk_information_bound {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (f η₁ η₂ : Plane → ℝ) (hf : ContDiff ℝ 1 f)
    (hη₁ : ContDiff ℝ 1 η₁) (hη₂ : ContDiff ℝ 1 η₂)
    (hc₁ : HasCompactSupport η₁) (hc₂ : HasCompactSupport η₂)
    (hs₁ : tsupport η₁ ⊆ Ω) (hs₂ : tsupport η₂ ⊆ Ω)
    (z w : Plane) (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane)
    {v : ℝ≥0} (hv : v ≠ 0) (lo hi : ℝ) (hlohi : lo ≤ hi)
    (htarget : ∀ᵐ m ∂priorLaw p, lo ≤ f m ∧ f m ≤ hi)
    (hden : 0 < priorInformation p η₁ η₂ z w + channelInformation p η₁ η₂ z w r₁ r₂ / (v : ℝ)) :
    sensitivity p f η₁ η₂ z w ^ 2 /
      (priorInformation p η₁ η₂ z w + channelInformation p η₁ η₂ z w r₁ r₂ / (v : ℝ)) ≤
        rowOptimalRisk p f r₁ r₂ c v := by
  letI := jointLaw_isProbability p hp0 hpi hpn r₁ r₂ c hv
  letI : Nonempty (BorelRisk.BorelDecoder Plane) := ⟨⟨fun _ => 0, measurable_const⟩⟩
  have ht : Measurable (fun q : Plane × Plane => f q.1) := hf.continuous.measurable.comp measurable_fst
  have hb := jointLaw_ae_of_priorLaw p hp hp0 r₁ r₂ c v (P := fun m => lo ≤ f m ∧ f m ≤ hi) htarget
  rw [rowOptimalRisk, (BorelRisk.iInf_bayesRisk_toReal _ _ ht measurable_snd hlohi hb).2]
  apply le_ciInf
  intro D
  have he := BorelRisk.clipped_error_memLp ht (D.2.comp measurable_snd) hlohi hb
  exact regular_information_bound hΩ p hp hp0 hpC hpPos f η₁ η₂ hf hη₁ hη₂ hc₁ hc₂
    hs₁ hs₂ z w r₁ r₂ c hv (fun y => Decoder.clip lo hi (D.1 y)) he hden

/-- With total complex noise power `2v`, the sharp information denominator is
`2 B_channel + 2 v B_prior`. -/
theorem rowOptimalRisk_normalized_bound {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (f η₁ η₂ : Plane → ℝ) (hf : ContDiff ℝ 1 f)
    (hη₁ : ContDiff ℝ 1 η₁) (hη₂ : ContDiff ℝ 1 η₂)
    (hc₁ : HasCompactSupport η₁) (hc₂ : HasCompactSupport η₂)
    (hs₁ : tsupport η₁ ⊆ Ω) (hs₂ : tsupport η₂ ⊆ Ω)
    (z w : Plane) (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane)
    {v : ℝ≥0} (hv : v ≠ 0) (lo hi : ℝ) (hlohi : lo ≤ hi)
    (htarget : ∀ᵐ m ∂priorLaw p, lo ≤ f m ∧ f m ≤ hi)
    (henergy : 0 < channelInformation p η₁ η₂ z w r₁ r₂) :
    sensitivity p f η₁ η₂ z w ^ 2 /
      (2 * channelInformation p η₁ η₂ z w r₁ r₂ +
        2 * (v : ℝ) * priorInformation p η₁ η₂ z w) ≤
      rowOptimalRisk p f r₁ r₂ c v / (2 * (v : ℝ)) := by
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hden := add_pos_of_nonneg_of_pos (priorInformation_nonnegative p η₁ η₂ hp0 z w)
    (div_pos henergy hvpos)
  have hb := rowOptimalRisk_information_bound hΩ p hp hp0 hpi hpn hpC hpPos f η₁ η₂
    hf hη₁ hη₂ hc₁ hc₂ hs₁ hs₂ z w r₁ r₂ c hv lo hi hlohi htarget hden
  have heq : sensitivity p f η₁ η₂ z w ^ 2 /
      (2 * channelInformation p η₁ η₂ z w r₁ r₂ + 2 * (v : ℝ) * priorInformation p η₁ η₂ z w) =
      (sensitivity p f η₁ η₂ z w ^ 2 /
        (priorInformation p η₁ η₂ z w + channelInformation p η₁ η₂ z w r₁ r₂ / (v : ℝ))) /
          (2 * (v : ℝ)) := by
    rw [div_div]
    congr 1
    field_simp
    ring
  rw [heq]
  exact div_le_div_of_nonneg_right hb (by positivity)

/-- A fixed smooth test detecting a nonzero sensitivity forces divergence of
the *actual all-Borel optimum* whenever its moving-channel energy tends to zero.
Neither score identities nor a statistical information bound are assumed. -/
theorem singular_row_sequence_diverges {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (f η₁ η₂ : Plane → ℝ) (hf : ContDiff ℝ 1 f)
    (hη₁ : ContDiff ℝ 1 η₁) (hη₂ : ContDiff ℝ 1 η₂)
    (hc₁ : HasCompactSupport η₁) (hc₂ : HasCompactSupport η₂)
    (hs₁ : tsupport η₁ ⊆ Ω) (hs₂ : tsupport η₂ ⊆ Ω)
    (z w : Plane) (r₁ r₂ : ℕ → Plane →L[ℝ] ℝ) (c : ℕ → Plane)
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hvlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0))
    (lo hi : ℝ) (hlohi : lo ≤ hi)
    (htarget : ∀ᵐ m ∂priorLaw p, lo ≤ f m ∧ f m ≤ hi)
    (hA : sensitivity p f η₁ η₂ z w ≠ 0)
    (henergy : ∀ n, 0 < channelInformation p η₁ η₂ z w (r₁ n) (r₂ n))
    (hlimit : Tendsto (fun n => channelInformation p η₁ η₂ z w (r₁ n) (r₂ n)) atTop (𝓝 0)) :
    Tendsto (fun n => rowOptimalRisk p f (r₁ n) (r₂ n) (c n) (v n) / (2 * (v n : ℝ)))
      atTop atTop := by
  apply risk_tendsto_atTop_of_denominator_zero (sq_pos_of_ne_zero hA)
  · have h := (hlimit.const_mul 2).add ((hvlim.const_mul 2).mul_const
      (priorInformation p η₁ η₂ z w))
    simpa using h
  · intro n
    exact add_pos_of_pos_of_nonneg (mul_pos (by norm_num) (henergy n))
      (mul_nonneg (by positivity) (priorInformation_nonnegative p η₁ η₂ hp0 z w))
  · intro n
    exact rowOptimalRisk_normalized_bound hΩ p hp hp0 hpi hpn hpC hpPos f η₁ η₂ hf hη₁ hη₂
      hc₁ hc₂ hs₁ hs₂ z w (r₁ n) (r₂ n) (c n) (hv n) lo hi hlohi htarget (henergy n)

/-- A scalar test in a fixed moment direction has sensitivity equal to its
prior correlation with the directional derivative. -/
theorem scalar_test_sensitivity (p f χ : Plane → ℝ) (hp : Measurable p)
    (hp0 : ∀ m, 0 ≤ p m) (z : Plane) :
    sensitivity p f χ 0 z 0 = ∫ m, χ m * fderiv ℝ f m z ∂priorLaw p := by
  rw [sensitivity, priorLaw_integral p hp hp0]
  simp only [Pi.zero_apply, mul_zero, integral_zero, add_zero]
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => by ring

/-- Its channel energy factors into the test's second moment and the sensed
energy of that fixed moment direction. -/
theorem scalar_test_channelInformation (p χ : Plane → ℝ) (hp : Measurable p)
    (hp0 : ∀ m, 0 ≤ p m) (z : Plane) (r₁ r₂ : Plane →L[ℝ] ℝ) :
    channelInformation p χ 0 z 0 r₁ r₂ =
      (∫ m, χ m ^ 2 ∂priorLaw p) * ((r₁ z)^2 + (r₂ z)^2) := by
  rw [channelInformation, priorLaw_integral p hp hp0, ← integral_mul_const]
  apply integral_congr_ae
  refine Eventually.of_forall fun m => ?_
  simp only [Pi.zero_apply, mul_zero, zero_smul, add_zero, map_smul, smul_eq_mul]
  by_cases h : p m = 0
  · simp [h]
  · field_simp

/-- Nonzero correlation forces a strictly positive second moment. -/
theorem positive_second_moment_of_correlation {μ : Measure Plane} [IsFiniteMeasure μ]
    (χ h : Plane → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hcor : 0 < ∫ m, χ m * h m ∂μ) : 0 < ∫ m, χ m ^ 2 ∂μ := by
  have hi : Integrable (fun m => χ m ^ 2) μ :=
    (hχ.pow 2).integrable_of_hasCompactSupport (hc.comp_left (g := fun x : ℝ => x^2) (by norm_num))
  have hn := integral_nonneg (μ := μ) (fun m => sq_nonneg (χ m))
  apply lt_of_le_of_ne hn
  intro hz
  have ha := (integral_eq_zero_iff_of_nonneg (fun m => sq_nonneg (χ m)) hi).mp hz.symm
  have he : (∫ m, χ m * h m ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ha] with m hm
    have hm0 : χ m = 0 := sq_eq_zero_iff.mp hm
    simp [hm0]
  linarith

/-- A detecting smooth compact test is *constructed* from a positive target
second moment. Thus a direction lost by a limiting channel forces divergence
of the actual all-Borel optimal normalized risk. The receiver may rotate or
change offsets arbitrarily; only its energy in this direction matters. -/
theorem singular_direction_sequence_diverges {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (hfull : ∀ᵐ m ∂priorLaw p, m ∈ Ω)
    (f : Plane → ℝ) (hf : ContDiff ℝ 1 f) (z : Plane)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ m, ‖fderiv ℝ f m z‖ ≤ C)
    (hpositive : 0 < ∫ m, (fderiv ℝ f m z)^2 ∂priorLaw p)
    (r₁ r₂ : ℕ → Plane →L[ℝ] ℝ) (c : ℕ → Plane)
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hvlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0))
    (lo hi : ℝ) (hlohi : lo ≤ hi)
    (htarget : ∀ᵐ m ∂priorLaw p, lo ≤ f m ∧ f m ≤ hi)
    (henergy : ∀ n, 0 < (r₁ n z)^2 + (r₂ n z)^2)
    (hlimit : Tendsto (fun n => (r₁ n z)^2 + (r₂ n z)^2) atTop (𝓝 0)) :
    Tendsto (fun n => rowOptimalRisk p f (r₁ n) (r₂ n) (c n) (v n) / (2 * (v n : ℝ)))
      atTop atTop := by
  letI := priorLaw_isProbability p hp0 hpi hpn
  have hd : Continuous (fun m => fderiv ℝ f m z) :=
    (hf.continuous_fderiv le_rfl).clm_apply continuous_const
  obtain ⟨χ, hχ, hc, hs, hcor⟩ :=
    WeightedVariational.exists_positive_scalar_test hd hΩ hfull hC hbound hpositive
  have hsecond := positive_second_moment_of_correlation χ _ hχ.continuous hc hcor
  have hscalar := scalar_test_channelInformation p χ hp hp0 z
  have hz : tsupport (0 : Plane → ℝ) = ∅ := tsupport_eq_empty_iff.mpr rfl
  have hczero : HasCompactSupport (0 : Plane → ℝ) := by
    change IsCompact (tsupport (0 : Plane → ℝ))
    rw [hz]
    exact isCompact_empty
  have hszero : tsupport (0 : Plane → ℝ) ⊆ Ω := by rw [hz]; exact empty_subset _
  apply singular_row_sequence_diverges hΩ p hp hp0 hpi hpn hpC hpPos f χ 0 hf
    (hχ.of_le (by norm_num)) contDiff_const hc hczero
    hs hszero z 0 r₁ r₂ c v hv hvlim lo hi hlohi htarget
  · rw [scalar_test_sensitivity p f χ hp hp0 z]
    exact ne_of_gt hcor
  · intro n
    rw [hscalar]
    exact mul_pos hsecond (henergy n)
  · simp_rw [hscalar]
    simpa using hlimit.const_mul (∫ m, χ m ^ 2 ∂priorLaw p)

/-- Every fixed test gives its sharp lower coefficient along changing receiver
rows when its channel energy converges to a positive limit. -/
theorem nonsingular_row_sequence_lower {Ω : Set Plane} (hΩ : IsOpen Ω)
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (hpC : ContDiffOn ℝ 1 p Ω) (hpPos : ∀ m ∈ Ω, 0 < p m)
    (f η₁ η₂ : Plane → ℝ) (hf : ContDiff ℝ 1 f)
    (hη₁ : ContDiff ℝ 1 η₁) (hη₂ : ContDiff ℝ 1 η₂)
    (hc₁ : HasCompactSupport η₁) (hc₂ : HasCompactSupport η₂)
    (hs₁ : tsupport η₁ ⊆ Ω) (hs₂ : tsupport η₂ ⊆ Ω)
    (z w : Plane) (r₁ r₂ : ℕ → Plane →L[ℝ] ℝ) (c : ℕ → Plane)
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hvlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0))
    (lo hi : ℝ) (hlohi : lo ≤ hi)
    (htarget : ∀ᵐ m ∂priorLaw p, lo ≤ f m ∧ f m ≤ hi)
    (henergy : ∀ n, 0 < channelInformation p η₁ η₂ z w (r₁ n) (r₂ n))
    (E₀ : ℝ) (hE₀ : 0 < E₀)
    (hlimit : Tendsto (fun n => channelInformation p η₁ η₂ z w (r₁ n) (r₂ n)) atTop (𝓝 E₀)) :
    LowerAsymptotic (fun n => rowOptimalRisk p f (r₁ n) (r₂ n) (c n) (v n) / (2 * (v n : ℝ)))
      (sensitivity p f η₁ η₂ z w ^ 2 / (2 * E₀)) := by
  apply lowerAsymptotic_of_ratio (mul_pos (by norm_num) hE₀)
  · have h := (hlimit.const_mul 2).add ((hvlim.const_mul 2).mul_const
      (priorInformation p η₁ η₂ z w))
    simpa using h
  · intro n
    exact rowOptimalRisk_normalized_bound hΩ p hp hp0 hpi hpn hpC hpPos f η₁ η₂ hf hη₁ hη₂
      hc₁ hc₂ hs₁ hs₂ z w (r₁ n) (r₂ n) (c n) (hv n) lo hi hlohi htarget (henergy n)

end Analog.GaussianSequentialConverse
