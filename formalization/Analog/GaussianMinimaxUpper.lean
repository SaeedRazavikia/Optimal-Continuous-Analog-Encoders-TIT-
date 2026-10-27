import Analog.FixedPriorGaussianLimit
import Analog.GaussianWorstCase

/-!
# Actual fixed-channel Gaussian minimax upper bound

The endpoint-extension decoder supplies a finite conditional Gaussian risk at
every moment. Its proved uniform small-noise limit bounds the genuine infimum
over all Borel decoders in the density-based worst-case model.
-/
noncomputable section
namespace Analog.GaussianMinimaxUpper
open Set Filter MeasureTheory
open GeneralTargetGaussianAchievability FixedPriorGaussianLimit GaussianBayesConverse
open GaussianWorstCase
open scoped Topology NNReal ENNReal

abbrev Plane := ℝ × ℝ

/-- The inverse-channel energy in the coordinates used by the converse. -/
def channelEnergy (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (m : Plane) : ℝ :=
  ‖T.symm.toContinuousLinearMap.adjoint (gradient (planeExtension r₁ r₂) m)‖^2/2

theorem decoder_energy (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : Plane) (m : Plane) :
    UniformSmallNoise.energy (decoderDerivative r₁ r₂ T (Complex.equivRealProdCLM.symm c))
      (Complex.equivRealProdCLM.symm c + T (Complex.equivRealProdCLM.symm m)) =
      channelEnergy r₁ r₂ T m := by
  simp only [UniformSmallNoise.energy, decoderDerivative, add_sub_cancel_left,
    T.symm_apply_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [GaussianGramCoefficient.inverse_derivative_energy]
  unfold channelEnergy
  rw [planeExtension_gradient]
  simp [extendedDerivative]

/-- The actual conditional likelihood law is the additive Gaussian law. -/
theorem pointRisk_constructed (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : Plane)
    {v : ℝ≥0} (hv : v ≠ 0) (m : Plane) :
    pointRisk (planeExtension r₁ r₂) (planeDecoder r₁ r₂ T c)
      (receiverFirst T) (receiverSecond T) c v m =
    ENNReal.ofReal (2*(v : ℝ) * UniformSmallNoise.powerRisk
      (decoder r₁ r₂ T (Complex.equivRealProdCLM.symm c)) (2*(v : ℝ))
      (Complex.equivRealProdCLM.symm c + T (Complex.equivRealProdCLM.symm m))) := by
  let D := decoder r₁ r₂ T (Complex.equivRealProdCLM.symm c)
  let x := Complex.equivRealProdCLM.symm c + T (Complex.equivRealProdCLM.symm m)
  obtain ⟨hC, _, L, _, _, hLip⟩ := decoder_regularity r₁ r₂ T (Complex.equivRealProdCLM.symm c)
  have hd : Measurable (planeDecoder r₁ r₂ T c) :=
    hC.continuous.measurable.comp Complex.equivRealProdCLM.symm.continuous.measurable
  have hobs (z : ℂ) :
      Complex.equivRealProdCLM.symm (GaussianLawBridge.additiveObservation
        (receiverFirst T) (receiverSecond T) c v m z) = x+Real.sqrt (2*(v : ℝ)) • z := by
    simpa [x, ArbitraryEncoder.asComplex] using
      GaussianLawBridge.additiveObservation_asComplex T (Complex.equivRealProdCLM.symm c) v m z
  have hLaw : observationLaw (receiverFirst T) (receiverSecond T) c v m =
      GaussianNoise.standardComplexGaussian.map
        (GaussianLawBridge.additiveObservation (receiverFirst T) (receiverSecond T) c v m) := by
    rw [GaussianLawBridge.conditional_additive_law,
      GaussianLawBridge.conditional_density_law _ _ _ hv]
    rfl
  have he : D x = planeExtension r₁ r₂ m := by simp [D, x, decoder, planeExtension]
  have hi : Integrable (fun z : ℂ => (D (x+Real.sqrt (2*(v : ℝ)) • z)-D x)^2)
      GaussianNoise.standardComplexGaussian := by
    apply (GaussianNoise.complex_norm_square_integrable.const_mul
      (((L : ℝ)*|Real.sqrt (2*(v : ℝ))|)^2)).mono'
    · exact (((hC.continuous.measurable.comp (measurable_const.add
        (measurable_id.const_smul (Real.sqrt (2*(v : ℝ)))))).sub measurable_const).pow_const 2).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h := hLip.dist_le_mul (x+Real.sqrt (2*(v : ℝ)) • z) x
        simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h
        have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
        simpa only [sq_abs, mul_pow, mul_assoc] using hs
  have hN : (2:ℝ)*(v : ℝ) ≠ 0 := mul_ne_zero (by norm_num) (NNReal.coe_ne_zero.mpr hv)
  rw [pointRisk, BorelRisk.squareRisk, hLaw,
    lintegral_map ((hd.sub measurable_const).pow_const 2).ennreal_ofReal
      (by unfold GaussianLawBridge.additiveObservation; fun_prop)]
  simp_rw [planeDecoder, hobs]
  change (∫⁻ z, ENNReal.ofReal ((D (x+Real.sqrt (2*(v : ℝ)) • z)-planeExtension r₁ r₂ m)^2)
      ∂GaussianNoise.standardComplexGaussian) = _
  rw [← he, ← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  congr 1
  change _ = 2*(v : ℝ) * UniformSmallNoise.powerRisk D (2*(v : ℝ)) x
  unfold UniformSmallNoise.powerRisk
  field_simp

/-- The constructed decoder's normalized conditional risk has a uniform finite
bound at every nonnegative noise power. -/
theorem powerRisk_bounded (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : Plane) :
    ∃ L : ℝ≥0, ∀ N : ℝ, 0 ≤ N → ∀ x : ℂ,
      UniformSmallNoise.powerRisk (decoder r₁ r₂ T (Complex.equivRealProdCLM.symm c)) N x ≤ (L : ℝ)^2 := by
  obtain ⟨_, _, L, _, _, hLip⟩ := decoder_regularity r₁ r₂ T (Complex.equivRealProdCLM.symm c)
  refine ⟨L, fun N hN x => ?_⟩
  rw [← UniformSmallNoise.risk_sqrt_eq_powerRisk _ hN]
  exact UniformSmallNoise.risk_bound _ hLip _ _

/-- Fixed-channel upper bound for the genuine all-Borel minimax risk. The
coefficient is the actual supremum of inverse-channel gradient energy on M;
the Gaussian law, decoder, and uniform expansion have all been derived. -/
theorem fixed_minimax_upper (M : Set Plane) (hM : IsCompact M) (hne : M.Nonempty)
    (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : Plane)
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0)) :
    ∀ b > sSup (channelEnergy r₁ r₂ T '' M), ∀ᶠ n in atTop,
      minimaxRisk M (planeExtension r₁ r₂) (receiverFirst T) (receiverSecond T) c (v n) /
        (2*(v n : ℝ)) < b := by
  let D := decoder r₁ r₂ T (Complex.equivRealProdCLM.symm c)
  let J := decoderDerivative r₁ r₂ T (Complex.equivRealProdCLM.symm c)
  let R : Plane → ℂ := fun m => Complex.equivRealProdCLM.symm c + T (Complex.equivRealProdCLM.symm m)
  have hR : Continuous R := continuous_const.add
    (T.continuous.comp Complex.equivRealProdCLM.symm.continuous)
  obtain ⟨hC, hJ, L, hL, hb, hLip⟩ := decoder_regularity r₁ r₂ T (Complex.equivRealProdCLM.symm c)
  obtain ⟨ystar, ⟨mstar, hmstar, rfl⟩, hmax, hconv⟩ :=
    UniformSmallNoise.worst_case_power_limit D J (decoder_hasFDerivAt r₁ r₂ T _)
      hJ hL hb (R '' M) (hM.image hR) (hne.image R)
  have hmax' : ∀ m ∈ M, channelEnergy r₁ r₂ T m ≤ channelEnergy r₁ r₂ T mstar := by
    intro m hm
    simpa only [J, R, decoder_energy] using hmax (R m) (Set.mem_image_of_mem R hm)
  have hgreat : IsGreatest (channelEnergy r₁ r₂ T '' M) (channelEnergy r₁ r₂ T mstar) :=
    ⟨Set.mem_image_of_mem _ hmstar, by rintro _ ⟨m, hm, rfl⟩; exact hmax' m hm⟩
  have hs : sSup (channelEnergy r₁ r₂ T '' M) = channelEnergy r₁ r₂ T mstar := hgreat.csSup_eq
  have hcoef0 : 0 ≤ channelEnergy r₁ r₂ T mstar := div_nonneg (sq_nonneg _) (by norm_num)
  have hvlim : Tendsto (fun n => 2*(v n : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using hlim.const_mul 2, Filter.Eventually.of_forall (fun n => ?_)⟩
    change 0 < 2*(v n : ℝ)
    exact mul_pos (by norm_num) (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (hv n)))
  have hconv' := hconv.comp hvlim
  simp only [J, R, decoder_energy] at hconv'
  intro b hbcoef
  rw [hs] at hbcoef
  let bmid := (channelEnergy r₁ r₂ T mstar+b)/2
  have hmid : channelEnergy r₁ r₂ T mstar < bmid := by dsimp [bmid]; linarith
  have hmidb : bmid < b := by dsimp [bmid]; linarith
  have hmid0 : 0 ≤ bmid := hcoef0.trans hmid.le
  have hevent := hconv'.eventually_lt_const hmid
  filter_upwards [hevent] with n hn
  have hN : 0 < 2*(v n : ℝ) := mul_pos (by norm_num)
    (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (hv n)))
  have hbounded : BddAbove (UniformSmallNoise.powerRisk D (2*(v n : ℝ)) '' (R '' M)) := by
    refine ⟨(L : ℝ)^2, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    rw [← UniformSmallNoise.risk_sqrt_eq_powerRisk _ hN.le]
    exact UniformSmallNoise.risk_bound D hLip _ _
  have hpoint : ∀ m ∈ M, pointRisk (planeExtension r₁ r₂) (planeDecoder r₁ r₂ T c)
      (receiverFirst T) (receiverSecond T) c (v n) m ≤ ENNReal.ofReal (2*(v n : ℝ)*bmid) := by
    intro m hm
    rw [pointRisk_constructed _ _ _ _ (hv n)]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hN.le
    have hle := le_csSup hbounded (Set.mem_image_of_mem _ (Set.mem_image_of_mem R hm))
    exact hle.trans (le_of_lt hn)
  have hDmeas : Measurable (planeDecoder r₁ r₂ T c) :=
    hC.continuous.measurable.comp Complex.equivRealProdCLM.symm.continuous.measurable
  have hu := minimaxRisk_le_of_uniform_bound M (planeExtension r₁ r₂)
    (receiverFirst T) (receiverSecond T) c (v n) ⟨planeDecoder r₁ r₂ T c, hDmeas⟩
    (mul_nonneg hN.le hmid0) hpoint
  have hnorm : minimaxRisk M (planeExtension r₁ r₂) (receiverFirst T) (receiverSecond T) c (v n) /
      (2*(v n : ℝ)) ≤ bmid :=
    (div_le_iff₀ hN).mpr (by simpa only [mul_comm bmid] using hu)
  exact hnorm.trans_lt hmidb

/-- Targets agreeing at every attainable moment have identical minimax risk. -/
theorem minimaxRisk_congr_target (M : Set Plane) (f g : Plane → ℝ)
    (hfg : EqOn f g M) (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0) :
    minimaxRisk M f r₁ r₂ c v = minimaxRisk M g r₁ r₂ c v := by
  unfold minimaxRisk
  congr 1
  apply iInf_congr
  intro D
  unfold worstRisk
  apply iSup_congr
  intro m
  unfold pointRisk
  rw [hfg m.2]

/-- The upper bound stated for the original prescribed readout and its
prescribed slopes on the actual compact attainable moment set. -/
theorem fixed_minimax_upper_prescribed (M : Set Plane) (hM : IsCompact M) (hne : M.Nonempty)
    (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : Plane)
    (hrect : ∀ m ∈ M, Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂)
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0)) :
    ∀ b > sSup (planeCoefficient r₁ r₂ T '' M), ∀ᶠ n in atTop,
      minimaxRisk M (planeTarget r₁ r₂) (receiverFirst T) (receiverSecond T) c (v n) /
        (2*(v n : ℝ)) < b := by
  have hfg : EqOn (planeTarget r₁ r₂) (planeExtension r₁ r₂) M := by
    intro m hm
    exact (extension_agrees r₁ r₂ (hrect m hm)).1.symm
  have himage : planeCoefficient r₁ r₂ T '' M = channelEnergy r₁ r₂ T '' M := by
    apply Set.image_congr
    intro m hm
    exact coefficient_eq_inverse_energy r₁ r₂ T (hrect m hm)
  intro b hb
  rw [himage] at hb
  filter_upwards [fixed_minimax_upper M hM hne r₁ r₂ T c v hv hlim b hb] with n hn
  rw [minimaxRisk_congr_target M _ _ hfg]
  exact hn

end Analog.GaussianMinimaxUpper
