import Analog.GaussianMinimaxUpper
import Analog.GaussianMinimaxConverse

/-!
# The full fixed-encoder Gaussian minimax limit

The actual localized all-Borel converse and the constructed endpoint-extension
upper bound give the sharp fixed-channel minimax limit. The same fixed decoder
achieves the attained maximal coefficient, with genuine finite worst-case risk.
-/
noncomputable section
namespace Analog.GaussianFixedMinimax
open Set Filter MeasureTheory
open GeneralTargetGaussianAchievability FixedPriorGaussianLimit GaussianBayesConverse
open GaussianWorstCase GaussianMinimaxUpper GaussianMinimaxConverse
open scoped Topology NNReal ENNReal

abbrev Plane := ℝ × ℝ

/-- Constant-channel specialization of the actual minimax converse, matched
with the proved uniform upper bound for the original prescribed readout. -/
theorem fixed_minimax_sequential_limit
    (M : Set Plane) (hM : IsCompact M) (hne : M.Nonempty)
    (hregular : M ⊆ closure (interior M))
    (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : Plane)
    (hrect : ∀ m ∈ M, Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂)
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => minimaxRisk M (planeTarget r₁ r₂) (receiverFirst T) (receiverSecond T)
      c (v n) / (2*(v n : ℝ))) atTop (𝓝 (sSup (planeCoefficient r₁ r₂ T '' M))) := by
  obtain ⟨C, hC, hgrad⟩ := planeExtension_gradient_bounded r₁ r₂
  obtain ⟨B, hB, hb⟩ := target_bounded r₁ r₂
  have hbound : ∀ m ∈ M, -B ≤ planeExtension r₁ r₂ m ∧ planeExtension r₁ r₂ m ≤ B := by
    intro m hm
    change -B ≤ extendedTarget r₁ r₂ (Complex.equivRealProdCLM.symm m) ∧
      extendedTarget r₁ r₂ (Complex.equivRealProdCLM.symm m) ≤ B
    rw [(extension_agrees r₁ r₂ (hrect m hm)).1]
    exact abs_le.mp (hb _ (hrect m hm))
  have hlo := moving_minimax_converse M hne hregular (planeExtension r₁ r₂)
    (planeExtension_contDiff r₁ r₂) hC hgrad (fun _ => T) T
    tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds (fun _ => c)
    v hv hlim (-B) B (by linarith) hbound
  have hfg : EqOn (planeTarget r₁ r₂) (planeExtension r₁ r₂) M := by
    intro m hm
    exact (extension_agrees r₁ r₂ (hrect m hm)).1.symm
  have himage : localCoefficient (planeExtension r₁ r₂) T '' M = planeCoefficient r₁ r₂ T '' M := by
    apply Set.image_congr
    intro m hm
    exact (coefficient_eq_inverse_energy r₁ r₂ T (hrect m hm)).symm
  have hcoef : maxCoefficient M (planeExtension r₁ r₂) T = sSup (planeCoefficient r₁ r₂ T '' M) := by
    rw [maxCoefficient, himage]
  rw [hcoef] at hlo
  have hu := fixed_minimax_upper_prescribed M hM hne r₁ r₂ T c hrect v hv hlim
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have ham : a < (a+sSup (planeCoefficient r₁ r₂ T '' M))/2 := by linarith
    have hma : (a+sSup (planeCoefficient r₁ r₂ T '' M))/2 < sSup (planeCoefficient r₁ r₂ T '' M) := by linarith
    filter_upwards [hlo _ hma] with n hn
    rw [minimaxRisk_congr_target M _ _ hfg]
    exact ham.trans_le hn
  · exact hu

/-- Full one-sided fixed-encoder minimax equality at zero total noise power. -/
theorem fixed_minimax_limit
    (M : Set Plane) (hM : IsCompact M) (hne : M.Nonempty)
    (hregular : M ⊆ closure (interior M))
    (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : Plane)
    (hrect : ∀ m ∈ M, Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂) :
    Tendsto (fun v : ℝ≥0 => minimaxRisk M (planeTarget r₁ r₂) (receiverFirst T) (receiverSecond T)
      c v / (2*(v : ℝ))) (𝓝[>] (0 : ℝ≥0)) (𝓝 (sSup (planeCoefficient r₁ r₂ T '' M))) := by
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro v hv
  have hvpos : ∀ᶠ n in atTop, 0 < v n := hv.eventually self_mem_nhdsWithin
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hvpos
  apply (Filter.tendsto_add_atTop_iff_nat n₀).mp
  have hv' : ∀ n, v (n+n₀) ≠ 0 := fun n => ne_of_gt (hn₀ _ (Nat.le_add_left _ _))
  have hvl : Tendsto (fun n => (v (n+n₀) : ℝ)) atTop (𝓝 0) :=
    NNReal.tendsto_coe.mpr ((tendsto_nhds_of_tendsto_nhdsWithin hv).comp
      (Filter.tendsto_add_atTop_nat n₀))
  exact fixed_minimax_sequential_limit M hM hne hregular r₁ r₂ T c hrect
    (fun n => v (n+n₀)) hv' hvl

/-- Equal targets on M give identical actual worst-case risks for every decoder. -/
theorem worstRisk_congr_target (M : Set Plane) (f g D : Plane → ℝ)
    (hfg : EqOn f g M) (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0) :
    worstRisk M f D r₁ r₂ c v = worstRisk M g D r₁ r₂ c v := by
  unfold worstRisk
  apply iSup_congr
  intro m
  unfold pointRisk
  rw [hfg m.2]

/-- Exact equality between the density-based worst-case risk and the real
supremum of actual additive-Gaussian normalized risks of the constructed decoder. -/
theorem constructed_worstRisk_eq (M : Set Plane) (r₁ r₂ : IntervalReadout)
    (T : ℂ ≃L[ℝ] ℂ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0) :
    (worstRisk M (planeExtension r₁ r₂) (planeDecoder r₁ r₂ T c)
      (receiverFirst T) (receiverSecond T) c v).toReal / (2*(v : ℝ)) =
      sSup (UniformSmallNoise.powerRisk (decoder r₁ r₂ T (Complex.equivRealProdCLM.symm c))
        (2*(v : ℝ)) '' ((fun m : Plane =>
          Complex.equivRealProdCLM.symm c + T (Complex.equivRealProdCLM.symm m)) '' M)) := by
  let D := decoder r₁ r₂ T (Complex.equivRealProdCLM.symm c)
  let R : Plane → ℂ := fun m => Complex.equivRealProdCLM.symm c + T (Complex.equivRealProdCLM.symm m)
  have hN : 0 < 2*(v : ℝ) := mul_pos (by norm_num) (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv))
  have hnn (m : M) : 0 ≤ 2*(v : ℝ) * UniformSmallNoise.powerRisk D (2*(v : ℝ)) (R m) := by
    apply mul_nonneg hN.le
    exact div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) hN.le
  have hfinite (m : M) : pointRisk (planeExtension r₁ r₂) (planeDecoder r₁ r₂ T c)
      (receiverFirst T) (receiverSecond T) c v m ≠ ⊤ := by
    rw [pointRisk_constructed _ _ _ _ hv]
    exact ENNReal.ofReal_ne_top
  rw [worstRisk, ENNReal.toReal_iSup hfinite]
  simp_rw [pointRisk_constructed _ _ _ _ hv]
  change (⨆ m : M, (ENNReal.ofReal (2*(v : ℝ) * UniformSmallNoise.powerRisk D (2*(v : ℝ)) (R m))).toReal) /
    (2*(v : ℝ)) = _
  simp_rw [ENNReal.toReal_ofReal (hnn _)]
  rw [← Real.mul_iSup_of_nonneg hN.le]
  rw [mul_div_cancel_left₀ _ hN.ne']
  rw [Set.image_image, Set.image_eq_range, sSup_range]

/-- The constructed decoder has finite genuine worst-case risk at every
positive variance, with the global Lipschitz/noise-energy bound. -/
theorem constructed_worstRisk_finite (M : Set Plane) (r₁ r₂ : IntervalReadout)
    (T : ℂ ≃L[ℝ] ℂ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0) :
    worstRisk M (planeExtension r₁ r₂) (planeDecoder r₁ r₂ T c)
      (receiverFirst T) (receiverSecond T) c v ≠ ⊤ := by
  obtain ⟨L, hb⟩ := powerRisk_bounded r₁ r₂ T c
  apply ne_of_lt
  apply lt_of_le_of_lt (b := ENNReal.ofReal (2*(v : ℝ)*(L : ℝ)^2))
  · apply iSup_le
    intro m
    rw [pointRisk_constructed _ _ _ _ hv]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (hb _ (by positivity) _) (by positivity))
  · exact ENNReal.ofReal_lt_top

/-- The single prescribed endpoint decoder, independent of noise power,
achieves an attained maximum coefficient in the actual worst-case risk. -/
theorem fixed_decoder_attains (M : Set Plane) (hM : IsCompact M) (hne : M.Nonempty)
    (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : Plane)
    (hrect : ∀ m ∈ M, Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂) :
    ∃ mstar ∈ M,
      (∀ m ∈ M, planeCoefficient r₁ r₂ T m ≤ planeCoefficient r₁ r₂ T mstar) ∧
      Tendsto (fun v : ℝ≥0 => (worstRisk M (planeTarget r₁ r₂) (planeDecoder r₁ r₂ T c)
        (receiverFirst T) (receiverSecond T) c v).toReal / (2*(v : ℝ)))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 (planeCoefficient r₁ r₂ T mstar)) := by
  let D := decoder r₁ r₂ T (Complex.equivRealProdCLM.symm c)
  let J := decoderDerivative r₁ r₂ T (Complex.equivRealProdCLM.symm c)
  let R : Plane → ℂ := fun m => Complex.equivRealProdCLM.symm c + T (Complex.equivRealProdCLM.symm m)
  have hR : Continuous R := continuous_const.add
    (T.continuous.comp Complex.equivRealProdCLM.symm.continuous)
  obtain ⟨_, hJ, L, hL, hb, _⟩ := decoder_regularity r₁ r₂ T (Complex.equivRealProdCLM.symm c)
  obtain ⟨_, ⟨mstar, hmstar, rfl⟩, hmax, hconv⟩ :=
    UniformSmallNoise.worst_case_power_limit D J (decoder_hasFDerivAt r₁ r₂ T _)
      hJ hL hb (R '' M) (hM.image hR) (hne.image R)
  have henergy (m : Plane) (hm : m ∈ M) :
      UniformSmallNoise.energy J (R m) = planeCoefficient r₁ r₂ T m := by
    rw [show UniformSmallNoise.energy J (R m) = channelEnergy r₁ r₂ T m from decoder_energy r₁ r₂ T c m]
    exact (coefficient_eq_inverse_energy r₁ r₂ T (hrect m hm)).symm
  refine ⟨mstar, hmstar, ?_, ?_⟩
  · intro m hm
    rw [← henergy m hm, ← henergy mstar hmstar]
    exact hmax _ (Set.mem_image_of_mem R hm)
  · have hvariance : Tendsto (fun v : ℝ≥0 => 2*(v : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa using (NNReal.continuous_coe.tendsto (0 : ℝ≥0)).const_mul 2 |>.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with v hv
        change 0 < 2*(v : ℝ)
        exact mul_pos (by norm_num) (NNReal.coe_pos.mpr hv)
    have hc := hconv.comp hvariance
    rw [henergy mstar hmstar] at hc
    have hfg : EqOn (planeTarget r₁ r₂) (planeExtension r₁ r₂) M := by
      intro m hm
      exact (extension_agrees r₁ r₂ (hrect m hm)).1.symm
    apply hc.congr'
    filter_upwards [self_mem_nhdsWithin] with v hv
    rw [worstRisk_congr_target M _ _ _ hfg, constructed_worstRisk_eq M r₁ r₂ T c (ne_of_gt hv)]
    rfl

/-- The fixed-encoder half of the manuscript's Gaussian minimax theorem:
the maximum coefficient is attained, equals the all-Borel minimax limit, and
is achieved by one explicitly constructed noise-independent Borel decoder. -/
theorem fixed_encoder_minimax (M : Set Plane) (hM : IsCompact M) (hne : M.Nonempty)
    (hregular : M = closure (interior M))
    (r₁ r₂ : IntervalReadout) (T : ℂ ≃L[ℝ] ℂ) (c : Plane)
    (hrect : ∀ m ∈ M, Complex.equivRealProdCLM.symm m ∈ rectangle r₁ r₂) :
    ∃ mstar ∈ M,
      (∀ m ∈ M, planeCoefficient r₁ r₂ T m ≤ planeCoefficient r₁ r₂ T mstar) ∧
      Measurable (planeDecoder r₁ r₂ T c) ∧
      (∀ v : ℝ≥0, v ≠ 0 → worstRisk M (planeTarget r₁ r₂) (planeDecoder r₁ r₂ T c)
        (receiverFirst T) (receiverSecond T) c v ≠ ⊤) ∧
      Tendsto (fun v : ℝ≥0 => minimaxRisk M (planeTarget r₁ r₂) (receiverFirst T) (receiverSecond T)
        c v / (2*(v : ℝ))) (𝓝[>] (0 : ℝ≥0)) (𝓝 (planeCoefficient r₁ r₂ T mstar)) ∧
      Tendsto (fun v : ℝ≥0 => (worstRisk M (planeTarget r₁ r₂) (planeDecoder r₁ r₂ T c)
        (receiverFirst T) (receiverSecond T) c v).toReal / (2*(v : ℝ)))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 (planeCoefficient r₁ r₂ T mstar)) := by
  obtain ⟨mstar, hmstar, hmax, hdec⟩ := fixed_decoder_attains M hM hne r₁ r₂ T c hrect
  refine ⟨mstar, hmstar, hmax, ?_, ?_, ?_, hdec⟩
  · exact (decoder_regularity r₁ r₂ T (Complex.equivRealProdCLM.symm c)).1.continuous.measurable.comp
      Complex.equivRealProdCLM.symm.continuous.measurable
  · intro v hv
    have hfg : EqOn (planeTarget r₁ r₂) (planeExtension r₁ r₂) M := by
      intro m hm
      exact (extension_agrees r₁ r₂ (hrect m hm)).1.symm
    rw [worstRisk_congr_target M _ _ _ hfg]
    exact constructed_worstRisk_finite M r₁ r₂ T c hv
  · have hs : IsGreatest (planeCoefficient r₁ r₂ T '' M) (planeCoefficient r₁ r₂ T mstar) :=
      ⟨Set.mem_image_of_mem _ hmstar, by rintro _ ⟨m, hm, rfl⟩; exact hmax m hm⟩
    rw [← hs.csSup_eq]
    exact fixed_minimax_limit M hM hne hregular.subset r₁ r₂ T c hrect

end Analog.GaussianFixedMinimax
