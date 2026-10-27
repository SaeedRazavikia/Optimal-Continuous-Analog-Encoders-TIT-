import Analog.GaussianDesignAttainment
import Analog.GaussianGramCoefficient
import Analog.GaussianBayesConverse

/-! # The actual finite-node Gaussian channel from coefficient parameters -/
noncomputable section
namespace Analog.GaussianParameterChannel
open HeterogeneousAttainment GaussianDesignAttainment GaussianGramCoefficient

def columnComplex (u : ℝ × ℝ) : ℂ := ⟨u.1,u.2⟩

def channelMap {K : ℕ} (p : Parameters K) : ℂ →L[ℝ] ℂ :=
  (K : ℝ) • (Complex.reCLM.smulRight (columnComplex p.2.1) +
    Complex.imCLM.smulRight (columnComplex p.2.2))

theorem channelMap_apply {K : ℕ} (p : Parameters K) (z : ℂ) :
    channelMap p z =
      (⟨(K:ℝ)*(p.2.1.1*z.re+p.2.2.1*z.im),
        (K:ℝ)*(p.2.1.2*z.re+p.2.2.2*z.im)⟩ : ℂ) := by
  apply Complex.ext <;> simp [channelMap, columnComplex] <;> ring

theorem channelMap_injective {K : ℕ} (hK : 0 < K) {p : Parameters K}
    (hp : coefficientDet p ≠ 0) : Function.Injective (channelMap p) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  change channelMap p z = 0 at hz
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp only [channelMap_apply,
    Complex.zero_re, Complex.zero_im] at hr hi
  have hr' : p.2.1.1*z.re+p.2.2.1*z.im=0 := (mul_eq_zero.mp hr).resolve_left hk
  have hi' : p.2.1.2*z.re+p.2.2.2*z.im=0 := (mul_eq_zero.mp hi).resolve_left hk
  have hzre : z.re * coefficientDet p = 0 := by
    unfold coefficientDet
    linear_combination p.2.2.2*hr' - p.2.2.1*hi'
  have hzim : z.im * coefficientDet p = 0 := by
    unfold coefficientDet
    linear_combination -p.2.1.2*hr' + p.2.1.1*hi'
  exact Complex.ext ((mul_eq_zero.mp hzre).resolve_right hp)
    ((mul_eq_zero.mp hzim).resolve_right hp)

def channelEquiv {K : ℕ} (hK : 0 < K) (p : Parameters K) (hp : coefficientDet p ≠ 0) :
    ℂ ≃L[ℝ] ℂ :=
  (LinearEquiv.ofBijective (channelMap p).toLinearMap
    ⟨channelMap_injective hK hp,
      LinearMap.injective_iff_surjective.mp (channelMap_injective hK hp)⟩).toContinuousLinearEquiv

theorem channelEquiv_apply {K : ℕ} (hK : 0 < K) (p : Parameters K)
    (hp : coefficientDet p ≠ 0) (z : ℂ) : channelEquiv hK p hp z = channelMap p z := rfl

def firstRow {K : ℕ} (p : Parameters K) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (K : ℝ) • (p.2.1.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
    p.2.2.1 • ContinuousLinearMap.snd ℝ ℝ ℝ)

def secondRow {K : ℕ} (p : Parameters K) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (K : ℝ) • (p.2.1.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
    p.2.2.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)

def totalOffset {K : ℕ} (p : Parameters K) : ℝ × ℝ := ∑ k, p.1 k

theorem receiverFirst_eq {K : ℕ} (hK : 0 < K) (p : Parameters K)
    (hp : coefficientDet p ≠ 0) :
    GaussianBayesConverse.receiverFirst (channelEquiv hK p hp) = firstRow p := by
  apply ContinuousLinearMap.ext
  intro m
  simp [GaussianBayesConverse.receiverFirst, channelEquiv_apply, channelMap_apply,
    firstRow, mul_add]

theorem receiverSecond_eq {K : ℕ} (hK : 0 < K) (p : Parameters K)
    (hp : coefficientDet p ≠ 0) :
    GaussianBayesConverse.receiverSecond (channelEquiv hK p hp) = secondRow p := by
  apply ContinuousLinearMap.ext
  intro m
  simp [GaussianBayesConverse.receiverSecond, channelEquiv_apply, channelMap_apply,
    secondRow, mul_add]

theorem parameter_inverse_energy {K : ℕ} (hK : 0 < K) (p : Parameters K)
    (hp : coefficientDet p ≠ 0) (w : ℂ) :
    ‖(channelEquiv hK p hp).symm.toContinuousLinearMap.adjoint w‖^2 =
      inverseCoefficient p (fun _ : Unit => (w.re,w.im)) () / (K : ℝ)^2 := by
  rw [inverse_adjoint_energy]
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hD := (parameter_gram_positive hp).2.ne'
  simp only [gramA, gramB, gramC, channelEquiv_apply, channelMap_apply,
    Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add, add_zero]
  rw [inverseCoefficient, GramSynthesis.dual_formula]
  dsimp [parameterPlanar, GramSynthesis.Planar.A, GramSynthesis.Planar.B,
    GramSynthesis.Planar.C, GramSynthesis.det] at hD ⊢
  have hfact :
      (((K:ℝ)*p.2.1.1)^2+((K:ℝ)*p.2.1.2)^2)*
        (((K:ℝ)*p.2.2.1)^2+((K:ℝ)*p.2.2.2)^2)-
      ((K:ℝ)*p.2.1.1*((K:ℝ)*p.2.2.1)+(K:ℝ)*p.2.1.2*((K:ℝ)*p.2.2.2))^2 =
      (K:ℝ)^4*((p.2.1.1^2+p.2.1.2^2)*(p.2.2.1^2+p.2.2.2^2)-
        (p.2.1.1*p.2.2.1+p.2.1.2*p.2.2.2)^2) := by ring
  rw [hfact]
  field_simp

theorem firstRow_apply {K : ℕ} (p : Parameters K) (m : ℝ × ℝ) :
    firstRow p m = (K:ℝ)*(p.2.1.1*m.1+p.2.2.1*m.2) := by
  simp [firstRow, mul_add]

theorem secondRow_apply {K : ℕ} (p : Parameters K) (m : ℝ × ℝ) :
    secondRow p m = (K:ℝ)*(p.2.1.2*m.1+p.2.2.2*m.2) := by
  simp [secondRow, mul_add]

theorem firstRow_continuous {K : ℕ} : Continuous (firstRow (K := K)) := by
  unfold firstRow
  fun_prop

theorem secondRow_continuous {K : ℕ} : Continuous (secondRow (K := K)) := by
  unfold secondRow
  fun_prop

theorem direction_energy_positive {K : ℕ} (hK : 0 < K) (p : Parameters K)
    (hp : coefficientDet p ≠ 0) (z : ℝ × ℝ) (hz : z ≠ 0) :
    0 < (firstRow p z)^2 + (secondRow p z)^2 := by
  have hn : (firstRow p z)^2 + (secondRow p z)^2 ≥ 0 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  by_contra hnot
  have hr : firstRow p z = 0 := by nlinarith [sq_nonneg (secondRow p z)]
  have hi : secondRow p z = 0 := by nlinarith [sq_nonneg (firstRow p z)]
  have hzero : channelMap p (columnComplex z) = 0 := by
    apply Complex.ext
    · simpa [channelMap_apply, firstRow_apply, columnComplex] using hr
    · simpa [channelMap_apply, secondRow_apply, columnComplex] using hi
  have hz' : columnComplex z = 0 := (channelMap_injective hK hp)
    (by simpa only [map_zero] using hzero)
  apply hz
  exact Prod.ext (congrArg Complex.re hz') (congrArg Complex.im hz')

theorem direction_energy_continuous {K : ℕ} (z : ℝ × ℝ) :
    Continuous (fun p : Parameters K => (firstRow p z)^2+(secondRow p z)^2) := by
  simp only [firstRow_apply, secondRow_apply]
  fun_prop

theorem totalOffset_continuous {K : ℕ} : Continuous (totalOffset (K := K)) := by
  unfold totalOffset
  fun_prop

theorem parameter_gramA {K : ℕ} (hK : 0 < K) (p : Parameters K) (hp : coefficientDet p ≠ 0) :
    gramA (channelEquiv hK p hp) = (K:ℝ)^2*(parameterPlanar p).A := by
  simp [gramA, channelEquiv_apply, channelMap_apply, parameterPlanar, GramSynthesis.Planar.A]
  ring

theorem parameter_gramB {K : ℕ} (hK : 0 < K) (p : Parameters K) (hp : coefficientDet p ≠ 0) :
    gramB (channelEquiv hK p hp) = (K:ℝ)^2*(parameterPlanar p).B := by
  simp [gramB, channelEquiv_apply, channelMap_apply, parameterPlanar, GramSynthesis.Planar.B]
  ring

theorem parameter_gramC {K : ℕ} (hK : 0 < K) (p : Parameters K) (hp : coefficientDet p ≠ 0) :
    gramC (channelEquiv hK p hp) = (K:ℝ)^2*(parameterPlanar p).C := by
  simp [gramC, channelEquiv_apply, channelMap_apply, parameterPlanar, GramSynthesis.Planar.C]
  ring

/-- The likelihood rows and offset reproduce the physical finite-node sum. -/
theorem received_eq_channel {K : ℕ} (hK : 0 < K) (p : Parameters K)
    (γ : Fin K → ℝ → ℝ × ℝ) (s : Fin K → ℝ) :
    HeterogeneousScore.received (HeterogeneousScore.encoder (parameterPlanar p) p.1 γ) s =
      totalOffset p + (firstRow p (HeterogeneousScore.meanStatistic γ s),
        secondRow p (HeterogeneousScore.meanStatistic γ s)) := by
  rw [HeterogeneousScore.received_encoder_mean hK]
  ext <;> simp [totalOffset, firstRow_apply, secondRow_apply, parameterPlanar,
    Prod.fst_sum, Prod.snd_sum]

end Analog.GaussianParameterChannel
