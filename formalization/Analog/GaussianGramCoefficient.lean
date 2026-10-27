import Analog.GeneralTargetSmallNoise
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The actual Gaussian coefficient in inverse-Gram coordinates

The inverse-adjoint energy from the variational converse and the derivative
energy from Gaussian achievability are the same quadratic form. These lemmas
identify that form with the manuscript's two-by-two inverse Gram expression.
-/

noncomputable section
namespace Analog.GaussianGramCoefficient
open MeasureTheory
open scoped RealInnerProductSpace

theorem complex_linear_apply (S : ℂ →L[ℝ] ℂ) (z : ℂ) :
    S z = z.re • S 1 + z.im • S Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz, map_add, map_smul, map_smul]

theorem real_inner_coordinates (u v : ℂ) :
    inner ℝ u v = u.re * v.re + u.im * v.im := by
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
  change (v * star u).re = _
  rw [Complex.star_def]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

def gramA (S : ℂ ≃L[ℝ] ℂ) : ℝ := (S 1).re ^ 2 + (S 1).im ^ 2
def gramB (S : ℂ ≃L[ℝ] ℂ) : ℝ := (S Complex.I).re ^ 2 + (S Complex.I).im ^ 2
def gramC (S : ℂ ≃L[ℝ] ℂ) : ℝ :=
  (S 1).re * (S Complex.I).re + (S 1).im * (S Complex.I).im
def channelDet (S : ℂ ≃L[ℝ] ℂ) : ℝ :=
  (S 1).re * (S Complex.I).im - (S 1).im * (S Complex.I).re

theorem channelDet_ne_zero (S : ℂ ≃L[ℝ] ℂ) : channelDet S ≠ 0 := by
  have h₁ := congrArg Complex.re (S.apply_symm_apply (1 : ℂ))
  have h₂ := congrArg Complex.im (S.apply_symm_apply (1 : ℂ))
  have h₃ := congrArg Complex.re (S.apply_symm_apply Complex.I)
  have h₄ := congrArg Complex.im (S.apply_symm_apply Complex.I)
  have he (z : ℂ) : S z = z.re • S 1 + z.im • S Complex.I :=
    complex_linear_apply S.toContinuousLinearMap z
  rw [he] at h₁ h₂ h₃ h₄
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    smul_eq_mul, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im] at h₁ h₂ h₃ h₄
  have he : channelDet S * channelDet S.symm = 1 := by
    calc
      channelDet S * channelDet S.symm =
          ((S.symm 1).re * (S 1).re + (S.symm 1).im * (S Complex.I).re) *
            ((S.symm Complex.I).re * (S 1).im + (S.symm Complex.I).im * (S Complex.I).im) -
          ((S.symm Complex.I).re * (S 1).re + (S.symm Complex.I).im * (S Complex.I).re) *
            ((S.symm 1).re * (S 1).im + (S.symm 1).im * (S Complex.I).im) := by
              unfold channelDet
              ring
      _ = 1 := by rw [h₁, h₂, h₃, h₄]; norm_num
  intro hz
  rw [hz, zero_mul] at he
  norm_num at he

theorem gram_det_pos (S : ℂ ≃L[ℝ] ℂ) :
    0 < gramA S * gramB S - gramC S ^ 2 := by
  have he : gramA S * gramB S - gramC S ^ 2 = channelDet S ^ 2 := by
    unfold gramA gramB gramC channelDet
    ring
  rw [he]
  exact sq_pos_of_ne_zero (channelDet_ne_zero S)

theorem inverse_adjoint_energy (S : ℂ ≃L[ℝ] ℂ) (w : ℂ) :
    ‖S.symm.toContinuousLinearMap.adjoint w‖ ^ 2 =
      (gramB S * w.re ^ 2 - 2 * gramC S * w.re * w.im + gramA S * w.im ^ 2) /
        (gramA S * gramB S - gramC S ^ 2) := by
  let h := S.symm.toContinuousLinearMap.adjoint w
  have h₁ := S.symm.toContinuousLinearMap.adjoint_inner_left (S 1) w
  have h₂ := S.symm.toContinuousLinearMap.adjoint_inner_left (S Complex.I) w
  change inner ℝ h (S 1) = inner ℝ w (S.symm (S 1)) at h₁
  change inner ℝ h (S Complex.I) = inner ℝ w (S.symm (S Complex.I)) at h₂
  rw [S.symm_apply_apply, real_inner_coordinates, real_inner_coordinates] at h₁ h₂
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero, zero_add] at h₁ h₂
  have hr : h.re = ((S Complex.I).im * w.re - (S 1).im * w.im) / channelDet S := by
    apply (eq_div_iff (channelDet_ne_zero S)).mpr
    unfold channelDet
    linear_combination (S Complex.I).im * h₁ - (S 1).im * h₂
  have hi : h.im = (-(S Complex.I).re * w.re + (S 1).re * w.im) / channelDet S := by
    apply (eq_div_iff (channelDet_ne_zero S)).mpr
    unfold channelDet
    linear_combination -(S Complex.I).re * h₁ + (S 1).re * h₂
  change ‖h‖ ^ 2 = _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hr, hi]
  simpa only [gramA, gramB, gramC, channelDet, one_mul, one_pow, pow_two] using
    SmallNoise.gram_gradient_energy (S 1).re (S 1).im (S Complex.I).re
      (S Complex.I).im 1 w.re w.im

/-- The achievability directional coefficient is exactly the inverse-adjoint
energy used by the all-decoder variational lower bound. -/
theorem inverse_derivative_energy (S : ℂ ≃L[ℝ] ℂ) (J : ℂ →L[ℝ] ℝ) :
    (J (S.symm 1)) ^ 2 + (J (S.symm Complex.I)) ^ 2 =
      ‖S.symm.toContinuousLinearMap.adjoint (⟨J 1, J Complex.I⟩ : ℂ)‖ ^ 2 := by
  let w : ℂ := ⟨J 1, J Complex.I⟩
  have he (z : ℂ) : J z = inner ℝ w z := by
    rw [GeneralTargetSmallNoise.complex_clm_apply, real_inner_coordinates]
    dsimp [w]
    ring
  have ha (z : ℂ) : inner ℝ w (S.symm z) =
      inner ℝ (S.symm.toContinuousLinearMap.adjoint w) z :=
    (S.symm.toContinuousLinearMap.adjoint_inner_left z w).symm
  rw [he, he, ha, ha,
    real_inner_coordinates, real_inner_coordinates, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply]
  simp [w, pow_two]

def gramMatrix (S : ℂ ≃L[ℝ] ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![gramA S, gramC S; gramC S, gramB S]

def inverseGramMatrix (S : ℂ ≃L[ℝ] ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![gramB S / (gramA S * gramB S - gramC S ^ 2),
    -gramC S / (gramA S * gramB S - gramC S ^ 2);
    -gramC S / (gramA S * gramB S - gramC S ^ 2),
    gramA S / (gramA S * gramB S - gramC S ^ 2)]

theorem gram_mul_inverse (S : ℂ ≃L[ℝ] ℂ) :
    gramMatrix S * inverseGramMatrix S = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramMatrix, inverseGramMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [ne_of_gt (gram_det_pos S)] <;> ring

theorem inverseGramMatrix_eq_inverse (S : ℂ ≃L[ℝ] ℂ) :
    inverseGramMatrix S = (gramMatrix S)⁻¹ :=
  (Matrix.inv_eq_right_inv (gram_mul_inverse S)).symm

def gradientSecondMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (w : Ω → ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![∫ x, (w x).re ^ 2 ∂μ, ∫ x, (w x).re * (w x).im ∂μ;
    ∫ x, (w x).re * (w x).im ∂μ, ∫ x, (w x).im ^ 2 ∂μ]

/-- Integration gives the exact weighted inverse-trace objective, including
the off-diagonal second moment. -/
theorem integrated_inverse_gram_trace {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : ℂ ≃L[ℝ] ℂ) (w : Ω → ℂ) (hw : Measurable w)
    (hr : Integrable (fun x => (w x).re ^ 2) μ)
    (hi : Integrable (fun x => (w x).im ^ 2) μ) :
    (∫ x, ‖S.symm.toContinuousLinearMap.adjoint (w x)‖ ^ 2 ∂μ) =
      Matrix.trace (gradientSecondMoment μ w * inverseGramMatrix S) := by
  have hri := SmallNoise.integrable_mul_of_squares
    (Complex.measurable_re.comp hw) (Complex.measurable_im.comp hw) hr hi
  change Integrable (fun x => (w x).re * (w x).im) μ at hri
  simp_rw [inverse_adjoint_energy]
  rw [integral_div]
  have he : (fun x => gramB S * (w x).re ^ 2 -
        2 * gramC S * (w x).re * (w x).im + gramA S * (w x).im ^ 2) =
      (fun x => gramB S * (w x).re ^ 2 -
        (2 * gramC S) * ((w x).re * (w x).im) + gramA S * (w x).im ^ 2) := by
    funext x
    ring
  have hsum := integral_add ((hr.const_mul (gramB S)).sub (hri.const_mul (2 * gramC S)))
    (hi.const_mul (gramA S))
  have hsub := integral_sub (hr.const_mul (gramB S)) (hri.const_mul (2 * gramC S))
  simp only [Pi.sub_apply] at hsum
  rw [he, hsum, hsub]
  simp only [integral_const_mul]
  simp [Matrix.trace, gradientSecondMoment, inverseGramMatrix,
    Fin.sum_univ_two]
  ring

theorem integrated_inverse_trace {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : ℂ ≃L[ℝ] ℂ) (w : Ω → ℂ) (hw : Measurable w)
    (hr : Integrable (fun x => (w x).re ^ 2) μ)
    (hi : Integrable (fun x => (w x).im ^ 2) μ) :
    (∫ x, ‖S.symm.toContinuousLinearMap.adjoint (w x)‖ ^ 2 ∂μ) =
      Matrix.trace (gradientSecondMoment μ w * (gramMatrix S)⁻¹) := by
  rw [← inverseGramMatrix_eq_inverse]
  exact integrated_inverse_gram_trace μ S w hw hr hi

end Analog.GaussianGramCoefficient
