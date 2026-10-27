import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# Actual Gaussian likelihood and the compact-flux score identity

These results use the Gaussian density, rather than a stipulated statistical
information inequality. Compact C¹ test fluxes eliminate boundary terms and
the decoder is an arbitrary scalar at each fixed observation: no derivative
of the decoder occurs. The remaining joint-integrability and prior-localization
interfaces are stated explicitly in the companion completion note.
-/

noncomputable section
namespace Analog.GaussianScoreIdentity
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal

abbrev Plane := ℝ × ℝ

/-- The actual density of two independent Gaussian coordinates, with a linear
mean map and a separate fixed offset. The coordinate variance is `v`, so total
complex noise power is `2*v`. -/
def likelihood (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0)
    (m y : Plane) : ℝ :=
  gaussianPDFReal (c.1 + r₁ m) v y.1 * gaussianPDFReal (c.2 + r₂ m) v y.2

/-- Positivity of every nondegenerate likelihood, including singular mean maps. -/
theorem likelihood_pos (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0}
    (hv : v ≠ 0) (m y : Plane) : 0 < likelihood r₁ r₂ c v m y :=
  mul_pos (gaussianPDFReal_pos _ _ _ hv) (gaussianPDFReal_pos _ _ _ hv)

/-- Normalization of the actual observation density. -/
theorem likelihood_integral (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0}
    (hv : v ≠ 0) (m : Plane) : (∫ y : Plane, likelihood r₁ r₂ c v m y) = 1 := by
  change (∫ y : Plane, gaussianPDFReal (c.1 + r₁ m) v y.1 *
    gaussianPDFReal (c.2 + r₂ m) v y.2 ∂volume.prod volume) = 1
  rw [integral_prod_mul, integral_gaussianPDFReal_eq_one _ hv,
    integral_gaussianPDFReal_eq_one _ hv, one_mul]

/-- Parameter smoothness of the likelihood requires no invertibility. -/
theorem likelihood_contDiff (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane)
    (v : ℝ≥0) (y : Plane) : ContDiff ℝ ⊤ (fun m => likelihood r₁ r₂ c v m y) := by
  unfold likelihood gaussianPDFReal
  fun_prop

/-- Coordinate Gaussian density differentiated with respect to its mean. -/
theorem gaussian_mean_derivative (r : Plane →L[ℝ] ℝ) (c y : ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) (m : Plane) :
    HasFDerivAt (fun x => gaussianPDFReal (c + r x) v y)
      (((y - (c + r m)) / (v : ℝ) * gaussianPDFReal (c + r m) v y) • r) m := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hr : HasFDerivAt (fun x => c + r x) r m := r.hasFDerivAt.const_add c
  have h := (((hr.const_sub y).pow 2).neg.mul_const (2 * (v : ℝ))⁻¹).exp.const_mul
    (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  have hmap :
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ •
        Real.exp (-(y - (c + r m)) ^ 2 * (2 * (v : ℝ))⁻¹) •
          (2 * (v : ℝ))⁻¹ • -((2 • (y - (c + r m)) ^ (2 - 1)) • -r) =
      ((y - (c + r m)) / (v : ℝ) * gaussianPDFReal (c + r m) v y) • r := by
    apply ContinuousLinearMap.ext
    intro z
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
      smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, gaussianPDFReal]
    norm_num
    field_simp
  rw [← hmap]
  exact h

/-- The Gaussian parameter score in a chosen moment direction. -/
def meanScore (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0)
    (m y z : Plane) : ℝ :=
  ((y.1 - (c.1 + r₁ m)) * r₁ z + (y.2 - (c.2 + r₂ m)) * r₂ z) / (v : ℝ)

/-- Actual likelihood derivative equals the Gaussian score times the density. -/
theorem likelihood_fderiv (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0}
    (hv : v ≠ 0) (m y z : Plane) :
    fderiv ℝ (fun x => likelihood r₁ r₂ c v x y) m z =
      meanScore r₁ r₂ c v m y z * likelihood r₁ r₂ c v m y := by
  have h := (gaussian_mean_derivative r₁ c.1 y.1 hv m).mul
    (gaussian_mean_derivative r₂ c.2 y.2 hv m)
  have he := congrArg (fun L : Plane →L[ℝ] ℝ => L z) h.fderiv
  change fderiv ℝ (fun x => likelihood r₁ r₂ c v x y) m z = _ at he
  rw [he]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  unfold meanScore likelihood
  ring

/-- Boundary-free integration by parts with a genuinely compact C¹ flux.
The scalar `d` may be an arbitrary decoder value; it is never differentiated. -/
theorem compact_flux_identity (f g : Plane → ℝ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hgs : HasCompactSupport g) (d : ℝ) (z : Plane) :
    (∫ m, (d - f m) * fderiv ℝ g m z) =
      ∫ m, fderiv ℝ f m z * g m := by
  have hf' : Continuous (fun m => fderiv ℝ f m z) :=
    (hf.continuous_fderiv le_rfl).clm_apply continuous_const
  have hg' : Continuous (fun m => fderiv ℝ g m z) :=
    (hg.continuous_fderiv le_rfl).clm_apply continuous_const
  have h₁ : Integrable (fun m => fderiv ℝ (fun x => d - f x) m z * g m) := by
    have he : (fun m => fderiv ℝ (fun x => d - f x) m z * g m) =
        (fun m => -(fderiv ℝ f m z) * g m) := by
      ext m
      rw [fderiv_const_sub d]
      rfl
    rw [he]
    exact (hf'.neg.mul hg.continuous).integrable_of_hasCompactSupport hgs.mul_left
  have h₂ : Integrable (fun m => (d - f m) * fderiv ℝ g m z) :=
    ((continuous_const.sub hf.continuous).mul hg').integrable_of_hasCompactSupport
      (hgs.fderiv_apply ℝ z).mul_left
  have h₃ : Integrable (fun m => (d - f m) * g m) :=
    ((continuous_const.sub hf.continuous).mul hg.continuous).integrable_of_hasCompactSupport
      hgs.mul_left
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h₁ h₂ h₃
    ((contDiff_const.sub hf).differentiable le_rfl) (hg.differentiable le_rfl)
  rw [h]
  simp_rw [fderiv_const_sub d,
    ContinuousLinearMap.neg_apply, neg_mul, integral_neg, neg_neg]

/-- Actual Gaussian weighted-score identity at each observation. The compact
flux is `a = p*η_i` in the manuscript. No statistical score identity is assumed. -/
theorem gaussian_flux_identity (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane)
    {v : ℝ≥0} (hv : v ≠ 0) (f a : Plane → ℝ)
    (hf : ContDiff ℝ 1 f) (ha : ContDiff ℝ 1 a)
    (has : HasCompactSupport a) (d : ℝ) (y z : Plane) :
    (∫ m, (d - f m) *
      (fderiv ℝ a m z + a m * meanScore r₁ r₂ c v m y z) *
        likelihood r₁ r₂ c v m y) =
      ∫ m, fderiv ℝ f m z * a m * likelihood r₁ r₂ c v m y := by
  have hq : ContDiff ℝ 1 (fun m => likelihood r₁ r₂ c v m y) :=
    (likelihood_contDiff r₁ r₂ c v y).of_le (by simp)
  have h := compact_flux_identity f (fun m => a m * likelihood r₁ r₂ c v m y)
    hf (ha.mul hq) has.mul_right d z
  convert h using 1
  · apply integral_congr_ae
    filter_upwards [] with m
    have he := congrArg (fun L : Plane →L[ℝ] ℝ => L z)
      ((ha.differentiable le_rfl m).hasFDerivAt.mul (hq.differentiable le_rfl m).hasFDerivAt).fderiv
    change fderiv ℝ (fun m => a m * likelihood r₁ r₂ c v m y) m z = _ at he
    rw [he]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [likelihood_fderiv r₁ r₂ c hv]
    ring
  · apply integral_congr_ae
    filter_upwards [] with m
    ring

/-- The likelihood is jointly continuous in moment and observation. -/
theorem likelihood_joint_continuous (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane)
    (v : ℝ≥0) : Continuous (fun p : Plane × Plane => likelihood r₁ r₂ c v p.1 p.2) := by
  unfold likelihood gaussianPDFReal
  fun_prop

/-- The normalized likelihood is integrable for every moment vector. -/
theorem likelihood_integrable (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane)
    (v : ℝ≥0) (m : Plane) : Integrable (likelihood r₁ r₂ c v m) :=
  (integrable_gaussianPDFReal _ _).mul_prod (integrable_gaussianPDFReal _ _)

/-- Integrating a compact parameter weight against the observation density
preserves its integrability; no uniform bound on the mean map is needed. -/
theorem likelihood_weight_integrable (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane)
    {v : ℝ≥0} (hv : v ≠ 0) (b : Plane → ℝ)
    (hb : Continuous b) (hbs : HasCompactSupport b) :
    Integrable (fun p : Plane × Plane => b p.1 * likelihood r₁ r₂ c v p.1 p.2) := by
  have hm : AEStronglyMeasurable
      (fun p : Plane × Plane => b p.1 * likelihood r₁ r₂ c v p.1 p.2)
      (volume.prod volume) :=
    ((hb.comp continuous_fst).mul (likelihood_joint_continuous r₁ r₂ c v)).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun m => (likelihood_integrable r₁ r₂ c v m).const_mul (b m))
  · have he : (fun m : Plane => ∫ y : Plane, ‖b m * likelihood r₁ r₂ c v m y‖) =
        (fun m => ‖b m‖) := by
      ext m
      simp_rw [norm_mul, Real.norm_eq_abs,
        abs_of_pos (likelihood_pos r₁ r₂ c hv m _)]
      rw [integral_const_mul, likelihood_integral r₁ r₂ c hv, mul_one]
    rw [he]
    exact (hb.integrable_of_hasCompactSupport hbs).norm

/-- Marginalization of the compact parameter weight against the actual
Gaussian observation density. -/
theorem likelihood_weight_integral (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane)
    {v : ℝ≥0} (hv : v ≠ 0) (b : Plane → ℝ)
    (hb : Continuous b) (hbs : HasCompactSupport b) :
    (∫ p : Plane × Plane, b p.1 * likelihood r₁ r₂ c v p.1 p.2) = ∫ m, b m := by
  change (∫ p : Plane × Plane, b p.1 * likelihood r₁ r₂ c v p.1 p.2
    ∂volume.prod volume) = _
  rw [integral_prod _ (likelihood_weight_integrable r₁ r₂ c hv b hb hbs)]
  simp_rw [integral_const_mul, likelihood_integral r₁ r₂ c hv, mul_one]

/-- The integrated score identity. The decoder is arbitrary; the explicit
integrability premise concerns the displayed joint product, not an assumed
information inequality or covariance identity. -/
theorem gaussian_joint_flux_identity (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane)
    {v : ℝ≥0} (hv : v ≠ 0) (f a : Plane → ℝ) (D : Plane → ℝ)
    (hf : ContDiff ℝ 1 f) (ha : ContDiff ℝ 1 a)
    (has : HasCompactSupport a) (z : Plane)
    (hi : Integrable (fun p : Plane × Plane => (D p.2 - f p.1) *
      (fderiv ℝ a p.1 z + a p.1 * meanScore r₁ r₂ c v p.1 p.2 z) *
        likelihood r₁ r₂ c v p.1 p.2)) :
    (∫ p : Plane × Plane, (D p.2 - f p.1) *
      (fderiv ℝ a p.1 z + a p.1 * meanScore r₁ r₂ c v p.1 p.2 z) *
        likelihood r₁ r₂ c v p.1 p.2) = ∫ m, fderiv ℝ f m z * a m := by
  have hb : Continuous (fun m => fderiv ℝ f m z * a m) :=
    ((hf.continuous_fderiv le_rfl).clm_apply continuous_const).mul ha.continuous
  have hbs : HasCompactSupport (fun m => fderiv ℝ f m z * a m) := has.mul_left
  have hir := likelihood_weight_integrable r₁ r₂ c hv _ hb hbs
  change (∫ p : Plane × Plane, (D p.2 - f p.1) *
    (fderiv ℝ a p.1 z + a p.1 * meanScore r₁ r₂ c v p.1 p.2 z) *
      likelihood r₁ r₂ c v p.1 p.2 ∂volume.prod volume) = _
  rw [integral_prod_symm _ hi]
  simp_rw [gaussian_flux_identity r₁ r₂ c hv f a hf ha has]
  calc
    (∫ y : Plane, ∫ m : Plane, fderiv ℝ f m z * a m * likelihood r₁ r₂ c v m y) =
        ∫ p : Plane × Plane, (fderiv ℝ f p.1 z * a p.1) *
          likelihood r₁ r₂ c v p.1 p.2 := (integral_prod_symm _ hir).symm
    _ = _ := likelihood_weight_integral r₁ r₂ c hv _ hb hbs

/-- Transfer integrability from the actual Gaussian measure to its density. -/
theorem gaussian_density_integrable {v : ℝ≥0} (hv : v ≠ 0) (u : ℝ)
    (g : ℝ → ℝ) (hg : Integrable g (gaussianReal u v)) :
    Integrable (fun x => g x * gaussianPDFReal u v x) := by
  rw [gaussianReal_of_var_ne_zero _ hv] at hg
  have h := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF u v) (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top))).mp hg
  simpa only [toReal_gaussianPDF, smul_eq_mul, mul_comm] using h

/-- First centered density moment. -/
theorem centered_density_mean (u : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ x : ℝ, (x - u) * gaussianPDFReal u v x) = 0 := by
  have hi : Integrable (fun x : ℝ => x) (gaussianReal u v) :=
    (memLp_id_gaussianReal (μ := u) (v := v) 1).integrable (by norm_num)
  have h : (∫ x : ℝ, x - u ∂gaussianReal u v) = 0 := by
    rw [integral_sub hi (integrable_const u)]
    simp
  rw [integral_gaussianReal_eq_integral_smul hv] at h
  simpa only [smul_eq_mul, mul_comm] using h

/-- Second centered density moment. -/
theorem centered_density_second (u : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ x : ℝ, (x - u) ^ 2 * gaussianPDFReal u v x) = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := u) (v := v)
  rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id.aemeasurable,
    integral_id_gaussianReal, integral_gaussianReal_eq_integral_smul hv] at h
  simpa only [smul_eq_mul, mul_comm] using h

/-- The centered density first moment is absolutely integrable. -/
theorem centered_density_integrable (u : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x : ℝ => (x - u) * gaussianPDFReal u v x) := by
  apply gaussian_density_integrable hv
  exact ((memLp_id_gaussianReal (μ := u) (v := v) 1).integrable (by norm_num)).sub
    (integrable_const _)

/-- The centered density second moment is absolutely integrable. -/
theorem centered_density_square_integrable (u : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x : ℝ => (x - u) ^ 2 * gaussianPDFReal u v x) := by
  apply gaussian_density_integrable hv
  exact ((memLp_id_gaussianReal (μ := u) (v := v) 2).sub (memLp_const u)).integrable_sq

/-- Every squared affine observation score is integrable against the product Gaussian density. -/
theorem gaussian_affine_square_integrable (u₁ u₂ d a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun y : Plane => (d + a * (y.1 - u₁) + b * (y.2 - u₂)) ^ 2 *
      (gaussianPDFReal u₁ v y.1 * gaussianPDFReal u₂ v y.2)) := by
  have h₀ := (integrable_gaussianPDFReal u₁ v).mul_prod (integrable_gaussianPDFReal u₂ v)
  have h₁ := (centered_density_integrable u₁ hv).mul_prod (integrable_gaussianPDFReal u₂ v)
  have h₂ := (integrable_gaussianPDFReal u₁ v).mul_prod (centered_density_integrable u₂ hv)
  have h₃ := (centered_density_square_integrable u₁ hv).mul_prod (integrable_gaussianPDFReal u₂ v)
  have h₄ := (integrable_gaussianPDFReal u₁ v).mul_prod (centered_density_square_integrable u₂ hv)
  have h₅ := (centered_density_integrable u₁ hv).mul_prod (centered_density_integrable u₂ hv)
  have hi := (((((h₀.const_mul (d^2)).add (h₁.const_mul (2*d*a))).add
    (h₂.const_mul (2*d*b))).add (h₃.const_mul (a^2))).add
    (h₄.const_mul (b^2))).add (h₅.const_mul (2*a*b))
  convert hi using 1
  ext y
  simp only [Pi.add_apply]
  ring

/-- Exact affine-score second moment for the genuine product Gaussian density. -/
theorem gaussian_affine_square (u₁ u₂ d a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ y : Plane, (d + a * (y.1 - u₁) + b * (y.2 - u₂)) ^ 2 *
      (gaussianPDFReal u₁ v y.1 * gaussianPDFReal u₂ v y.2)) =
      d ^ 2 + (v : ℝ) * (a ^ 2 + b ^ 2) := by
  let g₀ : Plane → ℝ := fun y => gaussianPDFReal u₁ v y.1 * gaussianPDFReal u₂ v y.2
  let g₁ : Plane → ℝ := fun y => ((y.1 - u₁) * gaussianPDFReal u₁ v y.1) * gaussianPDFReal u₂ v y.2
  let g₂ : Plane → ℝ := fun y => gaussianPDFReal u₁ v y.1 * ((y.2 - u₂) * gaussianPDFReal u₂ v y.2)
  let g₃ : Plane → ℝ := fun y => ((y.1 - u₁) ^ 2 * gaussianPDFReal u₁ v y.1) * gaussianPDFReal u₂ v y.2
  let g₄ : Plane → ℝ := fun y => gaussianPDFReal u₁ v y.1 * ((y.2 - u₂) ^ 2 * gaussianPDFReal u₂ v y.2)
  let g₅ : Plane → ℝ := fun y => ((y.1 - u₁) * gaussianPDFReal u₁ v y.1) * ((y.2 - u₂) * gaussianPDFReal u₂ v y.2)
  have h₀ : Integrable g₀ := (integrable_gaussianPDFReal _ _).mul_prod (integrable_gaussianPDFReal _ _)
  have h₁ : Integrable g₁ := (centered_density_integrable _ hv).mul_prod (integrable_gaussianPDFReal _ _)
  have h₂ : Integrable g₂ := (integrable_gaussianPDFReal _ _).mul_prod (centered_density_integrable _ hv)
  have h₃ : Integrable g₃ := (centered_density_square_integrable _ hv).mul_prod (integrable_gaussianPDFReal _ _)
  have h₄ : Integrable g₄ := (integrable_gaussianPDFReal _ _).mul_prod (centered_density_square_integrable _ hv)
  have h₅ : Integrable g₅ := (centered_density_integrable _ hv).mul_prod (centered_density_integrable _ hv)
  have I₀ : (∫ y, g₀ y) = 1 := by
    change (∫ y : Plane, gaussianPDFReal u₁ v y.1 * gaussianPDFReal u₂ v y.2 ∂volume.prod volume) = _
    rw [integral_prod_mul, integral_gaussianPDFReal_eq_one _ hv, integral_gaussianPDFReal_eq_one _ hv, one_mul]
  have I₁ : (∫ y, g₁ y) = 0 := by
    change (∫ y : Plane, ((y.1 - u₁) * gaussianPDFReal u₁ v y.1) * gaussianPDFReal u₂ v y.2 ∂volume.prod volume) = _
    rw [integral_prod_mul (fun x : ℝ => (x-u₁) * gaussianPDFReal u₁ v x) (gaussianPDFReal u₂ v), centered_density_mean _ hv, zero_mul]
  have I₂ : (∫ y, g₂ y) = 0 := by
    change (∫ y : Plane, gaussianPDFReal u₁ v y.1 * ((y.2 - u₂) * gaussianPDFReal u₂ v y.2) ∂volume.prod volume) = _
    rw [integral_prod_mul (gaussianPDFReal u₁ v) (fun x : ℝ => (x-u₂) * gaussianPDFReal u₂ v x), centered_density_mean _ hv, mul_zero]
  have I₃ : (∫ y, g₃ y) = (v : ℝ) := by
    change (∫ y : Plane, ((y.1 - u₁) ^ 2 * gaussianPDFReal u₁ v y.1) * gaussianPDFReal u₂ v y.2 ∂volume.prod volume) = _
    rw [integral_prod_mul (fun x : ℝ => (x-u₁)^2 * gaussianPDFReal u₁ v x) (gaussianPDFReal u₂ v), centered_density_second _ hv, integral_gaussianPDFReal_eq_one _ hv, mul_one]
  have I₄ : (∫ y, g₄ y) = (v : ℝ) := by
    change (∫ y : Plane, gaussianPDFReal u₁ v y.1 * ((y.2 - u₂) ^ 2 * gaussianPDFReal u₂ v y.2) ∂volume.prod volume) = _
    rw [integral_prod_mul (gaussianPDFReal u₁ v) (fun x : ℝ => (x-u₂)^2 * gaussianPDFReal u₂ v x), centered_density_second _ hv, integral_gaussianPDFReal_eq_one _ hv, one_mul]
  have I₅ : (∫ y, g₅ y) = 0 := by
    change (∫ y : Plane, ((y.1 - u₁) * gaussianPDFReal u₁ v y.1) * ((y.2 - u₂) * gaussianPDFReal u₂ v y.2) ∂volume.prod volume) = _
    rw [integral_prod_mul (fun x : ℝ => (x-u₁) * gaussianPDFReal u₁ v x) (fun x : ℝ => (x-u₂) * gaussianPDFReal u₂ v x), centered_density_mean _ hv, zero_mul]
  have he : (fun y : Plane => (d + a * (y.1 - u₁) + b * (y.2 - u₂)) ^ 2 *
      (gaussianPDFReal u₁ v y.1 * gaussianPDFReal u₂ v y.2)) =
      (fun y => d ^ 2 * g₀ y) + (fun y => (2 * d * a) * g₁ y) +
      (fun y => (2 * d * b) * g₂ y) + (fun y => a ^ 2 * g₃ y) +
      (fun y => b ^ 2 * g₄ y) + (fun y => (2 * a * b) * g₅ y) := by
    ext y
    dsimp [g₀, g₁, g₂, g₃, g₄, g₅]
    ring
  rw [he]
  have hT₀ := h₀.const_mul (d ^ 2)
  have hT₁ := h₁.const_mul (2 * d * a)
  have hT₂ := h₂.const_mul (2 * d * b)
  have hT₃ := h₃.const_mul (a ^ 2)
  have hT₄ := h₄.const_mul (b ^ 2)
  have hT₅ := h₅.const_mul (2 * a * b)
  have hI₅ := integral_add ((((hT₀.add hT₁).add hT₂).add hT₃).add hT₄) hT₅
  have hI₄ := integral_add (((hT₀.add hT₁).add hT₂).add hT₃) hT₄
  have hI₃ := integral_add ((hT₀.add hT₁).add hT₂) hT₃
  have hI₂ := integral_add (hT₀.add hT₁) hT₂
  have hI₁ := integral_add hT₀ hT₁
  simp only [Pi.add_apply] at hI₅ hI₄ hI₃ hI₂ hI₁
  change (∫ y, d^2*g₀ y + (2*d*a)*g₁ y + (2*d*b)*g₂ y + a^2*g₃ y +
    b^2*g₄ y + (2*a*b)*g₅ y) = _
  rw [hI₅, hI₄, hI₃, hI₂, hI₁]
  simp only [integral_const_mul, I₀, I₁, I₂, I₃, I₄, I₅]
  ring

/-- Exact conditional second moment of the complete weighted Gaussian score,
with a free prior-score offset. -/
theorem gaussian_score_second (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane)
    {v : ℝ≥0} (hv : v ≠ 0) (m z : Plane) (s : ℝ) :
    (∫ y : Plane, (s + meanScore r₁ r₂ c v m y z) ^ 2 *
      likelihood r₁ r₂ c v m y) =
      s ^ 2 + ((r₁ z) ^ 2 + (r₂ z) ^ 2) / (v : ℝ) := by
  have h := gaussian_affine_square (c.1 + r₁ m) (c.2 + r₂ m) s
    (r₁ z / (v : ℝ)) (r₂ z / (v : ℝ)) hv
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  convert h using 1
  · apply integral_congr_ae
    filter_upwards [] with y
    unfold meanScore likelihood
    congr 1
    congr 1
    ring
  · field_simp

/-- A second-moment information inequality from an actual score covariance.
The proof is the nonnegativity of the squared estimation residual after
subtracting its best linear score multiple. -/
theorem information_bound_of_covariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (error score : Ω → ℝ)
    (he : MemLp error 2 μ) (hs : MemLp score 2 μ)
    (hpos : 0 < ∫ x, score x ^ 2 ∂μ) :
    (∫ x, error x * score x ∂μ) ^ 2 / (∫ x, score x ^ 2 ∂μ) ≤
      ∫ x, error x ^ 2 ∂μ := by
  let A := ∫ x, error x * score x ∂μ
  let B := ∫ x, score x ^ 2 ∂μ
  let R := ∫ x, error x ^ 2 ∂μ
  have hep : Integrable (fun x => error x * score x) μ := he.integrable_mul hs
  have hexp : (∫ x, (error x - (A / B) * score x) ^ 2 ∂μ) =
      R - 2 * (A / B) * A + (A / B) ^ 2 * B := by
    have hp : (fun x => (error x - (A / B) * score x) ^ 2) =
        (fun x => error x ^ 2 - (2 * (A / B)) * (error x * score x) +
          (A / B) ^ 2 * score x ^ 2) := by ext x; ring
    rw [hp]
    have hadd := integral_add (he.integrable_sq.sub (hep.const_mul (2 * (A / B))))
      (hs.integrable_sq.const_mul ((A / B) ^ 2))
    have hsub := integral_sub he.integrable_sq (hep.const_mul (2 * (A / B)))
    simp only [Pi.sub_apply] at hadd
    rw [hadd, hsub, integral_const_mul, integral_const_mul]
  have hnonneg : 0 ≤ R - 2 * (A / B) * A + (A / B) ^ 2 * B := by
    rw [← hexp]
    exact integral_nonneg (fun _ => sq_nonneg _)
  change A ^ 2 / B ≤ R
  have hB : 0 < B := hpos
  apply (div_le_iff₀ hB).mpr
  have hcancel : (R - 2 * (A / B) * A + (A / B) ^ 2 * B) * B = R * B - A ^ 2 := by
    field_simp
    ring
  have hmul := mul_nonneg hnonneg hB.le
  rw [hcancel] at hmul
  linarith

/-- Joint moment-observation law represented by its genuine Gaussian density. -/
def jointLaw (p : Plane → ℝ) (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0) :
    Measure (Plane × Plane) :=
  volume.withDensity (fun q => ENNReal.ofReal (p q.1 * likelihood r₁ r₂ c v q.1 q.2))

/-- Any integrable prior weight remains jointly integrable after multiplication
by the normalized Gaussian likelihood. No global continuity of the prior is required. -/
theorem likelihood_weight_integrable_of_integrable
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0)
    (b : Plane → ℝ) (hb : Integrable b) :
    Integrable (fun q : Plane × Plane => b q.1 * likelihood r₁ r₂ c v q.1 q.2) := by
  have hm : AEStronglyMeasurable
      (fun q : Plane × Plane => b q.1 * likelihood r₁ r₂ c v q.1 q.2)
      (volume.prod volume) :=
    (hb.aestronglyMeasurable.comp_fst).mul
      (likelihood_joint_continuous r₁ r₂ c v).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun m => (likelihood_integrable r₁ r₂ c v m).const_mul (b m))
  · have he : (fun m : Plane => ∫ y : Plane, ‖b m * likelihood r₁ r₂ c v m y‖) =
        (fun m => ‖b m‖) := by
      ext m
      simp_rw [norm_mul, Real.norm_eq_abs,
        abs_of_pos (likelihood_pos r₁ r₂ c hv m _)]
      rw [integral_const_mul, likelihood_integral r₁ r₂ c hv, mul_one]
    rw [he]
    exact hb.norm

/-- The likelihood preserves the total integral of an arbitrary integrable prior. -/
theorem likelihood_weight_integral_of_integrable
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0)
    (b : Plane → ℝ) (hb : Integrable b) :
    (∫ q : Plane × Plane, b q.1 * likelihood r₁ r₂ c v q.1 q.2) = ∫ m, b m := by
  change (∫ q : Plane × Plane, b q.1 * likelihood r₁ r₂ c v q.1 q.2
    ∂volume.prod volume) = _
  rw [integral_prod _ (likelihood_weight_integrable_of_integrable r₁ r₂ c hv b hb)]
  simp_rw [integral_const_mul, likelihood_integral r₁ r₂ c hv, mul_one]

/-- A nonnegative unit-integral prior gives an actual probability joint law. -/
theorem jointLaw_isProbability (p : Plane → ℝ) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0) :
    IsProbabilityMeasure (jointLaw p r₁ r₂ c v) := by
  constructor
  rw [jointLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (likelihood_weight_integrable_of_integrable r₁ r₂ c hv p hpi)
      (Filter.Eventually.of_forall (fun q => mul_nonneg (hp0 q.1)
        (likelihood_pos r₁ r₂ c hv q.1 q.2).le)),
    likelihood_weight_integral_of_integrable r₁ r₂ c hv p hpi, hpn]
  norm_num

/-- A compact scalar test flux and a fixed parameter direction define a
weighted score. A vector-field score is the sum of two coordinate scores. -/
def fluxScore (p a : Plane → ℝ) (z : Plane)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0) (q : Plane × Plane) : ℝ :=
  (fderiv ℝ a q.1 z + a q.1 * meanScore r₁ r₂ c v q.1 q.2 z) / p q.1

/-- Linearity of the actual Gaussian parameter score in its direction. -/
theorem meanScore_smul (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0)
    (m y z : Plane) (t : ℝ) :
    meanScore r₁ r₂ c v m y (t • z) = t * meanScore r₁ r₂ c v m y z := by
  simp only [meanScore, map_smul, smul_eq_mul]
  ring

/-- Sum-linearity of the actual Gaussian parameter score. -/
theorem meanScore_add (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0)
    (m y z w : Plane) :
    meanScore r₁ r₂ c v m y (z + w) =
      meanScore r₁ r₂ c v m y z + meanScore r₁ r₂ c v m y w := by
  simp only [meanScore, map_add]
  ring

/-- Flux-score decomposition into prior and Gaussian scores. -/
theorem fluxScore_eq (p a : Plane → ℝ) (z : Plane)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0) (m y : Plane) :
    fluxScore p a z r₁ r₂ c v (m,y) =
      fderiv ℝ a m z / p m +
        meanScore r₁ r₂ c v m y ((a m / p m) • z) := by
  rw [meanScore_smul]
  unfold fluxScore
  ring

/-- Conditional flux information under the actual likelihood. -/
theorem flux_information_conditional (p a : Plane → ℝ) (z : Plane)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0) (m : Plane) :
    (∫ y : Plane, p m * likelihood r₁ r₂ c v m y *
      fluxScore p a z r₁ r₂ c v (m,y) ^ 2) =
      (fderiv ℝ a m z) ^ 2 / p m +
        (a m ^ 2 / p m) * ((r₁ z)^2 + (r₂ z)^2) / (v : ℝ) := by
  have h := gaussian_score_second r₁ r₂ c hv m ((a m / p m) • z)
    (fderiv ℝ a m z / p m)
  have he : (fun y : Plane => p m * likelihood r₁ r₂ c v m y *
      fluxScore p a z r₁ r₂ c v (m,y)^2) =
      (fun y => p m * ((fderiv ℝ a m z / p m +
        meanScore r₁ r₂ c v m y ((a m / p m) • z))^2 * likelihood r₁ r₂ c v m y)) := by
    ext y
    rw [fluxScore_eq]
    ring
  rw [he, integral_const_mul, h]
  simp only [map_smul, smul_eq_mul]
  by_cases hp : p m = 0
  · simp [hp]
  · field_simp

/-- Integration against the actual joint law equals density-weighted integration. -/
theorem jointLaw_integral (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0)
    (g : Plane × Plane → ℝ) :
    (∫ q, g q ∂jointLaw p r₁ r₂ c v) =
      ∫ q : Plane × Plane, (p q.1 * likelihood r₁ r₂ c v q.1 q.2) * g q := by
  unfold jointLaw
  have hm : Measurable (fun q : Plane × Plane => ENNReal.ofReal (p q.1 * likelihood r₁ r₂ c v q.1 q.2)) :=
    ((hp.comp measurable_fst).mul (likelihood_joint_continuous r₁ r₂ c v).measurable).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [ENNReal.toReal_ofReal (mul_nonneg (hp0 q.1) (likelihood_pos r₁ r₂ c hv q.1 q.2).le)]
  rfl

/-- Integrability transfer for the actual joint density. -/
theorem jointLaw_integrable_iff (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0)
    (g : Plane × Plane → ℝ) :
    Integrable g (jointLaw p r₁ r₂ c v) ↔
      Integrable (fun q : Plane × Plane => (p q.1 * likelihood r₁ r₂ c v q.1 q.2) * g q) := by
  unfold jointLaw
  have hm : Measurable (fun q : Plane × Plane => ENNReal.ofReal (p q.1 * likelihood r₁ r₂ c v q.1 q.2)) :=
    ((hp.comp measurable_fst).mul (likelihood_joint_continuous r₁ r₂ c v).measurable).ennreal_ofReal
  rw [integrable_withDensity_iff_integrable_smul' hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (mul_nonneg (hp0 _) (likelihood_pos r₁ r₂ c hv _ _).le), smul_eq_mul]

/-- Each conditional squared flux score is integrable under the true likelihood. -/
theorem conditional_flux_integrable (p a : Plane → ℝ) (z : Plane)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0) (m : Plane) :
    Integrable (fun y : Plane => p m * likelihood r₁ r₂ c v m y *
      fluxScore p a z r₁ r₂ c v (m,y) ^ 2) := by
  have hi := (gaussian_affine_square_integrable (c.1 + r₁ m) (c.2 + r₂ m)
    (fderiv ℝ a m z / p m) ((a m / p m) * r₁ z / (v : ℝ))
      ((a m / p m) * r₂ z / (v : ℝ)) hv).const_mul (p m)
  convert hi using 1
  ext y
  unfold fluxScore meanScore likelihood
  ring

/-- Actual score information is finite whenever its two explicit prior
integrals are finite; this is proved by conditional Gaussian integration. -/
theorem flux_information_integrable (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (a : Plane → ℝ) (ha : ContDiff ℝ 1 a) (z : Plane)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0)
    (hb : Integrable (fun m => (fderiv ℝ a m z)^2 / p m))
    (hA : Integrable (fun m => a m^2 / p m)) :
    Integrable (fun q : Plane × Plane => p q.1 * likelihood r₁ r₂ c v q.1 q.2 *
      fluxScore p a z r₁ r₂ c v q ^ 2) := by
  have hd : Continuous (fun m => fderiv ℝ a m z) :=
    (ha.continuous_fderiv le_rfl).clm_apply continuous_const
  have haC := ha.continuous
  have hs : Measurable (fluxScore p a z r₁ r₂ c v) := by
    unfold fluxScore meanScore
    fun_prop
  have hm : AEStronglyMeasurable
      (fun q : Plane × Plane => p q.1 * likelihood r₁ r₂ c v q.1 q.2 *
        fluxScore p a z r₁ r₂ c v q ^ 2) (volume.prod volume) :=
    (((hp.comp measurable_fst).mul (likelihood_joint_continuous r₁ r₂ c v).measurable).mul
      (hs.pow_const 2)).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall (conditional_flux_integrable p a z r₁ r₂ c hv)
  · have he : (fun m : Plane => ∫ y : Plane,
        ‖p m * likelihood r₁ r₂ c v m y * fluxScore p a z r₁ r₂ c v (m,y)^2‖) =
        (fun m => (fderiv ℝ a m z)^2 / p m +
          (a m^2 / p m) * (((r₁ z)^2 + (r₂ z)^2) / (v : ℝ))) := by
      ext m
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (mul_nonneg (hp0 m) (likelihood_pos r₁ r₂ c hv m _).le) (sq_nonneg _))]
      rw [flux_information_conditional p a z r₁ r₂ c hv]
      ring
    rw [he]
    exact hb.add (hA.mul_const _)

/-- The actual joint score variance equals its prior-score plus channel
information terms, with no covariance identity premise. -/
theorem jointLaw_flux_information (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (a : Plane → ℝ) (ha : ContDiff ℝ 1 a) (z : Plane)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0)
    (hb : Integrable (fun m => (fderiv ℝ a m z)^2 / p m))
    (hA : Integrable (fun m => a m^2 / p m)) :
    (∫ q, fluxScore p a z r₁ r₂ c v q ^ 2 ∂jointLaw p r₁ r₂ c v) =
      (∫ m, (fderiv ℝ a m z)^2 / p m) +
        (((r₁ z)^2 + (r₂ z)^2) / (v : ℝ)) * (∫ m, a m^2 / p m) := by
  rw [jointLaw_integral p hp hp0 r₁ r₂ c hv]
  change (∫ q : Plane × Plane, p q.1 * likelihood r₁ r₂ c v q.1 q.2 *
    fluxScore p a z r₁ r₂ c v q ^ 2 ∂volume.prod volume) = _
  rw [integral_prod _ (flux_information_integrable p hp hp0 a ha z r₁ r₂ c hv hb hA)]
  simp_rw [flux_information_conditional p a z r₁ r₂ c hv, div_eq_mul_inv]
  have hi := integral_add hb ((hA.mul_const ((r₁ z)^2 + (r₂ z)^2)).mul_const (v : ℝ)⁻¹)
  simp only [div_eq_mul_inv] at hi
  rw [hi, integral_mul_const, integral_mul_const]
  ring

/-- Square integrability of the actual weighted score follows from explicit
finite prior energies, which compact regular tests supply automatically. -/
theorem fluxScore_memLp (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (a : Plane → ℝ) (ha : ContDiff ℝ 1 a) (z : Plane)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0)
    (hb : Integrable (fun m => (fderiv ℝ a m z)^2 / p m))
    (hA : Integrable (fun m => a m^2 / p m)) :
    MemLp (fluxScore p a z r₁ r₂ c v) 2 (jointLaw p r₁ r₂ c v) := by
  have hd : Continuous (fun m => fderiv ℝ a m z) :=
    (ha.continuous_fderiv le_rfl).clm_apply continuous_const
  have haC := ha.continuous
  have hs : Measurable (fluxScore p a z r₁ r₂ c v) := by
    unfold fluxScore meanScore
    fun_prop
  apply (memLp_two_iff_integrable_sq hs.aestronglyMeasurable).mpr
  apply (jointLaw_integrable_iff p hp hp0 r₁ r₂ c hv _).mpr
  exact flux_information_integrable p hp hp0 a ha z r₁ r₂ c hv hb hA

/-- The score numerator vanishes where the density vanishes whenever the
compact test flux and its directional derivative do. -/
theorem flux_density_identity (p a : Plane → ℝ) (z : Plane)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0)
    (hz : ∀ m, p m = 0 → a m = 0 ∧ fderiv ℝ a m z = 0)
    (q : Plane × Plane) (e : ℝ) :
    (p q.1 * likelihood r₁ r₂ c v q.1 q.2) * (e * fluxScore p a z r₁ r₂ c v q) =
      e * (fderiv ℝ a q.1 z + a q.1 * meanScore r₁ r₂ c v q.1 q.2 z) *
        likelihood r₁ r₂ c v q.1 q.2 := by
  by_cases h : p q.1 = 0
  · obtain ⟨ha, hd⟩ := hz q.1 h
    simp [fluxScore, h, ha, hd]
  · unfold fluxScore
    field_simp

/-- A model-level weighted score covariance for any decoder whose product
with this score is integrable under the actual joint law. -/
theorem jointLaw_score_covariance (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0)
    (f a : Plane → ℝ) (D : Plane → ℝ) (z : Plane)
    (hf : ContDiff ℝ 1 f) (ha : ContDiff ℝ 1 a) (has : HasCompactSupport a)
    (hz : ∀ m, p m = 0 → a m = 0 ∧ fderiv ℝ a m z = 0)
    (hi : Integrable (fun q => (D q.2 - f q.1) * fluxScore p a z r₁ r₂ c v q)
      (jointLaw p r₁ r₂ c v)) :
    (∫ q, (D q.2 - f q.1) * fluxScore p a z r₁ r₂ c v q ∂jointLaw p r₁ r₂ c v) =
      ∫ m, fderiv ℝ f m z * a m := by
  have hprod := (jointLaw_integrable_iff p hp hp0 r₁ r₂ c hv _).mp hi
  simp_rw [flux_density_identity p a z r₁ r₂ c v hz] at hprod
  rw [jointLaw_integral p hp hp0 r₁ r₂ c hv]
  simp_rw [flux_density_identity p a z r₁ r₂ c v hz]
  exact gaussian_joint_flux_identity r₁ r₂ c hv f a D hf ha has z hprod

/-- A genuine Gaussian van Trees lower bound for each compact test flux.
The covariance is derived from the likelihood and integration by parts,
not assumed. The square-integrability premises express finite actual risk
and finite score information. -/
theorem gaussian_directional_information_bound
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0)
    (f a : Plane → ℝ) (D : Plane → ℝ) (z : Plane)
    (hf : ContDiff ℝ 1 f) (ha : ContDiff ℝ 1 a) (has : HasCompactSupport a)
    (hz : ∀ m, p m = 0 → a m = 0 ∧ fderiv ℝ a m z = 0)
    (he : MemLp (fun q : Plane × Plane => D q.2 - f q.1) 2 (jointLaw p r₁ r₂ c v))
    (hs : MemLp (fluxScore p a z r₁ r₂ c v) 2 (jointLaw p r₁ r₂ c v))
    (hpos : 0 < ∫ q, fluxScore p a z r₁ r₂ c v q ^ 2 ∂jointLaw p r₁ r₂ c v) :
    (∫ m, fderiv ℝ f m z * a m) ^ 2 /
      (∫ q, fluxScore p a z r₁ r₂ c v q ^ 2 ∂jointLaw p r₁ r₂ c v) ≤
        ∫ q, (D q.2 - f q.1) ^ 2 ∂jointLaw p r₁ r₂ c v := by
  have hc := jointLaw_score_covariance p hp hp0 r₁ r₂ c hv f a D z hf ha has hz
    (he.integrable_mul hs)
  have hi := information_bound_of_covariance (jointLaw p r₁ r₂ c v)
    (fun q => D q.2 - f q.1) (fluxScore p a z r₁ r₂ c v) he hs hpos
  rwa [hc] at hi

/-- The two-coordinate compact-flux score; directions can be any fixed basis. -/
def twoFluxScore (p a b : Plane → ℝ) (z w : Plane)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0) (q : Plane × Plane) : ℝ :=
  fluxScore p a z r₁ r₂ c v q + fluxScore p b w r₁ r₂ c v q

/-- Exact conditional information for a genuinely vector-valued test flux. -/
theorem twoFlux_information_conditional (p a b : Plane → ℝ) (z w : Plane)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0) (m : Plane) :
    (∫ y : Plane, p m * likelihood r₁ r₂ c v m y *
      twoFluxScore p a b z w r₁ r₂ c v (m,y) ^ 2) =
      (fderiv ℝ a m z + fderiv ℝ b m w)^2 / p m +
        ((r₁ (a m • z + b m • w))^2 + (r₂ (a m • z + b m • w))^2) /
          p m / (v : ℝ) := by
  have he : ∀ y, twoFluxScore p a b z w r₁ r₂ c v (m,y) =
      (fderiv ℝ a m z + fderiv ℝ b m w) / p m +
        meanScore r₁ r₂ c v m y ((p m)⁻¹ • (a m • z + b m • w)) := by
    intro y
    simp only [twoFluxScore, fluxScore_eq, meanScore_add, meanScore_smul]
    ring
  simp_rw [he]
  have hfun : (fun y : Plane => p m * likelihood r₁ r₂ c v m y *
      ((fderiv ℝ a m z + fderiv ℝ b m w) / p m +
        meanScore r₁ r₂ c v m y ((p m)⁻¹ • (a m • z + b m • w)))^2) =
      (fun y => p m * (((fderiv ℝ a m z + fderiv ℝ b m w) / p m +
        meanScore r₁ r₂ c v m y ((p m)⁻¹ • (a m • z + b m • w)))^2 * likelihood r₁ r₂ c v m y)) := by
    ext y
    ring
  rw [hfun, integral_const_mul, gaussian_score_second r₁ r₂ c hv]
  simp only [map_smul, smul_eq_mul]
  by_cases hp : p m = 0
  · simp [hp]
  · field_simp

/-- Joint covariance for the full two-coordinate Gaussian score. -/
theorem jointLaw_twoFlux_covariance
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0)
    (f a b : Plane → ℝ) (D : Plane → ℝ) (z w : Plane)
    (hf : ContDiff ℝ 1 f) (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (has : HasCompactSupport a) (hbs : HasCompactSupport b)
    (hza : ∀ m, p m = 0 → a m = 0 ∧ fderiv ℝ a m z = 0)
    (hzb : ∀ m, p m = 0 → b m = 0 ∧ fderiv ℝ b m w = 0)
    (he : MemLp (fun q : Plane × Plane => D q.2 - f q.1) 2 (jointLaw p r₁ r₂ c v))
    (hsa : MemLp (fluxScore p a z r₁ r₂ c v) 2 (jointLaw p r₁ r₂ c v))
    (hsb : MemLp (fluxScore p b w r₁ r₂ c v) 2 (jointLaw p r₁ r₂ c v)) :
    (∫ q, (D q.2 - f q.1) * twoFluxScore p a b z w r₁ r₂ c v q ∂jointLaw p r₁ r₂ c v) =
      (∫ m, fderiv ℝ f m z * a m) + (∫ m, fderiv ℝ f m w * b m) := by
  have hia := he.integrable_mul hsa
  have hib := he.integrable_mul hsb
  have hsum := integral_add hia hib
  simp only [Pi.mul_apply] at hsum
  simp_rw [twoFluxScore, mul_add]
  rw [hsum, jointLaw_score_covariance p hp hp0 r₁ r₂ c hv f a D z hf ha has hza hia,
    jointLaw_score_covariance p hp hp0 r₁ r₂ c hv f b D w hf hb hbs hzb hib]

/-- Exact information of the full vector-field score, expressed entirely in
prior-weighted derivatives and the actual receiver rows. -/
theorem jointLaw_twoFlux_information
    (p : Plane → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (a b : Plane → ℝ) (z w : Plane)
    (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) {v : ℝ≥0} (hv : v ≠ 0)
    (hsa : MemLp (fluxScore p a z r₁ r₂ c v) 2 (jointLaw p r₁ r₂ c v))
    (hsb : MemLp (fluxScore p b w r₁ r₂ c v) 2 (jointLaw p r₁ r₂ c v)) :
    (∫ q, twoFluxScore p a b z w r₁ r₂ c v q ^ 2 ∂jointLaw p r₁ r₂ c v) =
      ∫ m, (fderiv ℝ a m z + fderiv ℝ b m w)^2 / p m +
        ((r₁ (a m • z + b m • w))^2 + (r₂ (a m • z + b m • w))^2) /
          p m / (v : ℝ) := by
  have hs : MemLp (twoFluxScore p a b z w r₁ r₂ c v) 2 (jointLaw p r₁ r₂ c v) := hsa.add hsb
  have hi := (jointLaw_integrable_iff p hp hp0 r₁ r₂ c hv _).mp hs.integrable_sq
  rw [jointLaw_integral p hp hp0 r₁ r₂ c hv]
  change (∫ q : Plane × Plane, p q.1 * likelihood r₁ r₂ c v q.1 q.2 *
    twoFluxScore p a b z w r₁ r₂ c v q ^ 2 ∂volume.prod volume) = _
  rw [integral_prod _ hi]
  simp_rw [twoFlux_information_conditional p a b z w r₁ r₂ c hv]

/-- The moment prior described by a nonnegative Lebesgue density. -/
def priorLaw (p : Plane → ℝ) : Measure Plane :=
  volume.withDensity (fun m => ENNReal.ofReal (p m))

/-- Every almost-sure moment-prior property holds for the moment coordinate
under the actual joint observation law, at every noise power. -/
theorem jointLaw_ae_of_priorLaw (p : Plane → ℝ) (hp : Measurable p)
    (hp0 : ∀ m, 0 ≤ p m) (r₁ r₂ : Plane →L[ℝ] ℝ) (c : Plane) (v : ℝ≥0)
    {P : Plane → Prop} (hP : ∀ᵐ m ∂priorLaw p, P m) :
    ∀ᵐ q ∂jointLaw p r₁ r₂ c v, P q.1 := by
  have hbase := (ae_withDensity_iff hp.ennreal_ofReal).mp hP
  have hlift : ∀ᵐ q : Plane × Plane ∂volume.prod volume,
      ENNReal.ofReal (p q.1) ≠ 0 → P q.1 :=
    Measure.quasiMeasurePreserving_fst.ae hbase
  have hm : Measurable (fun q : Plane × Plane => ENNReal.ofReal (p q.1 * likelihood r₁ r₂ c v q.1 q.2)) :=
    ((hp.comp measurable_fst).mul (likelihood_joint_continuous r₁ r₂ c v).measurable).ennreal_ofReal
  apply (ae_withDensity_iff hm).mpr
  filter_upwards [hlift] with q hq hnonzero
  apply hq
  intro hz
  rw [ENNReal.ofReal_mul (hp0 q.1), hz, zero_mul] at hnonzero
  exact hnonzero rfl

/-- Prior expectation is an actual Lebesgue integral weighted by p. -/
theorem priorLaw_integral (p : Plane → ℝ) (hp : Measurable p)
    (hp0 : ∀ m, 0 ≤ p m) (g : Plane → ℝ) :
    (∫ m, g m ∂priorLaw p) = ∫ m, p m * g m := by
  unfold priorLaw
  rw [integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hp0 _), smul_eq_mul]

/-- The density assumptions supply a probability prior. -/
theorem priorLaw_isProbability (p : Plane → ℝ) (hp0 : ∀ m, 0 ≤ p m)
    (hpi : Integrable p) (hpn : (∫ m, p m) = 1) : IsProbabilityMeasure (priorLaw p) := by
  constructor
  rw [priorLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hpi (Filter.Eventually.of_forall hp0), hpn]
  norm_num

end Analog.GaussianScoreIdentity
