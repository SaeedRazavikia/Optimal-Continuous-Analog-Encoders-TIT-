import Analog.GaussianWorstCase
import Analog.GaussianMovingGram
import Analog.LocalBallPrior

/-!
# Localized Gaussian minimax converses

Actual normalized uniform-ball priors convert the all-Borel Bayes converse to
an interior pointwise worst-case converse. Continuity extends it to the closure
of the interior. This proves the changing-Gram minimax lower bound and excludes
singular limits detected by an interior directional derivative.
-/

noncomputable section
namespace Analog.GaussianMinimaxConverse
open MeasureTheory Set Filter GaussianScoreIdentity GaussianWorstCase GaussianBayesConverse
open scoped Topology NNReal ENNReal

abbrev Plane := ℝ × ℝ

def localCoefficient (f : Plane → ℝ) (S : ℂ ≃L[ℝ] ℂ) (m : Plane) : ℝ :=
  ‖S.symm.toContinuousLinearMap.adjoint (gradient f m)‖ ^ 2 / 2

def maxCoefficient (M : Set Plane) (f : Plane → ℝ) (S : ℂ ≃L[ℝ] ℂ) : ℝ :=
  sSup (localCoefficient f S '' M)

theorem localCoefficient_continuous (f : Plane → ℝ) (hf : ContDiff ℝ 1 f)
    (S : ℂ ≃L[ℝ] ℂ) : Continuous (localCoefficient f S) :=
  ((S.symm.toContinuousLinearMap.adjoint.continuous.comp (gradient_continuous hf)).norm.pow 2).div_const 2

/-- The worst-case coefficient is an attained maximum on every nonempty compact
moment domain. -/
theorem maxCoefficient_attained {M : Set Plane} (hM : IsCompact M) (hne : M.Nonempty)
    (f : Plane → ℝ) (hf : ContDiff ℝ 1 f) (S : ℂ ≃L[ℝ] ℂ) :
    ∃ m ∈ M, maxCoefficient M f S = localCoefficient f S m ∧
      ∀ x ∈ M, localCoefficient f S x ≤ localCoefficient f S m := by
  obtain ⟨m, hm, hmax⟩ := hM.exists_isMaxOn hne (localCoefficient_continuous f hf S).continuousOn
  refine ⟨m, hm, ?_, hmax⟩
  have hg : IsGreatest (localCoefficient f S '' M) (localCoefficient f S m) :=
    ⟨mem_image_of_mem _ hm, by rintro _ ⟨x, hx, rfl⟩; exact hmax hx⟩
  exact hg.csSup_eq

/-- Every interior moment point gives a sharp sequential lower bound. The
local prior used to derive it is constructed, normalized, and proved regular. -/
theorem moving_minimax_converse_at_interior
    (M : Set Plane) (f : Plane → ℝ) (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hC : 0 ≤ C) (hgrad : ∀ m, ‖gradient f m‖ ≤ C)
    (S : ℕ → ℂ ≃L[ℝ] ℂ) (S₀ : ℂ ≃L[ℝ] ℂ)
    (hA : Tendsto (fun n => GaussianGramCoefficient.gramA (S n)) atTop (𝓝 (GaussianGramCoefficient.gramA S₀)))
    (hB : Tendsto (fun n => GaussianGramCoefficient.gramB (S n)) atTop (𝓝 (GaussianGramCoefficient.gramB S₀)))
    (hcross : Tendsto (fun n => GaussianGramCoefficient.gramC (S n)) atTop (𝓝 (GaussianGramCoefficient.gramC S₀)))
    (c : ℕ → Plane) (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0))
    (lo hi : ℝ) (hlohi : lo ≤ hi) (hbound : ∀ m ∈ M, lo ≤ f m ∧ f m ≤ hi)
    {m : Plane} (hm : m ∈ interior M) :
    GaussianConverseLimits.LowerAsymptotic
      (fun n => minimaxRisk M f (receiverFirst (S n)) (receiverSecond (S n)) (c n) (v n) /
        (2 * (v n : ℝ))) (localCoefficient f S₀ m) := by
  intro a ha
  have hg : Continuous (fun x => ‖S₀.symm.toContinuousLinearMap.adjoint (gradient f x)‖ ^ 2) :=
    (S₀.symm.toContinuousLinearMap.adjoint.continuous.comp (gradient_continuous hf)).norm.pow 2
  have ha' : 2 * a < ‖S₀.symm.toContinuousLinearMap.adjoint (gradient f m)‖ ^ 2 := by
    dsimp [localCoefficient] at ha
    linarith
  obtain ⟨Ω, p, hΩ, hsub, hp, hp0, hpi, hpn, hpC, hpPos, hfull, havg⟩ :=
    LocalBallPrior.exists_regular_prior_above isOpen_interior hm _ hg ha'
  have hM : ∀ᵐ x ∂priorLaw p, x ∈ M := hfull.mono fun _ hx => interior_subset (hsub hx)
  have ht : ∀ᵐ x ∂priorLaw p, lo ≤ f x ∧ f x ≤ hi := hM.mono fun x hx => hbound x hx
  have hlower := GaussianMovingGram.moving_gram_bayes_converse hΩ p hp hp0 hpi hpn hpC hpPos
    hfull f hf hC hgrad S S₀ hA hB hcross c v hv hlim lo hi hlohi ht
  have haavg : a < (∫ x, ‖S₀.symm.toContinuousLinearMap.adjoint (gradient f x)‖ ^ 2 ∂priorLaw p) / 2 := by
    linarith
  filter_upwards [hlower a haavg] with n hn
  exact hn.trans (div_le_div_of_nonneg_right
    (rowOptimalRisk_le_minimaxRisk M p f hp hp0 hpi hpn hf.continuous.measurable hM
      lo hi hlohi hbound _ _ (c n) (hv n)) (by positivity))

/-- Nonsingular changing-Gram worst-case converse on the full attainable
moment domain. The optimized risk includes every Borel decoder. -/
theorem moving_minimax_converse
    (M : Set Plane) (hne : M.Nonempty) (hregular : M ⊆ closure (interior M))
    (f : Plane → ℝ) (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hC : 0 ≤ C) (hgrad : ∀ m, ‖gradient f m‖ ≤ C)
    (S : ℕ → ℂ ≃L[ℝ] ℂ) (S₀ : ℂ ≃L[ℝ] ℂ)
    (hA : Tendsto (fun n => GaussianGramCoefficient.gramA (S n)) atTop (𝓝 (GaussianGramCoefficient.gramA S₀)))
    (hB : Tendsto (fun n => GaussianGramCoefficient.gramB (S n)) atTop (𝓝 (GaussianGramCoefficient.gramB S₀)))
    (hcross : Tendsto (fun n => GaussianGramCoefficient.gramC (S n)) atTop (𝓝 (GaussianGramCoefficient.gramC S₀)))
    (c : ℕ → Plane) (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0))
    (lo hi : ℝ) (hlohi : lo ≤ hi) (hbound : ∀ m ∈ M, lo ≤ f m ∧ f m ≤ hi) :
    GaussianConverseLimits.LowerAsymptotic
      (fun n => minimaxRisk M f (receiverFirst (S n)) (receiverSecond (S n)) (c n) (v n) /
        (2 * (v n : ℝ))) (maxCoefficient M f S₀) := by
  have hinside : ∀ x ∈ interior M, GaussianConverseLimits.LowerAsymptotic
      (fun n => minimaxRisk M f (receiverFirst (S n)) (receiverSecond (S n)) (c n) (v n) /
        (2 * (v n : ℝ))) (localCoefficient f S₀ x) := fun _ hx =>
    moving_minimax_converse_at_interior M f hf hC hgrad S S₀ hA hB hcross
      c v hv hlim lo hi hlohi hbound hx
  intro a ha
  obtain ⟨q, hq, haq⟩ := exists_lt_of_lt_csSup (hne.image (localCoefficient f S₀)) ha
  obtain ⟨m, hm, rfl⟩ := hq
  exact lowerAsymptotic_at_closure (localCoefficient_continuous f hf S₀)
    hinside (hregular hm) a haq

/-- An interior target derivative in a direction lost by the limiting channel
forces actual optimized worst-case risk to diverge after noise normalization.
Both the regular local prior and detecting smooth test are constructed. -/
theorem localized_singular_minimax_diverges
    (M : Set Plane) (f : Plane → ℝ) (hf : ContDiff ℝ 1 f)
    (z : Plane) {x : Plane} (hx : x ∈ interior M) (hdetect : fderiv ℝ f x z ≠ 0)
    (C : ℝ) (hC : 0 ≤ C) (hdir : ∀ m, ‖fderiv ℝ f m z‖ ≤ C)
    (r₁ r₂ : ℕ → Plane →L[ℝ] ℝ) (c : ℕ → Plane)
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hvlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0))
    (lo hi : ℝ) (hlohi : lo ≤ hi) (hbound : ∀ m ∈ M, lo ≤ f m ∧ f m ≤ hi)
    (henergy : ∀ n, 0 < (r₁ n z)^2 + (r₂ n z)^2)
    (hlimit : Tendsto (fun n => (r₁ n z)^2 + (r₂ n z)^2) atTop (𝓝 0)) :
    Tendsto (fun n => minimaxRisk M f (r₁ n) (r₂ n) (c n) (v n) / (2 * (v n : ℝ))) atTop atTop := by
  have hd : Continuous (fun m => fderiv ℝ f m z) :=
    (hf.continuous_fderiv le_rfl).clm_apply continuous_const
  obtain ⟨Ω, p, hΩ, hsub, hp, hp0, hpi, hpn, hpC, hpPos, hfull, hpositive⟩ :=
    LocalBallPrior.exists_regular_prior_above isOpen_interior hx _ (hd.pow 2) (sq_pos_of_ne_zero hdetect)
  have hM : ∀ᵐ m ∂priorLaw p, m ∈ M := hfull.mono fun _ hm => interior_subset (hsub hm)
  have ht : ∀ᵐ m ∂priorLaw p, lo ≤ f m ∧ f m ≤ hi := hM.mono fun m hm => hbound m hm
  have h := GaussianSequentialConverse.singular_direction_sequence_diverges hΩ p hp hp0 hpi hpn
    hpC hpPos hfull f hf z C hC hdir hpositive r₁ r₂ c v hv hvlim lo hi hlohi ht henergy hlimit
  apply tendsto_atTop_mono _ h
  intro n
  exact div_le_div_of_nonneg_right
    (rowOptimalRisk_le_minimaxRisk M p f hp hp0 hpi hpn hf.continuous.measurable hM
      lo hi hlohi hbound _ _ (c n) (hv n)) (by positivity)

/-- The encoded complex gradient is exactly the real derivative in the two
coordinate directions. -/
theorem fderiv_apply_coordinates (f : Plane → ℝ) (m z : Plane) :
    fderiv ℝ f m z = (gradient f m).re * z.1 + (gradient f m).im * z.2 := by
  have hz : z = z.1 • firstDirection + z.2 • secondDirection := by
    ext <;> simp [firstDirection, secondDirection]
  conv_lhs => rw [hz, map_add, map_smul, map_smul]
  simp only [gradient, smul_eq_mul]
  ring

/-- A global gradient bound gives a concrete bound for every fixed directional
derivative, as required by the scalar smooth-test construction. -/
theorem directional_derivative_bound (f : Plane → ℝ) {C : ℝ}
    (hgrad : ∀ m, ‖gradient f m‖ ≤ C) (z m : Plane) :
    ‖fderiv ℝ f m z‖ ≤ C * (|z.1| + |z.2|) := by
  rw [fderiv_apply_coordinates, Real.norm_eq_abs]
  calc
    |(gradient f m).re * z.1 + (gradient f m).im * z.2| ≤
        |(gradient f m).re| * |z.1| + |(gradient f m).im| * |z.2| := by
      simpa only [abs_mul] using abs_add_le ((gradient f m).re * z.1) ((gradient f m).im * z.2)
    _ ≤ C * |z.1| + C * |z.2| := add_le_add
      (mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm _).trans (hgrad m)) (abs_nonneg _))
      (mul_le_mul_of_nonneg_right ((Complex.abs_im_le_norm _).trans (hgrad m)) (abs_nonneg _))
    _ = C * (|z.1| + |z.2|) := by ring

/-- Spanning of interior gradients supplies a detecting interior point for
every nonzero direction. -/
theorem detecting_point_of_gradient_span (M : Set Plane) (f : Plane → ℝ)
    (hspan : ∀ a b : ℝ,
      (∀ m ∈ interior M, (gradient f m).re*a + (gradient f m).im*b = 0) → a=0 ∧ b=0)
    {z : Plane} (hz : z ≠ 0) : ∃ x ∈ interior M, fderiv ℝ f x z ≠ 0 := by
  by_contra! hnone
  have hzero := hspan z.1 z.2 (fun m hm => by
    rw [← fderiv_apply_coordinates]
    exact hnone m hm)
  apply hz
  exact Prod.ext hzero.1 hzero.2

/-- With spanning interior gradients, every nonzero direction whose received
energy tends to zero excludes bounded normalized worst-case risk. This is the
full statistical singular-limit obstruction used by encoder optimization. -/
theorem singular_minimax_diverges_of_spanning
    (M : Set Plane) (f : Plane → ℝ) (hf : ContDiff ℝ 1 f)
    (hspan : ∀ a b : ℝ,
      (∀ m ∈ interior M, (gradient f m).re*a + (gradient f m).im*b = 0) → a=0 ∧ b=0)
    {C : ℝ} (hC : 0 ≤ C) (hgrad : ∀ m, ‖gradient f m‖ ≤ C)
    (z : Plane) (hz : z ≠ 0)
    (r₁ r₂ : ℕ → Plane →L[ℝ] ℝ) (c : ℕ → Plane)
    (v : ℕ → ℝ≥0) (hv : ∀ n, v n ≠ 0)
    (hvlim : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0))
    (lo hi : ℝ) (hlohi : lo ≤ hi) (hbound : ∀ m ∈ M, lo ≤ f m ∧ f m ≤ hi)
    (henergy : ∀ n, 0 < (r₁ n z)^2 + (r₂ n z)^2)
    (hlimit : Tendsto (fun n => (r₁ n z)^2 + (r₂ n z)^2) atTop (𝓝 0)) :
    Tendsto (fun n => minimaxRisk M f (r₁ n) (r₂ n) (c n) (v n) / (2 * (v n : ℝ))) atTop atTop := by
  obtain ⟨x, hx, hdetect⟩ := detecting_point_of_gradient_span M f hspan hz
  exact localized_singular_minimax_diverges M f hf z hx hdetect
    (C*(|z.1|+|z.2|)) (by positivity) (directional_derivative_bound f hgrad z)
    r₁ r₂ c v hv hvlim lo hi hlohi hbound henergy hlimit

end Analog.GaussianMinimaxConverse
