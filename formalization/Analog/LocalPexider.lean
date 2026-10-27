import Analog.GeneralRigidity
import Analog.Decoder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Continuous Pexider equations on rectangles

A continuous function of a sum which separates into a function of each
argument is affine on the rectangle, with a shared slope. Interval averaging
and the fundamental theorem of calculus supply the missing differentiability;
no differentiability of the separated functions is assumed.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Filter Topology MeasureTheory
namespace Analog.LocalPexider

private theorem first_derivative {a b c d : ℝ} (hcd : c < d)
    (L H Q : ℝ → ℝ) (hL : Continuous L)
    (hQ : ContinuousOn Q (Icc c d))
    (heq : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, L (x + y) = H x + Q y)
    {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt H ((Q d - Q c) / (d - c)) x := by
  let F : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, L t
  let R : ℝ → ℝ := fun z =>
    ((F (z + d) - F (z + c)) - ∫ t in c..d, Q t) / (d - c)
  have hF : ∀ z, HasDerivAt F (L z) z := fun z =>
    intervalIntegral.integral_hasDerivAt_right (hL.intervalIntegrable 0 z)
      hL.aestronglyMeasurable.stronglyMeasurableAtFilter hL.continuousAt
  have hR : HasDerivAt R ((L (x + d) - L (x + c)) / (d - c)) x := by
    convert (((hF (x + d)).comp x ((hasDerivAt_id x).add_const d)).sub
      ((hF (x + c)).comp x ((hasDerivAt_id x).add_const c))).sub_const
        (∫ t in c..d, Q t) |>.div_const (d - c) using 1
    simp
  have hrepresentation : ∀ z ∈ Icc a b, H z = R z := by
    intro z hz
    have hi : (∫ t in c..d, L (z + t)) = (d - c) * H z + ∫ t in c..d, Q t := by
      calc
        (∫ t in c..d, L (z + t)) = ∫ t in c..d, H z + Q t :=
          intervalIntegral.integral_congr (by
            intro t ht
            exact heq z hz t (by simpa [uIcc_of_le hcd.le] using ht))
        _ = (d - c) * H z + ∫ t in c..d, Q t := by
          rw [intervalIntegral.integral_add intervalIntegrable_const
            (hQ.intervalIntegrable_of_Icc hcd.le), intervalIntegral.integral_const]
          simp only [smul_eq_mul]
    have ht : F (z + d) - F (z + c) = ∫ t in c..d, L (z + t) := by
      dsimp [F]
      rw [intervalIntegral.integral_interval_sub_left
        (hL.intervalIntegrable 0 (z + d)) (hL.intervalIntegrable 0 (z + c))]
      exact (intervalIntegral.integral_comp_add_left (a := c) (b := d) L z).symm
    dsimp [R]
    rw [ht, hi]
    field_simp [ne_of_gt (sub_pos.mpr hcd)]
    ring
  have hev : H =ᶠ[𝓝 x] R := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with z hz
    exact hrepresentation z ⟨hz.1.le, hz.2.le⟩
  have hd := hR.congr_of_eventuallyEq hev
  convert hd using 1
  rw [heq x ⟨hx.1.le, hx.2.le⟩ d ⟨hcd.le, le_rfl⟩,
    heq x ⟨hx.1.le, hx.2.le⟩ c ⟨le_rfl, hcd.le⟩]
  ring

/-- The first separated function is affine on the closed interval. -/
theorem first_affine {a b c d : ℝ} (hcd : c < d)
    (L H Q : ℝ → ℝ) (hL : Continuous L)
    (hH : ContinuousOn H (Icc a b)) (hQ : ContinuousOn Q (Icc c d))
    (heq : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, L (x + y) = H x + Q y) :
    ∃ h₀ : ℝ, ∀ x ∈ Icc a b, H x = h₀ + ((Q d - Q c) / (d - c)) * x := by
  let lam := (Q d - Q c) / (d - c)
  let f : ℝ → ℝ := fun x => H x - lam * x
  have hfc : ContinuousOn f (Icc a b) := hH.sub (continuousOn_const.mul continuousOn_id)
  have hfd : ∀ x ∈ Ioo a b, HasDerivAt f 0 x := by
    intro x hx
    convert (first_derivative hcd L H Q hL hQ heq hx).sub
      ((hasDerivAt_id x).const_mul lam) using 1
    simp [lam]
  refine ⟨f a, ?_⟩
  intro x hx
  have hconst := Analog.DifferentialRigidity.constant_on_closed_interval hfc hfd x hx
  dsimp [f, lam] at hconst ⊢
  linarith

/-- A continuous Pexider identity on a nondegenerate closed rectangle has
one common affine slope in both variables, including all endpoints. -/
theorem rectangle_affine {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (L H Q : ℝ → ℝ) (hL : Continuous L)
    (hH : ContinuousOn H (Icc a b)) (hQ : ContinuousOn Q (Icc c d))
    (heq : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, L (x + y) = H x + Q y) :
    ∃ lam h₀ q₀ : ℝ,
      (∀ x ∈ Icc a b, H x = h₀ + lam * x) ∧
      (∀ y ∈ Icc c d, Q y = q₀ + lam * y) := by
  obtain ⟨h₀, hh⟩ := first_affine hcd L H Q hL hH hQ heq
  have heq' : ∀ y ∈ Icc c d, ∀ x ∈ Icc a b, L (y + x) = Q y + H x := by
    intro y hy x hx
    simpa [add_comm] using heq x hx y hy
  obtain ⟨q₀, hq⟩ := first_affine hab L Q H hL hQ hH heq'
  have hlam : (H b - H a) / (b - a) = (Q d - Q c) / (d - c) := by
    rw [hh b ⟨hab.le, le_rfl⟩, hh a ⟨le_rfl, hab.le⟩]
    field_simp [ne_of_gt (sub_pos.mpr hcd), ne_of_gt (sub_pos.mpr hab)]
    ring
  exact ⟨(Q d - Q c) / (d - c), h₀, q₀, hh, by simpa only [hlam] using hq⟩

/-- The rectangle theorem only requires continuity on the relevant interval
of sums; clamping gives a continuous global extension without strengthening
the mathematical assumptions. -/
theorem rectangle_affine_of_continuousOn {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (L H Q : ℝ → ℝ)
    (hL : ContinuousOn L (Icc (a + c) (b + d)))
    (hH : ContinuousOn H (Icc a b)) (hQ : ContinuousOn Q (Icc c d))
    (heq : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, L (x + y) = H x + Q y) :
    ∃ lam h₀ q₀ : ℝ,
      (∀ x ∈ Icc a b, H x = h₀ + lam * x) ∧
      (∀ y ∈ Icc c d, Q y = q₀ + lam * y) := by
  let L' : ℝ → ℝ := fun x => L (Analog.Decoder.clip (a + c) (b + d) x)
  have hL' : Continuous L' := by
    apply hL.comp_continuous (Analog.Decoder.clip_lipschitz (a + c) (b + d)).continuous
    intro x
    dsimp [Analog.Decoder.clip]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  apply rectangle_affine hab hcd L' H Q hL' hH hQ
  intro x hx y hy
  dsimp [L']
  rw [Analog.Decoder.clip_fixed (by linarith [hx.1, hy.1]) (by linarith [hx.2, hy.2])]
  exact heq x hx y hy

end Analog.LocalPexider
