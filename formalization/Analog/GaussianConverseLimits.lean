import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sequential deductions from information inequalities

This module proves the limit steps used after a statistical information bound
has been established. It does not assume differentiability of estimators and
does not interchange an optimization and a limit. The information inequalities
and variational test completeness remain explicit hypotheses here; their
Gaussian density-level derivation is a separate obligation.
-/

noncomputable section
namespace Analog.GaussianConverseLimits

open Filter Set
open scoped Topology

/-- A lower-liminf statement without the boundedness conventions of real liminf. -/
def LowerAsymptotic (risk : ℕ → ℝ) (coefficient : ℝ) : Prop :=
  ∀ a < coefficient, ∀ᶠ n in atTop, a ≤ risk n

/-- A convergent information ratio gives an eventual lower bound. -/
theorem lowerAsymptotic_of_ratio {risk denominator : ℕ → ℝ}
    {numerator limit : ℝ} (hlimit : 0 < limit)
    (hden : Tendsto denominator atTop (𝓝 limit))
    (hbound : ∀ n, numerator / denominator n ≤ risk n) :
    LowerAsymptotic risk (numerator / limit) := by
  intro a ha
  have hratio : Tendsto (fun n => numerator / denominator n) atTop
      (𝓝 (numerator / limit)) := tendsto_const_nhds.div hden (ne_of_gt hlimit)
  filter_upwards [hratio.eventually_const_le ha] with n hn
  exact hn.trans (hbound n)

/-- A positive numerator and a positive denominator tending to zero force
risk divergence. This is the scalar singular-Gram exclusion step. -/
theorem risk_tendsto_atTop_of_denominator_zero {risk denominator : ℕ → ℝ}
    {numerator : ℝ} (hnum : 0 < numerator)
    (hden : Tendsto denominator atTop (𝓝 (0 : ℝ)))
    (hpos : ∀ n, 0 < denominator n)
    (hbound : ∀ n, numerator / denominator n ≤ risk n) :
    Tendsto risk atTop atTop := by
  have hright : Tendsto denominator atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hden, Eventually.of_forall hpos⟩
  have hinv := tendsto_inv_nhdsGT_zero.comp hright
  have hratio : Tendsto (fun n => numerator / denominator n) atTop atTop := by
    simpa only [div_eq_mul_inv] using hinv.const_mul_atTop hnum
  exact tendsto_atTop_mono hbound hratio

/-- The actual denominator in the normalized weighted van Trees bound. -/
def informationDenominator (K : ℝ) (B N : ℕ → ℝ) (C : ℝ) (n : ℕ) : ℝ :=
  2 * K ^ 2 * B n + N n * C

theorem informationDenominator_tendsto (K C : ℝ) {B N : ℕ → ℝ} {B₀ : ℝ}
    (hB : Tendsto B atTop (𝓝 B₀)) (hN : Tendsto N atTop (𝓝 (0 : ℝ))) :
    Tendsto (informationDenominator K B N C) atTop (𝓝 (2 * K ^ 2 * B₀)) := by
  simpa only [informationDenominator, zero_mul, add_zero] using
    (hB.const_mul (2 * K ^ 2)).add (hN.mul_const C)

/-- Nonsingular sequential lower bound for one fixed test vector field. -/
theorem nonsingular_test_lower_bound (K A C : ℝ) {risk B N : ℕ → ℝ}
    {B₀ : ℝ} (hK : 0 < K) (hB₀ : 0 < B₀)
    (hB : Tendsto B atTop (𝓝 B₀)) (hN : Tendsto N atTop (𝓝 (0 : ℝ)))
    (hinfo : ∀ n, A ^ 2 / informationDenominator K B N C n ≤ risk n) :
    LowerAsymptotic risk (A ^ 2 / (2 * K ^ 2 * B₀)) := by
  apply lowerAsymptotic_of_ratio (by positivity)
    (informationDenominator_tendsto K C hB hN) hinfo

/-- Singular sequential exclusion with positive finite-n test energy.
The nonzero information numerator is what rules out bounded normalized risk. -/
theorem singular_test_risk_diverges (K A C : ℝ) {risk B N : ℕ → ℝ}
    (hK : 0 < K) (hA : A ≠ 0) (hC : 0 ≤ C)
    (hBpos : ∀ n, 0 < B n) (hNpos : ∀ n, 0 ≤ N n)
    (hB : Tendsto B atTop (𝓝 (0 : ℝ)))
    (hN : Tendsto N atTop (𝓝 (0 : ℝ)))
    (hinfo : ∀ n, A ^ 2 / informationDenominator K B N C n ≤ risk n) :
    Tendsto risk atTop atTop := by
  apply risk_tendsto_atTop_of_denominator_zero (sq_pos_of_ne_zero hA)
  · simpa using informationDenominator_tendsto K C hB hN
  · intro n
    dsimp [informationDenominator]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hK)) (hBpos n))
      (mul_nonneg (hNpos n) hC)
  · exact hinfo

/-- Approaching the variational supremum by fixed tests is enough; the tests
need not depend on noise power and the decoder sequence is arbitrary. -/
theorem lowerAsymptotic_of_tests {ι : Type*} {risk : ℕ → ℝ}
    (value : ι → ℝ) (target : ℝ)
    (htests : ∀ i, LowerAsymptotic risk (value i))
    (hcomplete : ∀ a < target, ∃ i, a < value i) :
    LowerAsymptotic risk target := by
  intro a ha
  obtain ⟨i, hi⟩ := hcomplete a ha
  exact htests i a hi

/-- A matching achievable upper sequence identifies the full limit. -/
theorem tendsto_of_lowerAsymptotic_upper {risk upper : ℕ → ℝ} {target : ℝ}
    (hlower : LowerAsymptotic risk target)
    (hupper : ∀ n, risk n ≤ upper n)
    (hlim : Tendsto upper atTop (𝓝 target)) :
    Tendsto risk atTop (𝓝 target) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have ham : a < (a + target) / 2 := by linarith
    have hmt : (a + target) / 2 < target := by linarith
    filter_upwards [hlower _ hmt] with n hn
    exact ham.trans_le hn
  · intro b hb
    filter_upwards [hlim.eventually_lt_const hb] with n hn
    exact (hupper n).trans_lt hn

/-- Optimization over arbitrary decoders as the actual infimum of their risks. -/
def optimalRisk {ι : Type*} (risk : ℕ → ι → ℝ) (n : ℕ) : ℝ :=
  sInf (Set.range (risk n))

/-- A bound uniform over all decoders passes to their actual infimum. -/
theorem le_optimalRisk {ι : Type*} [Nonempty ι] (risk : ℕ → ι → ℝ)
    (lower : ℕ → ℝ) (hbound : ∀ n i, lower n ≤ risk n i) :
    ∀ n, lower n ≤ optimalRisk risk n := by
  intro n
  apply le_csInf (Set.range_nonempty _)
  rintro r ⟨i, rfl⟩
  exact hbound n i

/-- Nonnegativity prevents real-infimum pathologies in statistical risk. -/
theorem optimalRisk_le {ι : Type*} (risk : ℕ → ι → ℝ)
    (hnonneg : ∀ n i, 0 ≤ risk n i) (i : ι) :
    ∀ n, optimalRisk risk n ≤ risk n i := by
  intro n
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨j, rfl⟩
    exact hnonneg n j
  · exact Set.mem_range_self i

/-- A decoder-uniform information bound gives the optimized lower limit. -/
theorem optimalRisk_lowerAsymptotic_of_ratio {ι : Type*} [Nonempty ι]
    (risk : ℕ → ι → ℝ) {denominator : ℕ → ℝ} {numerator limit : ℝ}
    (hlimit : 0 < limit) (hden : Tendsto denominator atTop (𝓝 limit))
    (hinfo : ∀ n i, numerator / denominator n ≤ risk n i) :
    LowerAsymptotic (optimalRisk risk) (numerator / limit) :=
  lowerAsymptotic_of_ratio hlimit hden
    (le_optimalRisk risk (fun n => numerator / denominator n) hinfo)

/-- Combining a uniform converse with one fixed achieving decoder proves
optimal-risk convergence, without exchanging an infimum and a limit. -/
theorem optimalRisk_tendsto {ι : Type*} (risk : ℕ → ι → ℝ)
    (hnonneg : ∀ n i, 0 ≤ risk n i) (i₀ : ι) {target : ℝ}
    (hlower : LowerAsymptotic (optimalRisk risk) target)
    (hachieves : Tendsto (fun n => risk n i₀) atTop (𝓝 target)) :
    Tendsto (optimalRisk risk) atTop (𝓝 target) :=
  tendsto_of_lowerAsymptotic_upper hlower (optimalRisk_le risk hnonneg i₀) hachieves

/-- Normalizing each risk by positive noise power commutes with the actual
decoder infimum. This is an algebraic scaling identity, not a limit exchange. -/
theorem optimalRisk_div {ι : Type*} [Nonempty ι] (risk : ℕ → ι → ℝ)
    (hnonneg : ∀ n i, 0 ≤ risk n i) (N : ℕ → ℝ) (hN : ∀ n, 0 < N n) :
    ∀ n, optimalRisk (fun n i => risk n i / N n) n = optimalRisk risk n / N n := by
  intro n
  have hnorm : ∀ n i, 0 ≤ risk n i / N n :=
    fun n i => div_nonneg (hnonneg n i) (hN n).le
  apply le_antisymm
  · apply (le_div_iff₀ (hN n)).mpr
    apply le_csInf (Set.range_nonempty _)
    rintro r ⟨i, rfl⟩
    exact (le_div_iff₀ (hN n)).mp
      (optimalRisk_le (fun n i => risk n i / N n) hnorm i n)
  · apply le_csInf (Set.range_nonempty _)
    rintro r ⟨i, rfl⟩
    exact div_le_div_of_nonneg_right (optimalRisk_le risk hnonneg i n) (hN n).le

end Analog.GaussianConverseLimits
