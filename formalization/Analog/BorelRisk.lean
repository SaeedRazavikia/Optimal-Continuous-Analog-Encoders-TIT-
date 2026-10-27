import Analog.Decoder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Tactic.Linarith

/-!
# Borel estimators, clipping, and genuine nonnegative risks

Unbounded estimators may have infinite squared risk. We use the nonnegative
Lebesgue integral for that risk, so a nonintegrable real Bochner integral is
never mistaken for zero risk. Clipping to the bounded target interval produces
an L² error and transfers any finite clipped-risk lower bound to every Borel
estimator. These results do not assume unbiasedness or exact decoding.
-/

noncomputable section
namespace Analog.BorelRisk
open MeasureTheory Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def squareRisk (μ : Measure Ω) (target estimate : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((estimate ω - target ω)^2) ∂μ

theorem clip_mem_interval {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    a ≤ Decoder.clip a b x ∧ Decoder.clip a b x ≤ b := by
  constructor
  · exact le_max_left _ _
  · exact max_le hab (min_le_left _ _)

theorem interval_error_bound {a b x t : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (ht : a ≤ t ∧ t ≤ b) : |x - t| ≤ b - a := by
  rw [abs_le]
  constructor <;> linarith

/-- Bounded Borel estimates and bounded targets have square-integrable error
under every finite measure, hence under the actual Gaussian joint law. -/
theorem bounded_error_memLp [IsFiniteMeasure μ] {target estimate : Ω → ℝ}
    (ht : Measurable target) (he : Measurable estimate) {a b : ℝ}
    (htarget : ∀ᵐ ω ∂μ, a ≤ target ω ∧ target ω ≤ b)
    (hestimate : ∀ᵐ ω ∂μ, a ≤ estimate ω ∧ estimate ω ≤ b) :
    MemLp (fun ω => estimate ω - target ω) 2 μ := by
  apply MemLp.of_bound (he.sub ht).aestronglyMeasurable (b-a)
  filter_upwards [htarget, hestimate] with ω htω heω
  exact interval_error_bound heω htω

/-- Clipped error is in L² even when the original Borel estimator has
infinite squared risk. -/
theorem clipped_error_memLp [IsFiniteMeasure μ] {target estimate : Ω → ℝ}
    (ht : Measurable target) (he : Measurable estimate) {a b : ℝ}
    (hab : a ≤ b) (htarget : ∀ᵐ ω ∂μ, a ≤ target ω ∧ target ω ≤ b) :
    MemLp (fun ω => Decoder.clip a b (estimate ω) - target ω) 2 μ := by
  apply bounded_error_memLp ht
    ((Decoder.clip_lipschitz a b).continuous.measurable.comp he) htarget
  exact Eventually.of_forall fun ω => clip_mem_interval hab (estimate ω)

theorem clipped_error_square_integrable [IsFiniteMeasure μ]
    {target estimate : Ω → ℝ} (ht : Measurable target) (he : Measurable estimate)
    {a b : ℝ} (hab : a ≤ b)
    (htarget : ∀ᵐ ω ∂μ, a ≤ target ω ∧ target ω ≤ b) :
    Integrable (fun ω => (Decoder.clip a b (estimate ω) - target ω)^2) μ := by
  exact (memLp_two_iff_integrable_sq
    (((Decoder.clip_lipschitz a b).continuous.measurable.comp he).sub ht).aestronglyMeasurable).mp
      (clipped_error_memLp ht he hab htarget)

/-- Clipping decreases the true nonnegative risk; no integrability of the
unclipped error is needed. -/
theorem clipped_squareRisk_le {target estimate : Ω → ℝ} {a b : ℝ}
    (htarget : ∀ᵐ ω ∂μ, a ≤ target ω ∧ target ω ≤ b) :
    squareRisk μ target (fun ω => Decoder.clip a b (estimate ω)) ≤
      squareRisk μ target estimate := by
  apply lintegral_mono_ae
  filter_upwards [htarget] with ω hω
  apply ENNReal.ofReal_le_ofReal
  have hdist := Decoder.clip_error hω.1 hω.2 (estimate ω)
  rw [Real.dist_eq, Real.dist_eq] at hdist
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hdist

/-- For finite squared risk, the nonnegative and real integral definitions agree. -/
theorem squareRisk_eq_ofReal_integral {target estimate : Ω → ℝ}
    (hi : Integrable (fun ω => (estimate ω - target ω)^2) μ) :
    squareRisk μ target estimate = ENNReal.ofReal (∫ ω, (estimate ω-target ω)^2 ∂μ) := by
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun ω => sq_nonneg (estimate ω-target ω))).symm

/-- A lower bound proved for the clipped L² estimator applies to the original
arbitrary Borel estimator, including when its risk is infinite. -/
theorem lower_bound_of_clipped_risk [IsFiniteMeasure μ]
    {target estimate : Ω → ℝ} (ht : Measurable target) (he : Measurable estimate)
    {a b bound : ℝ} (hab : a ≤ b)
    (htarget : ∀ᵐ ω ∂μ, a ≤ target ω ∧ target ω ≤ b)
    (hlower : bound ≤ ∫ ω, (Decoder.clip a b (estimate ω)-target ω)^2 ∂μ) :
    ENNReal.ofReal bound ≤ squareRisk μ target estimate := by
  calc
    ENNReal.ofReal bound ≤
        ENNReal.ofReal (∫ ω, (Decoder.clip a b (estimate ω)-target ω)^2 ∂μ) :=
      ENNReal.ofReal_le_ofReal hlower
    _ = squareRisk μ target (fun ω => Decoder.clip a b (estimate ω)) :=
      (squareRisk_eq_ofReal_integral (clipped_error_square_integrable ht he hab htarget)).symm
    _ ≤ squareRisk μ target estimate := clipped_squareRisk_le htarget

/-- All measurable decoders; no boundedness, exactness, or unbiasedness premise. -/
abbrev BorelDecoder (Y : Type*) [MeasurableSpace Y] := {D : Y → ℝ // Measurable D}

def clipDecoder {Y : Type*} [MeasurableSpace Y] (a b : ℝ) (D : BorelDecoder Y) :
    BorelDecoder Y :=
  ⟨fun y => Decoder.clip a b (D.1 y),
    (Decoder.clip_lipschitz a b).continuous.measurable.comp D.2⟩

def bayesRisk {Y : Type*} [MeasurableSpace Y] (μ : Measure Ω)
    (target : Ω → ℝ) (observation : Ω → Y) (D : BorelDecoder Y) : ℝ≥0∞ :=
  squareRisk μ target (D.1 ∘ observation)

/-- The all-Borel-decoder infimum equals the infimum over their bounded clips.
The risk is the actual nonnegative integral, so infinite-risk decoders are
included correctly. No limit interchange is involved. -/
theorem iInf_bayesRisk_eq_clipped {Y : Type*} [MeasurableSpace Y]
    (target : Ω → ℝ) (observation : Ω → Y) {a b : ℝ}
    (htarget : ∀ᵐ ω ∂μ, a ≤ target ω ∧ target ω ≤ b) :
    (⨅ D : BorelDecoder Y, bayesRisk μ target observation D) =
      ⨅ D : BorelDecoder Y, bayesRisk μ target observation (clipDecoder a b D) := by
  apply le_antisymm
  · apply le_iInf
    intro D
    exact iInf_le _ (clipDecoder a b D)
  · apply le_iInf
    intro D
    apply (iInf_le _ D).trans
    exact clipped_squareRisk_le htarget

/-- The unrestricted nonnegative-risk infimum equals the real infimum of
finite clipped risks, embedded in the extended nonnegative reals. -/
theorem iInf_bayesRisk_eq_ofReal_clipped [IsFiniteMeasure μ]
    {Y : Type*} [MeasurableSpace Y] (target : Ω → ℝ) (observation : Ω → Y)
    (ht : Measurable target) (hy : Measurable observation) {a b : ℝ}
    (hab : a ≤ b) (htarget : ∀ᵐ ω ∂μ, a ≤ target ω ∧ target ω ≤ b) :
    (⨅ D : BorelDecoder Y, bayesRisk μ target observation D) =
      ENNReal.ofReal (⨅ D : BorelDecoder Y,
        ∫ ω, (Decoder.clip a b (D.1 (observation ω))-target ω)^2 ∂μ) := by
  letI : Nonempty (BorelDecoder Y) := ⟨⟨fun _ => 0, measurable_const⟩⟩
  rw [iInf_bayesRisk_eq_clipped target observation htarget, ENNReal.ofReal_iInf]
  apply iInf_congr
  intro D
  exact squareRisk_eq_ofReal_integral
    (clipped_error_square_integrable ht (D.2.comp hy) hab htarget)

/-- In particular, an arbitrary-decoder optimal risk is finite; converting it
to a real number is legitimate and gives the same clipped real infimum. -/
theorem iInf_bayesRisk_toReal [IsFiniteMeasure μ]
    {Y : Type*} [MeasurableSpace Y] (target : Ω → ℝ) (observation : Ω → Y)
    (ht : Measurable target) (hy : Measurable observation) {a b : ℝ}
    (hab : a ≤ b) (htarget : ∀ᵐ ω ∂μ, a ≤ target ω ∧ target ω ≤ b) :
    (⨅ D : BorelDecoder Y, bayesRisk μ target observation D) ≠ ⊤ ∧
      (⨅ D : BorelDecoder Y, bayesRisk μ target observation D).toReal =
        ⨅ D : BorelDecoder Y,
          ∫ ω, (Decoder.clip a b (D.1 (observation ω))-target ω)^2 ∂μ := by
  letI : Nonempty (BorelDecoder Y) := ⟨⟨fun _ => 0, measurable_const⟩⟩
  rw [iInf_bayesRisk_eq_ofReal_clipped target observation ht hy hab htarget]
  refine ⟨ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal ?_⟩
  apply le_ciInf
  intro D
  exact integral_nonneg (fun ω => sq_nonneg _)

end Analog.BorelRisk
