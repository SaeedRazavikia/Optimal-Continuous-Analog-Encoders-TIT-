import Analog.Decoder
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Abel

/-!
# Additive disturbance and implementation errors

These results apply to every finite set of terminals in a normed ring,
including the complex channel. The implemented terminal values obey the
stated peak and approximation bounds; residual gains may add coherently.
-/

namespace Analog.Decoder

open scoped NNReal BigOperators

section Additive

variable {X E : Type*} [SeminormedAddCommGroup E]

/-- The observation-distance guarantee is exactly the all-disturbance
guarantee for an additive channel. -/
theorem uniform_iff_additive_noise (r : X → E) (f : X → ℝ) (L : ℝ≥0) (D : E → ℝ) :
    UniformBound r f L D ↔
      ∀ x n, |D (r x + n) - f x| ≤ (L : ℝ) * ‖n‖ := by
  constructor
  · intro h x n
    simpa [Real.dist_eq, dist_eq_norm] using h x (r x + n)
  · intro h x y
    simpa [Real.dist_eq, dist_eq_norm] using h x (y - r x)

/-- Feasibility of a fixed global disturbance constant is equivalent to the
pairwise condition, with an actual decoder constructed by McShane extension. -/
theorem additive_decoder_iff_pairwise (r : X → E) (f : X → ℝ) (L : ℝ≥0) :
    (∃ D : E → ℝ, ∀ x n, |D (r x + n) - f x| ≤ (L : ℝ) * ‖n‖) ↔
      PairwiseBound r f L := by
  simp_rw [← uniform_iff_additive_noise]
  exact uniform_decoder_iff_pairwise r f L

/-- Any deterministic observation perturbation bound transfers to target
error with the same Lipschitz factor. -/
theorem deterministic_error {r : X → E} {f : X → ℝ} {L : ℝ≥0} {D : E → ℝ}
    (h : UniformBound r f L D) (x : X) (y : E) {B : ℝ}
    (hB : ‖y - r x‖ ≤ B) : |D y - f x| ≤ (L : ℝ) * B := by
  have hy : |D y - f x| ≤ (L : ℝ) * ‖y - r x‖ := by
    simpa [Real.dist_eq, dist_eq_norm] using h x y
  exact hy.trans (mul_le_mul_of_nonneg_left hB L.coe_nonneg)

end Additive

section Ring

variable {ι A : Type*} [NormedRing A]

/-- Deterministic perturbation of a finite multiple-access sum. The radius R
stands for the square root of the peak-power constraint in the manuscript. -/
theorem received_implementation_error (s : Finset ι)
    (ideal implemented gain : ι → A) (N : A) (R ε : ℝ)
    (hpeak : ∀ k ∈ s, ‖implemented k‖ ≤ R)
    (happrox : ∀ k ∈ s, ‖implemented k - ideal k‖ ≤ ε * R) :
    ‖(∑ k ∈ s, (1 + gain k) * implemented k) + N - ∑ k ∈ s, ideal k‖ ≤
      ‖N‖ + (s.card : ℝ) * ε * R + R * ∑ k ∈ s, ‖gain k‖ := by
  have hterminal : ∀ k ∈ s,
      ‖(1 + gain k) * implemented k - ideal k‖ ≤ ε * R + ‖gain k‖ * R := by
    intro k hk
    calc
      ‖(1 + gain k) * implemented k - ideal k‖ =
          ‖(implemented k - ideal k) + gain k * implemented k‖ := by
        congr 1
        rw [add_mul, one_mul]
        abel
      _ ≤ ‖implemented k - ideal k‖ + ‖gain k * implemented k‖ := norm_add_le _ _
      _ ≤ ε * R + ‖gain k‖ * R :=
        add_le_add (happrox k hk)
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hpeak k hk) (norm_nonneg _)))
  calc
    ‖(∑ k ∈ s, (1 + gain k) * implemented k) + N - ∑ k ∈ s, ideal k‖ =
        ‖N + ∑ k ∈ s, ((1 + gain k) * implemented k - ideal k)‖ := by
      congr 1
      rw [Finset.sum_sub_distrib]
      abel
    _ ≤ ‖N‖ + ‖∑ k ∈ s, ((1 + gain k) * implemented k - ideal k)‖ := norm_add_le _ _
    _ ≤ ‖N‖ + ∑ k ∈ s, ‖(1 + gain k) * implemented k - ideal k‖ :=
      add_le_add_left (norm_sum_le _ _) _
    _ ≤ ‖N‖ + ∑ k ∈ s, (ε * R + ‖gain k‖ * R) :=
      add_le_add_left (Finset.sum_le_sum hterminal) _
    _ = ‖N‖ + (s.card : ℝ) * ε * R + R * ∑ k ∈ s, ‖gain k‖ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.sum_mul]
      ring

/-- Applying the ideal decoder gives the manuscript's coherent
implementation-and-gain error bound for arbitrary finite terminal sets. -/
theorem decoded_implementation_error {X : Type*}
    (s : Finset ι) (ideal implemented : X → ι → A) (gain : ι → A)
    (f : X → ℝ) (D : A → ℝ) (L : ℝ≥0)
    (hD : UniformBound (fun x => ∑ k ∈ s, ideal x k) f L D)
    (x : X) (N : A) (R ε : ℝ)
    (hpeak : ∀ k ∈ s, ‖implemented x k‖ ≤ R)
    (happrox : ∀ k ∈ s, ‖implemented x k - ideal x k‖ ≤ ε * R) :
    |D ((∑ k ∈ s, (1 + gain k) * implemented x k) + N) - f x| ≤
      (L : ℝ) * (‖N‖ + (s.card : ℝ) * ε * R + R * ∑ k ∈ s, ‖gain k‖) := by
  apply deterministic_error hD x
  exact received_implementation_error s (ideal x) (implemented x) gain N R ε hpeak happrox

/-- A uniform residual-gain bound produces a coherent error proportional to
the number of terminals; the gain term need not average away. -/
theorem received_implementation_error_uniform_gain (s : Finset ι)
    (ideal implemented gain : ι → A) (N : A) (R ε δ : ℝ) (hR : 0 ≤ R)
    (hpeak : ∀ k ∈ s, ‖implemented k‖ ≤ R)
    (happrox : ∀ k ∈ s, ‖implemented k - ideal k‖ ≤ ε * R)
    (hgain : ∀ k ∈ s, ‖gain k‖ ≤ δ) :
    ‖(∑ k ∈ s, (1 + gain k) * implemented k) + N - ∑ k ∈ s, ideal k‖ ≤
      ‖N‖ + (s.card : ℝ) * (ε + δ) * R := by
  have hsum : (∑ k ∈ s, ‖gain k‖) ≤ (s.card : ℝ) * δ := by
    simpa using Finset.sum_le_sum hgain
  calc
    _ ≤ ‖N‖ + (s.card : ℝ) * ε * R + R * ∑ k ∈ s, ‖gain k‖ :=
      received_implementation_error s ideal implemented gain N R ε hpeak happrox
    _ ≤ ‖N‖ + (s.card : ℝ) * ε * R + R * ((s.card : ℝ) * δ) :=
      add_le_add_left (mul_le_mul_of_nonneg_left hsum hR) _
    _ = ‖N‖ + (s.card : ℝ) * (ε + δ) * R := by ring

end Ring

section Quantization

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Contracting before quantization preserves the peak constraint and gives
at most twice the quantizer radius as encoder error. The local quantizer
hypothesis is required only at the actual contracted encoder value. -/
theorem peak_safe_quantization (e : E) (Q : E → E) (R ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hpeak : ‖e‖ ≤ R)
    (hQ : ‖Q ((1 - ρ) • e) - (1 - ρ) • e‖ ≤ ρ * R) :
    ‖Q ((1 - ρ) • e)‖ ≤ R ∧
      ‖Q ((1 - ρ) • e) - e‖ ≤ 2 * ρ * R := by
  have hc : ‖(1 - ρ) • e‖ ≤ (1 - ρ) * R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hρ1)]
    exact mul_le_mul_of_nonneg_left hpeak (sub_nonneg.mpr hρ1)
  have he : ‖(1 - ρ) • e - e‖ ≤ ρ * R := by
    have heq : (1 - ρ) • e - e = (-ρ) • e := by
      simp only [sub_smul, one_smul, neg_smul]
      abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hρ]
    exact mul_le_mul_of_nonneg_left hpeak hρ
  constructor
  · have htriangle := norm_add_le (Q ((1 - ρ) • e) - (1 - ρ) • e) ((1 - ρ) • e)
    simp only [sub_add_cancel] at htriangle
    have hsum := htriangle.trans (add_le_add hQ hc)
    nlinarith
  · have htriangle : ‖Q ((1 - ρ) • e) - e‖ ≤
        ‖Q ((1 - ρ) • e) - (1 - ρ) • e‖ + ‖(1 - ρ) • e - e‖ := by
      simpa only [dist_eq_norm] using
        dist_triangle (Q ((1 - ρ) • e)) ((1 - ρ) • e) e
    have hsum := htriangle.trans (add_le_add hQ he)
    nlinarith

end Quantization

end Analog.Decoder
