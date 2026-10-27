import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Finite certificate arithmetic for the current secant program

These results formalize the finite weighted-inequality step of the general
primal/dual certificate in `Main.tex`, Appendix "Verified Primal and Dual Bounds".
`finite_secant_upper_bound` exposes, rather than assumes implicitly, the trace
inequality and the common-block identity needed to specialize it to matrices.
The separate matrix lemma proves nonnegativity of the trace of a product of
PSD matrices. The module does not assemble the common-block trace identities,
extract attainable moment pairs, or certify exponential interval enclosures.
-/

open scoped BigOperators MatrixOrder

namespace Analog.FiniteCertificates

/-- The trace of a product of two real positive-semidefinite matrices is
nonnegative even when the product itself is not symmetric. -/
theorem psd_trace_product_nonnegative {n : Type*} [Fintype n]
    (Q H : Matrix n n ℝ) (hQ : Q.PosSemidef) (hH : H.PosSemidef) :
    0 ≤ (Q * H).trace := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  rw [hB, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  exact (hQ.mul_mul_conjTranspose_same B).trace_nonneg

/-- Nonnegative weighting preserves every sampled peak constraint. -/
theorem weighted_peak_bound {ι : Type*} (S : Finset ι)
    (α q : ι → ℝ) (P : ℝ)
    (hα : ∀ i ∈ S, 0 ≤ α i) (hq : ∀ i ∈ S, q i ≤ P) :
    (∑ i ∈ S, α i * q i) ≤ P * ∑ i ∈ S, α i := by
  calc
    (∑ i ∈ S, α i * q i) ≤ ∑ i ∈ S, α i * P := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hq i hi) (hα i hi)
    _ = P * ∑ i ∈ S, α i := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

/-- The finite secant dual bound, after the matrix trace step. The peak index
may encode both the node and its sample index; no identical-node reduction is
assumed. `htrace` is the nonnegative-PSD-pairing step, while `hcommon` expresses
the sum of shared-block pairings as the weighted separation quadratic forms. -/
theorem finite_secant_upper_bound {ι κ : Type*} (S : Finset ι) (R : Finset κ)
    (α q : ι → ℝ) (β a g : κ → ℝ) (P lam traceTotal : ℝ)
    (hlam : 0 ≤ lam)
    (hα : ∀ i ∈ S, 0 ≤ α i)
    (hβ : ∀ r ∈ R, 0 ≤ β r)
    (hpeak : ∀ i ∈ S, q i ≤ P)
    (hsep : ∀ r ∈ R, lam * a r ≤ g r)
    (htrace : traceTotal ≤ ∑ i ∈ S, α i * q i)
    (hcommon : traceTotal = ∑ r ∈ R, β r * g r)
    (hnorm : 1 ≤ ∑ r ∈ R, β r * a r) :
    lam ≤ P * ∑ i ∈ S, α i := by
  have hweighted : lam * (∑ r ∈ R, β r * a r) ≤
      ∑ r ∈ R, β r * g r := by
    calc
      lam * (∑ r ∈ R, β r * a r) = ∑ r ∈ R, β r * (lam * a r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring
      _ ≤ ∑ r ∈ R, β r * g r := by
        apply Finset.sum_le_sum
        intro r hr
        exact mul_le_mul_of_nonneg_left (hsep r hr) (hβ r hr)
  have hnormalized : lam ≤ lam * (∑ r ∈ R, β r * a r) := by
    simpa using mul_le_mul_of_nonneg_left hnorm hlam
  calc
    lam ≤ lam * (∑ r ∈ R, β r * a r) := hnormalized
    _ ≤ ∑ r ∈ R, β r * g r := hweighted
    _ = traceTotal := hcommon.symm
    _ ≤ ∑ i ∈ S, α i * q i := htrace
    _ ≤ P * ∑ i ∈ S, α i := weighted_peak_bound S α q P hα hpeak

/-- Homogeneous scaling preserves every separation constraint, including an
infinite family. This lemma cannot certify constraints omitted by sampling. -/
theorem scale_all_separations {ι : Type*} (a g : ι → ℝ)
    (lam rho : ℝ) (hrho : 0 ≤ rho) (hsep : ∀ i, lam * a i ≤ g i) :
    ∀ i, (rho * lam) * a i ≤ rho * g i := by
  intro i
  calc
    (rho * lam) * a i = rho * (lam * a i) := by ring
    _ ≤ rho * g i := mul_le_mul_of_nonneg_left (hsep i) hrho

/-- A positive continuum peak certificate gives a single scaling factor for
all nodes and all source inputs. -/
theorem scale_all_peaks {ι σ : Type*} (q : ι → σ → ℝ)
    (P B : ℝ) (hP : 0 < P) (hB : 0 < B)
    (hpeak : ∀ k s, q k s ≤ B) :
    ∀ k s, (P / B) * q k s ≤ P := by
  intro k s
  calc
    (P / B) * q k s ≤ (P / B) * B :=
      mul_le_mul_of_nonneg_left (hpeak k s) (div_nonneg hP.le hB.le)
    _ = P := div_mul_cancel₀ P (ne_of_gt hB)

/-- Primal and dual certificates bound absolute suboptimality. -/
theorem absolute_gap_bound (lower optimum upper : ℝ)
    (hlo : lower ≤ optimum) (hup : optimum ≤ upper) :
    0 ≤ optimum - lower ∧ optimum - lower ≤ upper - lower := by
  constructor <;> linarith

/-- The manuscript's relative loss denominator is the upper certificate.
Positivity of the lower certificate makes both relevant divisions valid. -/
theorem relative_loss_bound (lower optimum upper : ℝ)
    (hlower : 0 < lower) (hlo : lower ≤ optimum) (hup : optimum ≤ upper) :
    0 ≤ 1 - lower / optimum ∧
      1 - lower / optimum ≤ (upper - lower) / upper := by
  have hopt : 0 < optimum := hlower.trans_le hlo
  have hupp : 0 < upper := hopt.trans_le hup
  constructor
  · have hh : lower / optimum ≤ 1 := (div_le_one hopt).mpr hlo
    linarith
  · have hh : lower / upper ≤ lower / optimum :=
      div_le_div_of_nonneg_left hlower.le hopt hup
    have heq : (upper - lower) / upper = 1 - lower / upper := by
      field_simp
    rw [heq]
    linarith

end Analog.FiniteCertificates
