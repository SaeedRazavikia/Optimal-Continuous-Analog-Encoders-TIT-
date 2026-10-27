import Analog.FiniteCertificates
import Analog.HeterogeneousAttainment

/-!
# Matrix finite dual certificates for the actual heterogeneous secant SDP

This module derives the trace inequality and shared-block identity from the
actual PSD residual matrices and finite matrix witness equation. These are
conclusions of the proof, not additional scalar certificate hypotheses.
-/

noncomputable section
namespace Analog.HeterogeneousDualCertificate
open Set Matrix GramSynthesis HeterogeneousAttainment
open scoped BigOperators

/-- The lower-right two-by-two block. -/
def lowerBlock (H : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  H.submatrix Fin.succ Fin.succ

/-- Embed a two-by-two matrix as the lower block with zero leading row/column. -/
def embedLower (W : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![0, 0, 0], ![0, W 0 0, W 0 1], ![0, W 1 0, W 1 1]]

/-- Trace pairing of a rank-one matrix is the actual quadratic form. -/
theorem trace_outer_mul {n : Type*} [Fintype n]
    (z : n → ℝ) (H : Matrix n n ℝ) :
    (vecMulVec z z * H).trace = z ⬝ᵥ (H *ᵥ z) := by
  rw [Matrix.trace_mul_comm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

/-- The embedded dual block pairs only with the common lower primal block. -/
theorem trace_embed_mul (W : Matrix (Fin 2) (Fin 2) ℝ)
    (H : Matrix (Fin 3) (Fin 3) ℝ) :
    (embedLower W * H).trace = (W * lowerBlock H).trace := by
  simp [embedLower, lowerBlock, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Finite weighted matrix sums produce the weighted sampled quadratic forms. -/
theorem trace_weighted_outers {ι n : Type*} [Fintype ι] [Fintype n]
    (α : ι → ℝ) (z : ι → n → ℝ) (H : Matrix n n ℝ) :
    ((∑ i, α i • vecMulVec (z i) (z i)) * H).trace =
      ∑ i, α i * ((z i) ⬝ᵥ (H *ᵥ (z i))) := by
  rw [Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.smul_mul, Matrix.trace_smul, trace_outer_mul, smul_eq_mul]

/-- Each actual PSD residual yields the trace lower bound used by weak duality. -/
theorem node_trace_bound {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (z : ι → Fin 3 → ℝ)
    (H : Matrix (Fin 3) (Fin 3) ℝ) (W G : Matrix (Fin 2) (Fin 2) ℝ)
    (hH : H.PosSemidef) (hblock : lowerBlock H = G)
    (hQ : ((∑ i, α i • vecMulVec (z i) (z i)) - embedLower W).PosSemidef) :
    (W * G).trace ≤ ∑ i, α i * ((z i) ⬝ᵥ (H *ᵥ (z i))) := by
  have hnonneg := FiniteCertificates.psd_trace_product_nonnegative _ H hQ hH
  rw [Matrix.sub_mul, Matrix.trace_sub, trace_weighted_outers, trace_embed_mul, hblock] at hnonneg
  linarith

/-- The finite matrix witness equation derives the exact common-block trace
identity; it is not assumed as a separate scalar premise. -/
theorem common_block_trace_identity {κ τ : Type*} [Fintype κ] [Fintype τ]
    (W : κ → Matrix (Fin 2) (Fin 2) ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ)
    (β : τ → ℝ) (d : τ → Fin 2 → ℝ)
    (hW : ∑ k, W k = ∑ r, β r • vecMulVec (d r) (d r)) :
    ∑ k, (W k * G).trace = ∑ r, β r * ((d r) ⬝ᵥ (G *ᵥ (d r))) := by
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, hW, trace_weighted_outers]

/-- Full finite matrix weak-duality theorem, with all trace steps derived from
PSD residuals and the shared lower block. Sampled peaks and the selected
secants are the actual inequalities needed from the primal continuum program. -/
theorem matrix_dual_upper_bound {κ τ : Type*} (ι : κ → Type*)
    [Fintype κ] [∀ k, Fintype (ι k)] [Fintype τ]
    (H : κ → Matrix (Fin 3) (Fin 3) ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ)
    (z : ∀ k, ι k → Fin 3 → ℝ) (d : τ → Fin 2 → ℝ) (a : τ → ℝ)
    (α : ∀ k, ι k → ℝ) (β : τ → ℝ) (W : κ → Matrix (Fin 2) (Fin 2) ℝ)
    (P lam : ℝ) (hlam : 0 ≤ lam)
    (hH : ∀ k, (H k).PosSemidef) (hblock : ∀ k, lowerBlock (H k) = G)
    (hpeak : ∀ k i, (z k i) ⬝ᵥ ((H k) *ᵥ (z k i)) ≤ P)
    (hsep : ∀ r, lam * a r ≤ (d r) ⬝ᵥ (G *ᵥ (d r)))
    (hα : ∀ k i, 0 ≤ α k i) (hβ : ∀ r, 0 ≤ β r)
    (hQ : ∀ k, ((∑ i, α k i • vecMulVec (z k i) (z k i)) - embedLower (W k)).PosSemidef)
    (hW : ∑ k, W k = ∑ r, β r • vecMulVec (d r) (d r))
    (hnorm : 1 ≤ ∑ r, β r * a r) :
    lam ≤ P * ∑ k, ∑ i, α k i := by
  have hnormalized : lam ≤ lam * ∑ r, β r * a r := by
    simpa using mul_le_mul_of_nonneg_left hnorm hlam
  have hseparation : lam * (∑ r, β r * a r) ≤
      ∑ r, β r * ((d r) ⬝ᵥ (G *ᵥ (d r))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    have hr := mul_le_mul_of_nonneg_left (hsep r) (hβ r)
    nlinarith [hr]
  have htrace : (∑ k, (W k * G).trace) ≤
      ∑ k, ∑ i, α k i * ((z k i) ⬝ᵥ ((H k) *ᵥ (z k i))) := by
    apply Finset.sum_le_sum
    intro k _
    exact node_trace_bound (α k) (z k) (H k) (W k) G (hH k) (hblock k) (hQ k)
  have hpower : (∑ k, ∑ i, α k i * ((z k i) ⬝ᵥ ((H k) *ᵥ (z k i)))) ≤
      P * ∑ k, ∑ i, α k i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi := mul_le_mul_of_nonneg_left (hpeak k i) (hα k i)
    nlinarith [hi]
  exact hnormalized.trans (hseparation.trans ((common_block_trace_identity W G β d hW).symm ▸
    htrace.trans hpower))

/-- The current SDP point as an actual symmetric three-by-three matrix. -/
def matrixOfPoint {K : ℕ} (q : SDPPoint K) (k : Fin K) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![q.h k, q.l₁ k, q.l₂ k], ![q.l₁ k, q.A, q.C], ![q.l₂ k, q.C, q.B]]

/-- Its common two-by-two feature Gram matrix. -/
def gramOfPoint {K : ℕ} (q : SDPPoint K) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![q.A, q.C], ![q.C, q.B]]

/-- Actual feature vectors at the dual sample points. -/
def featureVector (γ : ℝ → ℝ × ℝ) (s : ℝ) : Fin 3 → ℝ :=
  ![1, (γ s).1, (γ s).2]

/-- Actual moment-difference vectors at the selected attainable pairs. -/
def differenceVector (μ ν : ℝ × ℝ) : Fin 2 → ℝ :=
  ![μ.1 - ν.1, μ.2 - ν.2]

theorem matrixOfPoint_quadratic {K : ℕ} (q : SDPPoint K) (k : Fin K)
    (z : Fin 3 → ℝ) :
    z ⬝ᵥ (matrixOfPoint q k *ᵥ z) =
      form3 (q.h k) (q.l₁ k) (q.l₂ k) q.A q.B q.C (z 0) (z 1) (z 2) := by
  simp [matrixOfPoint, dotProduct, Matrix.mulVec, Fin.sum_univ_succ, form3, form2]
  ring

theorem gramOfPoint_quadratic {K : ℕ} (q : SDPPoint K) (μ ν : ℝ × ℝ) :
    differenceVector μ ν ⬝ᵥ (gramOfPoint q *ᵥ differenceVector μ ν) =
      form2 q.A q.B q.C (μ.1 - ν.1) (μ.2 - ν.2) := by
  simp [gramOfPoint, differenceVector, dotProduct, Matrix.mulVec, Fin.sum_univ_succ, form2]
  ring

theorem matrixOfPoint_lowerBlock {K : ℕ} (q : SDPPoint K) (k : Fin K) :
    lowerBlock (matrixOfPoint q k) = gramOfPoint q := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Scalar PSD3 in the operational program is genuine matrix PSD. -/
theorem matrixOfPoint_posSemidef {K : ℕ} (q : SDPPoint K) (k : Fin K)
    (h : PSD3 (q.h k) (q.l₁ k) (q.l₂ k) q.A q.B q.C) :
    (matrixOfPoint q k).PosSemidef := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [matrixOfPoint, Matrix.conjTranspose]
  · intro z
    simpa only [star_trivial, matrixOfPoint_quadratic] using h (z 0) (z 1) (z 2)

/-- The exact finite dual witness in the manuscript bounds every feasible
point of the actual heterogeneous secant program. The selected pairs are
required to lie in its actual finite-input attainable set. PSD trace pairing,
common-block identities, and sampled peak bounds are all derived. -/
theorem current_program_dual_upper_bound {K : ℕ} {τ : Type*}
    (ι : Fin K → Type*) [∀ k, Fintype (ι k)] [Fintype τ]
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ) (P : ℝ)
    (q : SDPPoint K) (hq : SDPFeasible γ F P q)
    (t : ∀ k, ι k → ℝ) (α : ∀ k, ι k → ℝ)
    (μ ν : τ → ℝ × ℝ) (β : τ → ℝ)
    (W : Fin K → Matrix (Fin 2) (Fin 2) ℝ)
    (ht : ∀ k i, t k i ∈ Icc (-1 : ℝ) 1)
    (hα : ∀ k i, 0 ≤ α k i) (hβ : ∀ r, 0 ≤ β r)
    (hμ : ∀ r, μ r ∈ HeterogeneousScore.attainable γ)
    (hν : ∀ r, ν r ∈ HeterogeneousScore.attainable γ)
    (hQ : ∀ k, ((∑ i, α k i • vecMulVec (featureVector (γ k) (t k i))
      (featureVector (γ k) (t k i))) - embedLower (W k)).PosSemidef)
    (hW : (∑ k, W k) = ∑ r, β r • vecMulVec (differenceVector (μ r) (ν r))
      (differenceVector (μ r) (ν r)))
    (hnorm : 1 ≤ ∑ r, β r * (F (μ r) - F (ν r))^2) :
    q.lam ≤ P * ∑ k, ∑ i, α k i := by
  apply matrix_dual_upper_bound ι (matrixOfPoint q) (gramOfPoint q)
    (fun k i => featureVector (γ k) (t k i))
    (fun r => differenceVector (μ r) (ν r))
    (fun r => (F (μ r) - F (ν r))^2) α β W P q.lam hq.1
    (fun k => matrixOfPoint_posSemidef q k (hq.2.1 k))
    (matrixOfPoint_lowerBlock q) ?_ ?_ hα hβ hQ hW hnorm
  · intro k i
    rw [matrixOfPoint_quadratic]
    exact hq.2.2.1 k (t k i) (ht k i)
  · intro r
    rw [gramOfPoint_quadratic]
    exact hq.2.2.2 (μ r) (hμ r) (ν r) (hν r)

end Analog.HeterogeneousDualCertificate
