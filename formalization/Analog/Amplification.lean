import Analog.Decoder
import Analog.Operational
import Mathlib.Data.Real.Sqrt

/-!
# Sharp uniform amplification

The actual infimum of squared received-distance quotients determines the
smallest uniform scalar-decoding constant. A positive score has an attaining
continuous decoder with constant `1 / sqrt score`; a zero score admits no
finite uniform constant when the target is nonconstant. This is the
operational content of the manuscript's amplification proposition, including
the convention that a zero score means infinite required amplification.
-/

noncomputable section

namespace Analog.Decoder

open scoped NNReal

variable {X Y : Type*} [PseudoMetricSpace Y]

/-- Actual squared-separation infimum for an arbitrary received map. -/
def metricScore (r : X → Y) (f : X → ℝ) : ℝ :=
  Operational.score Set.univ f (fun x z => dist (r x) (r z) ^ 2)

/-- The reciprocal-root constant. It is interpreted as the sharp finite
constant only under a positive-score hypothesis. -/
def sharpConstant (r : X → Y) (f : X → ℝ) : ℝ≥0 :=
  ⟨1 / Real.sqrt (metricScore r f),
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)⟩

lemma le_mul_iff_inverse_square {a b L : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hL : 0 < L) :
    a ≤ L * b ↔ (1 / L ^ 2) * a ^ 2 ≤ b ^ 2 := by
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (sq_pos_of_pos hL)]
  have hsq := sq_le_sq₀ ha (mul_nonneg hL.le hb)
  constructor
  · intro h
    have hh := hsq.mpr h
    nlinarith
  · intro h
    apply hsq.mp
    nlinarith

/-- Exact bridge from a Lipschitz constant to the operational infimum. -/
theorem pairwise_iff_inverse_square_le_score (r : X → Y) (f : X → ℝ)
    (hn : Operational.NonconstantOn Set.univ f) (L : ℝ≥0) (hL : 0 < L) :
    PairwiseBound r f L ↔ 1 / (L : ℝ) ^ 2 ≤ metricScore r f := by
  have hLr : 0 < (L : ℝ) := hL
  have hc : ∀ x ∈ (Set.univ : Set X), ∀ z ∈ (Set.univ : Set X),
      0 ≤ dist (r x) (r z) ^ 2 := fun _ _ _ _ => sq_nonneg _
  rw [metricScore, Operational.le_score_iff hn hc]
  constructor
  · intro h x _ z _
    have hsq := (le_mul_iff_inverse_square
      (dist_nonneg : 0 ≤ dist (f x) (f z))
      (dist_nonneg : 0 ≤ dist (r x) (r z)) hLr).mp (h x z)
    simpa only [Real.dist_eq, sq_abs] using hsq
  · intro h x z
    apply (le_mul_iff_inverse_square
      (dist_nonneg : 0 ≤ dist (f x) (f z))
      (dist_nonneg : 0 ≤ dist (r x) (r z)) hLr).mpr
    simpa only [Real.dist_eq, sq_abs] using h x (Set.mem_univ x) z (Set.mem_univ z)

/-- A nonconstant target cannot have uniform amplification zero. -/
theorem uniform_constant_pos {r : X → Y} {f : X → ℝ}
    (hn : Operational.NonconstantOn Set.univ f) {L : ℝ≥0} {D : Y → ℝ}
    (h : UniformBound r f L D) : 0 < L := by
  by_contra hL
  have hL0 : L = 0 := le_antisymm (le_of_not_gt hL) (zero_le _)
  obtain ⟨x, _, z, _, hne⟩ := hn
  have hpair := uniform_pairwise h x z
  have heq : f x = f z := by simpa [hL0] using hpair
  exact hne heq

/-- Every finite uniform decoder requires a strictly positive score. -/
theorem uniform_implies_positive_score {r : X → Y} {f : X → ℝ}
    (hn : Operational.NonconstantOn Set.univ f) {L : ℝ≥0} {D : Y → ℝ}
    (h : UniformBound r f L D) : 0 < metricScore r f := by
  have hL := uniform_constant_pos hn h
  have hbound := (pairwise_iff_inverse_square_le_score r f hn L hL).mp
    (uniform_pairwise h)
  exact lt_of_lt_of_le (div_pos (by norm_num) (sq_pos_of_pos (show 0 < (L : ℝ) from hL)))
    hbound

/-- The reciprocal-root constant is positive whenever the score is positive. -/
theorem sharpConstant_pos {r : X → Y} {f : X → ℝ}
    (hscore : 0 < metricScore r f) : 0 < sharpConstant r f := by
  show 0 < (1 / Real.sqrt (metricScore r f) : ℝ)
  exact div_pos (by norm_num) (Real.sqrt_pos.mpr hscore)

/-- The sharp constant satisfies the pairwise condition without any assumed
decoder; the operational infimum supplies the needed lower bound. -/
theorem sharpConstant_pairwise (r : X → Y) (f : X → ℝ)
    (hn : Operational.NonconstantOn Set.univ f)
    (hscore : 0 < metricScore r f) : PairwiseBound r f (sharpConstant r f) := by
  apply (pairwise_iff_inverse_square_le_score r f hn _ (sharpConstant_pos hscore)).mpr
  change 1 / (1 / Real.sqrt (metricScore r f)) ^ 2 ≤ metricScore r f
  simp only [one_div, inv_pow, inv_inv, Real.sq_sqrt hscore.le]
  exact le_rfl

/-- Every feasible uniform constant is at least the reciprocal square root
of the actual operational score. -/
theorem sharpConstant_le_uniform {r : X → Y} {f : X → ℝ}
    (hn : Operational.NonconstantOn Set.univ f)
    (hscore : 0 < metricScore r f) {L : ℝ≥0} {D : Y → ℝ}
    (h : UniformBound r f L D) : sharpConstant r f ≤ L := by
  have hL := uniform_constant_pos hn h
  have hLr : 0 < (L : ℝ) := hL
  have hbound := (pairwise_iff_inverse_square_le_score r f hn L hL).mp
    (uniform_pairwise h)
  have hprod : 1 ≤ metricScore r f * (L : ℝ) ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hLr)).mp hbound
  change 1 / Real.sqrt (metricScore r f) ≤ (L : ℝ)
  apply (sq_le_sq₀ (div_nonneg (by norm_num) (Real.sqrt_nonneg _)) L.coe_nonneg).mp
  rw [div_pow, one_pow, Real.sq_sqrt hscore.le]
  exact (div_le_iff₀ hscore).mpr (by nlinarith)

/-- The optimal uniform amplification is attained by a global Lipschitz,
hence continuous, exact decoder. The final conjunct states global optimality
among every decoder and every finite nonnegative constant. -/
theorem sharp_uniform_decoder (r : X → Y) (f : X → ℝ)
    (hn : Operational.NonconstantOn Set.univ f)
    (hscore : 0 < metricScore r f) :
    ∃ D : Y → ℝ, LipschitzWith (sharpConstant r f) D ∧ Continuous D ∧
      (∀ x, D (r x) = f x) ∧ UniformBound r f (sharpConstant r f) D ∧
      ∀ (L : ℝ≥0) (D' : Y → ℝ), UniformBound r f L D' → sharpConstant r f ≤ L := by
  obtain ⟨D, hD, he⟩ := pairwise_exists_lipschitz (sharpConstant_pairwise r f hn hscore)
  exact ⟨D, hD, hD.continuous, he, lipschitz_exact_uniform hD he,
    fun _ _ hu => sharpConstant_le_uniform hn hscore hu⟩

/-- A finite uniform decoder exists exactly when the operational score is
positive. Thus a zero score has no finite decoder constant. -/
theorem finite_uniform_decoder_iff_positive_score (r : X → Y) (f : X → ℝ)
    (hn : Operational.NonconstantOn Set.univ f) :
    (∃ (L : ℝ≥0) (D : Y → ℝ), UniformBound r f L D) ↔ 0 < metricScore r f := by
  constructor
  · rintro ⟨L, D, h⟩
    exact uniform_implies_positive_score hn h
  · intro hscore
    obtain ⟨D, _, _, _, hu, _⟩ := sharp_uniform_decoder r f hn hscore
    exact ⟨sharpConstant r f, D, hu⟩

theorem zero_score_no_finite_uniform_decoder (r : X → Y) (f : X → ℝ)
    (hn : Operational.NonconstantOn Set.univ f) (hzero : metricScore r f = 0) :
    ¬ ∃ (L : ℝ≥0) (D : Y → ℝ), UniformBound r f L D := by
  rw [finite_uniform_decoder_iff_positive_score r f hn, hzero]
  exact lt_irrefl 0

end Analog.Decoder
