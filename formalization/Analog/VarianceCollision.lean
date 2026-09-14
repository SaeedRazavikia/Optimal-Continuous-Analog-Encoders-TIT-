import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Variance collisions for arbitrary encoders

We formalize the first step of the continuous-encoder rigidity argument for
variance. The encoder is an arbitrary map from real inputs to the real plane;
no polynomial, moment-curve, or continuity hypothesis is built into its type.
Exact variance computation by K >= 4 terminals implies that an encoded
collision between two triples preserves both their first and second moments.

The proof uses two common completions of the triples, at fourth inputs 0 and
1/2, with all remaining inputs zero. It does not prove the subsequent
topological rigidity theorem or the operational score formula.

We also formalize the operational prerequisite that a positive uniform
separation lower bound implies exact computation, and hence the same triple
collision conclusion. This lower-bound formulation does not define an
infimum or identify its value with the finite-dimensional Gram score.
-/

noncomputable section

namespace Analog
namespace ArbitraryEncoder

/-- The allowed source interval. -/
def InSource (x : ℝ) : Prop := -1 ≤ x ∧ x ≤ 1

/-- A source tuple represented as a list of the prescribed length. -/
def ValidInput (K : ℕ) (xs : List ℝ) : Prop :=
  xs.length = K ∧ ∀ x ∈ xs, InSource x

/-- The first unnormalized empirical moment. -/
def firstMoment (xs : List ℝ) : ℝ := xs.sum

/-- The second unnormalized empirical moment. -/
def secondMoment (xs : List ℝ) : ℝ := (xs.map (fun x => x ^ 2)).sum

/-- The noiseless multiple-access channel sum, for an arbitrary planar encoder. -/
def received (E : ℝ → ℝ × ℝ) (xs : List ℝ) : ℝ × ℝ := (xs.map E).sum

/-- The empirical variance computed by K terminals. -/
def variance (K : ℕ) (xs : List ℝ) : ℝ :=
  secondMoment xs / (K : ℝ) - (firstMoment xs / (K : ℝ)) ^ 2

/-- Exact computation means equal channel outputs have equal target values. -/
def ExactVariance (K : ℕ) (E : ℝ → ℝ × ℝ) : Prop :=
  ∀ xs ys : List ℝ, ValidInput K xs → ValidInput K ys →
    received E xs = received E ys → variance K xs = variance K ys

/-- Squared Euclidean distance in the received-signal plane. -/
def squaredDistance (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- A uniform lower bound on squared channel-output separation in terms of
squared target separation. This definition is a pairwise inequality, not a
formula for the operational separation infimum. -/
def SeparationLowerBound (K : ℕ) (E : ℝ → ℝ × ℝ) (lam : ℝ) : Prop :=
  ∀ xs ys : List ℝ, ValidInput K xs → ValidInput K ys →
    lam * (variance K xs - variance K ys) ^ 2 ≤
      squaredDistance (received E xs) (received E ys)

/-- Every positive uniform separation lower bound ensures exact variance
computation for an arbitrary encoder. -/
theorem positive_separation_implies_exact {K : ℕ} {E : ℝ → ℝ × ℝ}
    {lam : ℝ} (hlam : 0 < lam) (hsep : SeparationLowerBound K E lam) :
    ExactVariance K E := by
  intro xs ys hxs hys hcollision
  have h := hsep xs ys hxs hys
  simp only [squaredDistance, hcollision, sub_self, zero_pow (by decide : 2 ≠ 0),
    add_zero] at h
  have hsq : (variance K xs - variance K ys) ^ 2 ≤ 0 :=
    (mul_le_mul_iff_right₀ hlam).mp (by simpa only [mul_zero] using h)
  nlinarith [sq_nonneg (variance K xs - variance K ys)]

/-- Add a common fourth input and enough zeros to obtain K terminals. -/
def completeTriple (K : ℕ) (xs : List ℝ) (w : ℝ) : List ℝ :=
  xs ++ w :: List.replicate (K - 4) 0

lemma completeTriple_valid {K : ℕ} (hK : 4 ≤ K) {xs : List ℝ}
    (hxs : ValidInput 3 xs) {w : ℝ} (hw : InSource w) :
    ValidInput K (completeTriple K xs w) := by
  constructor
  · simp only [completeTriple, List.length_append, List.length_cons,
      List.length_replicate, hxs.1]
    omega
  · intro x hx
    simp only [completeTriple, List.mem_append, List.mem_cons,
      List.mem_replicate] at hx
    rcases hx with hx | hx | ⟨_, hx⟩
    · exact hxs.2 x hx
    · simpa [hx] using hw
    · subst x
      norm_num [InSource]

lemma firstMoment_complete (K : ℕ) (xs : List ℝ) (w : ℝ) :
    firstMoment (completeTriple K xs w) = firstMoment xs + w := by
  simp [firstMoment, completeTriple]

lemma secondMoment_complete (K : ℕ) (xs : List ℝ) (w : ℝ) :
    secondMoment (completeTriple K xs w) = secondMoment xs + w ^ 2 := by
  simp [secondMoment, completeTriple]

lemma received_complete_collision (K : ℕ) (E : ℝ → ℝ × ℝ)
    (xs ys : List ℝ) (w : ℝ) (h : received E xs = received E ys) :
    received E (completeTriple K xs w) =
      received E (completeTriple K ys w) := by
  simp only [received, completeTriple, List.map_append, List.sum_append]
  change received E xs + _ = received E ys + _
  rw [h]

/-- Pure algebra: agreement at two distinct common fourth inputs determines
both unnormalized moments. -/
lemma two_completions_determine_moments (k S T S' T' : ℝ) (hk : k ≠ 0)
    (hzero : T / k - (S / k) ^ 2 = T' / k - (S' / k) ^ 2)
    (hhalf : (T + (1 / 2 : ℝ) ^ 2) / k - ((S + 1 / 2) / k) ^ 2 =
      (T' + (1 / 2 : ℝ) ^ 2) / k - ((S' + 1 / 2) / k) ^ 2) :
    S = S' ∧ T = T' := by
  have hzero' : T * k - S ^ 2 = T' * k - S' ^ 2 := by
    field_simp at hzero ⊢
    nlinarith [hzero]
  have hhalf' : (T + (1 / 2 : ℝ) ^ 2) * k - (S + 1 / 2) ^ 2 =
      (T' + (1 / 2 : ℝ) ^ 2) * k - (S' + 1 / 2) ^ 2 := by
    field_simp at hhalf ⊢
    nlinarith [hhalf]
  have hS : S = S' := by nlinarith [hzero', hhalf']
  refine ⟨hS, ?_⟩
  have hTk : T * k = T' * k := by rw [hS] at hzero'; linarith
  exact mul_right_cancel₀ hk hTk

/-- For every number of terminals K >= 4 and every planar encoder, exact
variance computation forces every encoded triple collision to preserve both
moments. In particular, this applies to all continuous encoders. -/
theorem triple_collision_preserves_moments {K : ℕ} (hK : 4 ≤ K)
    (E : ℝ → ℝ × ℝ) (hexact : ExactVariance K E)
    (xs ys : List ℝ) (hxs : ValidInput 3 xs) (hys : ValidInput 3 ys)
    (hcollision : received E xs = received E ys) :
    firstMoment xs = firstMoment ys ∧ secondMoment xs = secondMoment ys := by
  have hcompletion (w : ℝ) (hw : InSource w) :
      (secondMoment xs + w ^ 2) / (K : ℝ) -
          ((firstMoment xs + w) / (K : ℝ)) ^ 2 =
        (secondMoment ys + w ^ 2) / (K : ℝ) -
          ((firstMoment ys + w) / (K : ℝ)) ^ 2 := by
    have h := hexact (completeTriple K xs w) (completeTriple K ys w)
      (completeTriple_valid hK hxs hw) (completeTriple_valid hK hys hw)
      (received_complete_collision K E xs ys w hcollision)
    simpa only [variance, firstMoment_complete, secondMoment_complete] using h
  have hzero := hcompletion 0 (by norm_num [InSource])
  have hhalf := hcompletion (1 / 2) (by norm_num [InSource])
  have hk : (K : ℝ) ≠ 0 := by
    have hn : K ≠ 0 := by omega
    exact_mod_cast hn
  apply two_completions_determine_moments (K : ℝ)
    (firstMoment xs) (secondMoment xs) (firstMoment ys) (secondMoment ys) hk
  · simpa using hzero
  · exact hhalf

/-- A positive uniform separation lower bound forces moment preservation in
all encoded triple collisions, for every K >= 4 and every planar encoder. -/
theorem positive_separation_triple_collision {K : ℕ} (hK : 4 ≤ K)
    (E : ℝ → ℝ × ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hsep : SeparationLowerBound K E lam)
    (xs ys : List ℝ) (hxs : ValidInput 3 xs) (hys : ValidInput 3 ys)
    (hcollision : received E xs = received E ys) :
    firstMoment xs = firstMoment ys ∧ secondMoment xs = secondMoment ys := by
  exact triple_collision_preserves_moments hK E
    (positive_separation_implies_exact hlam hsep) xs ys hxs hys hcollision

end ArbitraryEncoder
end Analog
