import Analog.HeterogeneousAttainment
import Analog.TwoStatisticAttainment

/-!
# Compactness of the actual heterogeneous coefficient class

Functional independence makes the coefficient map injective. Its inverse on
the finite-dimensional function image is continuous, so the already-derived
compact peak class pulls back to a compact coefficient class. Singular shared
columns remain included, as required when extracting limits of designs.
-/
noncomputable section
namespace Analog.GaussianDesignCompactness
open Set HeterogeneousAttainment
open scoped BigOperators

section CompactSource
variable {K : ℕ} {S : Type*} [TopologicalSpace S] [CompactSpace S]

def IndependentFeatures (γ : Fin K → C(S, ℝ × ℝ)) : Prop :=
  ∀ k c a b, (∀ s, c + a * (γ k s).1 + b * (γ k s).2 = 0) →
    c = 0 ∧ a = 0 ∧ b = 0

def coefficientPeakSet (γ : Fin K → C(S, ℝ × ℝ)) (P : ℝ) : Set (Parameters K) :=
  {p | ∀ k s, ((coefficientMap γ p) k s).1 ^ 2 +
    ((coefficientMap γ p) k s).2 ^ 2 ≤ P}

omit [CompactSpace S] in
theorem coefficientMap_injective (hK : 0 < K) (γ : Fin K → C(S, ℝ × ℝ))
    (hind : IndependentFeatures γ) : Function.Injective (coefficientMap γ) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro p hp
  have hcoords (k : Fin K) :
      (p.1 k).1 = 0 ∧ p.2.1.1 = 0 ∧ p.2.2.1 = 0 := by
    apply hind k
    intro s
    have hh := congrArg (fun E : EncoderSpace K S => (E k s).1) hp
    simpa [coefficientMap] using hh
  have hcoords' (k : Fin K) :
      (p.1 k).2 = 0 ∧ p.2.1.2 = 0 ∧ p.2.2.2 = 0 := by
    apply hind k
    intro s
    have hh := congrArg (fun E : EncoderSpace K S => (E k s).2) hp
    simpa [coefficientMap] using hh
  have h₀ := hcoords ⟨0, hK⟩
  have h₀' := hcoords' ⟨0, hK⟩
  apply Prod.ext
  · funext k
    exact Prod.ext (hcoords k).1 (hcoords' k).1
  · exact Prod.ext (Prod.ext h₀.2.1 h₀'.2.1) (Prod.ext h₀.2.2 h₀'.2.2)

/-- The full peak-feasible coefficient set is compact, including its singular
boundary. No coefficient bound or compactness assumption is supplied. -/
theorem coefficientPeakSet_isCompact (hK : 0 < K) (γ : Fin K → C(S, ℝ × ℝ))
    (hind : IndependentFeatures γ) {P : ℝ} (hP : 0 ≤ P) :
    IsCompact (coefficientPeakSet γ P) := by
  let e : Parameters K ≃L[ℝ] LinearMap.range (coefficientMap γ) :=
    (LinearEquiv.ofInjective (coefficientMap γ) (coefficientMap_injective hK γ hind)).toContinuousLinearEquiv
  have he : coefficientPeakSet γ P =
      e.symm '' peakSet (LinearMap.range (coefficientMap γ)) P := by
    ext p
    constructor
    · intro hp
      refine ⟨e p, ?_, e.symm_apply_apply p⟩
      exact hp
    · rintro ⟨q, hq, rfl⟩
      change ∀ k s, ((coefficientMap γ (e.symm q)) k s).1 ^ 2 +
        ((coefficientMap γ (e.symm q)) k s).2 ^ 2 ≤ P
      have hmap : coefficientMap γ (e.symm q) = q.val :=
        congrArg Subtype.val (e.apply_symm_apply q)
      rw [hmap]
      exact hq
  rw [he]
  exact (peakSet_isCompact _ hP).image e.symm.continuous

/-- A small multiple of the identity channel is genuinely peak feasible. -/
theorem exists_identity_peak (γ : Fin K → C(S, ℝ × ℝ)) {P : ℝ} (hP : 0 < P) :
    ∃ ε : ℝ, 0 < ε ∧
      ((fun _ => (0, 0)), (ε, 0), (0, ε)) ∈ coefficientPeakSet γ P := by
  let B : ℝ := 1 + ∑ k, ‖γ k‖ ^ 2
  have hB : 0 < B := by
    have hh : 0 ≤ ∑ k, ‖γ k‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    dsimp [B]
    linarith
  let ε := Real.sqrt (P / (2 * B))
  have hε : 0 < ε := Real.sqrt_pos.mpr (div_pos hP (by positivity))
  have heq : ε ^ 2 * (2 * B) = P := by
    dsimp [ε]
    rw [Real.sq_sqrt (by positivity)]
    exact div_mul_cancel₀ _ (by positivity)
  refine ⟨ε, hε, ?_⟩
  intro k s
  have hn : ‖γ k s‖ ≤ ‖γ k‖ := (γ k).norm_coe_le_norm s
  have hx : |(γ k s).1| ≤ ‖γ k‖ :=
    (le_max_left _ _ : ‖(γ k s).1‖ ≤ max ‖(γ k s).1‖ ‖(γ k s).2‖).trans hn
  have hy : |(γ k s).2| ≤ ‖γ k‖ :=
    (le_max_right _ _ : ‖(γ k s).2‖ ≤ max ‖(γ k s).1‖ ‖(γ k s).2‖).trans hn
  have hx2 : (γ k s).1 ^ 2 ≤ ‖γ k‖ ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hy2 : (γ k s).2 ^ 2 ≤ ‖γ k‖ ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hy 2
  have hk : ‖γ k‖ ^ 2 ≤ B := by
    have hh := Finset.single_le_sum (fun (j : Fin K) _ => sq_nonneg ‖γ j‖)
      (Finset.mem_univ k)
    dsimp [B]
    linarith
  have hb := mul_le_mul_of_nonneg_left
    (show (γ k s).1 ^ 2 + (γ k s).2 ^ 2 ≤ 2 * B by linarith) (sq_nonneg ε)
  dsimp [coefficientMap]
  nlinarith

end CompactSource
end Analog.GaussianDesignCompactness
