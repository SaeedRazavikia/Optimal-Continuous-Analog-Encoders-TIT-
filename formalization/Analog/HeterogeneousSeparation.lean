import Analog.HeterogeneousRigidity

/-!
# Derived distinct-node anchors and differential rigidity

Each local feature curve is continuous on the closed interval and
interior-differentiable, and the constant plus its two coordinates are
functionally independent. These hypotheses produce independent tangent
columns from different nodes. The final differential theorem derives its
anchors and common coefficients. Its triple determinant premises are derived
from exact computation by `HeterogeneousRegularity`,
`HeterogeneousAnalyticRigidity`, and the completed `HeterogeneousFullRigidity`
assembly.
-/

noncomputable section
open Set
namespace Analog.HeterogeneousSeparation
open GeneralRigidity HeterogeneousRigidity

/-- Two independently spanning pairs contain a nonparallel cross-pair. -/
theorem exists_cross_determinant
    (a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ)
    (ha : a₀ * b₁ - a₁ * b₀ ≠ 0)
    (hc : c₀ * d₁ - c₁ * d₀ ≠ 0) :
    a₀ * d₀ - c₀ * b₀ ≠ 0 ∨ a₀ * d₁ - c₁ * b₀ ≠ 0 := by
  by_contra h
  push_neg at h
  have hax : a₀ * (c₀ * d₁ - c₁ * d₀) = 0 := by
    linear_combination c₀ * h.2 - c₁ * h.1
  have hbx : b₀ * (c₀ * d₁ - c₁ * d₀) = 0 := by
    linear_combination d₀ * h.2 - d₁ * h.1
  have ha₀ : a₀ = 0 := (mul_eq_zero.mp hax).resolve_right hc
  have hb₀ : b₀ = 0 := (mul_eq_zero.mp hbx).resolve_right hc
  exact ha (by simp [ha₀, hb₀])

/-- Functional independence separately at two nodes supplies nonsingular
cross-node tangent columns. No feature inversion is assumed. -/
theorem independent_tangents_across_nodes {a b : ℝ}
    (φ₁ φ₂ ψ₁ ψ₂ : ℝ → ℝ)
    (hφ₁ : ContinuousOn φ₁ (Icc a b))
    (hφ₂ : ContinuousOn φ₂ (Icc a b))
    (hψ₁ : ContinuousOn ψ₁ (Icc a b))
    (hψ₂ : ContinuousOn ψ₂ (Icc a b))
    (hdφ₁ : DifferentiableOn ℝ φ₁ (Ioo a b))
    (hdφ₂ : DifferentiableOn ℝ φ₂ (Ioo a b))
    (hdψ₁ : DifferentiableOn ℝ ψ₁ (Ioo a b))
    (hdψ₂ : DifferentiableOn ℝ ψ₂ (Ioo a b))
    (hindφ : NotInAffineLine (Icc a b) φ₁ φ₂)
    (hindψ : NotInAffineLine (Icc a b) ψ₁ ψ₂) :
    ∃ x ∈ Ioo a b, ∃ y ∈ Ioo a b,
      deriv φ₁ x * deriv ψ₂ y - deriv ψ₁ y * deriv φ₂ x ≠ 0 := by
  obtain ⟨x₀, hx₀, x₁, _, hφ⟩ :=
    independent_tangents hφ₁ hφ₂ hdφ₁ hdφ₂ hindφ
  obtain ⟨y₀, hy₀, y₁, hy₁, hψ⟩ :=
    independent_tangents hψ₁ hψ₂ hdψ₁ hdψ₂ hindψ
  obtain h | h := exists_cross_determinant
    (deriv φ₁ x₀) (deriv φ₁ x₁) (deriv φ₂ x₀) (deriv φ₂ x₁)
    (deriv ψ₁ y₀) (deriv ψ₁ y₁) (deriv ψ₂ y₀) (deriv ψ₂ y₁) hφ hψ
  · exact ⟨x₀, hx₀, y₀, hy₀, h⟩
  · exact ⟨x₀, hx₀, y₁, hy₁, h⟩

/-- Differential rigidity with all independent anchors and common derivative
coefficients derived from the local feature hypotheses. Four distinct indices
are supplied, but no tangent nondegeneracy witnesses are assumed. -/
theorem common_derivatives_of_independence
    {ι : Type*} {a b : ℝ} (φ₁ φ₂ e : ι → ℝ → ℝ)
    (i₀ i₁ i₂ i₃ : ι)
    (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h03 : i₀ ≠ i₃)
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    (h₁ : ∀ i, ContinuousOn (φ₁ i) (Icc a b))
    (h₂ : ∀ i, ContinuousOn (φ₂ i) (Icc a b))
    (hd₁ : ∀ i, DifferentiableOn ℝ (φ₁ i) (Ioo a b))
    (hd₂ : ∀ i, DifferentiableOn ℝ (φ₂ i) (Ioo a b))
    (hind : ∀ i, NotInAffineLine (Icc a b) (φ₁ i) (φ₂ i))
    (hdet : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, ∀ z ∈ Ioo a b,
        deriv (φ₁ j) y * deriv (φ₂ k) z - deriv (φ₁ k) z * deriv (φ₂ j) y ≠ 0 →
        tripleDet (fun i => deriv (φ₁ i)) (fun i => deriv (φ₂ i))
          (fun i => deriv (e i)) i j k x y z = 0) :
    ∃ α β : ℝ, ∀ i x, x ∈ Ioo a b →
      deriv (e i) x = α * deriv (φ₁ i) x + β * deriv (φ₂ i) x := by
  obtain ⟨s₀, hs₀, s₁, hs₁, ha⟩ := independent_tangents_across_nodes
    (φ₁ i₀) (φ₂ i₀) (φ₁ i₁) (φ₂ i₁)
    (h₁ i₀) (h₂ i₀) (h₁ i₁) (h₂ i₁)
    (hd₁ i₀) (hd₂ i₀) (hd₁ i₁) (hd₂ i₁) (hind i₀) (hind i₁)
  obtain ⟨s₂, hs₂, s₃, hs₃, hb⟩ := independent_tangents_across_nodes
    (φ₁ i₂) (φ₂ i₂) (φ₁ i₃) (φ₂ i₃)
    (h₁ i₂) (h₂ i₂) (h₁ i₃) (h₂ i₃)
    (hd₁ i₂) (hd₂ i₂) (hd₁ i₃) (hd₂ i₃) (hind i₂) (hind i₃)
  obtain ⟨α, β, he₀, he₁⟩ := coefficients_exist
    (deriv (φ₁ i₀) s₀) (deriv (φ₁ i₁) s₁)
    (deriv (φ₂ i₀) s₀) (deriv (φ₂ i₁) s₁)
    (deriv (e i₀) s₀) (deriv (e i₁) s₁) ha
  have haway : ∀ i, i ≠ i₀ → i ≠ i₁ → ∀ x ∈ Ioo a b,
      deriv (e i) x = α * deriv (φ₁ i) x + β * deriv (φ₂ i) x := by
    intro i hi₀ hi₁ x hx
    exact relation_of_two_anchors _ _ _ _ _ _ _ _ _ α β ha he₀ he₁
      (hdet i i₀ i₁ hi₀ hi₁ h01 x hx s₀ hs₀ s₁ hs₁ ha)
  have he₂ := haway i₂ (Ne.symm h02) (Ne.symm h12) s₂ hs₂
  have he₃ := haway i₃ (Ne.symm h03) (Ne.symm h13) s₃ hs₃
  refine ⟨α, β, ?_⟩
  intro i x hx
  by_cases hi₀ : i = i₀
  · subst i
    exact relation_of_two_anchors _ _ _ _ _ _ _ _ _ α β hb he₂ he₃
      (hdet i₀ i₂ i₃ h02 h03 h23 x hx s₂ hs₂ s₃ hs₃ hb)
  by_cases hi₁ : i = i₁
  · subst i
    exact relation_of_two_anchors _ _ _ _ _ _ _ _ _ α β hb he₂ he₃
      (hdet i₁ i₂ i₃ h12 h13 h23 x hx s₂ hs₂ s₃ hs₃ hb)
  exact haway i hi₀ hi₁ x hx

/-- Endpoint-inclusive heterogeneous differential rigidity. Only the
encoder differentiability and three-node determinant identities remain as
structural premises beyond the manuscript's local-feature assumptions. -/
theorem affine_of_independence_and_triple_determinants
    {K : ℕ} (hK : 4 ≤ K) {a b : ℝ} (φ₁ φ₂ e : Fin K → ℝ → ℝ)
    (h₁ : ∀ i, ContinuousOn (φ₁ i) (Icc a b))
    (h₂ : ∀ i, ContinuousOn (φ₂ i) (Icc a b))
    (he : ∀ i, ContinuousOn (e i) (Icc a b))
    (hd₁ : ∀ i, DifferentiableOn ℝ (φ₁ i) (Ioo a b))
    (hd₂ : ∀ i, DifferentiableOn ℝ (φ₂ i) (Ioo a b))
    (hde : ∀ i, DifferentiableOn ℝ (e i) (Ioo a b))
    (hind : ∀ i, NotInAffineLine (Icc a b) (φ₁ i) (φ₂ i))
    (hdet : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, ∀ z ∈ Ioo a b,
        deriv (φ₁ j) y * deriv (φ₂ k) z - deriv (φ₁ k) z * deriv (φ₂ j) y ≠ 0 →
        tripleDet (fun i => deriv (φ₁ i)) (fun i => deriv (φ₂ i))
          (fun i => deriv (e i)) i j k x y z = 0) :
    ∃ α β : ℝ, ∃ c : Fin K → ℝ, ∀ i x, x ∈ Icc a b →
      e i x = c i + α * φ₁ i x + β * φ₂ i x := by
  let i₀ : Fin K := ⟨0, by omega⟩
  let i₁ : Fin K := ⟨1, by omega⟩
  let i₂ : Fin K := ⟨2, by omega⟩
  let i₃ : Fin K := ⟨3, by omega⟩
  obtain ⟨α, β, hrel⟩ := common_derivatives_of_independence φ₁ φ₂ e i₀ i₁ i₂ i₃
    (by simp [i₀, i₁]) (by simp [i₀, i₂]) (by simp [i₀, i₃])
    (by simp [i₁, i₂]) (by simp [i₁, i₃]) (by simp [i₂, i₃])
    h₁ h₂ hd₁ hd₂ hind hdet
  obtain ⟨c, hc⟩ := integrate_common_derivatives φ₁ φ₂ e h₁ h₂ he hd₁ hd₂ hde hrel
  exact ⟨α, β, c, hc⟩

end Analog.HeterogeneousSeparation
