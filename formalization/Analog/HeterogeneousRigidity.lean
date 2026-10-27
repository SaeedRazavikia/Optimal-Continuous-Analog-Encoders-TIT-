import Analog.GeneralRigidity

/-!
# The distinct-node algebra in the current rigidity proof

The current manuscript allows different preprocessing functions and different
encoders at each node.  The earlier rigidity modules use one shared curve.
This module supplies the algebraic propagation across four distinct nodes
and the subsequent endpoint-inclusive integration for a node-indexed family.

The determinant identities and independent reference columns are explicit
hypotheses in this algebraic module. `HeterogeneousSeparation` derives the
columns, and the completed `HeterogeneousFullRigidity` chain derives the
identities from exact computation through dense separation, planar topology,
and automatic encoder regularity.
-/

noncomputable section
open Set

namespace Analog.HeterogeneousRigidity

/-- The three-column determinant used in Appendix A, with potentially
different preprocessing and encoder derivatives at every node. -/
def tripleDet {ι : Type*} (d₁ d₂ de : ι → ℝ → ℝ)
    (i j k : ι) (x y z : ℝ) : ℝ :=
  de i x * (d₁ j y * d₂ k z - d₁ k z * d₂ j y) +
  de j y * (d₁ k z * d₂ i x - d₁ i x * d₂ k z) +
  de k z * (d₁ i x * d₂ j y - d₁ j y * d₂ i x)

/-- If two independent columns already obey a fixed linear combination,
the vanishing three-column determinant forces it at the remaining column. -/
theorem relation_of_two_anchors
    (ax ay az bx by_ bz ex ey ez α β : ℝ)
    (hdet : ay * bz - az * by_ ≠ 0)
    (hy : ey = α * ay + β * by_)
    (hz : ez = α * az + β * bz)
    (hd : ex * (ay * bz - az * by_) + ey * (az * bx - ax * bz) +
      ez * (ax * by_ - ay * bx) = 0) :
    ex = α * ax + β * bx := by
  have hprod : (ex - (α * ax + β * bx)) * (ay * bz - az * by_) = 0 := by
    calc
      _ = ex * (ay * bz - az * by_) +
          (α * ay + β * by_) * (az * bx - ax * bz) +
          (α * az + β * bz) * (ax * by_ - ay * bx) := by ring
      _ = 0 := by rw [← hy, ← hz]; exact hd
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hdet)

/-- Four distinct nodes suffice to propagate common coefficients to every
node, including the two nodes used to determine the coefficients. -/
theorem common_slopes_of_four_anchors
    {ι : Type*} (domain : Set ℝ) (d₁ d₂ de : ι → ℝ → ℝ)
    (i₀ i₁ i₂ i₃ : ι) (s₀ s₁ s₂ s₃ α β : ℝ)
    (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h03 : i₀ ≠ i₃)
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    (hs₀ : s₀ ∈ domain) (hs₁ : s₁ ∈ domain)
    (hs₂ : s₂ ∈ domain) (hs₃ : s₃ ∈ domain)
    (ha : d₁ i₀ s₀ * d₂ i₁ s₁ - d₁ i₁ s₁ * d₂ i₀ s₀ ≠ 0)
    (hb : d₁ i₂ s₂ * d₂ i₃ s₃ - d₁ i₃ s₃ * d₂ i₂ s₂ ≠ 0)
    (he₀ : de i₀ s₀ = α * d₁ i₀ s₀ + β * d₂ i₀ s₀)
    (he₁ : de i₁ s₁ = α * d₁ i₁ s₁ + β * d₂ i₁ s₁)
    (hd : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ∀ x ∈ domain, ∀ y ∈ domain, ∀ z ∈ domain,
        tripleDet d₁ d₂ de i j k x y z = 0) :
    ∀ i x, x ∈ domain → de i x = α * d₁ i x + β * d₂ i x := by
  have haway : ∀ i, i ≠ i₀ → i ≠ i₁ → ∀ x ∈ domain,
      de i x = α * d₁ i x + β * d₂ i x := by
    intro i hi₀ hi₁ x hx
    exact relation_of_two_anchors _ _ _ _ _ _ _ _ _ α β ha he₀ he₁
      (hd i i₀ i₁ hi₀ hi₁ h01 x hx s₀ hs₀ s₁ hs₁)
  have he₂ := haway i₂ (Ne.symm h02) (Ne.symm h12) s₂ hs₂
  have he₃ := haway i₃ (Ne.symm h03) (Ne.symm h13) s₃ hs₃
  intro i x hx
  by_cases hi₀ : i = i₀
  · subst i
    exact relation_of_two_anchors _ _ _ _ _ _ _ _ _ α β hb he₂ he₃
      (hd i₀ i₂ i₃ h02 h03 h23 x hx s₂ hs₂ s₃ hs₃)
  by_cases hi₁ : i = i₁
  · subst i
    exact relation_of_two_anchors _ _ _ _ _ _ _ _ _ α β hb he₂ he₃
      (hd i₁ i₂ i₃ h12 h13 h23 x hx s₂ hs₂ s₃ hs₃)
  exact haway i hi₀ hi₁ x hx

/-- The two independent reference columns determine real coefficients. -/
theorem coefficients_exist (a₀ a₁ b₀ b₁ e₀ e₁ : ℝ)
    (hd : a₀ * b₁ - a₁ * b₀ ≠ 0) :
    ∃ α β : ℝ, e₀ = α * a₀ + β * b₀ ∧ e₁ = α * a₁ + β * b₁ := by
  refine ⟨(e₀ * b₁ - e₁ * b₀) / (a₀ * b₁ - a₁ * b₀),
    (a₀ * e₁ - a₁ * e₀) / (a₀ * b₁ - a₁ * b₀), ?_, ?_⟩ <;>
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div] <;>
    apply (eq_div_iff hd).2 <;> ring

/-- Common derivative coefficients integrate to common feature coefficients,
while each node retains its own offset. Both endpoints are included. -/
theorem integrate_common_derivatives
    {ι : Type*} {a b α β : ℝ} (φ₁ φ₂ e : ι → ℝ → ℝ)
    (h₁ : ∀ i, ContinuousOn (φ₁ i) (Icc a b))
    (h₂ : ∀ i, ContinuousOn (φ₂ i) (Icc a b))
    (he : ∀ i, ContinuousOn (e i) (Icc a b))
    (hd₁ : ∀ i, DifferentiableOn ℝ (φ₁ i) (Ioo a b))
    (hd₂ : ∀ i, DifferentiableOn ℝ (φ₂ i) (Ioo a b))
    (hde : ∀ i, DifferentiableOn ℝ (e i) (Ioo a b))
    (hrel : ∀ i x, x ∈ Ioo a b →
      deriv (e i) x = α * deriv (φ₁ i) x + β * deriv (φ₂ i) x) :
    ∃ c : ι → ℝ, ∀ i x, x ∈ Icc a b →
      e i x = c i + α * φ₁ i x + β * φ₂ i x := by
  have hc : ∀ i, ∃ c : ℝ, ∀ x ∈ Icc a b,
      e i x = c + α * φ₁ i x + β * φ₂ i x := by
    intro i
    exact GeneralRigidity.affine_of_derivative_relation
      (h₁ i) (h₂ i) (he i) (hd₁ i) (hd₂ i) (hde i) (hrel i)
  exact ⟨fun i => Classical.choose (hc i),
    fun i => Classical.choose_spec (hc i)⟩

end Analog.HeterogeneousRigidity
