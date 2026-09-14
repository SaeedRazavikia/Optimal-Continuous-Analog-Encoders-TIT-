import Analog.Certificate
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The algebraic differential step of moment rigidity

`featureSlope` and `encoderSlope` stand for scalar derivative functions.  We
prove the linear-algebra implication from annihilation of every two-moment
kernel to affine dependence on the feature slope.  This is the algebraic
part of Step 3 in manuscript Lemma `lem:affine`.

The final declarations also integrate the slope relation and extend the
representation to the endpoints, using continuity on a closed interval.
The hypotheses do not establish automatic differentiability, identify tangent
spaces, or prove continuous-encoder rigidity. Those are separate analytic
obligations.
-/

namespace Analog.DifferentialRigidity

/-- The derivative of an encoded triple sum vanishes on the kernel of the
two moment derivatives, for all source triples in `domain`. -/
def TripleKernelAnnihilation (domain : Set ℝ)
    (featureSlope encoderSlope : ℝ → ℝ) : Prop :=
  ∀ x ∈ domain, ∀ y ∈ domain, ∀ z ∈ domain,
    ∀ a b c : ℝ,
      a + b + c = 0 →
      featureSlope x * a + featureSlope y * b + featureSlope z * c = 0 →
      encoderSlope x * a + encoderSlope y * b + encoderSlope z * c = 0

/-- A scalar row annihilating the two-moment kernel has zero determinant
with the constant row and the feature-derivative row. -/
theorem kernel_annihilation_determinant
    (dx dy dz ex ey ez : ℝ)
    (h : ∀ a b c : ℝ, a + b + c = 0 →
      dx * a + dy * b + dz * c = 0 →
      ex * a + ey * b + ez * c = 0) :
    ex * (dy - dz) + ey * (dz - dx) + ez * (dx - dy) = 0 := by
  apply h
  · ring
  · ring

/-- Two distinct anchor feature slopes determine coefficients valid at any
third point whose encoded differential annihilates the moment kernel. -/
theorem affine_slope_from_kernel
    (dx dy dz ex ey ez : ℝ) (hdyz : dy ≠ dz)
    (h : ∀ a b c : ℝ, a + b + c = 0 →
      dx * a + dy * b + dz * c = 0 →
      ex * a + ey * b + ez * c = 0) :
    ex = (ey - (ey - ez) / (dy - dz) * dy) +
      (ey - ez) / (dy - dz) * dx := by
  have hdet := kernel_annihilation_determinant dx dy dz ex ey ez h
  have hne : dy - dz ≠ 0 := sub_ne_zero.mpr hdyz
  field_simp [hne]
  nlinarith [hdet]

/-- Fixed anchors yield the same affine derivative coefficients throughout
the source domain. -/
theorem global_affine_slopes (domain : Set ℝ)
    (featureSlope encoderSlope : ℝ → ℝ)
    (hkernel : TripleKernelAnnihilation domain featureSlope encoderSlope)
    {y z : ℝ} (hy : y ∈ domain) (hz : z ∈ domain)
    (hanchor : featureSlope y ≠ featureSlope z) :
    ∃ α β : ℝ, ∀ x ∈ domain,
      encoderSlope x = α + β * featureSlope x := by
  refine ⟨encoderSlope y -
    (encoderSlope y - encoderSlope z) / (featureSlope y - featureSlope z) *
      featureSlope y,
    (encoderSlope y - encoderSlope z) / (featureSlope y - featureSlope z), ?_⟩
  intro x hx
  exact affine_slope_from_kernel _ _ _ _ _ _ hanchor
    (hkernel x hx y hy z hz)

/-- Affine dependence on the feature slope is sufficient for annihilation
of every two-moment derivative kernel. -/
theorem affine_slopes_annihilate_kernel (domain : Set ℝ)
    (featureSlope encoderSlope : ℝ → ℝ) (α β : ℝ)
    (hslopes : ∀ x ∈ domain, encoderSlope x = α + β * featureSlope x) :
    TripleKernelAnnihilation domain featureSlope encoderSlope := by
  intro x hx y hy z hz a b c habc hmom
  rw [hslopes x hx, hslopes y hy, hslopes z hz]
  calc
    _ = α * (a + b + c) + β *
        (featureSlope x * a + featureSlope y * b + featureSlope z * c) := by ring
    _ = 0 := by rw [habc, hmom]; ring

/-- The two-anchor nondegeneracy makes the affine slope coefficients unique. -/
theorem affine_slope_coefficients_unique (domain : Set ℝ)
    (featureSlope encoderSlope : ℝ → ℝ)
    {y z : ℝ} (hy : y ∈ domain) (hz : z ∈ domain)
    (hanchor : featureSlope y ≠ featureSlope z)
    {α β α' β' : ℝ}
    (h : ∀ x ∈ domain, encoderSlope x = α + β * featureSlope x)
    (h' : ∀ x ∈ domain, encoderSlope x = α' + β' * featureSlope x) :
    α = α' ∧ β = β' := by
  have hy' := (h y hy).symm.trans (h' y hy)
  have hz' := (h z hz).symm.trans (h' z hz)
  have hprod : (β - β') * (featureSlope y - featureSlope z) = 0 := by
    nlinarith [hy', hz']
  have hβ : β = β' := sub_eq_zero.mp
    ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hanchor))
  constructor
  · rw [hβ] at hy'
    linarith
  · exact hβ

/-- On a domain containing two distinct feature slopes, kernel annihilation
is equivalent to affine dependence of the encoded derivative. -/
theorem kernel_annihilation_iff_affine_slopes (domain : Set ℝ)
    (featureSlope encoderSlope : ℝ → ℝ)
    {y z : ℝ} (hy : y ∈ domain) (hz : z ∈ domain)
    (hanchor : featureSlope y ≠ featureSlope z) :
    TripleKernelAnnihilation domain featureSlope encoderSlope ↔
      ∃ α β : ℝ, ∀ x ∈ domain,
        encoderSlope x = α + β * featureSlope x := by
  constructor
  · exact fun h => global_affine_slopes domain featureSlope encoderSlope h hy hz hanchor
  · rintro ⟨α, β, h⟩
    exact affine_slopes_annihilate_kernel domain featureSlope encoderSlope α β h

/-- A continuous scalar function with zero derivative throughout the interior
of a closed interval is constant, including its endpoints. -/
theorem constant_on_closed_interval {a b : ℝ} {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f 0 x) :
    ∀ x ∈ Set.Icc a b, f x = f a := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hax | hax
  · rw [← hax]
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) hax
      (hcont.mono (Set.Icc_subset_Icc le_rfl hx.2))
      (fun t ht => hderiv t ⟨ht.1, lt_of_lt_of_le ht.2 hx.2⟩)
    have hne : x - a ≠ 0 := sub_ne_zero.mpr hax.ne'
    have heq : f x - f a = 0 :=
      (div_eq_zero_iff.mp hslope.symm).resolve_right hne
    exact sub_eq_zero.mp heq

/-- Integrating a fixed affine derivative relation gives the corresponding
affine feature representation on the entire closed interval. Endpoint
derivatives are not assumed. -/
theorem affine_representation_of_derivative_relation
    {a b α β : ℝ} {feature encoder : ℝ → ℝ}
    (hfeature : ContinuousOn feature (Set.Icc a b))
    (hencoder : ContinuousOn encoder (Set.Icc a b))
    (hdfeature : DifferentiableOn ℝ feature (Set.Ioo a b))
    (hdencoder : DifferentiableOn ℝ encoder (Set.Ioo a b))
    (hslopes : ∀ x ∈ Set.Ioo a b,
      deriv encoder x = α + β * deriv feature x) :
    ∃ c : ℝ, ∀ x ∈ Set.Icc a b,
      encoder x = c + α * x + β * feature x := by
  let f : ℝ → ℝ := fun x => encoder x - α * x - β * feature x
  have hfcont : ContinuousOn f (Set.Icc a b) :=
    (hencoder.sub (continuousOn_const.mul continuousOn_id)).sub
      (continuousOn_const.mul hfeature)
  have hfderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f 0 x := by
    intro x hx
    have he := ((hdencoder x hx).differentiableAt
      (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
    have hφ := ((hdfeature x hx).differentiableAt
      (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
    convert (he.sub ((hasDerivAt_id x).const_mul α)).sub (hφ.const_mul β) using 1
    simp only [mul_one, hslopes x hx]
    ring
  refine ⟨f a, ?_⟩
  intro x hx
  have hc := constant_on_closed_interval hfcont hfderiv x hx
  dsimp [f] at hc ⊢
  linarith

/-- The complete scalar final step of differential rigidity: under actual
interior differentiability and the differential-kernel hypothesis, a scalar
encoder component is affine in the two features, including both endpoints. -/
theorem affine_representation_of_differential_kernel
    {a b : ℝ} {feature encoder : ℝ → ℝ}
    (hfeature : ContinuousOn feature (Set.Icc a b))
    (hencoder : ContinuousOn encoder (Set.Icc a b))
    (hdfeature : DifferentiableOn ℝ feature (Set.Ioo a b))
    (hdencoder : DifferentiableOn ℝ encoder (Set.Ioo a b))
    (hkernel : TripleKernelAnnihilation (Set.Ioo a b)
      (deriv feature) (deriv encoder))
    {y z : ℝ} (hy : y ∈ Set.Ioo a b) (hz : z ∈ Set.Ioo a b)
    (hanchor : deriv feature y ≠ deriv feature z) :
    ∃ c α β : ℝ, ∀ x ∈ Set.Icc a b,
      encoder x = c + α * x + β * feature x := by
  obtain ⟨α, β, hslopes⟩ :=
    global_affine_slopes _ _ _ hkernel hy hz hanchor
  obtain ⟨c, hc⟩ := affine_representation_of_derivative_relation
    hfeature hencoder hdfeature hdencoder hslopes
  exact ⟨c, α, β, hc⟩

/-- A continuous, interior-differentiable nonaffine feature has two distinct
interior derivative values.  No endpoint derivatives are required. -/
theorem nonaffine_has_distinct_interior_slopes
    {a b : ℝ} (hab : a < b) {feature : ℝ → ℝ}
    (hfeature : ContinuousOn feature (Set.Icc a b))
    (hdfeature : DifferentiableOn ℝ feature (Set.Ioo a b))
    (hnonaffine : ¬ ∃ c α : ℝ, ∀ x ∈ Set.Icc a b,
      feature x = c + α * x) :
    ∃ y ∈ Set.Ioo a b, ∃ z ∈ Set.Ioo a b,
      deriv feature y ≠ deriv feature z := by
  classical
  by_contra h
  let m : ℝ := (a + b) / 2
  have hm : m ∈ Set.Ioo a b := by
    constructor <;> dsimp [m] <;> linarith
  have hconst : ∀ x ∈ Set.Ioo a b, deriv feature x = deriv feature m := by
    intro x hx
    by_contra hne
    exact h ⟨x, hx, m, hm, hne⟩
  obtain ⟨c, hc⟩ := affine_representation_of_derivative_relation
    (α := deriv feature m) (β := 0) hfeature hfeature hdfeature hdfeature
    (fun x hx => by simpa using hconst x hx)
  apply hnonaffine
  exact ⟨c, deriv feature m, fun x hx => by simpa using hc x hx⟩

/-- For a nonaffine feature, the scalar differential-kernel hypothesis gives
an affine feature representation throughout the closed interval. -/
theorem nonaffine_differential_rigidity
    {a b : ℝ} (hab : a < b) {feature encoder : ℝ → ℝ}
    (hfeature : ContinuousOn feature (Set.Icc a b))
    (hencoder : ContinuousOn encoder (Set.Icc a b))
    (hdfeature : DifferentiableOn ℝ feature (Set.Ioo a b))
    (hdencoder : DifferentiableOn ℝ encoder (Set.Ioo a b))
    (hnonaffine : ¬ ∃ c α : ℝ, ∀ x ∈ Set.Icc a b,
      feature x = c + α * x)
    (hkernel : TripleKernelAnnihilation (Set.Ioo a b)
      (deriv feature) (deriv encoder)) :
    ∃ c α β : ℝ, ∀ x ∈ Set.Icc a b,
      encoder x = c + α * x + β * feature x := by
  obtain ⟨y, hy, z, hz, hanchor⟩ :=
    nonaffine_has_distinct_interior_slopes hab hfeature hdfeature hnonaffine
  exact affine_representation_of_differential_kernel
    hfeature hencoder hdfeature hdencoder hkernel hy hz hanchor

/-- The planar affine representation follows componentwise once interior
differentiability and both differential-kernel identities have been proved.
This result includes the source endpoints, but does not assert independence
of `u` and `v`, nor derive the differential hypotheses from exactness. -/
theorem planar_differential_rigidity
    {a b : ℝ} (hab : a < b)
    {feature : ℝ → ℝ} {encoder : ℝ → ℝ × ℝ}
    (hfeature : ContinuousOn feature (Set.Icc a b))
    (hencoder : ContinuousOn encoder (Set.Icc a b))
    (hdfeature : DifferentiableOn ℝ feature (Set.Ioo a b))
    (hdencoder : DifferentiableOn ℝ encoder (Set.Ioo a b))
    (hnonaffine : ¬ ∃ c α : ℝ, ∀ x ∈ Set.Icc a b,
      feature x = c + α * x)
    (hkernelx : TripleKernelAnnihilation (Set.Ioo a b)
      (deriv feature) (deriv fun x => (encoder x).1))
    (hkernely : TripleKernelAnnihilation (Set.Ioo a b)
      (deriv feature) (deriv fun x => (encoder x).2)) :
    ∃ c u v : ℝ × ℝ, ∀ x ∈ Set.Icc a b,
      encoder x = c + x • u + feature x • v := by
  obtain ⟨cx, ux, vx, hx⟩ := nonaffine_differential_rigidity
    hab hfeature hencoder.fst hdfeature hdencoder.fst hnonaffine hkernelx
  obtain ⟨cy, uy, vy, hy⟩ := nonaffine_differential_rigidity
    hab hfeature hencoder.snd hdfeature hdencoder.snd hnonaffine hkernely
  refine ⟨(cx, cy), (ux, uy), (vx, vy), ?_⟩
  intro x hxi
  apply Prod.ext
  · simpa [mul_comm] using hx x hxi
  · simpa [mul_comm] using hy x hxi

end Analog.DifferentialRigidity
