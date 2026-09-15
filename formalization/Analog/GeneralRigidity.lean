import Analog.RigidityAnalysis
import Analog.AdditiveStatistics

/-!
# Differential rigidity for two arbitrary prescribed statistics

This file generalizes the differential and inverse-function parts of the
manuscript's extended rigidity proof to `γ = (φ₁, φ₂)`. Interior differentiability
of the encoder and local constancy on statistic fibers are explicit hypotheses;
the topological factorization and smoothing steps are not asserted here.
-/

noncomputable section
open Set Filter Topology
namespace Analog.GeneralRigidity
open RigidityAnalysis

/-- The determinant of two planar statistic derivatives. -/
def tangentDet (φ₁ φ₂ : ℝ → ℝ) (y z : ℝ) : ℝ :=
  deriv φ₁ y * deriv φ₂ z - deriv φ₁ z * deriv φ₂ y

/-- The differential kernel condition for two arbitrary additive statistics. -/
def TripleKernel (domain : Set ℝ) (d₁ d₂ de : ℝ → ℝ) : Prop :=
  ∀ x ∈ domain, ∀ y ∈ domain, ∀ z ∈ domain, ∀ a b c : ℝ,
    d₁ x * a + d₁ y * b + d₁ z * c = 0 →
    d₂ x * a + d₂ y * b + d₂ z * c = 0 →
    de x * a + de y * b + de z * c = 0

/-- The cross product of the two statistic rows is a kernel vector. -/
theorem kernel_determinant (ax ay az bx b_y bz ex ey ez : ℝ)
    (h : ∀ a b c : ℝ, ax * a + ay * b + az * c = 0 →
      bx * a + b_y * b + bz * c = 0 → ex * a + ey * b + ez * c = 0) :
    ex * (ay * bz - az * b_y) + ey * (az * bx - ax * bz) +
      ez * (ax * b_y - ay * bx) = 0 := by
  apply h <;> ring

/-- Two independent anchors determine the same coefficients at a third input. -/
theorem slope_of_kernel (ax ay az bx b_y bz ex ey ez : ℝ)
    (hdet : ay * bz - az * b_y ≠ 0)
    (h : ∀ a b c : ℝ, ax * a + ay * b + az * c = 0 →
      bx * a + b_y * b + bz * c = 0 → ex * a + ey * b + ez * c = 0) :
    ex = (ey * bz - ez * b_y) / (ay * bz - az * b_y) * ax +
      (ay * ez - az * ey) / (ay * bz - az * b_y) * bx := by
  have hd := kernel_determinant ax ay az bx b_y bz ex ey ez h
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
  apply (eq_div_iff hdet).2
  linear_combination hd

/-- Kernel annihilation gives fixed coefficients over the entire source domain. -/
theorem global_slopes (domain : Set ℝ) (d₁ d₂ de : ℝ → ℝ)
    (hk : TripleKernel domain d₁ d₂ de) {y z : ℝ}
    (hy : y ∈ domain) (hz : z ∈ domain)
    (hdet : d₁ y * d₂ z - d₁ z * d₂ y ≠ 0) :
    ∃ α β : ℝ, ∀ x ∈ domain, de x = α * d₁ x + β * d₂ x := by
  refine ⟨(de y * d₂ z - de z * d₂ y) / (d₁ y * d₂ z - d₁ z * d₂ y),
    (d₁ y * de z - d₁ z * de y) / (d₁ y * d₂ z - d₁ z * d₂ y), ?_⟩
  intro x hx
  exact slope_of_kernel _ _ _ _ _ _ _ _ _ hdet (hk x hx y hy z hz)

/-- Integrate a two-statistic derivative relation, including both endpoints. -/
theorem affine_of_derivative_relation {a b α β : ℝ} {φ₁ φ₂ e : ℝ → ℝ}
    (h₁ : ContinuousOn φ₁ (Icc a b)) (h₂ : ContinuousOn φ₂ (Icc a b))
    (he : ContinuousOn e (Icc a b))
    (hd₁ : DifferentiableOn ℝ φ₁ (Ioo a b))
    (hd₂ : DifferentiableOn ℝ φ₂ (Ioo a b))
    (hde : DifferentiableOn ℝ e (Ioo a b))
    (hrel : ∀ x ∈ Ioo a b, deriv e x = α * deriv φ₁ x + β * deriv φ₂ x) :
    ∃ c : ℝ, ∀ x ∈ Icc a b, e x = c + α * φ₁ x + β * φ₂ x := by
  let f : ℝ → ℝ := fun x => e x - α * φ₁ x - β * φ₂ x
  have hfc : ContinuousOn f (Icc a b) :=
    (he.sub (continuousOn_const.mul h₁)).sub (continuousOn_const.mul h₂)
  have hfd : ∀ x ∈ Ioo a b, HasDerivAt f 0 x := by
    intro x hx
    have hxe := ((hde x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
    have hx₁ := ((hd₁ x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
    have hx₂ := ((hd₂ x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
    convert (hxe.sub (hx₁.const_mul α)).sub (hx₂.const_mul β) using 1
    rw [hrel x hx]
    ring
  refine ⟨f a, ?_⟩
  intro x hx
  have hh := DifferentialRigidity.constant_on_closed_interval hfc hfd x hx
  dsimp [f] at hh ⊢
  linarith

/-- Independence of `1, φ₁, φ₂`, stated without choosing a coordinate basis. -/
def NotInAffineLine (domain : Set ℝ) (φ₁ φ₂ : ℝ → ℝ) : Prop :=
  ¬ ∃ A B C : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧
    ∀ x ∈ domain, A * φ₁ x + B * φ₂ x = C

/-- The derivative of any fixed linear combination vanishes when all tangents
are annihilated by the same nonzero covector. -/
theorem constant_combination_of_zero_derivative {a b A B : ℝ} {φ₁ φ₂ : ℝ → ℝ}
    (h₁ : ContinuousOn φ₁ (Icc a b)) (h₂ : ContinuousOn φ₂ (Icc a b))
    (hd₁ : DifferentiableOn ℝ φ₁ (Ioo a b))
    (hd₂ : DifferentiableOn ℝ φ₂ (Ioo a b))
    (hz : ∀ x ∈ Ioo a b, A * deriv φ₁ x + B * deriv φ₂ x = 0) :
    ∀ x ∈ Icc a b, A * φ₁ x + B * φ₂ x = A * φ₁ a + B * φ₂ a := by
  apply DifferentialRigidity.constant_on_closed_interval
    ((continuousOn_const.mul h₁).add (continuousOn_const.mul h₂))
  intro x hx
  have hx₁ := ((hd₁ x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
  have hx₂ := ((hd₂ x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
  simpa only [hz x hx] using (hx₁.const_mul A).add (hx₂.const_mul B)

/-- A continuous interior-differentiable curve outside every affine line has
an independent pair of interior tangents. No endpoint derivatives are needed. -/
theorem independent_tangents {a b : ℝ} {φ₁ φ₂ : ℝ → ℝ}
    (h₁ : ContinuousOn φ₁ (Icc a b)) (h₂ : ContinuousOn φ₂ (Icc a b))
    (hd₁ : DifferentiableOn ℝ φ₁ (Ioo a b))
    (hd₂ : DifferentiableOn ℝ φ₂ (Ioo a b))
    (hind : NotInAffineLine (Icc a b) φ₁ φ₂) :
    ∃ y ∈ Ioo a b, ∃ z ∈ Ioo a b, tangentDet φ₁ φ₂ y z ≠ 0 := by
  classical
  by_contra h
  have hzero : ∀ y ∈ Ioo a b, ∀ z ∈ Ioo a b,
      deriv φ₁ y * deriv φ₂ z - deriv φ₁ z * deriv φ₂ y = 0 := by
    intro y hy z hz
    by_contra hne
    exact h ⟨y, hy, z, hz, hne⟩
  by_cases hv : ∃ y ∈ Ioo a b, deriv φ₁ y ≠ 0 ∨ deriv φ₂ y ≠ 0
  · obtain ⟨y, hy, hny⟩ := hv
    have hrel : ∀ x ∈ Ioo a b,
        (-deriv φ₂ y) * deriv φ₁ x + deriv φ₁ y * deriv φ₂ x = 0 := by
      intro x hx
      nlinarith [hzero y hy x hx]
    apply hind
    refine ⟨-deriv φ₂ y, deriv φ₁ y, _, ?_,
      constant_combination_of_zero_derivative h₁ h₂ hd₁ hd₂ hrel⟩
    exact hny.elim (fun hh => Or.inr hh) (fun hh => Or.inl (neg_ne_zero.mpr hh))
  · have hrel : ∀ x ∈ Ioo a b, (1 : ℝ) * deriv φ₁ x + 0 * deriv φ₂ x = 0 := by
      intro x hx
      have hz : deriv φ₁ x = 0 := by
        by_contra hh
        exact hv ⟨x, hx, Or.inl hh⟩
      simp [hz]
    exact hind ⟨1, 0, _, Or.inl one_ne_zero,
      constant_combination_of_zero_derivative h₁ h₂ hd₁ hd₂ hrel⟩

/-- Scalar rigidity after differentiability and the two-statistic differential
kernel have been established. The nondegeneracy anchors are proved, not assumed. -/
theorem scalar_affine_of_kernel {a b : ℝ} {φ₁ φ₂ e : ℝ → ℝ}
    (h₁ : ContinuousOn φ₁ (Icc a b)) (h₂ : ContinuousOn φ₂ (Icc a b))
    (he : ContinuousOn e (Icc a b))
    (hd₁ : DifferentiableOn ℝ φ₁ (Ioo a b))
    (hd₂ : DifferentiableOn ℝ φ₂ (Ioo a b))
    (hde : DifferentiableOn ℝ e (Ioo a b))
    (hind : NotInAffineLine (Icc a b) φ₁ φ₂)
    (hk : TripleKernel (Ioo a b) (deriv φ₁) (deriv φ₂) (deriv e)) :
    ∃ c α β : ℝ, ∀ x ∈ Icc a b, e x = c + α * φ₁ x + β * φ₂ x := by
  obtain ⟨y, hy, z, hz, hdet⟩ := independent_tangents h₁ h₂ hd₁ hd₂ hind
  obtain ⟨α, β, hrel⟩ := global_slopes _ _ _ _ hk hy hz hdet
  obtain ⟨c, hc⟩ := affine_of_derivative_relation h₁ h₂ he hd₁ hd₂ hde hrel
  exact ⟨c, α, β, hc⟩



/-- The pair map for arbitrary two preprocessing functions. -/
def pairStatistic (φ₁ φ₂ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (φ₁ p.1 + φ₁ p.2, φ₂ p.1 + φ₂ p.2)

/-- Its two-by-two derivative. -/
def pairDerivative (ay az by' bz : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ay • ContinuousLinearMap.fst ℝ ℝ ℝ + az • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (by' • ContinuousLinearMap.fst ℝ ℝ ℝ + bz • ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem pairDerivative_apply (ay az by' bz : ℝ) (p : ℝ × ℝ) :
    pairDerivative ay az by' bz p = (ay * p.1 + az * p.2, by' * p.1 + bz * p.2) := rfl

lemma pairDerivative_injective {ay az by' bz : ℝ} (hd : ay * bz - az * by' ≠ 0) :
    Function.Injective (pairDerivative ay az by' bz) := by
  intro p q hpq
  have h₁ := congrArg Prod.fst hpq
  have h₂ := congrArg Prod.snd hpq
  simp only [pairDerivative_apply] at h₁ h₂
  have hx : (ay * bz - az * by') * (p.1 - q.1) = 0 := by
    linear_combination bz * h₁ - az * h₂
  have hy : (ay * bz - az * by') * (p.2 - q.2) = 0 := by
    linear_combination ay * h₂ - by' * h₁
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hd))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hd))

lemma pairDerivative_surjective {ay az by' bz : ℝ} (hd : ay * bz - az * by' ≠ 0) :
    Function.Surjective (pairDerivative ay az by' bz) := by
  intro p
  refine ⟨((bz * p.1 - az * p.2) / (ay * bz - az * by'),
    (ay * p.2 - by' * p.1) / (ay * bz - az * by')), ?_⟩
  apply Prod.ext <;> simp only [pairDerivative_apply]
  · rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
    apply (div_eq_iff hd).2
    ring
  · rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
    apply (div_eq_iff hd).2
    ring

def pairDerivativeEquiv (ay az by' bz : ℝ) (hd : ay * bz - az * by' ≠ 0) :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearEquiv.ofBijective (pairDerivative ay az by' bz)
    (LinearMap.ker_eq_bot.mpr (pairDerivative_injective hd))
    (LinearMap.range_eq_top.mpr (pairDerivative_surjective hd))

@[simp] lemma pairDerivativeEquiv_coe (ay az by' bz : ℝ) (hd : ay * bz - az * by' ≠ 0) :
    (pairDerivativeEquiv ay az by' bz hd : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) =
      pairDerivative ay az by' bz := ContinuousLinearEquiv.coe_ofBijective _ _ _

lemma pairStatistic_hasStrictFDerivAt {φ₁ φ₂ : ℝ → ℝ} {y z ay az by' bz : ℝ}
    (h₁y : HasStrictDerivAt φ₁ ay y) (h₁z : HasStrictDerivAt φ₁ az z)
    (h₂y : HasStrictDerivAt φ₂ by' y) (h₂z : HasStrictDerivAt φ₂ bz z) :
    HasStrictFDerivAt (pairStatistic φ₁ φ₂) (pairDerivative ay az by' bz) (y, z) := by
  have hfst : HasStrictFDerivAt (fun p : ℝ × ℝ => p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (y, z) := hasStrictFDerivAt_fst
  have hsnd : HasStrictFDerivAt (fun p : ℝ × ℝ => p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (y, z) := hasStrictFDerivAt_snd
  have h₁ := (h₁y.hasStrictFDerivAt.comp (y, z) hfst).add
    (h₁z.hasStrictFDerivAt.comp (y, z) hsnd)
  have h₂ := (h₂y.hasStrictFDerivAt.comp (y, z) hfst).add
    (h₂z.hasStrictFDerivAt.comp (y, z) hsnd)
  convert h₁.prodMk h₂ using 1
  ext <;> simp [pairDerivative, ContinuousLinearMap.comp_apply]

/-- The actual inverse function theorem supplies a local pair-statistic section
at every independent pair of strict derivatives. -/
theorem pairStatistic_local_section {φ₁ φ₂ : ℝ → ℝ} {y z ay az by' bz : ℝ}
    (h₁y : HasStrictDerivAt φ₁ ay y) (h₁z : HasStrictDerivAt φ₁ az z)
    (h₂y : HasStrictDerivAt φ₂ by' y) (h₂z : HasStrictDerivAt φ₂ bz z)
    (hdet : ay * bz - az * by' ≠ 0) :
    ∃ g : (ℝ × ℝ) → (ℝ × ℝ),
      DifferentiableAt ℝ g (pairStatistic φ₁ φ₂ (y, z)) ∧
      g (pairStatistic φ₁ φ₂ (y, z)) = (y, z) ∧
      ∀ᶠ p in 𝓝 (pairStatistic φ₁ φ₂ (y, z)), pairStatistic φ₁ φ₂ (g p) = p := by
  have hd : HasStrictFDerivAt (pairStatistic φ₁ φ₂)
      (pairDerivativeEquiv ay az by' bz hdet : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (y, z) := by
    simpa only [pairDerivativeEquiv_coe] using pairStatistic_hasStrictFDerivAt h₁y h₁z h₂y h₂z
  exact ⟨hd.localInverse (pairStatistic φ₁ φ₂) (pairDerivativeEquiv ay az by' bz hdet) (y, z),
    hd.to_localInverse.hasFDerivAt.differentiableAt,
    hd.localInverse_apply_image, hd.eventually_right_inverse⟩

/-- The sum of both prescribed statistics over a source triple. -/
def tripleStatistic (φ₁ φ₂ : ℝ → ℝ) (p : Triple) : ℝ × ℝ :=
  (tripleSum φ₁ p, tripleSum φ₂ p)

/-- Fixing one input converts a pair-statistic inverse into a triple section. -/
theorem triple_section_of_pair {φ₁ φ₂ : ℝ → ℝ} {x y z : ℝ}
    {g : (ℝ × ℝ) → (ℝ × ℝ)}
    (hg : DifferentiableAt ℝ g (pairStatistic φ₁ φ₂ (y, z)))
    (hgp : g (pairStatistic φ₁ φ₂ (y, z)) = (y, z))
    (hgr : ∀ᶠ p in 𝓝 (pairStatistic φ₁ φ₂ (y, z)), pairStatistic φ₁ φ₂ (g p) = p) :
    ∃ r : (ℝ × ℝ) → Triple,
      DifferentiableAt ℝ r (tripleStatistic φ₁ φ₂ (x, y, z)) ∧
      r (tripleStatistic φ₁ φ₂ (x, y, z)) = (x, y, z) ∧
      ∀ᶠ p in 𝓝 (tripleStatistic φ₁ φ₂ (x, y, z)), tripleStatistic φ₁ φ₂ (r p) = p := by
  let shift : (ℝ × ℝ) → (ℝ × ℝ) := fun p => (p.1 - φ₁ x, p.2 - φ₂ x)
  have hdshift : Differentiable ℝ shift :=
    (differentiable_fst.sub_const (φ₁ x)).prodMk (differentiable_snd.sub_const (φ₂ x))
  have hshift : shift (tripleStatistic φ₁ φ₂ (x, y, z)) = pairStatistic φ₁ φ₂ (y, z) := by
    apply Prod.ext <;> dsimp [shift, tripleStatistic, tripleSum, pairStatistic] <;> ring
  have hdcomp := (hshift.symm ▸ hg).comp _ hdshift.differentiableAt
  refine ⟨fun p => (x, g (shift p)), (differentiableAt_const x).prodMk hdcomp, ?_, ?_⟩
  · simp [hshift, hgp]
  · have hc : Tendsto shift (𝓝 (tripleStatistic φ₁ φ₂ (x, y, z)))
        (𝓝 (pairStatistic φ₁ φ₂ (y, z))) := by
      simpa only [ContinuousAt, hshift] using
        (hdshift (tripleStatistic φ₁ φ₂ (x, y, z))).continuousAt
    filter_upwards [hc hgr] with p hp
    have h₁ := congrArg Prod.fst hp
    have h₂ := congrArg Prod.snd hp
    apply Prod.ext
    · dsimp [pairStatistic, shift] at h₁
      dsimp [tripleStatistic, tripleSum]
      linarith
    · dsimp [pairStatistic, shift] at h₂
      dsimp [tripleStatistic, tripleSum]
      linarith

/-- The derivative kernel follows from actual local statistic fibers and a
local right section. There is no differentiability assumption on a decoder. -/
theorem triple_kernel_of_section {φ₁ φ₂ e : ℝ → ℝ} {x y z : ℝ}
    (h₁x : DifferentiableAt ℝ φ₁ x) (h₁y : DifferentiableAt ℝ φ₁ y)
    (h₁z : DifferentiableAt ℝ φ₁ z) (h₂x : DifferentiableAt ℝ φ₂ x)
    (h₂y : DifferentiableAt ℝ φ₂ y) (h₂z : DifferentiableAt ℝ φ₂ z)
    (hex : DifferentiableAt ℝ e x) (hey : DifferentiableAt ℝ e y)
    (hez : DifferentiableAt ℝ e z)
    {r : (ℝ × ℝ) → Triple} {U : Set Triple}
    (hr : DifferentiableAt ℝ r (tripleStatistic φ₁ φ₂ (x, y, z)))
    (hrp : r (tripleStatistic φ₁ φ₂ (x, y, z)) = (x, y, z))
    (hrr : ∀ᶠ p in 𝓝 (tripleStatistic φ₁ φ₂ (x, y, z)), tripleStatistic φ₁ φ₂ (r p) = p)
    (hU : U ∈ 𝓝 ((x, y, z) : Triple))
    (hf : ∀ p ∈ U, ∀ q ∈ U, tripleStatistic φ₁ φ₂ p = tripleStatistic φ₁ φ₂ q →
      tripleSum e p = tripleSum e q)
    {a b c : ℝ}
    (hk₁ : deriv φ₁ x * a + deriv φ₁ y * b + deriv φ₁ z * c = 0)
    (hk₂ : deriv φ₂ x * a + deriv φ₂ y * b + deriv φ₂ z * c = 0) :
    deriv e x * a + deriv e y * b + deriv e z * c = 0 := by
  have hm := (tripleSum_hasFDerivAt h₁x.hasDerivAt h₁y.hasDerivAt h₁z.hasDerivAt).prodMk
    (tripleSum_hasFDerivAt h₂x.hasDerivAt h₂y.hasDerivAt h₂z.hasDerivAt)
  have he := tripleSum_hasFDerivAt hex.hasDerivAt hey.hasDerivAt hez.hasDerivAt
  change HasFDerivAt (tripleStatistic φ₁ φ₂) _ _ at hm
  have hv : fderiv ℝ (tripleStatistic φ₁ φ₂) (x, y, z) (a, b, c) = 0 := by
    rw [hm.fderiv]
    apply Prod.ext
    · simpa [slopeRow_apply] using hk₁
    · simpa [slopeRow_apply] using hk₂
  have hh := fderiv_annihilates_of_local_section
    hm.differentiableAt he.differentiableAt hr hrp hrr hU hf hv
  simpa [he.fderiv, slopeRow_apply] using hh

/-- Local scalar fiber constancy at regular triples, stated only where an
independent tangent pair makes the statistic map a submersion. -/
def LocalStatisticFibers (domain : Set ℝ) (φ₁ φ₂ e : ℝ → ℝ) : Prop :=
  ∀ x ∈ domain, ∀ y ∈ domain, ∀ z ∈ domain, tangentDet φ₁ φ₂ y z ≠ 0 →
    ∃ U ∈ 𝓝 ((x, y, z) : Triple),
      ∀ p ∈ U, ∀ q ∈ U, tripleStatistic φ₁ φ₂ p = tripleStatistic φ₁ φ₂ q →
        tripleSum e p = tripleSum e q

/-- General scalar affine representation after local fiber constancy and
interior differentiability. The sections, derivative kernels, anchors,
constant coefficients, integration, and endpoint extension are all proved. -/
theorem scalar_affine_of_local_fibers {a b : ℝ} {φ₁ φ₂ e : ℝ → ℝ}
    (h₁ : ContinuousOn φ₁ (Icc a b)) (h₂ : ContinuousOn φ₂ (Icc a b))
    (he : ContinuousOn e (Icc a b))
    (hC₁ : ContDiffOn ℝ 1 φ₁ (Ioo a b))
    (hC₂ : ContDiffOn ℝ 1 φ₂ (Ioo a b))
    (hde : DifferentiableOn ℝ e (Ioo a b))
    (hind : NotInAffineLine (Icc a b) φ₁ φ₂)
    (hf : LocalStatisticFibers (Ioo a b) φ₁ φ₂ e) :
    ∃ c α β : ℝ, ∀ x ∈ Icc a b, e x = c + α * φ₁ x + β * φ₂ x := by
  have hd₁ := hC₁.differentiableOn_one
  have hd₂ := hC₂.differentiableOn_one
  obtain ⟨y, hy, z, hz, hdet⟩ := independent_tangents h₁ h₂ hd₁ hd₂ hind
  have hs₁ : ∀ t ∈ Ioo a b, HasStrictDerivAt φ₁ (deriv φ₁ t) t := by
    intro t ht
    exact ((hC₁ t ht).contDiffAt (Ioo_mem_nhds ht.1 ht.2)).hasStrictDerivAt le_rfl
  have hs₂ : ∀ t ∈ Ioo a b, HasStrictDerivAt φ₂ (deriv φ₂ t) t := by
    intro t ht
    exact ((hC₂ t ht).contDiffAt (Ioo_mem_nhds ht.1 ht.2)).hasStrictDerivAt le_rfl
  obtain ⟨g, hg, hgp, hgr⟩ := pairStatistic_local_section
    (hs₁ y hy) (hs₁ z hz) (hs₂ y hy) (hs₂ z hz) hdet
  let α := (deriv e y * deriv φ₂ z - deriv e z * deriv φ₂ y) / tangentDet φ₁ φ₂ y z
  let β := (deriv φ₁ y * deriv e z - deriv φ₁ z * deriv e y) / tangentDet φ₁ φ₂ y z
  have hrel : ∀ x ∈ Ioo a b, deriv e x = α * deriv φ₁ x + β * deriv φ₂ x := by
    intro x hx
    obtain ⟨r, hr, hrp, hrr⟩ := triple_section_of_pair (x := x) hg hgp hgr
    obtain ⟨U, hU, hfU⟩ := hf x hx y hy z hz hdet
    apply slope_of_kernel _ _ _ _ _ _ _ _ _ hdet
    intro u v w hku hkv
    exact triple_kernel_of_section
      (hs₁ x hx).hasDerivAt.differentiableAt (hs₁ y hy).hasDerivAt.differentiableAt
      (hs₁ z hz).hasDerivAt.differentiableAt (hs₂ x hx).hasDerivAt.differentiableAt
      (hs₂ y hy).hasDerivAt.differentiableAt (hs₂ z hz).hasDerivAt.differentiableAt
      ((hde x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2))
      ((hde y hy).differentiableAt (Ioo_mem_nhds hy.1 hy.2))
      ((hde z hz).differentiableAt (Ioo_mem_nhds hz.1 hz.2))
      hr hrp hrr hU hfU hku hkv
  obtain ⟨c, hc⟩ := affine_of_derivative_relation h₁ h₂ he hd₁ hd₂ hde hrel
  exact ⟨c, α, β, hc⟩



/-- Planar local constancy on regular statistic fibers. -/
def LocalPlanarStatisticFibers (domain : Set ℝ) (φ₁ φ₂ : ℝ → ℝ)
    (E : ℝ → ℝ × ℝ) : Prop :=
  ∀ x ∈ domain, ∀ y ∈ domain, ∀ z ∈ domain, tangentDet φ₁ φ₂ y z ≠ 0 →
    ∃ U ∈ 𝓝 ((x, y, z) : Triple),
      ∀ p ∈ U, ∀ q ∈ U, tripleStatistic φ₁ φ₂ p = tripleStatistic φ₁ φ₂ q →
        E p.1 + E p.2.1 + E p.2.2 = E q.1 + E q.2.1 + E q.2.2

/-- General planar rigidity through both source endpoints, conditional only
on the two still-separate analytic conclusions: encoder differentiability and
local constancy on regular statistic fibers. -/
theorem planar_affine_of_local_fibers {a b : ℝ} {φ₁ φ₂ : ℝ → ℝ}
    {E : ℝ → ℝ × ℝ}
    (h₁ : ContinuousOn φ₁ (Icc a b)) (h₂ : ContinuousOn φ₂ (Icc a b))
    (hE : ContinuousOn E (Icc a b))
    (hC₁ : ContDiffOn ℝ 1 φ₁ (Ioo a b))
    (hC₂ : ContDiffOn ℝ 1 φ₂ (Ioo a b))
    (hdE : DifferentiableOn ℝ E (Ioo a b))
    (hind : NotInAffineLine (Icc a b) φ₁ φ₂)
    (hf : LocalPlanarStatisticFibers (Ioo a b) φ₁ φ₂ E) :
    ∃ c u v : ℝ × ℝ, ∀ x ∈ Icc a b, E x = c + φ₁ x • u + φ₂ x • v := by
  have hfx : LocalStatisticFibers (Ioo a b) φ₁ φ₂ (fun x => (E x).1) := by
    intro x hx y hy z hz hd
    obtain ⟨U, hU, hfU⟩ := hf x hx y hy z hz hd
    refine ⟨U, hU, ?_⟩
    intro p hp q hq hm
    simpa only [tripleSum, Prod.fst_add] using congrArg Prod.fst (hfU p hp q hq hm)
  have hfy : LocalStatisticFibers (Ioo a b) φ₁ φ₂ (fun x => (E x).2) := by
    intro x hx y hy z hz hd
    obtain ⟨U, hU, hfU⟩ := hf x hx y hy z hz hd
    refine ⟨U, hU, ?_⟩
    intro p hp q hq hm
    simpa only [tripleSum, Prod.snd_add] using congrArg Prod.snd (hfU p hp q hq hm)
  obtain ⟨cx, ux, vx, hx⟩ := scalar_affine_of_local_fibers
    h₁ h₂ hE.fst hC₁ hC₂ hdE.fst hind hfx
  obtain ⟨cy, uy, vy, hy⟩ := scalar_affine_of_local_fibers
    h₁ h₂ hE.snd hC₁ hC₂ hdE.snd hind hfy
  refine ⟨(cx, cy), (ux, uy), (vx, vy), ?_⟩
  intro x hxi
  apply Prod.ext
  · simpa [mul_comm] using hx x hxi
  · simpa [mul_comm] using hy x hxi

/-- A local factorization, with any postprocessing map H, yields the fiber
constancy used above. No additional regularity of H is assumed. -/
theorem local_fibers_of_factorization {domain : Set ℝ} {φ₁ φ₂ : ℝ → ℝ}
    {E : ℝ → ℝ × ℝ}
    (hf : ∀ x ∈ domain, ∀ y ∈ domain, ∀ z ∈ domain,
      tangentDet φ₁ φ₂ y z ≠ 0 →
      ∃ U ∈ 𝓝 ((x, y, z) : Triple), ∃ H : (ℝ × ℝ) → (ℝ × ℝ),
        ∀ p ∈ U, E p.1 + E p.2.1 + E p.2.2 = H (tripleStatistic φ₁ φ₂ p)) :
    LocalPlanarStatisticFibers domain φ₁ φ₂ E := by
  intro x hx y hy z hz hd
  obtain ⟨U, hU, H, hH⟩ := hf x hx y hy z hz hd
  refine ⟨U, hU, ?_⟩
  intro p hp q hq hm
  rw [hH p hp, hH q hq, hm]



/-- Functional linear independence implies exclusion of every affine line. -/
theorem notInAffineLine_of_independent {domain : Set ℝ} {φ₁ φ₂ : ℝ → ℝ}
    (hind : ∀ c a b : ℝ, (∀ s ∈ domain, c + a * φ₁ s + b * φ₂ s = 0) →
      c = 0 ∧ a = 0 ∧ b = 0) : NotInAffineLine domain φ₁ φ₂ := by
  rintro ⟨a, b, c, hne, hline⟩
  have hz := hind (-c) a b (fun s hs => by have := hline s hs; linarith)
  exact hne.elim (fun hh => hh hz.2.1) (fun hh => hh hz.2.2)

/-- The image of interior triples with an independent pair of tangent columns.
Permuting a regular triple places such a pair in the last two positions. -/
def regularTripleImage (φ₁ φ₂ : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ x ∈ Ioo (-1 : ℝ) 1, ∃ y ∈ Ioo (-1 : ℝ) 1,
    ∃ z ∈ Ioo (-1 : ℝ) 1, tangentDet φ₁ φ₂ y z ≠ 0 ∧
      tripleStatistic φ₁ φ₂ (x, y, z) = p}

/-- The regular triple-statistic image is nonempty under the manuscript's
continuity, interior differentiability, and independence assumptions. -/
theorem regularTripleImage_nonempty {φ₁ φ₂ : ℝ → ℝ}
    (h₁ : ContinuousOn φ₁ (Icc (-1 : ℝ) 1))
    (h₂ : ContinuousOn φ₂ (Icc (-1 : ℝ) 1))
    (hd₁ : DifferentiableOn ℝ φ₁ (Ioo (-1 : ℝ) 1))
    (hd₂ : DifferentiableOn ℝ φ₂ (Ioo (-1 : ℝ) 1))
    (hind : NotInAffineLine (Icc (-1 : ℝ) 1) φ₁ φ₂) :
    (regularTripleImage φ₁ φ₂).Nonempty := by
  obtain ⟨y, hy, z, hz, hd⟩ := independent_tangents h₁ h₂ hd₁ hd₂ hind
  exact ⟨tripleStatistic φ₁ φ₂ (y, y, z), y, hy, y, hy, z, hz, hd, rfl⟩

/-- Every point of the regular image is represented by an actual valid triple,
with no convex-hull relaxation. -/
theorem regularTripleImage_valid {φ₁ φ₂ : ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ regularTripleImage φ₁ φ₂) :
    ∃ xs : List ℝ, ArbitraryEncoder.ValidInput 3 xs ∧
      AdditiveStatistics.statisticSum (fun s => (φ₁ s, φ₂ s)) xs = p := by
  obtain ⟨x, hx, y, hy, z, hz, _, hp⟩ := hp
  refine ⟨[x, y, z], ⟨rfl, ?_⟩, ?_⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨hx.1.le, hx.2.le⟩
    · exact ⟨hy.1.le, hy.2.le⟩
    · exact ⟨hz.1.le, hz.2.le⟩
  · rw [← hp]
    apply Prod.ext <;>
      simp [AdditiveStatistics.statisticSum, tripleStatistic, tripleSum, add_assoc]



/-- Pull a closure point back through a map that sends the source neighborhood
filter onto the target neighborhood filter, retaining any source neighborhood. -/
theorem closure_preimage_of_map_nhds {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {f : E → F} {x : E} {O : Set F} {S : Set E}
    (hm : Filter.map f (𝓝 x) = 𝓝 (f x)) (hx : f x ∈ closure O) (hS : S ∈ 𝓝 x) :
    x ∈ closure (S ∩ f ⁻¹' O) := by
  apply mem_closure_iff_nhds.mpr
  intro U hU
  have him : f '' (U ∩ S) ∈ 𝓝 (f x) := by
    rw [← hm]
    exact Filter.image_mem_map (inter_mem hU hS)
  obtain ⟨p, ⟨q, hq, hqp⟩, hp⟩ := mem_closure_iff_nhds.mp hx _ him
  exact ⟨q, hq.1, hq.2, by change f q ∈ O; rwa [hqp]⟩

/-- Vanishing on a set extends to a closure point under continuity at that
point; global continuity outside the source interval is not needed. -/
theorem zero_at_closure {E : Type*} [TopologicalSpace E] {f : E → ℝ} {x : E} {A : Set E}
    (hc : ContinuousAt f x) (hx : x ∈ closure A) (hz : ∀ a ∈ A, f a = 0) : f x = 0 := by
  by_contra hne
  obtain ⟨a, ha, hA⟩ := mem_closure_iff_nhds.mp hx _ (hc.eventually_ne hne)
  exact ha (hz a hA)

/-- Admissible pairs with independent statistic tangents. -/
def regularPairs (φ₁ φ₂ : ℝ → ℝ) : Set (ℝ × ℝ) :=
  ((Ioo (-1 : ℝ) 1) ×ˢ (Ioo (-1 : ℝ) 1)) ∩
    {p | tangentDet φ₁ φ₂ p.1 p.2 ≠ 0}

lemma regularPairs_mem_nhds {φ₁ φ₂ : ℝ → ℝ} {y z : ℝ}
    (hC₁ : ContDiffOn ℝ 1 φ₁ (Ioo (-1 : ℝ) 1))
    (hC₂ : ContDiffOn ℝ 1 φ₂ (Ioo (-1 : ℝ) 1))
    (hy : y ∈ Ioo (-1 : ℝ) 1) (hz : z ∈ Ioo (-1 : ℝ) 1)
    (hd : tangentDet φ₁ φ₂ y z ≠ 0) : regularPairs φ₁ φ₂ ∈ 𝓝 (y, z) := by
  have h₁ := hC₁.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have h₂ := hC₂.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have h₁y := (h₁ y hy).continuousAt (Ioo_mem_nhds hy.1 hy.2)
  have h₁z := (h₁ z hz).continuousAt (Ioo_mem_nhds hz.1 hz.2)
  have h₂y := (h₂ y hy).continuousAt (Ioo_mem_nhds hy.1 hy.2)
  have h₂z := (h₂ z hz).continuousAt (Ioo_mem_nhds hz.1 hz.2)
  have hdet : ContinuousAt (fun p : ℝ × ℝ => tangentDet φ₁ φ₂ p.1 p.2) (y, z) := by
    unfold tangentDet
    fun_prop
  exact inter_mem (prod_mem_nhds (Ioo_mem_nhds hy.1 hy.2) (Ioo_mem_nhds hz.1 hz.2))
    (hdet.eventually_ne hd)

/-- A fixed first input and independent anchor pair are approximated by
regular pairs whose triple statistic lies in the dense identifying set O.
Density is used on the actual regular triple image, not on the whole plane. -/
theorem regular_pair_identifying_closure {φ₁ φ₂ : ℝ → ℝ} {x y z : ℝ}
    {O : Set (ℝ × ℝ)}
    (hC₁ : ContDiffOn ℝ 1 φ₁ (Ioo (-1 : ℝ) 1))
    (hC₂ : ContDiffOn ℝ 1 φ₂ (Ioo (-1 : ℝ) 1))
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1)
    (hz : z ∈ Ioo (-1 : ℝ) 1) (hd : tangentDet φ₁ φ₂ y z ≠ 0)
    (hdense : regularTripleImage φ₁ φ₂ ⊆ closure O) :
    (y, z) ∈ closure (regularPairs φ₁ φ₂ ∩
      (fun p : ℝ × ℝ => tripleStatistic φ₁ φ₂ (x, p.1, p.2)) ⁻¹' O) := by
  have hs₁ : ∀ t ∈ Ioo (-1 : ℝ) 1, HasStrictDerivAt φ₁ (deriv φ₁ t) t := by
    intro t ht
    exact ((hC₁ t ht).contDiffAt (Ioo_mem_nhds ht.1 ht.2)).hasStrictDerivAt le_rfl
  have hs₂ : ∀ t ∈ Ioo (-1 : ℝ) 1, HasStrictDerivAt φ₂ (deriv φ₂ t) t := by
    intro t ht
    exact ((hC₂ t ht).contDiffAt (Ioo_mem_nhds ht.1 ht.2)).hasStrictDerivAt le_rfl
  have hp := pairStatistic_hasStrictFDerivAt (hs₁ y hy) (hs₁ z hz) (hs₂ y hy) (hs₂ z hz)
  have hf : HasStrictFDerivAt
      (fun p : ℝ × ℝ => tripleStatistic φ₁ φ₂ (x, p.1, p.2))
      (pairDerivative (deriv φ₁ y) (deriv φ₁ z) (deriv φ₂ y) (deriv φ₂ z)) (y, z) := by
    convert hp.const_add (φ₁ x, φ₂ x) using 1
    ext p <;> simp [tripleStatistic, tripleSum, pairStatistic, add_assoc]
  apply closure_preimage_of_map_nhds
    (hf.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr (pairDerivative_surjective hd)))
    (hdense ⟨x, hx, y, hy, z, hz, hd, rfl⟩)
    (regularPairs_mem_nhds hC₁ hC₂ hy hz hd)

/-- The encoded derivative row has zero determinant with both statistic rows
at any locally constant regular statistic fiber. -/
theorem determinant_of_local_fibers {φ₁ φ₂ e : ℝ → ℝ} {x y z : ℝ}
    (h₁x : DifferentiableAt ℝ φ₁ x) (h₂x : DifferentiableAt ℝ φ₂ x)
    (h₁y : HasStrictDerivAt φ₁ (deriv φ₁ y) y)
    (h₁z : HasStrictDerivAt φ₁ (deriv φ₁ z) z)
    (h₂y : HasStrictDerivAt φ₂ (deriv φ₂ y) y)
    (h₂z : HasStrictDerivAt φ₂ (deriv φ₂ z) z)
    (hex : DifferentiableAt ℝ e x) (hey : DifferentiableAt ℝ e y)
    (hez : DifferentiableAt ℝ e z)
    (hd : tangentDet φ₁ φ₂ y z ≠ 0) {U : Set Triple}
    (hU : U ∈ 𝓝 ((x, y, z) : Triple))
    (hf : ∀ p ∈ U, ∀ q ∈ U, tripleStatistic φ₁ φ₂ p = tripleStatistic φ₁ φ₂ q →
      tripleSum e p = tripleSum e q) :
    deriv e x * tangentDet φ₁ φ₂ y z +
      deriv e y * tangentDet φ₁ φ₂ z x +
      deriv e z * tangentDet φ₁ φ₂ x y = 0 := by
  obtain ⟨g, hg, hgp, hgr⟩ := pairStatistic_local_section h₁y h₁z h₂y h₂z hd
  obtain ⟨r, hr, hrp, hrr⟩ := triple_section_of_pair (x := x) hg hgp hgr
  apply kernel_determinant
  intro a b c ha hb
  exact triple_kernel_of_section h₁x h₁y.hasDerivAt.differentiableAt
    h₁z.hasDerivAt.differentiableAt h₂x h₂y.hasDerivAt.differentiableAt
    h₂z.hasDerivAt.differentiableAt hex hey hez hr hrp hrr hU hf ha hb

/-- Cramer's formula from the determinant relation. -/
theorem slope_of_determinant (ax ay az bx b_y bz ex ey ez : ℝ)
    (hdet : ay * bz - az * b_y ≠ 0)
    (hd : ex * (ay * bz - az * b_y) + ey * (az * bx - ax * bz) +
      ez * (ax * b_y - ay * bx) = 0) :
    ex = (ey * bz - ez * b_y) / (ay * bz - az * b_y) * ax +
      (ay * ez - az * ey) / (ay * bz - az * b_y) * bx := by
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
  apply (eq_div_iff hdet).2
  linear_combination hd



/-- The determinant relations need hold only over the dense identifying
statistic set. Local submersion and derivative continuity propagate them to
fixed anchors, giving a global affine representation without strengthening
that density hypothesis. -/
theorem scalar_affine_of_dense_determinants {φ₁ φ₂ e : ℝ → ℝ} {O : Set (ℝ × ℝ)}
    (h₁ : ContinuousOn φ₁ (Icc (-1 : ℝ) 1))
    (h₂ : ContinuousOn φ₂ (Icc (-1 : ℝ) 1))
    (he : ContinuousOn e (Icc (-1 : ℝ) 1))
    (hC₁ : ContDiffOn ℝ 1 φ₁ (Ioo (-1 : ℝ) 1))
    (hC₂ : ContDiffOn ℝ 1 φ₂ (Ioo (-1 : ℝ) 1))
    (hCe : ContDiffOn ℝ 1 e (Ioo (-1 : ℝ) 1))
    (hind : NotInAffineLine (Icc (-1 : ℝ) 1) φ₁ φ₂)
    (hdense : regularTripleImage φ₁ φ₂ ⊆ closure O)
    (hzero : ∀ x ∈ Ioo (-1 : ℝ) 1, ∀ y ∈ Ioo (-1 : ℝ) 1,
      ∀ z ∈ Ioo (-1 : ℝ) 1, tangentDet φ₁ φ₂ y z ≠ 0 →
      tripleStatistic φ₁ φ₂ (x, y, z) ∈ O →
      deriv e x * tangentDet φ₁ φ₂ y z +
        deriv e y * tangentDet φ₁ φ₂ z x +
        deriv e z * tangentDet φ₁ φ₂ x y = 0) :
    ∃ c α β : ℝ, ∀ x ∈ Icc (-1 : ℝ) 1, e x = c + α * φ₁ x + β * φ₂ x := by
  obtain ⟨y, hy, z, hz, hd⟩ := independent_tangents h₁ h₂
    hC₁.differentiableOn_one hC₂.differentiableOn_one hind
  let α := (deriv e y * deriv φ₂ z - deriv e z * deriv φ₂ y) / tangentDet φ₁ φ₂ y z
  let β := (deriv φ₁ y * deriv e z - deriv φ₁ z * deriv e y) / tangentDet φ₁ φ₂ y z
  have hslopes : ∀ x ∈ Ioo (-1 : ℝ) 1, deriv e x = α * deriv φ₁ x + β * deriv φ₂ x := by
    intro x hx
    let D : (ℝ × ℝ) → ℝ := fun q => deriv e x * tangentDet φ₁ φ₂ q.1 q.2 +
      deriv e q.1 * tangentDet φ₁ φ₂ q.2 x + deriv e q.2 * tangentDet φ₁ φ₂ x q.1
    have hcl := regular_pair_identifying_closure hC₁ hC₂ hx hy hz hd hdense
    have hcont : ContinuousAt D (y, z) := by
      have hdc₁ := hC₁.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
      have hdc₂ := hC₂.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
      have hdce := hCe.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
      have h₁y := (hdc₁ y hy).continuousAt (Ioo_mem_nhds hy.1 hy.2)
      have h₁z := (hdc₁ z hz).continuousAt (Ioo_mem_nhds hz.1 hz.2)
      have h₂y := (hdc₂ y hy).continuousAt (Ioo_mem_nhds hy.1 hy.2)
      have h₂z := (hdc₂ z hz).continuousAt (Ioo_mem_nhds hz.1 hz.2)
      have hey := (hdce y hy).continuousAt (Ioo_mem_nhds hy.1 hy.2)
      have hez := (hdce z hz).continuousAt (Ioo_mem_nhds hz.1 hz.2)
      dsimp [D, tangentDet]
      fun_prop
    have hzD : D (y, z) = 0 := by
      apply zero_at_closure hcont hcl
      intro q hq
      exact hzero x hx q.1 hq.1.1.1 q.2 hq.1.1.2 hq.1.2 hq.2
    exact slope_of_determinant _ _ _ _ _ _ _ _ _ hd hzD
  obtain ⟨c, hc⟩ := affine_of_derivative_relation h₁ h₂ he hC₁.differentiableOn_one
    hC₂.differentiableOn_one hCe.differentiableOn_one hslopes
  exact ⟨c, α, β, hc⟩

end Analog.GeneralRigidity
