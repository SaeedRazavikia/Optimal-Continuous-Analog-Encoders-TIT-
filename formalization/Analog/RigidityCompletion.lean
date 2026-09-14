import Analog.DifferentialRigidity
import Analog.GeneralCollision
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# The finite-dimensional completion of encoder rigidity

The moment-neighborhood and coefficient-independence results below fill the
last step after an affine feature representation has been established. They
do not derive that representation for an arbitrary continuous encoder: the
topological and regularization steps remain separate obligations.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace Analog.RigidityCompletion
open Analog.ArbitraryEncoder Analog.GeneralCollision

/-- A planar encoder affine in the two sufficient statistics. -/
structure FeatureEncoder where
  c : ℝ × ℝ
  u : ℝ × ℝ
  v : ℝ × ℝ

def FeatureEncoder.encoder (e : FeatureEncoder) (φ : ℝ → ℝ) (s : ℝ) : ℝ × ℝ :=
  e.c + s • e.u + φ s • e.v

def FeatureEncoder.det (e : FeatureEncoder) : ℝ := e.u.1 * e.v.2 - e.u.2 * e.v.1

/-- The physical channel sum depends only on the two unnormalized moments. -/
theorem FeatureEncoder.received_encoder (e : FeatureEncoder) (φ : ℝ → ℝ)
    (xs : List ℝ) :
    received (e.encoder φ) xs =
      (xs.length : ℝ) • e.c + firstMoment xs • e.u + featureMoment φ xs • e.v := by
  induction xs with
  | nil => simp [received, firstMoment, featureMoment]
  | cons x xs ih =>
    simp only [received, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    apply Prod.ext <;>
      simp [FeatureEncoder.encoder, firstMoment, featureMoment, Nat.cast_add,
        Nat.cast_one, add_smul] <;> ring

/-- Nonzero determinant identifies both moments from equal channel sums. -/
theorem FeatureEncoder.collision_iff_moments (e : FeatureEncoder) (φ : ℝ → ℝ)
    (hdet : e.det ≠ 0) (xs ys : List ℝ) (hlen : xs.length = ys.length) :
    received (e.encoder φ) xs = received (e.encoder φ) ys ↔
      firstMoment xs = firstMoment ys ∧ featureMoment φ xs = featureMoment φ ys := by
  rw [e.received_encoder, e.received_encoder, hlen]
  constructor
  · intro h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hx hy
    have hS : e.det * (firstMoment xs - firstMoment ys) = 0 := by
      dsimp [FeatureEncoder.det]
      linear_combination e.v.2 * hx - e.v.1 * hy
    have hT : e.det * (featureMoment φ xs - featureMoment φ ys) = 0 := by
      dsimp [FeatureEncoder.det]
      linear_combination e.u.1 * hy - e.u.2 * hx
    exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hS).resolve_left hdet),
      sub_eq_zero.mp ((mul_eq_zero.mp hT).resolve_left hdet)⟩
  · rintro ⟨hS, hT⟩
    rw [hS, hT]

/-- Sufficiency in the rigidity theorem, for every feature/readout and every
transmitter count. Neither continuity nor a regular decoder is assumed. -/
theorem FeatureEncoder.exact_target (e : FeatureEncoder) (φ ψ : ℝ → ℝ)
    (hdet : e.det ≠ 0) (K : ℕ) : ExactTarget K φ ψ (e.encoder φ) := by
  intro xs ys hxs hys hr
  obtain ⟨hS, hT⟩ := (e.collision_iff_moments φ hdet xs ys
    (hxs.1.trans hys.1.symm)).mp hr
  simp only [target, hS, hT]

/-- The two-coordinate moment map used by the local rigidity chart. -/
def pairMoment (φ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 + p.2, φ p.1 + φ p.2)

def pairDerivative (dy dz : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ) + (ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
    (dy • (ContinuousLinearMap.fst ℝ ℝ ℝ) + dz • (ContinuousLinearMap.snd ℝ ℝ ℝ))

@[simp] theorem pairDerivative_apply (dy dz : ℝ) (p : ℝ × ℝ) :
    pairDerivative dy dz p = (p.1 + p.2, dy * p.1 + dz * p.2) := by
  rfl

theorem pairDerivative_injective {dy dz : ℝ} (h : dy ≠ dz) :
    Function.Injective (pairDerivative dy dz) := by
  intro p q hpq
  have h1 := congrArg Prod.fst hpq
  have h2 := congrArg Prod.snd hpq
  simp only [pairDerivative_apply] at h1 h2
  have hh : (dy - dz) * (p.1 - q.1) = 0 := by
    linear_combination h2 - dz * h1
  have hp : p.1 = q.1 := sub_eq_zero.mp
    ((mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr h))
  exact Prod.ext hp (by linarith)

theorem pairDerivative_surjective {dy dz : ℝ} (h : dy ≠ dz) :
    Function.Surjective (pairDerivative dy dz) := by
  intro p
  refine ⟨((p.2 - dz * p.1) / (dy - dz), (dy * p.1 - p.2) / (dy - dz)), ?_⟩
  apply Prod.ext <;> simp only [pairDerivative_apply] <;>
    field_simp [sub_ne_zero.mpr h] <;> ring

def pairDerivativeEquiv (dy dz : ℝ) (h : dy ≠ dz) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearEquiv.ofBijective (pairDerivative dy dz)
    (LinearMap.ker_eq_bot.mpr (pairDerivative_injective h))
    (LinearMap.range_eq_top.mpr (pairDerivative_surjective h))

@[simp] theorem pairDerivativeEquiv_coe (dy dz : ℝ) (h : dy ≠ dz) :
    (pairDerivativeEquiv dy dz h : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) =
      pairDerivative dy dz := by
  exact ContinuousLinearEquiv.coe_ofBijective _ _ _

theorem pairMoment_hasStrictFDerivAt {φ : ℝ → ℝ} {y z dy dz : ℝ}
    (hy : HasStrictDerivAt φ dy y) (hz : HasStrictDerivAt φ dz z) :
    HasStrictFDerivAt (pairMoment φ) (pairDerivative dy dz) (y, z) := by
  have h1 : HasStrictFDerivAt (fun p : ℝ × ℝ => p.1 + p.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ) + (ContinuousLinearMap.snd ℝ ℝ ℝ)) (y, z) :=
    hasStrictFDerivAt_fst.add hasStrictFDerivAt_snd
  have hfst : HasStrictFDerivAt (fun p : ℝ × ℝ => p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (y, z) := hasStrictFDerivAt_fst
  have hsnd : HasStrictFDerivAt (fun p : ℝ × ℝ => p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (y, z) := hasStrictFDerivAt_snd
  have h2 := (hy.hasStrictFDerivAt.comp (y, z) hfst).add
    (hz.hasStrictFDerivAt.comp (y, z) hsnd)
  convert h1.prodMk h2 using 1
  ext <;> simp [pairDerivative, ContinuousLinearMap.comp_apply]

/-- The pair moment map has a differentiable local right inverse at every
pair of distinct feature slopes. This is derived from the checked inverse
function theorem, rather than assumed as a moment-realizability condition. -/
theorem pairMoment_local_section {φ : ℝ → ℝ} {y z dy dz : ℝ}
    (hy : HasStrictDerivAt φ dy y) (hz : HasStrictDerivAt φ dz z) (hne : dy ≠ dz) :
    ∃ g : (ℝ × ℝ) → (ℝ × ℝ),
      DifferentiableAt ℝ g (pairMoment φ (y, z)) ∧
      g (pairMoment φ (y, z)) = (y, z) ∧
      ∀ᶠ p in 𝓝 (pairMoment φ (y, z)), pairMoment φ (g p) = p := by
  have hd : HasStrictFDerivAt (pairMoment φ)
      (pairDerivativeEquiv dy dz hne : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (y, z) := by
    simpa only [pairDerivativeEquiv_coe] using pairMoment_hasStrictFDerivAt hy hz
  refine ⟨hd.localInverse (pairMoment φ) (pairDerivativeEquiv dy dz hne) (y, z),
    hd.to_localInverse.hasFDerivAt.differentiableAt,
    hd.localInverse_apply_image, hd.eventually_right_inverse⟩

/-- Every sufficiently close pair of moments is realized by two admissible
inputs near the two anchors. The neighborhood is genuinely two-dimensional. -/
theorem pairMoment_neighborhood {φ : ℝ → ℝ} {y z dy dz : ℝ}
    (hy : HasStrictDerivAt φ dy y) (hz : HasStrictDerivAt φ dz z) (hne : dy ≠ dz)
    (hyi : y ∈ Ioo (-1 : ℝ) 1) (hzi : z ∈ Ioo (-1 : ℝ) 1) :
    ∃ ε > 0, ∀ S T : ℝ,
      |S - (y + z)| < ε → |T - (φ y + φ z)| < ε →
      ∃ a b : ℝ, InSource a ∧ InSource b ∧ a + b = S ∧ φ a + φ b = T := by
  let U : Set (ℝ × ℝ) := (Ioo (-1 : ℝ) 1) ×ˢ (Ioo (-1 : ℝ) 1)
  have hU : U ∈ 𝓝 (y, z) :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hyi, hzi⟩
  have hd := pairMoment_hasStrictFDerivAt hy hz
  have hmap := hd.map_nhds_eq_of_surj
    (LinearMap.range_eq_top.mpr (pairDerivative_surjective hne))
  have himage : pairMoment φ '' U ∈ 𝓝 (pairMoment φ (y, z)) := by
    rw [← hmap]
    exact Filter.image_mem_map hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp himage
  refine ⟨ε, hε, ?_⟩
  intro S T hS hT
  have hp : (S, T) ∈ Metric.ball (pairMoment φ (y, z)) ε := by
    simpa [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, pairMoment] using
      max_lt hS hT
  obtain ⟨⟨a, b⟩, hab, heq⟩ := hball hp
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg Prod.snd heq
  exact ⟨a, b, ⟨hab.1.1.le, hab.1.2.le⟩, ⟨hab.2.1.le, hab.2.2.le⟩, h1, h2⟩

/-- A rectangular neighborhood of actual triple moments. -/
def TripleMomentInterior (φ : ℝ → ℝ) : Prop :=
  ∃ S T ε : ℝ, 0 < ε ∧ ∀ S' T' : ℝ,
    |S' - S| < ε → |T' - T| < ε →
    ∃ xs : List ℝ, ValidInput 3 xs ∧ firstMoment xs = S' ∧ featureMoment φ xs = T'

/-- Distinct strict feature derivatives establish the actual triple-moment
interior required by the final coefficient-independence argument. -/
theorem tripleMomentInterior_of_strict_derivatives {φ : ℝ → ℝ} {y z dy dz : ℝ}
    (hy : HasStrictDerivAt φ dy y) (hz : HasStrictDerivAt φ dz z) (hne : dy ≠ dz)
    (hyi : y ∈ Ioo (-1 : ℝ) 1) (hzi : z ∈ Ioo (-1 : ℝ) 1) :
    TripleMomentInterior φ := by
  obtain ⟨ε, hε, hreal⟩ := pairMoment_neighborhood hy hz hne hyi hzi
  refine ⟨y + z, φ y + φ z + φ 0, ε, hε, ?_⟩
  intro S T hS hT
  obtain ⟨a, b, ha, hb, h1, h2⟩ := hreal S (T - φ 0) hS
    (by convert hT using 1; congr 1; ring)
  refine ⟨[a, b, 0], ?_, ?_, ?_⟩
  · constructor
    · rfl
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact ha
      · exact hb
      · norm_num [InSource]
  · simpa [firstMoment] using h1
  · simp only [featureMoment, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    linarith

/-- A singular pair of feature directions has a nonzero real kernel vector. -/
theorem FeatureEncoder.kernel_of_det_zero (e : FeatureEncoder) (hdet : e.det = 0) :
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
      e.u.1 * a + e.v.1 * b = 0 ∧ e.u.2 * a + e.v.2 * b = 0 := by
  dsimp [FeatureEncoder.det] at hdet
  by_cases hx : e.u.1 = 0
  · by_cases hy : e.u.2 = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hx], by simp [hy]⟩
    · refine ⟨e.v.2, -e.u.2, Or.inr (neg_ne_zero.mpr hy), ?_, by ring⟩
      nlinarith
  · exact ⟨e.v.1, -e.u.1, Or.inr (neg_ne_zero.mpr hx), by ring, by nlinarith⟩

/-- Injectivity on actual triple moments forces independent directions.
The only geometric input here is a neighborhood of realizable moments, not
an unproved invariance-of-domain assertion. -/
theorem FeatureEncoder.det_ne_zero_of_triple_injective (e : FeatureEncoder)
    (φ : ℝ → ℝ) (hinterior : TripleMomentInterior φ)
    (hinjective : ∀ xs ys : List ℝ, ValidInput 3 xs → ValidInput 3 ys →
      received (e.encoder φ) xs = received (e.encoder φ) ys →
      firstMoment xs = firstMoment ys ∧ featureMoment φ xs = featureMoment φ ys) :
    e.det ≠ 0 := by
  intro hdet
  obtain ⟨a, b, hab, h1, h2⟩ := e.kernel_of_det_zero hdet
  obtain ⟨S, T, ε, hε, hreal⟩ := hinterior
  let d : ℝ := |a| + |b| + 1
  have hd : 0 < d := by dsimp [d]; positivity
  let t : ℝ := ε / d
  have ht : 0 < t := div_pos hε hd
  have ha : |t * a| < ε := by
    rw [abs_mul, abs_of_pos ht]
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hd).2
    dsimp [d]
    nlinarith [abs_nonneg b]
  have hb : |t * b| < ε := by
    rw [abs_mul, abs_of_pos ht]
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hd).2
    dsimp [d]
    nlinarith [abs_nonneg a]
  obtain ⟨xs, hxs, hS, hT⟩ := hreal S T (by simpa using hε) (by simpa using hε)
  obtain ⟨ys, hys, hS', hT'⟩ := hreal (S + t * a) (T + t * b)
    (by simpa using ha) (by simpa using hb)
  have hr : received (e.encoder φ) xs = received (e.encoder φ) ys := by
    rw [e.received_encoder, e.received_encoder, hxs.1, hys.1, hS, hS', hT, hT']
    apply Prod.ext <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    · nlinarith [h1]
    · nlinarith [h2]
  obtain ⟨hcS, hcT⟩ := hinjective xs ys hxs hys hr
  rw [hS, hS'] at hcS
  rw [hT, hT'] at hcT
  have ha0 : a = 0 := (mul_eq_zero.mp (show t * a = 0 by linarith)).resolve_left ht.ne'
  have hb0 : b = 0 := (mul_eq_zero.mp (show t * b = 0 by linarith)).resolve_left ht.ne'
  exact hab.elim (fun h => h ha0) (fun h => h hb0)

/-- Necessity of independent feature directions for any exact affine-feature
encoder, using genuine strict derivatives at two interior anchors. -/
theorem FeatureEncoder.det_ne_zero_of_exact (e : FeatureEncoder)
    {K : ℕ} (hK : 4 ≤ K) (φ ψ : ℝ → ℝ)
    (hshape : StrictConvexOn ℝ (Ioo (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Ioo (-1 : ℝ) 1) ψ)
    (hexact : ExactTarget K φ ψ (e.encoder φ)) {y z dy dz : ℝ}
    (hy : HasStrictDerivAt φ dy y) (hz : HasStrictDerivAt φ dz z) (hne : dy ≠ dz)
    (hyi : y ∈ Ioo (-1 : ℝ) 1) (hzi : z ∈ Ioo (-1 : ℝ) 1) : e.det ≠ 0 := by
  apply e.det_ne_zero_of_triple_injective φ
    (tripleMomentInterior_of_strict_derivatives hy hz hne hyi hzi)
  exact triple_collision_preserves_moments hK φ ψ (e.encoder φ) hshape hexact

/-- The exactness equivalence is complete for affine-feature encoders.
Establishing affine-feature form for every continuous encoder remains the
separate continuous-rigidity obligation. -/
theorem FeatureEncoder.exact_iff_det_ne_zero (e : FeatureEncoder)
    {K : ℕ} (hK : 4 ≤ K) (φ ψ : ℝ → ℝ)
    (hshape : StrictConvexOn ℝ (Ioo (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Ioo (-1 : ℝ) 1) ψ)
    {y z dy dz : ℝ}
    (hy : HasStrictDerivAt φ dy y) (hz : HasStrictDerivAt φ dz z) (hne : dy ≠ dz)
    (hyi : y ∈ Ioo (-1 : ℝ) 1) (hzi : z ∈ Ioo (-1 : ℝ) 1) :
    ExactTarget K φ ψ (e.encoder φ) ↔ e.det ≠ 0 := by
  exact ⟨fun h => e.det_ne_zero_of_exact hK φ ψ hshape h hy hz hne hyi hzi,
    fun h => e.exact_target φ ψ h K⟩

/-- A continuous nonaffine C¹ feature has a two-dimensional neighborhood of
actual triple moments. Endpoint differentiability is not needed. -/
theorem tripleMomentInterior_of_nonaffine {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Icc (-1 : ℝ) 1))
    (hC1 : ContDiffOn ℝ 1 φ (Ioo (-1 : ℝ) 1))
    (hnonaffine : ¬ ∃ c a : ℝ, ∀ s ∈ Icc (-1 : ℝ) 1, φ s = c + a * s) :
    TripleMomentInterior φ := by
  obtain ⟨y, hy, z, hz, hne⟩ :=
    Analog.DifferentialRigidity.nonaffine_has_distinct_interior_slopes
      (by norm_num : (-1 : ℝ) < 1) hcont hC1.differentiableOn_one hnonaffine
  exact tripleMomentInterior_of_strict_derivatives
    ((hC1.contDiffAt (Ioo_mem_nhds hy.1 hy.2)).hasStrictDerivAt (by norm_num))
    ((hC1.contDiffAt (Ioo_mem_nhds hz.1 hz.2)).hasStrictDerivAt (by norm_num)) hne hy hz

/-- Under the original feature assumptions, exact computation by an affine
feature encoder is equivalent to independence of its two feature directions. -/
theorem FeatureEncoder.exact_iff_det_ne_zero_of_nonaffine (e : FeatureEncoder)
    {K : ℕ} (hK : 4 ≤ K) {φ ψ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Icc (-1 : ℝ) 1))
    (hC1 : ContDiffOn ℝ 1 φ (Ioo (-1 : ℝ) 1))
    (hnonaffine : ¬ ∃ c a : ℝ, ∀ s ∈ Icc (-1 : ℝ) 1, φ s = c + a * s)
    (hshape : StrictConvexOn ℝ (Ioo (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Ioo (-1 : ℝ) 1) ψ) :
    ExactTarget K φ ψ (e.encoder φ) ↔ e.det ≠ 0 := by
  constructor
  · intro hexact
    apply e.det_ne_zero_of_triple_injective φ
      (tripleMomentInterior_of_nonaffine hcont hC1 hnonaffine)
    exact triple_collision_preserves_moments hK φ ψ (e.encoder φ) hshape hexact
  · exact fun h => e.exact_target φ ψ h K

/-- Changing an encoder outside the source interval has no effect on the
physical channel for admissible input lists. -/
theorem received_congr_on_source {E F : ℝ → ℝ × ℝ}
    (hEF : ∀ s, InSource s → E s = F s) {K : ℕ} {xs : List ℝ}
    (hxs : ValidInput K xs) : received E xs = received F xs := by
  unfold received
  congr 1
  apply List.map_congr_left
  intro s hs
  exact hEF s (hxs.2 s hs)

/-- Exact target computation is unchanged when the encoder agrees on the
entire closed source interval. -/
theorem exactTarget_congr_on_source {K : ℕ} {φ ψ : ℝ → ℝ} {E F : ℝ → ℝ × ℝ}
    (hEF : ∀ s, InSource s → E s = F s) :
    ExactTarget K φ ψ E ↔ ExactTarget K φ ψ F := by
  have transfer {E F : ℝ → ℝ × ℝ} (hEF : ∀ s, InSource s → E s = F s)
      (he : ExactTarget K φ ψ E) : ExactTarget K φ ψ F := by
    intro xs ys hxs hys hr
    apply he xs ys hxs hys
    rw [received_congr_on_source hEF hxs, received_congr_on_source hEF hys]
    exact hr
  exact ⟨transfer hEF, transfer (fun s hs => (hEF s hs).symm)⟩

/-- The final necessity step of rigidity is now complete after the actual
interior differentiability and tangent-kernel conclusions have been supplied.
It includes both source endpoints and proves independence, rather than
assuming a nonsingular coefficient matrix. -/
theorem rigid_representation_of_differential_kernel
    {K : ℕ} (hK : 4 ≤ K) {φ ψ : ℝ → ℝ} {E : ℝ → ℝ × ℝ}
    (hφ : ContinuousOn φ (Icc (-1 : ℝ) 1))
    (hC1φ : ContDiffOn ℝ 1 φ (Ioo (-1 : ℝ) 1))
    (hE : ContinuousOn E (Icc (-1 : ℝ) 1))
    (hdE : DifferentiableOn ℝ E (Ioo (-1 : ℝ) 1))
    (hnonaffine : ¬ ∃ c a : ℝ, ∀ s ∈ Icc (-1 : ℝ) 1, φ s = c + a * s)
    (hshape : StrictConvexOn ℝ (Ioo (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Ioo (-1 : ℝ) 1) ψ)
    (hexact : ExactTarget K φ ψ E)
    (hkernelx : Analog.DifferentialRigidity.TripleKernelAnnihilation (Ioo (-1 : ℝ) 1)
      (deriv φ) (deriv fun s => (E s).1))
    (hkernely : Analog.DifferentialRigidity.TripleKernelAnnihilation (Ioo (-1 : ℝ) 1)
      (deriv φ) (deriv fun s => (E s).2)) :
    ∃ e : FeatureEncoder, e.det ≠ 0 ∧ ∀ s ∈ Icc (-1 : ℝ) 1, E s = e.encoder φ s := by
  obtain ⟨c, u, v, he⟩ := Analog.DifferentialRigidity.planar_differential_rigidity
    (by norm_num : (-1 : ℝ) < 1) hφ hE hC1φ.differentiableOn_one hdE
    hnonaffine hkernelx hkernely
  let e : FeatureEncoder := ⟨c, u, v⟩
  have hrep : ∀ s, InSource s → E s = e.encoder φ s := he
  have hexact' : ExactTarget K φ ψ (e.encoder φ) :=
    (exactTarget_congr_on_source hrep).mp hexact
  refine ⟨e, ?_, he⟩
  apply e.det_ne_zero_of_triple_injective φ (tripleMomentInterior_of_nonaffine hφ hC1φ hnonaffine)
  exact triple_collision_preserves_moments hK φ ψ (e.encoder φ) hshape hexact'

end Analog.RigidityCompletion
