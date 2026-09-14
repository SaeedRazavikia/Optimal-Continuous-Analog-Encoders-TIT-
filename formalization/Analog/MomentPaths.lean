import Analog.GeneralCollision
import Mathlib.Analysis.Convex.Deriv

/-! Actual finite-source paths realizing arbitrary tangent directions of the
first and feature moments. Only two transmitter inputs move. This construction
does not assume a local inverse for the moment map. -/

noncomputable section
open Set Filter
open scoped Topology

namespace Analog.MomentPaths
open Analog.ArbitraryEncoder Analog.GeneralCollision

def sourcePath (K : ℕ) (x y m a b t : ℝ) : List ℝ :=
  (x + a * t) :: (y + b * t) :: List.replicate (K - 2) m

lemma sourcePath_valid {K : ℕ} (hK : 2 ≤ K) (x y m a b t : ℝ)
    (hx : InSource (x + a * t)) (hy : InSource (y + b * t))
    (hm : InSource m) : ValidInput K (sourcePath K x y m a b t) := by
  constructor
  · simp only [sourcePath, List.length_cons, List.length_replicate]
    omega
  · intro z hz
    simp only [sourcePath, List.mem_cons, List.mem_replicate] at hz
    rcases hz with rfl | rfl | ⟨_, rfl⟩
    · exact hx
    · exact hy
    · exact hm

lemma sourcePath_eventually_valid {K : ℕ} (hK : 2 ≤ K) (x y m a b : ℝ)
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1)
    (hm : InSource m) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ValidInput K (sourcePath K x y m a b t) := by
  have hxc : ContinuousAt (fun t : ℝ => x + a * t) 0 := by fun_prop
  have hyc : ContinuousAt (fun t : ℝ => y + b * t) 0 := by fun_prop
  have hxe : ∀ᶠ t in 𝓝 (0 : ℝ), x + a * t ∈ Ioo (-1 : ℝ) 1 :=
    hxc (isOpen_Ioo.mem_nhds (by simpa using hx))
  have hye : ∀ᶠ t in 𝓝 (0 : ℝ), y + b * t ∈ Ioo (-1 : ℝ) 1 :=
    hyc (isOpen_Ioo.mem_nhds (by simpa using hy))
  filter_upwards [hxe, hye] with t ht hu
  exact sourcePath_valid hK x y m a b t ⟨ht.1.le, ht.2.le⟩ ⟨hu.1.le, hu.2.le⟩ hm

lemma firstMoment_sourcePath (K : ℕ) (x y m a b t : ℝ) :
    firstMoment (sourcePath K x y m a b t) =
      x + y + ((K - 2 : ℕ) : ℝ) * m + (a + b) * t := by
  simp [firstMoment, sourcePath, nsmul_eq_mul]
  ring

lemma featureMoment_sourcePath (K : ℕ) (φ : ℝ → ℝ) (x y m a b t : ℝ) :
    featureMoment φ (sourcePath K x y m a b t) =
      φ (x + a * t) + φ (y + b * t) + ((K - 2 : ℕ) : ℝ) * φ m := by
  simp [featureMoment, sourcePath, nsmul_eq_mul]
  ring

lemma firstMoment_sourcePath_hasDerivAt (K : ℕ) (x y m a b : ℝ) :
    HasDerivAt (fun t => firstMoment (sourcePath K x y m a b t)) (a + b) 0 := by
  simp only [firstMoment_sourcePath]
  simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (a + b)).const_add
    (x + y + ((K - 2 : ℕ) : ℝ) * m)

lemma featureMoment_sourcePath_hasDerivAt (K : ℕ) (φ : ℝ → ℝ)
    (x y m a b px py : ℝ) (hx : HasDerivAt φ px x) (hy : HasDerivAt φ py y) :
    HasDerivAt (fun t => featureMoment φ (sourcePath K x y m a b t))
      (px * a + py * b) 0 := by
  have ha : HasDerivAt (fun t : ℝ => x + a * t) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul a).const_add x
  have hb : HasDerivAt (fun t : ℝ => y + b * t) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul b).const_add y
  have hxa : HasDerivAt (fun t : ℝ => φ (x + a * t)) (px * a) 0 := by
    have hx' : HasDerivAt φ px (x + a * 0) := by simpa using hx
    exact hx'.comp 0 ha
  have hyb : HasDerivAt (fun t : ℝ => φ (y + b * t)) (py * b) 0 := by
    have hy' : HasDerivAt φ py (y + b * 0) := by simpa using hy
    exact hy'.comp 0 hb
  simp only [featureMoment_sourcePath]
  exact (hxa.add hyb).add_const _

lemma solve_moment_direction (px py dS dT : ℝ) (h : px ≠ py) :
    (dT - py * dS) / (px - py) + (px * dS - dT) / (px - py) = dS ∧
    px * ((dT - py * dS) / (px - py)) +
      py * ((px * dS - dT) / (px - py)) = dT := by
  have hd : px - py ≠ 0 := sub_ne_zero.mpr h
  constructor <;> field_simp <;> ring

/-- Every moment direction is realized by an actual admissible input path
through any two interior inputs whose feature derivatives differ. -/
theorem exists_source_path {K : ℕ} (hK : 2 ≤ K) (φ : ℝ → ℝ)
    (x y m px py dS dT : ℝ)
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1)
    (hm : InSource m) (hφx : HasDerivAt φ px x) (hφy : HasDerivAt φ py y)
    (hp : px ≠ py) :
    ∃ p : ℝ → List ℝ,
      ValidInput K (p 0) ∧ (∀ᶠ t in 𝓝 (0 : ℝ), ValidInput K (p t)) ∧
      firstMoment (p 0) = x + y + ((K - 2 : ℕ) : ℝ) * m ∧
      HasDerivAt (fun t => firstMoment (p t)) dS 0 ∧
      HasDerivAt (fun t => featureMoment φ (p t)) dT 0 := by
  let a := (dT - py * dS) / (px - py)
  let b := (px * dS - dT) / (px - py)
  have hs := solve_moment_direction px py dS dT hp
  refine ⟨sourcePath K x y m a b, ?_, ?_, ?_, ?_, ?_⟩
  · apply sourcePath_valid hK
    · simpa [InSource] using (show -1 ≤ x ∧ x ≤ 1 from ⟨hx.1.le, hx.2.le⟩)
    · simpa [InSource] using (show -1 ≤ y ∧ y ≤ 1 from ⟨hy.1.le, hy.2.le⟩)
    · exact hm
  · exact sourcePath_eventually_valid hK x y m a b hx hy hm
  · simp [firstMoment_sourcePath]
  · convert firstMoment_sourcePath_hasDerivAt K x y m a b using 1
    exact hs.1.symm
  · convert featureMoment_sourcePath_hasDerivAt K φ x y m a b px py hφx hφy using 1
    exact hs.2.symm

/-- Strict convexity or concavity makes all two distinct interior feature
slopes distinct, with no second derivative hypothesis. -/
theorem distinct_feature_slopes (φ : ℝ → ℝ)
    (hshape : StrictConvexOn ℝ (Ioo (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Ioo (-1 : ℝ) 1) φ)
    (hdiff : ∀ z ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ φ z)
    (x y : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1)
    (hxy : x < y) : deriv φ x ≠ deriv φ y := by
  rcases hshape with hc | hc
  · exact ne_of_lt (hc.strictMonoOn_deriv hdiff hx hy hxy)
  · exact ne_of_gt (hc.strictAntiOn_deriv hdiff hx hy hxy)

/-- At each interior empirical mean, actual finite source tuples realize
every first-order moment direction. The base mean is exactly prescribed,
which in particular permits passage to either endpoint mean. -/
theorem exists_source_path_at_mean {K : ℕ} (hK : 2 ≤ K) (φ : ℝ → ℝ)
    (hshape : StrictConvexOn ℝ (Ioo (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Ioo (-1 : ℝ) 1) φ)
    (hdiff : ∀ z ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ φ z)
    (m dS dT : ℝ) (hm : m ∈ Ioo (-1 : ℝ) 1) :
    ∃ p : ℝ → List ℝ,
      ValidInput K (p 0) ∧ (∀ᶠ t in 𝓝 (0 : ℝ), ValidInput K (p t)) ∧
      firstMoment (p 0) = (K : ℝ) * m ∧
      HasDerivAt (fun t => firstMoment (p t)) dS 0 ∧
      HasDerivAt (fun t => featureMoment φ (p t)) dT 0 := by
  let r := (1 - |m|) / 2
  have ham : |m| < 1 := abs_lt.mpr hm
  have hr : 0 < r := by dsimp [r]; linarith
  have hma := le_abs_self m
  have hmn := neg_abs_le m
  have hx : m - r ∈ Ioo (-1 : ℝ) 1 := by
    dsimp [r]
    constructor <;> linarith [abs_nonneg m]
  have hy : m + r ∈ Ioo (-1 : ℝ) 1 := by
    dsimp [r]
    constructor <;> linarith [abs_nonneg m]
  have hxy : m - r < m + r := by linarith
  obtain ⟨p, hp0, hp, hm0, hS, hT⟩ := exists_source_path hK φ (m-r) (m+r) m
    (deriv φ (m-r)) (deriv φ (m+r)) dS dT hx hy ⟨hm.1.le, hm.2.le⟩
    (hdiff _ hx).hasDerivAt (hdiff _ hy).hasDerivAt
    (distinct_feature_slopes φ hshape hdiff _ _ hx hy hxy)
  refine ⟨p, hp0, hp, ?_, hS, hT⟩
  rw [hm0, Nat.cast_sub hK]
  norm_num
  ring

/-- The closed-interval shape assumptions used by the score theorem imply
the same constructive tangent realization at every interior mean. -/
theorem realize_direction_at_mean {K : ℕ} (hK : 2 ≤ K) (φ : ℝ → ℝ)
    (hshape : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ)
    (hdiff : ∀ z ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ φ z)
    (m : ℝ) (hm : m ∈ Ioo (-1 : ℝ) 1) (dS dT : ℝ) :
    ∃ p : ℝ → List ℝ,
      ValidInput K (p 0) ∧ (∀ᶠ t in 𝓝 (0 : ℝ), ValidInput K (p t)) ∧
      firstMoment (p 0) = (K : ℝ) * m ∧
      HasDerivAt (fun t => firstMoment (p t)) dS 0 ∧
      HasDerivAt (fun t => featureMoment φ (p t)) dT 0 := by
  apply exists_source_path_at_mean hK φ _ hdiff m dS dT hm
  rcases hshape with hc | hc
  · exact Or.inl (hc.subset Ioo_subset_Icc_self (convex_Ioo _ _))
  · exact Or.inr (hc.subset Ioo_subset_Icc_self (convex_Ioo _ _))

end Analog.MomentPaths
