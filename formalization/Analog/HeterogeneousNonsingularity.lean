import Analog.HeterogeneousCoordinates

/-!
# Nonsingularity of the common affine coefficient map

Local injectivity on a nonempty planar open set forces the common coefficient
matrix to be nonsingular.  The proof is independent of any regularity of the
receiver and uses only linearity and the presence of an open neighborhood.
-/

noncomputable section
namespace Analog.HeterogeneousNonsingularity
open Set Filter Topology

abbrev Plane := ℝ × ℝ

/-- The common coefficient map as an actual continuous linear map. -/
def coefficientMap (u v : Plane) : Plane →L[ℝ] Plane :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight u +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v

@[simp] theorem coefficientMap_apply (u v p : Plane) :
    coefficientMap u v p = p.1 • u + p.2 • v := rfl

/-- Injectivity of an affine map on any nonempty open set forces global
injectivity of its linear part. -/
theorem linear_injective_of_affine_injOn_open
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (c : F) {U : Set E}
    (hU : IsOpen U) (hne : U.Nonempty) (hinj : InjOn (fun p => c + L p) U) :
    Function.Injective L := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro w hw
  have hw' : L w = 0 := hw
  obtain ⟨x, hx⟩ := hne
  have hc : ContinuousAt (fun t : ℝ => x + t • w) 0 := by fun_prop
  have hn : {t : ℝ | x + t • w ∈ U} ∈ 𝓝 (0 : ℝ) := by
    have hh := hc (hU.mem_nhds (show x + (0 : ℝ) • w ∈ U by simpa using hx))
    exact hh
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp hn
  have ht : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have hsame : c + L x = c + L (x + (ε / 2) • w) := by
    simp [map_add, map_smul, hw']
  have heq := hinj hx (he ht) hsame
  have hsmul : (ε / 2) • w = 0 := by
    exact add_left_cancel (show x + (ε / 2) • w = x + 0 by simpa using heq.symm)
  exact (smul_eq_zero.mp hsmul).resolve_left (ne_of_gt (half_pos hε))

/-- The actual two-column determinant cannot vanish for an injective
coefficient map. -/
theorem determinant_ne_zero_of_injective (u v : Plane)
    (hinj : Function.Injective (coefficientMap u v)) :
    u.1 * v.2 - v.1 * u.2 ≠ 0 := by
  intro hdet
  have hker₁ : coefficientMap u v (v.1, -u.1) = coefficientMap u v 0 := by
    ext <;> simp [coefficientMap_apply] <;> nlinarith
  have hker₂ : coefficientMap u v (v.2, -u.2) = coefficientMap u v 0 := by
    ext <;> simp [coefficientMap_apply] <;> nlinarith
  have hp₁ := hinj hker₁
  have hp₂ := hinj hker₂
  have hu₁ : u.1 = 0 := by simpa using congrArg Prod.snd hp₁
  have hu₂ : u.2 = 0 := by simpa using congrArg Prod.snd hp₂
  have hu : u = 0 := Prod.ext hu₁ hu₂
  have hbad : coefficientMap u v (1, 0) = coefficientMap u v 0 := by simp [hu]
  have hh := congrArg Prod.fst (hinj hbad)
  norm_num at hh

/-- Nonsingularity from local affine injectivity, with no global injectivity
or full-dimensionality premise besides the stated nonempty open set. -/
theorem determinant_ne_zero_of_affine_injOn_open (u v c : Plane) {U : Set Plane}
    (hU : IsOpen U) (hne : U.Nonempty)
    (hinj : InjOn (fun p => c + p.1 • u + p.2 • v) U) :
    u.1 * v.2 - v.1 * u.2 ≠ 0 := by
  apply determinant_ne_zero_of_injective u v
  apply linear_injective_of_affine_injOn_open (coefficientMap u v) c hU hne
  simpa only [coefficientMap_apply, add_assoc] using hinj

/-- A local recovery implication supplies injectivity of the affine
coefficient map on every fixed-first-coordinate target slice of an actual
source coordinate chart. -/
theorem affine_injOn_of_coordinate_slice
    (L : OpenPartialHomeomorph (ℝ × Plane) (ℝ × Plane))
    (M E : (ℝ × Plane) → Plane) (u v c : Plane)
    (hcoord : ∀ p, L p = (p.1, M p))
    (haffine : ∀ p ∈ L.source, E p = c + (M p).1 • u + (M p).2 • v)
    (hrecover : ∀ p ∈ L.source, ∀ q ∈ L.source, E p = E q → M p = M q)
    (t : ℝ) (B : Set Plane) (hB : ∀ m ∈ B, (t, m) ∈ L.target) :
    InjOn (fun m => c + m.1 • u + m.2 • v) B := by
  intro m hm n hn heq
  have hmS := L.map_target (hB m hm)
  have hnS := L.map_target (hB n hn)
  have hmM : M (L.symm (t, m)) = m := by
    have hh := L.right_inv (hB m hm)
    rw [hcoord] at hh
    exact congrArg Prod.snd hh
  have hnM : M (L.symm (t, n)) = n := by
    have hh := L.right_inv (hB n hn)
    rw [hcoord] at hh
    exact congrArg Prod.snd hh
  have he : E (L.symm (t, m)) = E (L.symm (t, n)) := by
    rw [haffine _ hmS, haffine _ hnS, hmM, hnM]
    exact heq
  have hh := hrecover _ hmS _ hnS he
  simpa only [hmM, hnM] using hh

/-- Consequently the common coefficient matrix is nonsingular whenever an
actual local source chart has the recovery implication and affine encoder
formula on its source. The needed nonempty planar open slice is constructed. -/
theorem determinant_ne_zero_of_local_recovery
    (L : OpenPartialHomeomorph (ℝ × Plane) (ℝ × Plane))
    (M E : (ℝ × Plane) → Plane) (u v c : Plane)
    (hcoord : ∀ p, L p = (p.1, M p))
    (haffine : ∀ p ∈ L.source, E p = c + (M p).1 • u + (M p).2 • v)
    (hrecover : ∀ p ∈ L.source, ∀ q ∈ L.source, E p = E q → M p = M q)
    (p : ℝ × Plane) (hp : p ∈ L.source) :
    u.1 * v.2 - v.1 * u.2 ≠ 0 := by
  let B : Set Plane := {m | (p.1, m) ∈ L.target}
  have hBopen : IsOpen B :=
    L.open_target.preimage (continuous_const.prodMk continuous_id)
  have hBne : B.Nonempty := by
    refine ⟨M p, ?_⟩
    have hh := L.map_source hp
    simpa only [hcoord] using hh
  exact determinant_ne_zero_of_affine_injOn_open u v c hBopen hBne
    (affine_injOn_of_coordinate_slice L M E u v c hcoord haffine hrecover p.1 B
      (fun _ hm => hm))

end Analog.HeterogeneousNonsingularity
