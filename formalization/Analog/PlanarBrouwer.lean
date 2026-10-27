/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license; see THIRD_PARTY_LICENSES/ClassificationOfSurfaces-LICENSE.
Authors: ClassificationOfSurfaces contributors

Adapted for Lean 4.24.0 from mccorvie/classification-of-surfaces,
commit e3c7230fe78d7b056a415d9ecae6f77887046b32,
ClassificationOfSurfaces/Moise/NoRetraction.lean and Moise/Brouwer.lean.
Only the ordinary closed-disk no-retraction and planar fixed-point chain is retained.
-/
import Mathlib

noncomputable section
namespace Analog.PlanarBrouwer

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/- The pinned mathlib has the local-homeomorphism theorem for the exponential
but predates its covering-map wrapper.  The following direct construction uses
the discrete kernel and a local inverse to trivialize each inverse image. -/
theorem circle_exp_isCoveringMap : IsCoveringMap Circle.exp := by
  let S : Set ℝ := {x | Circle.exp x = 1}
  have hsub : Set.Subsingleton (Circle.exp '' S) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ha.trans hb.symm
  letI : Subsingleton (Circle.exp '' S) := hsub.coe_sort
  letI : DiscreteTopology S :=
    isLocalHomeomorph_circleExp.isLocalHomeomorphOn.discreteTopology_of_image
  intro z
  obtain ⟨e, he, heq⟩ := isLocalHomeomorph_circleExp (Complex.arg z)
  have ez : z ∈ e.target := by
    rw [← Circle.exp_arg z, heq]
    exact e.map_source he
  have right_inv : ∀ y ∈ e.target, Circle.exp (e.symm y) = y := by
    intro y hy
    rw [heq]
    exact e.right_inv hy
  let H : (Circle.exp ⁻¹' e.target) ≃ₜ e.target × S :=
    { toFun := fun x =>
        (⟨Circle.exp x, x.2⟩,
          ⟨x - e.symm (Circle.exp x), by
            change Circle.exp ((x : ℝ) - e.symm (Circle.exp x)) = 1
            rw [Circle.exp_sub, right_inv _ x.2]
            simp⟩)
      invFun := fun y => ⟨e.symm y.1 + y.2, by
        change Circle.exp (e.symm y.1 + (y.2 : ℝ)) ∈ e.target
        rw [Circle.exp_add, y.2.2, mul_one, right_inv _ y.1.2]
        exact y.1.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simp
      right_inv := by
        intro y
        apply Prod.ext
        · apply Subtype.ext
          change Circle.exp (e.symm y.1 + (y.2 : ℝ)) = y.1
          rw [Circle.exp_add, y.2.2, mul_one, right_inv _ y.1.2]
        · apply Subtype.ext
          change e.symm y.1 + (y.2 : ℝ) -
            e.symm (Circle.exp (e.symm y.1 + (y.2 : ℝ))) = y.2
          rw [Circle.exp_add, y.2.2, mul_one, right_inv _ y.1.2]
          abel
      continuous_toFun := by
        have hc : Continuous fun x : Circle.exp ⁻¹' e.target => Circle.exp (x : ℝ) :=
          Circle.exp.continuous.comp continuous_subtype_val
        have hi : Continuous fun x : Circle.exp ⁻¹' e.target =>
            e.symm (Circle.exp (x : ℝ)) :=
          e.continuousOn_symm.comp_continuous hc (fun x => x.2)
        exact (hc.subtype_mk _).prodMk ((continuous_subtype_val.sub hi).subtype_mk _)
      continuous_invFun := by
        apply Continuous.subtype_mk
        have hi : Continuous fun y : e.target × S => e.symm (y.1 : Circle) :=
          e.continuousOn_symm.comp_continuous
            (continuous_subtype_val.comp continuous_fst) (fun y => y.1.2)
        exact hi.add (continuous_subtype_val.comp continuous_snd) }
  exact IsEvenlyCovered.to_isEvenlyCovered_preimage
    ⟨inferInstance, e.target, ez, e.open_target,
      e.open_target.preimage Circle.exp.continuous, H, fun _ => rfl⟩

open scoped Pointwise unitInterval

/-- The complex closed unit disk, used only as the standard model for the no-retraction
argument. -/
abbrev ClosedUnitDisk := Metric.closedBall (0 : ℂ) 1

/-- The boundary circle included in the closed unit disk. -/
def circleToClosedUnitDisk (z : Circle) : ClosedUnitDisk :=
  ⟨z, by
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [Circle.norm_coe]⟩

@[simp] theorem circleToClosedUnitDisk_coe (z : Circle) :
    (circleToClosedUnitDisk z : ℂ) = z :=
  rfl

theorem continuous_circleToClosedUnitDisk : Continuous circleToClosedUnitDisk := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

/-- The closed disk does not retract continuously onto its boundary circle. -/
theorem no_retraction_closedUnitDisk :
    ¬ ∃ r : ClosedUnitDisk → Circle,
      Continuous r ∧ ∀ z : Circle, r (circleToClosedUnitDisk z) = z := by
  rintro ⟨r, hr, hretract⟩
  letI : ContractibleSpace ClosedUnitDisk :=
    (convex_closedBall (0 : ℂ) 1).contractibleSpace ⟨0, by simp⟩
  letI : LocPathConnectedSpace ClosedUnitDisk :=
    (convex_closedBall (0 : ℂ) 1).locPathConnectedSpace
  let f : C(ClosedUnitDisk, Circle) := ⟨r, hr⟩
  let center : ClosedUnitDisk := ⟨0, by simp⟩
  let e₀ := Complex.arg (f center)
  have he₀ : Circle.exp e₀ = f center := Circle.exp_arg (f center)
  obtain ⟨F, hF, -⟩ :=
    circle_exp_isCoveringMap.existsUnique_continuousMap_lifts f center e₀ he₀
  have hFlifts : Circle.exp ∘ F = f := hF.2
  let γ : C(I, Circle) :=
    ⟨fun t => Circle.exp (2 * Real.pi * (t : ℝ)), by fun_prop⟩
  let Γ : C(I, ℝ) :=
    ⟨fun t => F (circleToClosedUnitDisk (γ t)),
      F.continuous.comp (continuous_circleToClosedUnitDisk.comp γ.continuous)⟩
  let Λ : C(I, ℝ) :=
    ⟨fun t => Γ 0 + 2 * Real.pi * (t : ℝ), by fun_prop⟩
  have hΓlift : Circle.exp ∘ Γ = γ := by
    funext t
    change Circle.exp (F (circleToClosedUnitDisk (γ t))) = γ t
    rw [show Circle.exp (F (circleToClosedUnitDisk (γ t))) =
      f (circleToClosedUnitDisk (γ t)) by exact congrFun hFlifts _]
    exact hretract (γ t)
  have hΛlift : Circle.exp ∘ Λ = γ := by
    funext t
    change Circle.exp (Γ 0 + 2 * Real.pi * (t : ℝ)) =
      Circle.exp (2 * Real.pi * (t : ℝ))
    rw [Circle.exp_add]
    have hΓ0 : Circle.exp (Γ 0) = 1 := by
      have h := congrFun hΓlift 0
      simpa [γ] using h
    rw [hΓ0, one_mul]
  have hΓ0 : Γ 0 = Λ 0 := by simp [Λ]
  have hΓeq : Γ = circle_exp_isCoveringMap.liftPath γ (Γ 0) (by
      simpa using (congrFun hΓlift 0).symm) :=
    (circle_exp_isCoveringMap.eq_liftPath_iff' (by
      simpa using (congrFun hΓlift 0).symm)).mpr ⟨hΓlift, rfl⟩
  have hΛeq : Λ = circle_exp_isCoveringMap.liftPath γ (Γ 0) (by
      simpa using (congrFun hΓlift 0).symm) :=
    (circle_exp_isCoveringMap.eq_liftPath_iff' (by
      simpa using (congrFun hΓlift 0).symm)).mpr ⟨hΛlift, hΓ0.symm⟩
  have hend : Γ 1 = Λ 1 := by rw [hΓeq, hΛeq]
  have hloop : Γ 1 = Γ 0 := by
    change F (circleToClosedUnitDisk (γ 1)) = F (circleToClosedUnitDisk (γ 0))
    congr 2
    apply Subtype.ext
    simp [γ]
  rw [hloop] at hend
  have hend' : Γ 0 = Γ 0 + 2 * Real.pi := by simp [Λ] at hend
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  apply hpi
  linarith

/-- The Euclidean plane and the complex plane are linearly isometric, using the orthonormal
basis `(1, I)` of `ℂ` over `ℝ`. -/
noncomputable abbrev planeComplexIsometry : Plane ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

/-- A complex unit direction, transported to the Euclidean plane, lies in the plane unit ball. -/
noncomputable def circleToPlaneClosedUnitBall (z : Circle) : Metric.closedBall (0 : Plane) 1 :=
  ⟨planeComplexIsometry.symm z, by
    rw [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map, Circle.norm_coe]⟩

/-- A point on the Euclidean unit sphere, transported to `ℂ`, is a point of `Circle`. -/
noncomputable def planeUnitSphereToCircle (x : Metric.sphere (0 : Plane) 1) : Circle :=
  ⟨planeComplexIsometry x, by
    exact show planeComplexIsometry (x : Plane) ∈ Metric.sphere (0 : ℂ) 1 from
      mem_sphere_zero_iff_norm.mpr (by
        rw [LinearIsometryEquiv.norm_map]
        exact mem_sphere_zero_iff_norm.mp x.2)⟩

@[simp] theorem planeUnitSphereToCircle_circleToPlaneClosedUnitBall (z : Circle) :
    planeUnitSphereToCircle
      ⟨(circleToPlaneClosedUnitBall z : Plane), by
        rw [mem_sphere_zero_iff_norm]
        change ‖planeComplexIsometry.symm (z : ℂ)‖ = 1
        rw [LinearIsometryEquiv.norm_map, Circle.norm_coe]⟩ = z := by
  apply Subtype.ext
  exact planeComplexIsometry.apply_symm_apply z

theorem continuous_circleToPlaneClosedUnitBall : Continuous circleToPlaneClosedUnitBall := by
  apply Continuous.subtype_mk
  exact planeComplexIsometry.symm.continuous.comp continuous_subtype_val

theorem continuous_planeUnitSphereToCircle : Continuous planeUnitSphereToCircle := by
  apply Continuous.subtype_mk
  exact planeComplexIsometry.continuous.comp continuous_subtype_val

/-- The linear isometry sends the complex unit disk to the plane unit ball. -/
noncomputable def complexDiskToPlaneClosedUnitBall
    (z : ClosedUnitDisk) : Metric.closedBall (0 : Plane) 1 :=
  ⟨planeComplexIsometry.symm z.1, by
    rw [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
    simpa [dist_zero_right] using Metric.mem_closedBall.mp z.2⟩

theorem continuous_complexDiskToPlaneClosedUnitBall :
    Continuous complexDiskToPlaneClosedUnitBall := by
  apply Continuous.subtype_mk
  exact planeComplexIsometry.symm.continuous.comp continuous_subtype_val

/-- The closed unit ball in the project's Euclidean plane does not retract onto its sphere. -/
theorem no_retraction_planeClosedUnitBall :
    ¬ ∃ r : Metric.closedBall (0 : Plane) 1 → Metric.sphere (0 : Plane) 1,
      Continuous r ∧
        ∀ z : Metric.sphere (0 : Plane) 1,
          r ⟨z.1, Metric.mem_closedBall.mpr z.2.le⟩ = z := by
  rintro ⟨r, hr, hretract⟩
  apply no_retraction_closedUnitDisk
  let r' : ClosedUnitDisk → Circle := fun z =>
    planeUnitSphereToCircle (r (complexDiskToPlaneClosedUnitBall z))
  refine ⟨r', ?_, ?_⟩
  · exact continuous_planeUnitSphereToCircle.comp
      (hr.comp continuous_complexDiskToPlaneClosedUnitBall)
  · intro z
    let zp : Metric.sphere (0 : Plane) 1 :=
      ⟨planeComplexIsometry.symm z, by
        rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, Circle.norm_coe]⟩
    change planeUnitSphereToCircle (r ⟨zp.1, Metric.mem_closedBall.mpr zp.2.le⟩) = z
    rw [hretract zp]
    exact planeUnitSphereToCircle_circleToPlaneClosedUnitBall z


open scoped InnerProductSpace

/-- The scale at which the ray from `p` through `x` meets the unit sphere.  Its intended use is
when `p` lies in the unit ball and `p ≠ x`. -/
noncomputable def fixedPointRayScale (p x : Plane) : ℝ :=
  let d := x - p
  let a := ⟪d, d⟫_ℝ
  let b := ⟪p, d⟫_ℝ
  (-b + Real.sqrt (b ^ 2 + a * (1 - ⟪p, p⟫_ℝ))) / a

private lemma fixedPointRayScale_mul_inner (p x : Plane) (hpx : p ≠ x) :
    ⟪x - p, x - p⟫_ℝ * fixedPointRayScale p x =
      -⟪p, x - p⟫_ℝ + Real.sqrt
        (⟪p, x - p⟫_ℝ ^ 2 + ⟪x - p, x - p⟫_ℝ * (1 - ⟪p, p⟫_ℝ)) := by
  rw [fixedPointRayScale]
  have hdenom : ⟪x - p, x - p⟫_ℝ ≠ 0 :=
    inner_self_ne_zero.mpr (sub_ne_zero.mpr hpx.symm)
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hdenom]

private lemma quadratic_root (a b c : ℝ) (ha : 0 < a) (hc : c ≤ 1) :
    a * ((-b + Real.sqrt (b ^ 2 + a * (1 - c))) / a) ^ 2 +
        2 * b * ((-b + Real.sqrt (b ^ 2 + a * (1 - c))) / a) + c = 1 := by
  let D := b ^ 2 + a * (1 - c)
  let t := (-b + Real.sqrt D) / a
  have hD : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg (sq_nonneg b) (mul_nonneg ha.le (sub_nonneg.mpr hc))
  have ht : a * t = -b + Real.sqrt D := by
    dsimp [t]
    field_simp [ha.ne']
  have hsqrt : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD
  change a * t ^ 2 + 2 * b * t + c = 1
  have htb : a * t + b = Real.sqrt D := by
    linarith
  calc
    a * t ^ 2 + 2 * b * t + c = ((a * t + b) ^ 2 - b ^ 2) / a + c := by
      field_simp [ha.ne']
      ring
    _ = (D - b ^ 2) / a + c := by rw [htb, hsqrt]
    _ = 1 := by
      dsimp [D]
      field_simp [ha.ne']
      ring

private lemma fixedPointRayScale_quadratic (p x : Plane) (hpx : p ≠ x)
    (hp : ‖p‖ ≤ 1) :
    ⟪x - p, x - p⟫_ℝ * fixedPointRayScale p x ^ 2 +
        2 * ⟪p, x - p⟫_ℝ * fixedPointRayScale p x + ⟪p, p⟫_ℝ = 1 := by
  have ha : 0 < ⟪x - p, x - p⟫_ℝ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr hpx.symm)
  have hc : ⟪p, p⟫_ℝ ≤ 1 := by
    rw [real_inner_self_eq_norm_sq]
    nlinarith [norm_nonneg p]
  simpa [fixedPointRayScale] using quadratic_root
    ⟪x - p, x - p⟫_ℝ ⟪p, x - p⟫_ℝ ⟪p, p⟫_ℝ ha hc

private lemma fixedPointRayEndpoint_mem_sphere (p x : Plane) (hpx : p ≠ x)
    (hp : ‖p‖ ≤ 1) :
    p + fixedPointRayScale p x • (x - p) ∈ Metric.sphere (0 : Plane) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hquad := fixedPointRayScale_quadratic p x hpx hp
  have hsq : ‖p + fixedPointRayScale p x • (x - p)‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [real_inner_comm p (x - p)]
    nlinarith [hquad]
  nlinarith [norm_nonneg (p + fixedPointRayScale p x • (x - p))]

private lemma fixedPointRayScale_eq_one_of_mem_sphere (p x : Plane) (hpx : p ≠ x)
    (hp : ‖p‖ ≤ 1) (hx : ‖x‖ = 1) :
    fixedPointRayScale p x = 1 := by
  let a := ⟪x - p, x - p⟫_ℝ
  let b := ⟪p, x - p⟫_ℝ
  let c := ⟪p, p⟫_ℝ
  let t := fixedPointRayScale p x
  have hroot : a * t ^ 2 + 2 * b * t + c = 1 := by
    simpa [a, b, c, t] using fixedPointRayScale_quadratic p x hpx hp
  have hxinner : ⟪x, x⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hx]
    norm_num
  have hrootOne : a + 2 * b + c = 1 := by
    rw [show x = p + (x - p) by abel] at hxinner
    simp only [inner_add_left, inner_add_right] at hxinner
    rw [real_inner_comm p (x - p)] at hxinner
    dsimp only [a, b, c]
    nlinarith [hxinner]
  let s : EuclideanGeometry.Sphere Plane := ⟨0, 1⟩
  have hxmem : x ∈ s := by
    change dist x (0 : Plane) = 1
    simpa [dist_zero_right] using hx
  have hple : dist p s.center ≤ s.radius := by
    simpa [s, dist_zero_right] using hp
  have hgeom : 0 < ⟪x - p, x⟫_ℝ := by
    simpa [s] using
      (EuclideanGeometry.inner_pos_or_eq_of_dist_le_radius hxmem hple).resolve_right hpx.symm
  have hab : 0 < a + b := by
    have hinner : ⟪x - p, x⟫_ℝ = a + b := by
      calc
        ⟪x - p, x⟫_ℝ = ⟪x - p, (x - p) + p⟫_ℝ := by
          congr 1
          abel
        _ = a + b := by
          rw [inner_add_right, real_inner_comm p (x - p)]
    rwa [hinner] at hgeom
  have ht : a * t = -b + Real.sqrt (b ^ 2 + a * (1 - c)) := by
    simpa [a, b, c, t] using fixedPointRayScale_mul_inner p x hpx
  have hfactor : 0 < a * (t + 1) + 2 * b := by
    nlinarith [Real.sqrt_nonneg (b ^ 2 + a * (1 - c))]
  have hprod : (t - 1) * (a * (t + 1) + 2 * b) = 0 := by
    nlinarith [hroot, hrootOne]
  have htOne : t = 1 := by
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · exact False.elim (hfactor.ne' h)
  exact htOne

private lemma continuous_fixedPointRayScale
    (f : Metric.closedBall (0 : Plane) 1 → Metric.closedBall (0 : Plane) 1)
    (hf : Continuous f) (hne : ∀ x, f x ≠ x) :
    Continuous fun x ↦ fixedPointRayScale (f x).1 x.1 := by
  have hfv : Continuous fun x ↦ (f x).1 := continuous_subtype_val.comp hf
  have hxv : Continuous fun x : Metric.closedBall (0 : Plane) 1 ↦ x.1 :=
    continuous_subtype_val
  have hd : Continuous fun x ↦ x.1 - (f x).1 := hxv.sub hfv
  have ha : Continuous fun x ↦ ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ := hd.inner hd
  have hb : Continuous fun x ↦ ⟪(f x).1, x.1 - (f x).1⟫_ℝ := hfv.inner hd
  have hc : Continuous fun x ↦ ⟪(f x).1, (f x).1⟫_ℝ := hfv.inner hfv
  have hdisc : Continuous fun x ↦
      ⟪(f x).1, x.1 - (f x).1⟫_ℝ ^ 2 +
        ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ * (1 - ⟪(f x).1, (f x).1⟫_ℝ) :=
    hb.pow 2 |>.add (ha.mul (continuous_const.sub hc))
  have hdenom : ∀ x, ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ ≠ 0 := by
    intro x
    apply inner_self_ne_zero.mpr
    apply sub_ne_zero.mpr
    intro h
    apply hne x
    exact Subtype.ext h.symm
  change Continuous fun x ↦
    (-⟪(f x).1, x.1 - (f x).1⟫_ℝ +
      Real.sqrt (⟪(f x).1, x.1 - (f x).1⟫_ℝ ^ 2 +
        ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ *
          (1 - ⟪(f x).1, (f x).1⟫_ℝ))) /
      ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ
  have hsqrt : Continuous fun x ↦
      Real.sqrt (⟪(f x).1, x.1 - (f x).1⟫_ℝ ^ 2 +
        ⟪x.1 - (f x).1, x.1 - (f x).1⟫_ℝ *
          (1 - ⟪(f x).1, (f x).1⟫_ℝ)) := by
    exact Real.continuous_sqrt.comp hdisc
  exact (hb.neg.add hsqrt).div ha hdenom

/-- Brouwer's fixed-point theorem for the closed unit disk in the Euclidean plane. -/
theorem brouwer_fixed_point_planeClosedUnitBall
    (f : Metric.closedBall (0 : Plane) 1 → Metric.closedBall (0 : Plane) 1)
    (hf : Continuous f) :
    ∃ x, f x = x := by
  by_contra hfixed
  have hne : ∀ x, f x ≠ x := by
    intro x hx
    exact hfixed ⟨x, hx⟩
  let r : Metric.closedBall (0 : Plane) 1 → Metric.sphere (0 : Plane) 1 := fun x ↦
    ⟨(f x).1 + fixedPointRayScale (f x).1 x.1 • (x.1 - (f x).1), by
      apply fixedPointRayEndpoint_mem_sphere
      · intro heq
        apply hne x
        exact Subtype.ext heq
      · have hp := (f x).2
        rw [Metric.mem_closedBall, dist_zero_right] at hp
        exact hp⟩
  apply no_retraction_planeClosedUnitBall
  refine ⟨r, ?_, ?_⟩
  · apply Continuous.subtype_mk
    have hfv : Continuous fun x ↦ (f x).1 := continuous_subtype_val.comp hf
    have hxv : Continuous fun x : Metric.closedBall (0 : Plane) 1 ↦ x.1 :=
      continuous_subtype_val
    exact hfv.add ((continuous_fixedPointRayScale f hf hne).smul (hxv.sub hfv))
  · intro z
    apply Subtype.ext
    let x : Metric.closedBall (0 : Plane) 1 :=
      ⟨z.1, Metric.mem_closedBall.mpr z.2.le⟩
    have hpx : (f x).1 ≠ z.1 := by
      intro heq
      apply hne x
      exact Subtype.ext heq
    have hp : ‖(f x).1‖ ≤ 1 := by
      have hp := (f x).2
      rw [Metric.mem_closedBall, dist_zero_right] at hp
      exact hp
    have hz : ‖z.1‖ = 1 := by
      exact mem_sphere_zero_iff_norm.mp z.2
    have hscale := fixedPointRayScale_eq_one_of_mem_sphere (f x).1 z.1 hpx hp hz
    change (f x).1 + fixedPointRayScale (f x).1 z.1 • (z.1 - (f x).1) = z.1
    rw [hscale, one_smul]
    abel

end Analog.PlanarBrouwer
