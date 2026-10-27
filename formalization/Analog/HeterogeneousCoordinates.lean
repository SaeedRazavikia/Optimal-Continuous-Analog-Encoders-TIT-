import Analog.HeterogeneousRegularity

/-!
# Actual source coordinates for a regular heterogeneous triple

The map retaining the first input and both feature sums is a genuine local
homeomorphism whenever the last two feature tangents are independent.  This
follows from the inverse function theorem and does not assume any topological
factorization or regularity of the encoders.
-/

noncomputable section
namespace Analog.HeterogeneousCoordinates
open GeneralRigidity RigidityAnalysis HeterogeneousRegularity

/-- The first input and the two actual feature statistics. -/
def coordinates (a b c d e f : ℝ → ℝ) (p : Triple) : Triple :=
  (p.1, tripleStatistic a b c d e f p)

/-- The first feature tangent as a continuous linear column. -/
def tangentColumn (ax dx : ℝ) : ℝ →L[ℝ] (ℝ × ℝ) :=
  (ax • ContinuousLinearMap.id ℝ ℝ).prod (dx • ContinuousLinearMap.id ℝ ℝ)

/-- The triangular derivative is invertible precisely from independence of
the last two feature tangents. -/
def coordinatesDerivative (ax by₁ cz dx ey fz : ℝ)
    (hdet : by₁ * fz - cz * ey ≠ 0) : Triple ≃L[ℝ] Triple :=
  (ContinuousLinearEquiv.refl ℝ ℝ).skewProd
    (pairDerivativeEquiv by₁ cz ey fz hdet) (tangentColumn ax dx)

/-- Strict derivative of the actual augmented statistic map. -/
theorem coordinates_hasStrictFDerivAt {a b c d e f : ℝ → ℝ}
    {x y z ax by₁ cz dx ey fz : ℝ}
    (ha : HasStrictDerivAt a ax x) (hb : HasStrictDerivAt b by₁ y)
    (hc : HasStrictDerivAt c cz z) (hd : HasStrictDerivAt d dx x)
    (he : HasStrictDerivAt e ey y) (hf : HasStrictDerivAt f fz z)
    (hdet : by₁ * fz - cz * ey ≠ 0) :
    HasStrictFDerivAt (coordinates a b c d e f)
      (coordinatesDerivative ax by₁ cz dx ey fz hdet : Triple →L[ℝ] Triple) (x, y, z) := by
  have hfst : HasStrictFDerivAt (fun p : Triple => p.1)
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) (x, y, z) := hasStrictFDerivAt_fst
  have hsnd : HasStrictFDerivAt (fun p : Triple => p.2)
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) (x, y, z) := hasStrictFDerivAt_snd
  have hx := (ha.hasStrictFDerivAt.comp (x, y, z) hfst).prodMk
    (hd.hasStrictFDerivAt.comp (x, y, z) hfst)
  have hyz := (pairStatistic_hasStrictFDerivAt hb hc he hf).comp (x, y, z) hsnd
  have hp (q : ℝ × ℝ) : pairDerivativeEquiv by₁ cz ey fz hdet q =
      pairDerivative by₁ cz ey fz q := by
    change (pairDerivativeEquiv by₁ cz ey fz hdet : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) q = _
    rw [pairDerivativeEquiv_coe]
  convert hfst.prodMk (hyz.add hx) using 1
  · ext p <;> simp [coordinates, HeterogeneousRegularity.tripleStatistic,
      HeterogeneousRegularity.tripleSum, HeterogeneousRegularity.pairStatistic] <;> ring
  · ext <;>
      simp [coordinatesDerivative, tangentColumn, ContinuousLinearEquiv.skewProd_apply,
        hp, pairDerivative, ContinuousLinearMap.comp_apply]

/-- A genuine local coordinate chart from six strict scalar derivatives. Its
underlying map is exactly the first input together with the two feature sums. -/
theorem coordinates_localHomeomorph_of_strictDeriv {a b c d e f : ℝ → ℝ}
    {x y z ax by₁ cz dx ey fz : ℝ}
    (ha : HasStrictDerivAt a ax x) (hb : HasStrictDerivAt b by₁ y)
    (hc : HasStrictDerivAt c cz z) (hd : HasStrictDerivAt d dx x)
    (he : HasStrictDerivAt e ey y) (hf : HasStrictDerivAt f fz z)
    (hdet : by₁ * fz - cz * ey ≠ 0) :
    ∃ L : OpenPartialHomeomorph Triple Triple,
      (L : Triple → Triple) = coordinates a b c d e f ∧ (x, y, z) ∈ L.source := by
  have h := coordinates_hasStrictFDerivAt ha hb hc hd he hf hdet
  exact ⟨h.toOpenPartialHomeomorph _, h.toOpenPartialHomeomorph_coe,
    h.mem_toOpenPartialHomeomorph_source⟩

/-- The C¹ feature hypotheses in the manuscript supply the actual source
coordinate chart without any regularity hypothesis on transmitted encoders. -/
theorem coordinates_localHomeomorph {a b c d e f : ℝ → ℝ} {x y z : ℝ}
    (hx : ContDiffAt ℝ 1 (fun s => (a s, d s)) x)
    (hy : ContDiffAt ℝ 1 (fun s => (b s, e s)) y)
    (hz : ContDiffAt ℝ 1 (fun s => (c s, f s)) z)
    (hdet : deriv b y * deriv f z - deriv c z * deriv e y ≠ 0) :
    ∃ L : OpenPartialHomeomorph Triple Triple,
      (L : Triple → Triple) = (fun p => (p.1, tripleStatistic a b c d e f p)) ∧
      (x, y, z) ∈ L.source := by
  exact coordinates_localHomeomorph_of_strictDeriv
    (hx.fst.hasStrictDerivAt le_rfl) (hy.fst.hasStrictDerivAt le_rfl)
    (hz.fst.hasStrictDerivAt le_rfl) (hx.snd.hasStrictDerivAt le_rfl)
    (hy.snd.hasStrictDerivAt le_rfl) (hz.snd.hasStrictDerivAt le_rfl) hdet

end Analog.HeterogeneousCoordinates
