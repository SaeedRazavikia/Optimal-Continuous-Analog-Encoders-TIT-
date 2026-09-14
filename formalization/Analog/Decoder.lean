import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

/-!
# Global scalar decoding

The McShane extension theorem identifies every feasible nonnegative uniform
decoding constant with a pairwise Lipschitz bound. The received map and the
input set are arbitrary; continuity and injectivity are not assumed. This file
also verifies clipping and the composition with a nonexpansive projection.
The explicit moment-strip projection formula and its sharp Gram-matrix
constant are separate results, not asserted here.
-/

namespace Analog.Decoder

open scoped NNReal

variable {X Y : Type*} [PseudoMetricSpace Y]

/-- A pairwise bound for target differences on the received set. -/
def PairwiseBound (r : X → Y) (f : X → ℝ) (L : ℝ≥0) : Prop :=
  ∀ x z, dist (f x) (f z) ≤ (L : ℝ) * dist (r x) (r z)

/-- One decoder has this bound for every input and every observation. -/
def UniformBound (r : X → Y) (f : X → ℝ) (L : ℝ≥0) (D : Y → ℝ) : Prop :=
  ∀ x y, dist (D y) (f x) ≤ (L : ℝ) * dist y (r x)

/-- A uniform guarantee includes exactness at every noiseless observation. -/
theorem uniform_exact {r : X → Y} {f : X → ℝ} {L : ℝ≥0} {D : Y → ℝ}
    (h : UniformBound r f L D) (x : X) : D (r x) = f x := by
  have hx := h x (r x)
  simpa using hx

/-- Comparing two noiseless observations gives the necessary pairwise bound. -/
theorem uniform_pairwise {r : X → Y} {f : X → ℝ} {L : ℝ≥0} {D : Y → ℝ}
    (h : UniformBound r f L D) : PairwiseBound r f L := by
  intro x z
  simpa only [uniform_exact h x] using h z (r x)

/-- A global Lipschitz exact decoder satisfies the disturbance bound. -/
theorem lipschitz_exact_uniform {r : X → Y} {f : X → ℝ} {L : ℝ≥0} {D : Y → ℝ}
    (hD : LipschitzWith L D) (hexact : ∀ x, D (r x) = f x) :
    UniformBound r f L D := by
  intro x y
  simpa only [hexact x] using hD.dist_le_mul y (r x)

/-- The pairwise condition is sufficient: the well-defined received-set
readout has a genuine global McShane extension with the same constant. -/
theorem pairwise_exists_lipschitz {r : X → Y} {f : X → ℝ} {L : ℝ≥0}
    (h : PairwiseBound r f L) :
    ∃ D : Y → ℝ, LipschitzWith L D ∧ ∀ x, D (r x) = f x := by
  classical
  have hfactor : f.FactorsThrough r := by
    intro x z hr
    have hxz := h x z
    simpa [hr] using hxz
  let g : Y → ℝ := Function.extend r f (fun _ => 0)
  have hg : ∀ x, g (r x) = f x := hfactor.extend_apply (fun _ => 0)
  have hglip : LipschitzOnWith L g (Set.range r) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro y ⟨x, rfl⟩ w ⟨z, rfl⟩
    simpa only [hg] using h x z
  obtain ⟨D, hD, hE⟩ := hglip.extend_real
  refine ⟨D, hD, fun x => ?_⟩
  exact (hE (Set.mem_range_self x)).symm.trans (hg x)

/-- Exact equivalence at each nonnegative constant, including zero. -/
theorem pairwise_iff_lipschitz_decoder (r : X → Y) (f : X → ℝ) (L : ℝ≥0) :
    PairwiseBound r f L ↔
      ∃ D : Y → ℝ, LipschitzWith L D ∧ ∀ x, D (r x) = f x := by
  constructor
  · exact pairwise_exists_lipschitz
  · rintro ⟨D, hD, hexact⟩
    exact uniform_pairwise (lipschitz_exact_uniform hD hexact)

/-- Uniform disturbance guarantees and pairwise bounds have exactly the
same feasible constants; no regularity is imposed on the decoder on the left. -/
theorem uniform_decoder_iff_pairwise (r : X → Y) (f : X → ℝ) (L : ℝ≥0) :
    (∃ D : Y → ℝ, UniformBound r f L D) ↔ PairwiseBound r f L := by
  constructor
  · rintro ⟨D, hD⟩
    exact uniform_pairwise hD
  · intro h
    obtain ⟨D, hD, he⟩ := pairwise_exists_lipschitz h
    exact ⟨D, lipschitz_exact_uniform hD he⟩

/-- Every feasible uniform constant has a continuous attaining decoder. -/
theorem pairwise_exists_continuous_uniform {r : X → Y} {f : X → ℝ} {L : ℝ≥0}
    (h : PairwiseBound r f L) :
    ∃ D : Y → ℝ, Continuous D ∧ UniformBound r f L D := by
  obtain ⟨D, hD, he⟩ := pairwise_exists_lipschitz h
  exact ⟨D, hD.continuous, lipschitz_exact_uniform hD he⟩

/-- Scalar clipping. -/
def clip (a b x : ℝ) : ℝ := max a (min b x)

theorem clip_lipschitz (a b : ℝ) : LipschitzWith 1 (clip a b) :=
  (LipschitzWith.id.const_min b).const_max a

theorem clip_fixed {a b x : ℝ} (ha : a ≤ x) (hb : x ≤ b) : clip a b x = x := by
  simp [clip, min_eq_right hb, max_eq_right ha]

/-- Clipping cannot increase error relative to a target inside the interval. -/
theorem clip_error {a b t : ℝ} (ha : a ≤ t) (hb : t ≤ b) (y : ℝ) :
    dist (clip a b y) t ≤ dist y t := by
  simpa only [clip_fixed ha hb, NNReal.coe_one, one_mul] using
    (clip_lipschitz a b).dist_le_mul y t

/-- Output clipping preserves the original constant for any decoder. -/
theorem clip_uniform {r : X → Y} {f : X → ℝ} {L : ℝ≥0} {D : Y → ℝ}
    (h : UniformBound r f L D) {a b : ℝ}
    (ha : ∀ x, a ≤ f x) (hb : ∀ x, f x ≤ b) :
    UniformBound r f L (fun y => clip a b (D y)) := by
  intro x y
  exact (clip_error (ha x) (hb x) (D y)).trans (h x y)

/-- A projection that fixes the received set and has Lipschitz constant one
preserves the guarantee of a readout that is Lipschitz on its image. -/
theorem projected_readout_uniform {r : X → Y} {f : X → ℝ} {L : ℝ≥0}
    (P : Y → Y) (g : Y → ℝ)
    (hP : LipschitzWith 1 P) (hfix : ∀ x, P (r x) = r x)
    (hg : LipschitzOnWith L g (Set.range P)) (he : ∀ x, g (r x) = f x) :
    UniformBound r f L (fun y => g (P y)) := by
  intro x y
  have hg' := hg.dist_le_mul (P y) (Set.mem_range_self y)
    (P (r x)) (Set.mem_range_self (r x))
  have hP' : dist (P y) (r x) ≤ dist y (r x) := by
    simpa only [hfix x, NNReal.coe_one, one_mul] using hP.dist_le_mul y (r x)
  calc
    dist (g (P y)) (f x) ≤ (L : ℝ) * dist (P y) (r x) := by
      simpa only [hfix x, he x] using hg'
    _ ≤ (L : ℝ) * dist y (r x) := mul_le_mul_of_nonneg_left hP' L.coe_nonneg

end Analog.Decoder
