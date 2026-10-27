import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# Compact-defect stability

This file proves the compactness step in the approximate-rigidity argument.
A continuous nonnegative defect on a compact class, whose zero set lies in
the specified exact class, admits a constructed monotone stability modulus.
The exact class need not be closed. No modulus or convergence statement is
assumed.

For the manuscript's complex encoders, we also prove the finite-sum channel
estimate, actual pair-defect continuity, and Arzelà–Ascoli compactness of the
peak/common-modulus class. Identification of exact encoders with affine
moment curves remains a separate premise; this file does not prove
unrestricted continuous rigidity.
-/

noncomputable section
open Set Filter Topology Metric

namespace Analog.ApproximateRigidity

variable {X : Type*} [MetricSpace X]

/-- Distances attained by members of the compact class below a defect level,
with zero inserted to cover an empty sublevel. -/
def distanceValues (C A : Set X) (d : X → ℝ) (ε : ℝ) : Set ℝ :=
  insert 0 ((fun x => infDist x A) '' {x | x ∈ C ∧ d x ≤ ε})

/-- The actual stability modulus, defined by a supremum over the sublevel. -/
def modulus (C A : Set X) (d : X → ℝ) (ε : ℝ) : ℝ :=
  sSup (distanceValues C A d ε)

lemma distanceValues_nonempty (C A : Set X) (d : X → ℝ) (ε : ℝ) :
    (distanceValues C A d ε).Nonempty :=
  ⟨0, Set.mem_insert _ _⟩

lemma distanceValues_bddAbove {C : Set X} (hC : IsCompact C)
    (A : Set X) (d : X → ℝ) (ε : ℝ) :
    BddAbove (distanceValues C A d ε) := by
  have hb : BddAbove ((fun x => infDist x A) '' C) :=
    (hC.image (continuous_infDist_pt A)).bddAbove
  apply (hb.insert 0).mono
  intro y hy
  rcases hy with rfl | ⟨x, hx, rfl⟩
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨x, hx.1, rfl⟩

theorem modulus_nonneg {C : Set X} (hC : IsCompact C)
    (A : Set X) (d : X → ℝ) (ε : ℝ) :
    0 ≤ modulus C A d ε :=
  le_csSup (distanceValues_bddAbove hC A d ε) (Set.mem_insert _ _)

theorem modulus_bound {C A : Set X} (hC : IsCompact C)
    (d : X → ℝ) {ε : ℝ} {x : X} (hx : x ∈ C) (hdx : d x ≤ ε) :
    infDist x A ≤ modulus C A d ε :=
  le_csSup (distanceValues_bddAbove hC A d ε)
    (Set.mem_insert_of_mem _ ⟨x, ⟨hx, hdx⟩, rfl⟩)

theorem modulus_monotone {C : Set X} (hC : IsCompact C)
    (A : Set X) (d : X → ℝ) : Monotone (modulus C A d) := by
  intro ε δ hεδ
  apply csSup_le_csSup (distanceValues_bddAbove hC A d δ)
    (distanceValues_nonempty C A d ε)
  intro y hy
  rcases hy with rfl | ⟨x, hx, rfl⟩
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨x, ⟨hx.1, hx.2.trans hεδ⟩, rfl⟩

/-- Compactness turns pointwise positivity of the defect away from the exact
class into a uniform positive threshold. This is proved using a minimum on
the compact set at distance at least δ from that class. -/
theorem uniform_small_defect {C A : Set X} (hC : IsCompact C) (d : X → ℝ)
    (hd : ContinuousOn d C) (hd0 : ∀ x ∈ C, 0 ≤ d x)
    (hzero : ∀ x ∈ C, d x = 0 → x ∈ A)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ C, d x ≤ ε → infDist x A < δ := by
  let B : Set X := C ∩ {x | δ ≤ infDist x A}
  have hB : IsCompact B :=
    hC.inter_right (isClosed_le continuous_const (continuous_infDist_pt A))
  by_cases hne : B.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hB.exists_isMinOn hne (hd.mono inter_subset_left)
    have hxpos : 0 < d x := by
      apply lt_of_le_of_ne (hd0 x hx.1)
      intro hz
      have ha := hzero x hx.1 hz.symm
      have hi := infDist_zero_of_mem ha
      exact (not_le_of_gt hδ) (by simpa [hi] using hx.2)
    refine ⟨d x / 2, by positivity, ?_⟩
    intro y hy hdy
    by_contra hyδ
    have hyB : y ∈ B := ⟨hy, le_of_not_gt hyδ⟩
    have hxy : d x ≤ d y := hmin hyB
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx _
    by_contra hxδ
    exact hne ⟨x, hx, le_of_not_gt hxδ⟩

theorem modulus_zero {C A : Set X} (hC : IsCompact C) (d : X → ℝ)
    (hd0 : ∀ x ∈ C, 0 ≤ d x)
    (hzero : ∀ x ∈ C, d x = 0 → x ∈ A) : modulus C A d 0 = 0 := by
  apply le_antisymm _ (modulus_nonneg hC A d 0)
  apply csSup_le (distanceValues_nonempty C A d 0)
  intro y hy
  rcases hy with rfl | ⟨x, hx, rfl⟩
  · exact le_rfl
  · change infDist x A ≤ 0
    rw [infDist_zero_of_mem (hzero x hx.1 (le_antisymm hx.2 (hd0 x hx.1)))]

/-- The constructed modulus tends to zero. The stronger two-sided limit is
valid because nonnegative defects give empty negative sublevels. -/
theorem modulus_tendsto_zero {C A : Set X} (hC : IsCompact C) (d : X → ℝ)
    (hd : ContinuousOn d C) (hd0 : ∀ x ∈ C, 0 ≤ d x)
    (hzero : ∀ x ∈ C, d x = 0 → x ∈ A) :
    Tendsto (modulus C A d) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun ε => ha.trans_le (modulus_nonneg hC A d ε)
  · intro b hb
    obtain ⟨ε, hε, hsmall⟩ := uniform_small_defect hC d hd hd0 hzero
      (by linarith : 0 < b / 2)
    filter_upwards [Iio_mem_nhds hε] with δ hδ
    have hbound : modulus C A d δ ≤ b / 2 := by
      apply csSup_le (distanceValues_nonempty C A d δ)
      intro y hy
      rcases hy with rfl | ⟨x, hx, rfl⟩
      · linarith
      · exact (hsmall x hx.1 (hx.2.trans hδ.le)).le
    linarith

/-- A compact continuous-defect problem has a nonnegative nondecreasing
stability modulus vanishing at zero and controlling every admissible point.
No closedness of the exact class A is needed. -/
theorem exists_stability_modulus {C A : Set X} (hC : IsCompact C) (d : X → ℝ)
    (hd : ContinuousOn d C) (hd0 : ∀ x ∈ C, 0 ≤ d x)
    (hzero : ∀ x ∈ C, d x = 0 → x ∈ A) :
    ∃ η : ℝ → ℝ, Monotone η ∧ (∀ ε, 0 ≤ η ε) ∧ η 0 = 0 ∧
      Tendsto η (𝓝[≥] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      ∀ ε : ℝ, ∀ x ∈ C, d x ≤ ε → infDist x A ≤ η ε := by
  refine ⟨modulus C A d, modulus_monotone hC A d, modulus_nonneg hC A d,
    modulus_zero hC d hd0 hzero,
    (modulus_tendsto_zero hC d hd hd0 hzero).mono_left nhdsWithin_le_nhds, ?_⟩
  intro ε x hx hdx
  exact modulus_bound hC d hx hdx

section PairDefect

variable {S Y : Type*} [MetricSpace Y]

/-- The normalized positive collision defect for one actual source pair. -/
def pairTerm (r : X → S → Y) (f : S → ℝ) (L : ℝ) (x : X) (p : S × S) : ℝ :=
  max 0 ((|f p.1 - f p.2| - L * dist (r x p.1) (r x p.2)) / 2)

/-- The actual supremum over all source pairs. Moving the positive factor
one half inside the supremum gives the defect used in Appendix H. -/
def pairDefect (r : X → S → Y) (f : S → ℝ) (L : ℝ) (x : X) : ℝ :=
  sSup (insert 0 (Set.range (pairTerm r f L x)))

omit [MetricSpace X] in
lemma pairDefect_bddAbove (r : X → S → Y) (f : S → ℝ)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hf : ∀ s, |f s| ≤ M) (x : X) :
    BddAbove (insert 0 (Set.range (pairTerm r f L x))) := by
  refine ⟨M, ?_⟩
  intro y hy
  rcases hy with rfl | ⟨p, rfl⟩
  · exact hM
  · apply max_le hM
    have ha := abs_sub (f p.1) (f p.2)
    have hn : 0 ≤ L * dist (r x p.1) (r x p.2) := mul_nonneg hL dist_nonneg
    linarith [hf p.1, hf p.2]

omit [MetricSpace X] in
theorem pairDefect_nonneg (r : X → S → Y) (f : S → ℝ)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hf : ∀ s, |f s| ≤ M) (x : X) :
    0 ≤ pairDefect r f L x :=
  le_csSup (pairDefect_bddAbove r f hL hM hf x) (Set.mem_insert _ _)

omit [MetricSpace X] in
lemma pairTerm_le_defect (r : X → S → Y) (f : S → ℝ)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hf : ∀ s, |f s| ≤ M)
    (x : X) (p : S × S) : pairTerm r f L x p ≤ pairDefect r f L x :=
  le_csSup (pairDefect_bddAbove r f hL hM hf x)
    (Set.mem_insert_of_mem _ (Set.mem_range_self p))

/-- A uniform channel perturbation estimate gives the sharp Lipschitz
constant Lk for the normalized pair defect. -/
lemma pairDefect_le_add (r : X → S → Y) (f : S → ℝ)
    {L M k : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hk : 0 ≤ k)
    (hf : ∀ s, |f s| ≤ M)
    (hr : ∀ x y s, dist (r x s) (r y s) ≤ k * dist x y) (x y : X) :
    pairDefect r f L x ≤ pairDefect r f L y + L * k * dist x y := by
  have hn : 0 ≤ L * k * dist x y := mul_nonneg (mul_nonneg hL hk) dist_nonneg
  apply csSup_le (Set.insert_nonempty _ _)
  intro z hz
  rcases hz with rfl | ⟨p, rfl⟩
  · exact add_nonneg (pairDefect_nonneg r f hL hM hf y) hn
  · have hd : dist (r y p.1) (r y p.2) - dist (r x p.1) (r x p.2) ≤
        2 * k * dist x y := by
      have hh := dist_dist_dist_le (r x p.1) (r x p.2) (r y p.1) (r y p.2)
      rw [Real.dist_eq, abs_sub_comm] at hh
      have hh' := (le_abs_self _).trans hh
      linarith [hr x y p.1, hr x y p.2]
    have hmul := mul_le_mul_of_nonneg_left hd hL
    have hraw : ((|f p.1 - f p.2| - L * dist (r x p.1) (r x p.2)) / 2) ≤
        pairTerm r f L y p + L * k * dist x y := by
      have hmax := le_max_right 0
        ((|f p.1 - f p.2| - L * dist (r y p.1) (r y p.2)) / 2)
      change _ ≤ pairTerm r f L y p at hmax
      nlinarith only [hmul, hmax]
    have ht : pairTerm r f L x p ≤ pairTerm r f L y p + L * k * dist x y :=
      max_le (add_nonneg (le_max_left _ _) hn) hraw
    exact ht.trans (add_le_add_right (pairTerm_le_defect r f hL hM hf y p) _)

theorem pairDefect_lipschitz (r : X → S → Y) (f : S → ℝ)
    {L M k : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hk : 0 ≤ k)
    (hf : ∀ s, |f s| ≤ M)
    (hr : ∀ x y s, dist (r x s) (r y s) ≤ k * dist x y) :
    LipschitzWith ⟨L * k, mul_nonneg hL hk⟩ (pairDefect r f L) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  change |pairDefect r f L x - pairDefect r f L y| ≤ L * k * dist x y
  have hxy := pairDefect_le_add r f hL hM hk hf hr x y
  have hyx := pairDefect_le_add r f hL hM hk hf hr y x
  rw [dist_comm y x] at hyx
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [MetricSpace X] in
/-- A zero pair defect supplies exact computation, rather than requiring
the collision implication as an extra analytic assumption. -/
theorem exact_of_pairDefect_zero (r : X → S → Y) (f : S → ℝ)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hf : ∀ s, |f s| ≤ M)
    {x : X} (hx : pairDefect r f L x = 0) :
    ∀ s t, r x s = r x t → f s = f t := by
  intro s t hst
  have ht := (le_max_right 0 _).trans (pairTerm_le_defect r f hL hM hf x (s, t))
  rw [hx] at ht
  change (|f s - f t| - L * dist (r x s) (r x t)) / 2 ≤ 0 at ht
  rw [hst, dist_self, mul_zero, sub_zero] at ht
  have ha : |f s - f t| = 0 := le_antisymm (by linarith) (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp ha)

omit [MetricSpace X] in
/-- Approximation by an L-Lipschitz decoder controls the actual pair defect. -/
theorem pairDefect_le_approximation (r : X → S → Y) (f : S → ℝ)
    {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) {x : X} (D : Y → ℝ)
    (hD : LipschitzWith ⟨L, hL⟩ D)
    (happrox : ∀ s, |D (r x s) - f s| ≤ ε) :
    pairDefect r f L x ≤ ε := by
  apply csSup_le (Set.insert_nonempty _ _)
  intro y hy
  rcases hy with rfl | ⟨p, rfl⟩
  · exact hε
  · have ht₁ := dist_triangle (f p.1) (D (r x p.1)) (f p.2)
    have ht₂ := dist_triangle (D (r x p.1)) (D (r x p.2)) (f p.2)
    have hlip := hD.dist_le_mul (r x p.1) (r x p.2)
    rw [Real.dist_eq, Real.dist_eq, Real.dist_eq] at ht₁ ht₂
    rw [abs_sub_comm (f p.1) (D (r x p.1))] at ht₁
    rw [Real.dist_eq] at hlip
    change |D (r x p.1) - D (r x p.2)| ≤ L * dist (r x p.1) (r x p.2) at hlip
    apply max_le hε
    change (|f p.1 - f p.2| - L * dist (r x p.1) (r x p.2)) / 2 ≤ ε
    linarith [happrox p.1, happrox p.2]

/-- The compact-defect theorem applied to actual approximate computation.
The conclusion constructs the modulus and derives defect continuity from
the channel estimate. The remaining structural premise is precisely the
classification of exact encoders inside the compact class. -/
theorem exists_computation_modulus {C A : Set X} (hC : IsCompact C)
    (r : X → S → Y) (f : S → ℝ)
    {L M k : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hk : 0 ≤ k)
    (hf : ∀ s, |f s| ≤ M)
    (hr : ∀ x y s, dist (r x s) (r y s) ≤ k * dist x y)
    (hclass : ∀ x ∈ C, (∀ s t, r x s = r x t → f s = f t) → x ∈ A) :
    ∃ η : ℝ → ℝ, Monotone η ∧ (∀ ε, 0 ≤ η ε) ∧ η 0 = 0 ∧
      Tendsto η (𝓝[≥] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      ∀ ε : ℝ, 0 ≤ ε → ∀ x ∈ C, ∀ D : Y → ℝ,
        LipschitzWith ⟨L, hL⟩ D →
        (∀ s, |D (r x s) - f s| ≤ ε) → infDist x A ≤ η ε := by
  obtain ⟨η, hm, hn, hz, ht, hb⟩ := exists_stability_modulus hC (pairDefect r f L)
    (pairDefect_lipschitz r f hL hM hk hf hr).continuous.continuousOn
    (fun x _ => pairDefect_nonneg r f hL hM hf x)
    (fun x hx hd => hclass x hx (exact_of_pairDefect_zero r f hL hM hf hd))
  refine ⟨η, hm, hn, hz, ht, ?_⟩
  intro ε hε x hx D hD ha
  exact hb ε x hx (pairDefect_le_approximation r f hL hε D hD ha)

end PairDefect

section ContinuousEncoders

open BoundedContinuousFunction
open scoped BigOperators

/-- Closed calibrated source interval. -/
abbrev Source := Set.Icc (-1 : ℝ) 1

/-- Continuous encoders on the compact source interval, with their uniform
metric. Boundedness in the type is automatic for every continuous encoder
on this interval. -/
abbrev Encoder := Source →ᵇ ℂ

/-- The physical sum over all K simultaneously transmitted complex symbols. -/
def sourceSuperposition (K : ℕ) (E : Encoder) (s : Fin K → Source) : ℂ :=
  ∑ i, E (s i)

/-- The exact K-Lipschitz channel estimate in the encoder's uniform metric. -/
theorem sourceSuperposition_dist (K : ℕ) (E F : Encoder) (s : Fin K → Source) :
    dist (sourceSuperposition K E s) (sourceSuperposition K F s) ≤
      (K : ℝ) * dist E F := by
  apply (dist_sum_sum_le Finset.univ _ _).trans
  calc
    ∑ i : Fin K, dist (E (s i)) (F (s i)) ≤ ∑ _i : Fin K, dist E F :=
      Finset.sum_le_sum fun i _ => dist_coe_le_dist (s i)
    _ = (K : ℝ) * dist E F := by simp

/-- Peak-bounded encoders sharing the prescribed continuity modulus. -/
def encoderClass (P : ℝ) (ω : ℝ → ℝ) : Set Encoder :=
  {E | (∀ s, ‖E s‖ ≤ Real.sqrt P) ∧
    ∀ s t, dist (E s) (E t) ≤ ω (dist s t)}

theorem encoderClass_isClosed (P : ℝ) (ω : ℝ → ℝ) :
    IsClosed (encoderClass P ω) := by
  have hp : IsClosed {E : Encoder | ∀ s, ‖E s‖ ≤ Real.sqrt P} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun s =>
      isClosed_le continuous_eval_const.norm continuous_const
  have hw : IsClosed {E : Encoder | ∀ s t, dist (E s) (E t) ≤ ω (dist s t)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun t =>
      isClosed_le (continuous_eval_const.dist continuous_eval_const) continuous_const
  exact hp.inter hw

/-- The one-sided vanishing modulus from the manuscript gives uniform
equicontinuity; no condition on the arbitrary value ω(0) is required. -/
theorem encoderClass_equicontinuous (P : ℝ) (ω : ℝ → ℝ)
    (hω : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    Equicontinuous (fun E : encoderClass P ω => (E.val : Source → ℂ)) := by
  apply UniformEquicontinuous.equicontinuous
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  have hw := hω (Iio_mem_nhds hε)
  obtain ⟨V, hV, hVω⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hw
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨δ, hδ, ?_⟩
  intro s t hst E
  by_cases heq : s = t
  · simpa [heq] using hε
  · have hdV : dist s t ∈ V := hδV (by
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg dist_nonneg] using hst)
    have hsmall : ω (dist s t) < ε := hVω ⟨hdV, dist_pos.mpr heq⟩
    exact (E.property.2 s t).trans_lt hsmall

/-- Arzelà–Ascoli proves compactness of the actual peak/modulus encoder
class. The class's compactness is a conclusion, not an assumption. -/
theorem encoderClass_isCompact (P : ℝ) (ω : ℝ → ℝ)
    (hω : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    IsCompact (encoderClass P ω) := by
  apply BoundedContinuousFunction.arzela_ascoli₂
    (Metric.closedBall (0 : ℂ) (Real.sqrt P)) (isCompact_closedBall _ _)
    (encoderClass P ω) (encoderClass_isClosed P ω)
  · intro E s hE
    simpa [Metric.mem_closedBall, dist_zero_right] using hE.1 s
  · exact encoderClass_equicontinuous P ω hω

/-- Approximate computation on the full continuous encoder class has a
constructed stability modulus relative to any class containing all exact
encoders. The finite-sum estimate, defect regularity, and Arzelà–Ascoli
compactness are all derived. Applying this result to affine moment curves
still requires the separate unrestricted rigidity theorem. -/
theorem continuous_encoder_stability (K : ℕ) (P : ℝ) (ω : ℝ → ℝ)
    (hω : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (f : (Fin K → Source) → ℝ) (hf : Continuous f)
    {L : ℝ} (hL : 0 ≤ L) (A : Set Encoder)
    (hclass : ∀ E ∈ encoderClass P ω,
      (∀ s t, sourceSuperposition K E s = sourceSuperposition K E t → f s = f t) → E ∈ A) :
    ∃ η : ℝ → ℝ, Monotone η ∧ (∀ ε, 0 ≤ η ε) ∧ η 0 = 0 ∧
      Tendsto η (𝓝[≥] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      ∀ ε : ℝ, 0 ≤ ε → ∀ E ∈ encoderClass P ω, ∀ D : ℂ → ℝ,
        LipschitzWith ⟨L, hL⟩ D →
        (∀ s, |D (sourceSuperposition K E s) - f s| ≤ ε) → infDist E A ≤ η ε := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hb : ∀ s, |f s| ≤ max M 0 := by
    intro s
    exact (hM s (Set.mem_univ s)).trans (le_max_left _ _)
  exact exists_computation_modulus (encoderClass_isCompact P ω hω)
    (sourceSuperposition K) f hL (le_max_right _ _) (Nat.cast_nonneg K)
    hb (sourceSuperposition_dist K) hclass

end ContinuousEncoders

end Analog.ApproximateRigidity
