import Analog.EuclideanBridge
import Analog.HeterogeneousMomentCompactness
import Mathlib.Topology.Order.Compact

/-!
# The attained compact-moment minimum decoder

This module identifies the displayed decoder of Theorem 3, rather than only
asserting existence of an extension.  Its infimum is a genuine minimum on
the actual compact moment set.  Neither injectivity nor nonsingularity of
the received map is needed.
-/

noncomputable section
namespace Analog.CompactMinimumDecoder

open Set
open scoped NNReal BigOperators

variable {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]

/-- The displayed McShane formula, with an actual minimum whenever the
compactness and continuity hypotheses below hold. -/
def compactMinimum (S : Set X) (r : X → Y) (f : X → ℝ)
    (L : ℝ≥0) (y : Y) : ℝ :=
  sInf ((fun x => f x + (L : ℝ) * dist y (r x)) '' S)

/-- Every observation has a minimizing moment, including singular channels. -/
theorem compactMinimum_attained {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    {r : X → Y} {f : X → ℝ} (hr : ContinuousOn r S) (hf : ContinuousOn f S)
    (L : ℝ≥0) (y : Y) :
    ∃ x ∈ S, compactMinimum S r f L y = f x + (L : ℝ) * dist y (r x) := by
  have hc : ContinuousOn (fun x => f x + (L : ℝ) * dist y (r x)) S :=
    hf.add (continuousOn_const.mul (continuous_dist.comp_continuousOn (continuousOn_const.prodMk hr)))
  obtain ⟨x, hx, he⟩ := (hS.image_of_continuousOn hc).sInf_mem (hne.image _)
  exact ⟨x, hx, he.symm⟩

/-- Each candidate bounds the minimum from above. -/
theorem compactMinimum_le {S : Set X} (hS : IsCompact S)
    {r : X → Y} {f : X → ℝ} (hr : ContinuousOn r S) (hf : ContinuousOn f S)
    (L : ℝ≥0) (y : Y) {x : X} (hx : x ∈ S) :
    compactMinimum S r f L y ≤ f x + (L : ℝ) * dist y (r x) := by
  have hc : ContinuousOn (fun x => f x + (L : ℝ) * dist y (r x)) S :=
    hf.add (continuousOn_const.mul (continuous_dist.comp_continuousOn (continuousOn_const.prodMk hr)))
  exact csInf_le (hS.image_of_continuousOn hc).bddBelow ⟨x, hx, rfl⟩

/-- The minimum formula is globally Lipschitz with precisely the supplied
constant; this property does not require a pairwise bound on the target. -/
theorem compactMinimum_lipschitz {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    {r : X → Y} {f : X → ℝ} (hr : ContinuousOn r S) (hf : ContinuousOn f S)
    (L : ℝ≥0) : LipschitzWith L (compactMinimum S r f L) := by
  have hb (y z : Y) :
      compactMinimum S r f L y - compactMinimum S r f L z ≤ (L : ℝ) * dist y z := by
    obtain ⟨x, hx, he⟩ := compactMinimum_attained hS hne hr hf L z
    have hle := compactMinimum_le hS hr hf L y hx
    have ht := mul_le_mul_of_nonneg_left (dist_triangle y z (r x)) L.coe_nonneg
    rw [he]
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [Real.dist_eq, abs_le]
  constructor
  · have h := hb z y
    rw [dist_comm z y] at h
    linarith
  · exact hb y z

/-- On a noiseless received point the minimum equals its target, even when
multiple moments have that received point. -/
theorem compactMinimum_exact {S : Set X} (hS : IsCompact S)
    {r : X → Y} {f : X → ℝ} (hr : ContinuousOn r S) (hf : ContinuousOn f S)
    (L : ℝ≥0)
    (hpair : ∀ x ∈ S, ∀ z ∈ S, dist (f x) (f z) ≤ (L : ℝ) * dist (r x) (r z))
    {x : X} (hx : x ∈ S) : compactMinimum S r f L (r x) = f x := by
  apply le_antisymm
  · simpa using compactMinimum_le hS hr hf L (r x) hx
  · obtain ⟨z, hz, he⟩ := compactMinimum_attained hS ⟨x, hx⟩ hr hf L (r x)
    rw [he]
    have hp := (le_abs_self (f x - f z)).trans (hpair x hx z hz)
    linarith

/-- The displayed decoder has the all-observation uniform error bound. -/
theorem compactMinimum_uniform {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    {r : X → Y} {f : X → ℝ} (hr : ContinuousOn r S) (hf : ContinuousOn f S)
    (L : ℝ≥0)
    (hpair : ∀ x ∈ S, ∀ z ∈ S, dist (f x) (f z) ≤ (L : ℝ) * dist (r x) (r z))
    {x : X} (hx : x ∈ S) (y : Y) :
    dist (compactMinimum S r f L y) (f x) ≤ (L : ℝ) * dist y (r x) := by
  simpa only [compactMinimum_exact hS hr hf L hpair hx] using
    (compactMinimum_lipschitz hS hne hr hf L).dist_le_mul y (r x)

/-- The operational sharp constant on the actual domain `S`. -/
def sharpOn (S : Set X) (r : X → Y) (f : X → ℝ) : ℝ≥0 :=
  Decoder.sharpConstant (fun x : S => r x) (fun x : S => f x)

omit [TopologicalSpace X] in
/-- Domain restriction preserves the nonconstant-target hypothesis. -/
theorem subtype_nonconstant {S : Set X} {f : X → ℝ}
    (hn : Operational.NonconstantOn S f) :
    Operational.NonconstantOn Set.univ (fun x : S => f x) := by
  obtain ⟨x, hx, z, hz, hne⟩ := hn
  exact ⟨⟨x, hx⟩, Set.mem_univ _, ⟨z, hz⟩, Set.mem_univ _, hne⟩

omit [TopologicalSpace X] in
/-- Positive operational score supplies the sharp pairwise bound; it is not
an additional regularity assumption on the decoder. -/
theorem sharpOn_pairwise {S : Set X} {r : X → Y} {f : X → ℝ}
    (hn : Operational.NonconstantOn S f)
    (hs : 0 < Decoder.metricScore (fun x : S => r x) (fun x : S => f x)) :
    ∀ x ∈ S, ∀ z ∈ S,
      dist (f x) (f z) ≤ (sharpOn S r f : ℝ) * dist (r x) (r z) := by
  intro x hx z hz
  exact Decoder.sharpConstant_pairwise _ _ (subtype_nonconstant hn) hs ⟨x, hx⟩ ⟨z, hz⟩

/-- The particular attained minimum formula realizes the sharp uniform
constant.  The final conclusion compares against every decoder, with no
continuity or measurability restriction on the competitor. -/
theorem compactMinimum_sharp {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    {r : X → Y} {f : X → ℝ} (hr : ContinuousOn r S) (hf : ContinuousOn f S)
    (hn : Operational.NonconstantOn S f)
    (hs : 0 < Decoder.metricScore (fun x : S => r x) (fun x : S => f x)) :
    LipschitzWith (sharpOn S r f) (compactMinimum S r f (sharpOn S r f)) ∧
    (∀ x ∈ S, compactMinimum S r f (sharpOn S r f) (r x) = f x) ∧
    (∀ x ∈ S, ∀ y, dist (compactMinimum S r f (sharpOn S r f) y) (f x) ≤
      (sharpOn S r f : ℝ) * dist y (r x)) ∧
    (∀ (L : ℝ≥0) (D : Y → ℝ),
      (∀ x ∈ S, ∀ y, dist (D y) (f x) ≤ (L : ℝ) * dist y (r x)) →
      sharpOn S r f ≤ L) := by
  have hp := sharpOn_pairwise hn hs
  refine ⟨compactMinimum_lipschitz hS hne hr hf _,
    fun x hx => compactMinimum_exact hS hr hf _ hp hx,
    fun x hx y => compactMinimum_uniform hS hne hr hf _ hp hx y, ?_⟩
  intro L D hu
  exact Decoder.sharpConstant_le_uniform (subtype_nonconstant hn) hs
    (fun x y => hu x x.property y)

open HeterogeneousScore GramSynthesis ArbitraryEncoder

/-- The true finite-node affine channel: the individual offsets sum, and
both normalized moments are multiplied by the actual node count. -/
def momentReceived {K : ℕ} (e : Planar) (c : Fin K → ℝ × ℝ) (m : ℝ × ℝ) : ℂ :=
  asComplex ((∑ k, (c k).1) + (K : ℝ) * (e.ux * m.1 + e.vx * m.2),
    (∑ k, (c k).2) + (K : ℝ) * (e.uy * m.1 + e.vy * m.2))

theorem momentReceived_continuous {K : ℕ} (e : Planar) (c : Fin K → ℝ × ℝ) :
    Continuous (momentReceived e c) := by
  unfold momentReceived asComplex
  exact Complex.equivRealProdCLM.symm.continuous.comp
    (show Continuous (fun m : ℝ × ℝ =>
      ((∑ k, (c k).1) + (K : ℝ) * (e.ux * m.1 + e.vx * m.2),
       (∑ k, (c k).2) + (K : ℝ) * (e.uy * m.1 + e.vy * m.2))) from by fun_prop)

/-- The moment channel equals the physical sum, including arbitrary offsets. -/
theorem momentReceived_mean {K : ℕ} (hK : 0 < K) (e : Planar)
    (c : Fin K → ℝ × ℝ) (γ : Fin K → ℝ → ℝ × ℝ) (s : Fin K → ℝ) :
    momentReceived e c (meanStatistic γ s) =
      asComplex (HeterogeneousScore.received (encoder e c γ) s) := by
  rw [received_encoder_mean hK]
  rfl

/-- Restricting to actual moments leaves precisely the original quotient
set. The metric here is complex Euclidean, not the product maximum metric. -/
theorem metricScore_eq_heterogeneousScore {K : ℕ} (hK : 0 < K) (e : Planar)
    (c : Fin K → ℝ × ℝ) (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ) :
    Decoder.metricScore (fun m : attainable γ => momentReceived e c m)
      (fun m : attainable γ => F m) = HeterogeneousScore.score γ F (encoder e c γ) := by
  unfold Decoder.metricScore HeterogeneousScore.score Operational.score
  congr 1
  ext q
  constructor
  · rintro ⟨m, _, n, _, hne, hq⟩
    obtain ⟨s, hs, hm⟩ := m.property
    obtain ⟨t, ht, hn⟩ := n.property
    refine ⟨s, hs, t, ht, ?_, ?_⟩
    · simpa only [Function.comp_apply, hm, hn] using hne
    · simpa only [Function.comp_apply, ← hm, ← hn, momentReceived_mean hK,
        asComplex_squared_distance] using hq
  · rintro ⟨s, hs, t, ht, hne, hq⟩
    refine ⟨⟨meanStatistic γ s, meanStatistic_mem_attainable γ hs⟩, Set.mem_univ _,
      ⟨meanStatistic γ t, meanStatistic_mem_attainable γ ht⟩, Set.mem_univ _, hne, ?_⟩
    simpa only [Function.comp_apply, momentReceived_mean hK,
      asComplex_squared_distance] using hq

/-- The exact reciprocal square root of the manuscript's operational score. -/
def momentConstant {K : ℕ} (e : Planar) (c : Fin K → ℝ × ℝ)
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ) : ℝ≥0 :=
  sharpOn (attainable γ) (momentReceived e c) F

theorem momentConstant_eq {K : ℕ} (hK : 0 < K) (e : Planar)
    (c : Fin K → ℝ × ℝ) (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ) :
    (momentConstant e c γ F : ℝ) =
      1 / Real.sqrt (HeterogeneousScore.score γ F (encoder e c γ)) := by
  simp only [momentConstant, sharpOn, Decoder.sharpConstant,
    metricScore_eq_heterogeneousScore hK, NNReal.coe_mk]

/-- The actual formula displayed in Theorem 3, over the exact attainable set. -/
def momentDecoder {K : ℕ} (e : Planar) (c : Fin K → ℝ × ℝ)
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ) : ℂ → ℝ :=
  compactMinimum (attainable γ) (momentReceived e c) F (momentConstant e c γ F)

/-- Theorem 3: the displayed minimum is attained, globally Lipschitz, exact
under zero noise, and has the optimal uniform noise amplification constant.
No determinant or invertibility hypothesis occurs. -/
theorem heterogeneous_minimum_decoder {K : ℕ} (hK : 0 < K) (e : Planar)
    (c : Fin K → ℝ × ℝ) (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Icc (-1 : ℝ) 1))
    (hF : ContinuousOn F (attainable γ))
    (hn : Operational.NonconstantOn (attainable γ) F)
    (hs : 0 < HeterogeneousScore.score γ F (encoder e c γ)) :
    (∀ y, ∃ m ∈ attainable γ,
      momentDecoder e c γ F y = F m + (momentConstant e c γ F : ℝ) *
        dist y (momentReceived e c m)) ∧
    LipschitzWith (momentConstant e c γ F) (momentDecoder e c γ F) ∧
    (∀ s ∈ HeterogeneousScore.ValidInput K, ∀ z : ℂ,
      |momentDecoder e c γ F
        (asComplex (HeterogeneousScore.received (encoder e c γ) s) + z) -
          F (meanStatistic γ s)| ≤ (momentConstant e c γ F : ℝ) * ‖z‖) ∧
    (∀ (L : ℝ≥0) (D : ℂ → ℝ),
      (∀ s ∈ HeterogeneousScore.ValidInput K, ∀ z : ℂ,
        |D (asComplex (HeterogeneousScore.received (encoder e c γ) s) + z) -
          F (meanStatistic γ s)| ≤ (L : ℝ) * ‖z‖) → momentConstant e c γ F ≤ L) := by
  have hcompact := HeterogeneousMomentCompactness.attainable_isCompact γ hγ
  have hne := HeterogeneousMomentCompactness.attainable_nonempty γ
  have hr : ContinuousOn (momentReceived e c) (attainable γ) :=
    (momentReceived_continuous e c).continuousOn
  have hs' : 0 < Decoder.metricScore
      (fun m : attainable γ => momentReceived e c m) (fun m : attainable γ => F m) := by
    rwa [metricScore_eq_heterogeneousScore hK]
  obtain ⟨hlip, hexact, huniform, hminimal⟩ :=
    compactMinimum_sharp hcompact hne hr hF hn hs'
  refine ⟨fun y => compactMinimum_attained hcompact hne hr hF _ y, hlip, ?_, ?_⟩
  · intro s hvalid z
    have hu := huniform (meanStatistic γ s) (meanStatistic_mem_attainable γ hvalid)
      (asComplex (HeterogeneousScore.received (encoder e c γ) s) + z)
    simpa only [momentDecoder, momentConstant, momentReceived_mean hK,
      Real.dist_eq, dist_eq_norm, add_sub_cancel_left] using hu
  · intro L D hb
    apply hminimal L D
    intro m hm y
    obtain ⟨s, hvalid, rfl⟩ := hm
    have hb' := hb s hvalid
      (y - asComplex (HeterogeneousScore.received (encoder e c γ) s))
    simpa only [momentReceived_mean hK, Real.dist_eq, dist_eq_norm,
      add_sub_cancel] using hb'

end Analog.CompactMinimumDecoder
