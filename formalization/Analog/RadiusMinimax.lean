import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic

/-!
# Minimax error at a fixed disturbance radius

This module formalizes the operational part of Proposition
`prop:radius-minimax` in the current manuscript. The target is real-valued
and bounded. The received map takes values in a real normed space.

For each observation, the decoder takes the midpoint of the infimum and
supremum of the target values consistent with the noise radius. The theorem
`radius_decoder_iff_pairwise` characterizes every attainable error level,
and `radius_minimax` identifies the smallest level as half the pair modulus.
For continuous compact input models, `modulus_attained` proves that the
supremum is an actual maximum. The final theorem `borel_radius_minimax`
also proves that the explicit midpoint decoder is Borel measurable,
including its zero value outside the possible-observation set.
-/

noncomputable section

namespace Analog.RadiusMinimax

open Set

variable {X Y : Type*} [NormedAddCommGroup Y]

/-- All target values consistent with an observation at radius `ρ`. -/
def consistentValues (r : X → Y) (f : X → ℝ) (ρ : ℝ) (y : Y) : Set ℝ :=
  {v | ∃ x, dist y (r x) ≤ ρ ∧ f x = v}

/-- A radius-specific guarantee, with no regularity assumed of the decoder. -/
def RadiusBound (r : X → Y) (f : X → ℝ) (ρ e : ℝ) (D : Y → ℝ) : Prop :=
  ∀ x y, dist y (r x) ≤ ρ → |D y - f x| ≤ e

/-- The necessary and sufficient pair constraint at a fixed radius. -/
def PairBound (r : X → Y) (f : X → ℝ) (ρ e : ℝ) : Prop :=
  ∀ x z, dist (r x) (r z) ≤ 2 * ρ → |f x - f z| ≤ 2 * e

/-- Midpoint of the consistency interval; the arbitrary empty-fiber value
has no effect on the operational guarantee. -/
def midpointDecoder (r : X → Y) (f : X → ℝ) (ρ : ℝ) (y : Y) : ℝ :=
  (sInf (consistentValues r f ρ y) + sSup (consistentValues r f ρ y)) / 2

lemma consistentValues_bddAbove {r : X → Y} {f : X → ℝ} {ρ : ℝ}
    {a b : ℝ} (hf : ∀ x, a ≤ f x ∧ f x ≤ b) (y : Y) :
    BddAbove (consistentValues r f ρ y) := by
  refine ⟨b, ?_⟩
  rintro v ⟨x, _, rfl⟩
  exact (hf x).2

lemma consistentValues_bddBelow {r : X → Y} {f : X → ℝ} {ρ : ℝ}
    {a b : ℝ} (hf : ∀ x, a ≤ f x ∧ f x ≤ b) (y : Y) :
    BddBelow (consistentValues r f ρ y) := by
  refine ⟨a, ?_⟩
  rintro v ⟨x, _, rfl⟩
  exact (hf x).1

/-- The received-signal midpoint is within half the separation of either
received value. This supplies the common observation in the lower bound. -/
theorem midpoint_observation [NormedSpace ℝ Y] (u v : Y) :
    ∃ y : Y, dist y u = dist u v / 2 ∧ dist y v = dist u v / 2 := by
  refine ⟨(1 / 2 : ℝ) • (u + v), ?_, ?_⟩
  · rw [dist_eq_norm]
    have h : (1 / 2 : ℝ) • (u + v) - u = (1 / 2 : ℝ) • (v - u) := by module
    rw [h, norm_smul, Real.norm_eq_abs]
    norm_num
    rw [← dist_eq_norm, dist_comm]
    ring
  · rw [dist_eq_norm]
    have h : (1 / 2 : ℝ) • (u + v) - v = (1 / 2 : ℝ) • (u - v) := by module
    rw [h, norm_smul, Real.norm_eq_abs]
    norm_num
    rw [← dist_eq_norm]
    ring

/-- Every decoder's radius guarantee implies the pairwise lower bound. -/
theorem pairBound_of_radiusBound [NormedSpace ℝ Y] {r : X → Y} {f : X → ℝ} {ρ e : ℝ}
    {D : Y → ℝ} (hD : RadiusBound r f ρ e D) : PairBound r f ρ e := by
  intro x z hxz
  obtain ⟨y, hyx, hyz⟩ := midpoint_observation (r x) (r z)
  have hx := hD x y (by rw [hyx]; linarith)
  have hz := hD z y (by rw [hyz]; linarith)
  have ht : |f x - f z| ≤ |D y - f x| + |D y - f z| := by
    simpa only [Real.dist_eq, abs_sub_comm] using dist_triangle (f x) (D y) (f z)
  linarith

/-- Consistency fibers have width at most twice a pairwise feasible error. -/
theorem consistent_width_le {r : X → Y} {f : X → ℝ} {ρ e : ℝ}
    (hp : PairBound r f ρ e) {y : Y}
    (hne : (consistentValues r f ρ y).Nonempty) :
    sSup (consistentValues r f ρ y) - sInf (consistentValues r f ρ y) ≤ 2 * e := by
  have hpair : ∀ u ∈ consistentValues r f ρ y,
      ∀ v ∈ consistentValues r f ρ y, u - v ≤ 2 * e := by
    rintro u ⟨x, hx, rfl⟩ v ⟨z, hz, rfl⟩
    apply (le_abs_self _).trans
    apply hp x z
    have ht := dist_triangle (r x) y (r z)
    rw [dist_comm (r x) y] at ht
    linarith
  have hupper : ∀ v ∈ consistentValues r f ρ y,
      sSup (consistentValues r f ρ y) ≤ v + 2 * e := by
    intro v hv
    apply csSup_le hne
    intro u hu
    linarith [hpair u hu v hv]
  have hlow : sSup (consistentValues r f ρ y) - 2 * e ≤
      sInf (consistentValues r f ρ y) := by
    apply le_csInf hne
    intro v hv
    linarith [hupper v hv]
  linarith

/-- The consistency-interval midpoint achieves every pairwise feasible
error level. This includes zero radius and target collisions. -/
theorem midpointDecoder_radiusBound {r : X → Y} {f : X → ℝ} {ρ e : ℝ}
    {a b : ℝ} (hf : ∀ x, a ≤ f x ∧ f x ≤ b)
    (hp : PairBound r f ρ e) : RadiusBound r f ρ e (midpointDecoder r f ρ) := by
  intro x y hxy
  have hx : f x ∈ consistentValues r f ρ y := ⟨x, hxy, rfl⟩
  have hlo := csInf_le (consistentValues_bddBelow hf y) hx
  have hhi := le_csSup (consistentValues_bddAbove hf y) hx
  have hw := consistent_width_le hp ⟨f x, hx⟩
  rw [midpointDecoder, abs_le]
  constructor <;> linarith

/-- Exact characterization of attainable error levels at a fixed radius.
The left quantifies over all decoders, not only exact or continuous ones. -/
theorem radius_decoder_iff_pairwise [NormedSpace ℝ Y] (r : X → Y) (f : X → ℝ) (ρ e : ℝ)
    {a b : ℝ} (hf : ∀ x, a ≤ f x ∧ f x ≤ b) :
    (∃ D : Y → ℝ, RadiusBound r f ρ e D) ↔ PairBound r f ρ e := by
  constructor
  · rintro ⟨D, hD⟩
    exact pairBound_of_radiusBound hD
  · intro hp
    exact ⟨midpointDecoder r f ρ, midpointDecoder_radiusBound hf hp⟩

/-- The absolute target differences of pairs at received distance `≤ d`. -/
def pairValues (r : X → Y) (f : X → ℝ) (d : ℝ) : Set ℝ :=
  {v | ∃ x z, dist (r x) (r z) ≤ d ∧ |f x - f z| = v}

/-- Modulus of distinguishability; compact continuous input models attain
this supremum, but attainment is unnecessary for the operational theorem. -/
def modulus (r : X → Y) (f : X → ℝ) (d : ℝ) : ℝ :=
  sSup (pairValues r f d)

lemma pairValues_bddAbove {r : X → Y} {f : X → ℝ} {d : ℝ}
    {a b : ℝ} (hf : ∀ x, a ≤ f x ∧ f x ≤ b) :
    BddAbove (pairValues r f d) := by
  refine ⟨b - a, ?_⟩
  rintro v ⟨x, z, _, rfl⟩
  rw [abs_le]
  constructor <;> linarith [(hf x).1, (hf x).2, (hf z).1, (hf z).2]

lemma pairValues_nonempty [Nonempty X] (r : X → Y) (f : X → ℝ)
    {d : ℝ} (hd : 0 ≤ d) : (pairValues r f d).Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty X›
  exact ⟨0, x, x, by simpa using hd, by simp⟩

/-- The radius-specific minimax error is exactly half the pair modulus:
the displayed decoder attains it and every feasible error is at least it. -/
theorem radius_minimax [NormedSpace ℝ Y] [Nonempty X] (r : X → Y) (f : X → ℝ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) {a b : ℝ}
    (hf : ∀ x, a ≤ f x ∧ f x ≤ b) :
    RadiusBound r f ρ (modulus r f (2 * ρ) / 2) (midpointDecoder r f ρ) ∧
      ∀ (D : Y → ℝ) (e : ℝ), RadiusBound r f ρ e D →
        modulus r f (2 * ρ) / 2 ≤ e := by
  constructor
  · apply midpointDecoder_radiusBound hf
    intro x z hxz
    have hle := le_csSup (pairValues_bddAbove hf)
      (show |f x - f z| ∈ pairValues r f (2 * ρ) from ⟨x, z, hxz, rfl⟩)
    dsimp [modulus]
    linarith
  · intro D e hD
    have hp := pairBound_of_radiusBound hD
    have hm : modulus r f (2 * ρ) ≤ 2 * e := by
      apply csSup_le (pairValues_nonempty r f (by linarith : 0 ≤ 2 * ρ))
      rintro v ⟨x, z, hxz, rfl⟩
      exact hp x z hxz
    linarith

section CompactInput

variable [TopologicalSpace X] [CompactSpace X]

/-- Continuity on the compact input space supplies the bounded-target
hypothesis used in the operational theorem. -/
theorem continuous_target_bounded {f : X → ℝ} (hf : Continuous f) :
    ∃ a b : ℝ, ∀ x, a ≤ f x ∧ f x ≤ b := by
  have hc : IsCompact (Set.range f) := isCompact_range hf
  obtain ⟨a, ha⟩ := hc.bddBelow
  obtain ⟨b, hb⟩ := hc.bddAbove
  exact ⟨a, b, fun x => ⟨ha (Set.mem_range_self x), hb (Set.mem_range_self x)⟩⟩

/-- Every consistency fiber has a compact target-value set. -/
theorem consistentValues_isCompact {r : X → Y} {f : X → ℝ}
    (hr : Continuous r) (hf : Continuous f) (ρ : ℝ) (y : Y) :
    IsCompact (consistentValues r f ρ y) := by
  have hc : IsCompact {x : X | dist y (r x) ≤ ρ} :=
    (isClosed_le (continuous_const.dist hr) continuous_const).isCompact
  exact hc.image hf

/-- The target-difference set for distance-constrained input pairs is
compact, so the manuscript may use a maximum instead of a supremum. -/
theorem pairValues_isCompact {r : X → Y} {f : X → ℝ}
    (hr : Continuous r) (hf : Continuous f) (d : ℝ) :
    IsCompact (pairValues r f d) := by
  have hc : IsCompact {p : X × X | dist (r p.1) (r p.2) ≤ d} :=
    (isClosed_le ((hr.comp continuous_fst).dist (hr.comp continuous_snd))
      continuous_const).isCompact
  have ht : Continuous (fun p : X × X => |f p.1 - f p.2|) :=
    ((hf.comp continuous_fst).sub (hf.comp continuous_snd)).abs
  convert hc.image ht using 1
  ext v
  simp only [pairValues, Set.mem_image, Set.mem_setOf_eq, Prod.exists]

/-- The actual pair modulus is attained on a compact continuous input
model at every nonnegative distance. -/
theorem modulus_attained [Nonempty X] {r : X → Y} {f : X → ℝ}
    (hr : Continuous r) (hf : Continuous f) {d : ℝ} (hd : 0 ≤ d) :
    ∃ x z, dist (r x) (r z) ≤ d ∧ |f x - f z| = modulus r f d := by
  exact (pairValues_isCompact hr hf d).sSup_mem (pairValues_nonempty r f hd)

/-- Compact-input form of the manuscript's radius proposition. The worst
pair exists, its half-separation is achieved by the consistency midpoint,
and no decoder can have a smaller radius-specific error bound. -/
theorem compact_radius_minimax [NormedSpace ℝ Y] [Nonempty X]
    (r : X → Y) (f : X → ℝ) (hr : Continuous r) (hf : Continuous f)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ x z, dist (r x) (r z) ≤ 2 * ρ ∧
      (∀ u v, dist (r u) (r v) ≤ 2 * ρ → |f u - f v| ≤ |f x - f z|) ∧
      RadiusBound r f ρ (|f x - f z| / 2) (midpointDecoder r f ρ) ∧
      ∀ (D : Y → ℝ) (e : ℝ), RadiusBound r f ρ e D → |f x - f z| / 2 ≤ e := by
  obtain ⟨a, b, hb⟩ := continuous_target_bounded hf
  obtain ⟨x, z, hxz, heq⟩ := modulus_attained hr hf (by linarith : 0 ≤ 2 * ρ)
  obtain ⟨hupper, hlower⟩ := radius_minimax r f hρ hb
  refine ⟨x, z, hxz, ?_, ?_, ?_⟩
  · intro u v huv
    rw [heq]
    exact le_csSup (pairValues_bddAbove hb) ⟨u, v, huv, rfl⟩
  · simpa only [heq] using hupper
  · simpa only [heq] using hlower

/-- A closed constraint on a compact input space gives a closed set of
possible observations. The target space need not itself be compact. -/
theorem consistent_closed_constraint {r : X → Y} (hr : Continuous r)
    (ρ : ℝ) {A : Set X} (hA : IsClosed A) :
    IsClosed {y : Y | ∃ x, dist y (r x) ≤ ρ ∧ x ∈ A} := by
  have hc : IsClosed {p : X × Y | dist p.2 (r p.1) ≤ ρ ∧ p.1 ∈ A} :=
    (isClosed_le (continuous_snd.dist (hr.comp continuous_fst)) continuous_const).inter
      (hA.preimage continuous_fst)
  have hi := isClosedMap_snd_of_compactSpace _ hc
  convert hi using 1
  ext y
  constructor
  · rintro ⟨x, hx, hxa⟩
    exact ⟨(x, y), ⟨hx, hxa⟩, rfl⟩
  · rintro ⟨⟨x, z⟩, ⟨hx, hxa⟩, hzy⟩
    change z = y at hzy
    subst z
    exact ⟨x, hx, hxa⟩

theorem possibleObservations_isClosed {r : X → Y} {f : X → ℝ}
    (hr : Continuous r) (ρ : ℝ) :
    IsClosed {y : Y | (consistentValues r f ρ y).Nonempty} := by
  have hc := consistent_closed_constraint hr ρ isClosed_univ
  convert hc using 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_univ, and_true]
  constructor
  · rintro ⟨v, x, hx, _⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨f x, x, hx, rfl⟩

theorem upperEndpoint_superlevel_iff {r : X → Y} {f : X → ℝ}
    (hr : Continuous r) (hf : Continuous f) (ρ a : ℝ) (y : Y)
    (hne : (consistentValues r f ρ y).Nonempty) :
    a ≤ sSup (consistentValues r f ρ y) ↔ ∃ x, dist y (r x) ≤ ρ ∧ a ≤ f x := by
  have hc := consistentValues_isCompact hr hf ρ y
  constructor
  · intro ha
    obtain ⟨x, hx, hfx⟩ := hc.sSup_mem hne
    exact ⟨x, hx, by simpa only [hfx] using ha⟩
  · rintro ⟨x, hx, ha⟩
    exact ha.trans (le_csSup hc.bddAbove ⟨x, hx, rfl⟩)

theorem lowerEndpoint_sublevel_iff {r : X → Y} {f : X → ℝ}
    (hr : Continuous r) (hf : Continuous f) (ρ a : ℝ) (y : Y)
    (hne : (consistentValues r f ρ y).Nonempty) :
    sInf (consistentValues r f ρ y) ≤ a ↔ ∃ x, dist y (r x) ≤ ρ ∧ f x ≤ a := by
  have hc := consistentValues_isCompact hr hf ρ y
  constructor
  · intro ha
    obtain ⟨x, hx, hfx⟩ := hc.sInf_mem hne
    exact ⟨x, hx, by simpa only [hfx] using ha⟩
  · rintro ⟨x, hx, ha⟩
    exact (csInf_le hc.bddBelow ⟨x, hx, rfl⟩).trans ha

section Measurability

variable [MeasurableSpace Y] [BorelSpace Y]

/-- The upper consistency endpoint is Borel measurable, including the
chosen zero value at impossible observations. -/
theorem upperEndpoint_measurable {r : X → Y} {f : X → ℝ}
    (hr : Continuous r) (hf : Continuous f) (ρ : ℝ) :
    Measurable (fun y => sSup (consistentValues r f ρ y)) := by
  apply measurable_of_Ici
  intro a
  have he : IsClosed {y : Y | ∃ x, dist y (r x) ≤ ρ ∧ a ≤ f x} :=
    consistent_closed_constraint hr ρ (isClosed_le continuous_const hf)
  have hn := possibleObservations_isClosed (f := f) hr ρ
  by_cases ha : a ≤ 0
  · have hset : (fun y => sSup (consistentValues r f ρ y)) ⁻¹' Ici a =
        {y : Y | ∃ x, dist y (r x) ≤ ρ ∧ a ≤ f x} ∪
        {y : Y | ¬ (consistentValues r f ρ y).Nonempty} := by
      ext y
      by_cases hy : (consistentValues r f ρ y).Nonempty
      · simpa only [mem_preimage, mem_Ici, mem_union, mem_setOf_eq, hy,
          not_true_eq_false, or_false] using upperEndpoint_superlevel_iff hr hf ρ a y hy
      · have hempty := Set.not_nonempty_iff_eq_empty.mp hy
        have hex : ¬ ∃ x, dist y (r x) ≤ ρ ∧ a ≤ f x := by
          rintro ⟨x, hx, _⟩
          exact hy ⟨f x, x, hx, rfl⟩
        simp [hempty, hex, ha]
    rw [hset]
    exact he.measurableSet.union hn.measurableSet.compl
  · have hset : (fun y => sSup (consistentValues r f ρ y)) ⁻¹' Ici a =
        {y : Y | ∃ x, dist y (r x) ≤ ρ ∧ a ≤ f x} := by
      ext y
      by_cases hy : (consistentValues r f ρ y).Nonempty
      · exact upperEndpoint_superlevel_iff hr hf ρ a y hy
      · have hempty := Set.not_nonempty_iff_eq_empty.mp hy
        have hex : ¬ ∃ x, dist y (r x) ≤ ρ ∧ a ≤ f x := by
          rintro ⟨x, hx, _⟩
          exact hy ⟨f x, x, hx, rfl⟩
        simp [hempty, hex, ha]
    rw [hset]
    exact he.measurableSet

/-- The lower consistency endpoint is Borel measurable. -/
theorem lowerEndpoint_measurable {r : X → Y} {f : X → ℝ}
    (hr : Continuous r) (hf : Continuous f) (ρ : ℝ) :
    Measurable (fun y => sInf (consistentValues r f ρ y)) := by
  apply measurable_of_Iic
  intro a
  have he : IsClosed {y : Y | ∃ x, dist y (r x) ≤ ρ ∧ f x ≤ a} :=
    consistent_closed_constraint hr ρ (isClosed_le hf continuous_const)
  have hn := possibleObservations_isClosed (f := f) hr ρ
  by_cases ha : 0 ≤ a
  · have hset : (fun y => sInf (consistentValues r f ρ y)) ⁻¹' Iic a =
        {y : Y | ∃ x, dist y (r x) ≤ ρ ∧ f x ≤ a} ∪
        {y : Y | ¬ (consistentValues r f ρ y).Nonempty} := by
      ext y
      by_cases hy : (consistentValues r f ρ y).Nonempty
      · simpa only [mem_preimage, mem_Iic, mem_union, mem_setOf_eq, hy,
          not_true_eq_false, or_false] using lowerEndpoint_sublevel_iff hr hf ρ a y hy
      · have hempty := Set.not_nonempty_iff_eq_empty.mp hy
        have hex : ¬ ∃ x, dist y (r x) ≤ ρ ∧ f x ≤ a := by
          rintro ⟨x, hx, _⟩
          exact hy ⟨f x, x, hx, rfl⟩
        simp [hempty, hex, ha]
    rw [hset]
    exact he.measurableSet.union hn.measurableSet.compl
  · have hset : (fun y => sInf (consistentValues r f ρ y)) ⁻¹' Iic a =
        {y : Y | ∃ x, dist y (r x) ≤ ρ ∧ f x ≤ a} := by
      ext y
      by_cases hy : (consistentValues r f ρ y).Nonempty
      · exact lowerEndpoint_sublevel_iff hr hf ρ a y hy
      · have hempty := Set.not_nonempty_iff_eq_empty.mp hy
        have hex : ¬ ∃ x, dist y (r x) ≤ ρ ∧ f x ≤ a := by
          rintro ⟨x, hx, _⟩
          exact hy ⟨f x, x, hx, rfl⟩
        simp [hempty, hex, ha]
    rw [hset]
    exact he.measurableSet

/-- The explicit radius-optimal midpoint decoder is Borel measurable. -/
theorem midpointDecoder_measurable {r : X → Y} {f : X → ℝ}
    (hr : Continuous r) (hf : Continuous f) (ρ : ℝ) :
    Measurable (midpointDecoder r f ρ) :=
  ((lowerEndpoint_measurable hr hf ρ).add (upperEndpoint_measurable hr hf ρ)).div_const 2

/-- Full compact-input radius minimax theorem with a Borel attaining
midpoint decoder and a lower bound against all decoders. -/
theorem borel_radius_minimax [NormedSpace ℝ Y] [Nonempty X]
    (r : X → Y) (f : X → ℝ) (hr : Continuous r) (hf : Continuous f)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Measurable (midpointDecoder r f ρ) ∧
      RadiusBound r f ρ (modulus r f (2 * ρ) / 2) (midpointDecoder r f ρ) ∧
      ∀ (D : Y → ℝ) (e : ℝ), RadiusBound r f ρ e D →
        modulus r f (2 * ρ) / 2 ≤ e := by
  obtain ⟨a, b, hb⟩ := continuous_target_bounded hf
  exact ⟨midpointDecoder_measurable hr hf ρ, radius_minimax r f hρ hb⟩

end Measurability

end CompactInput

end Analog.RadiusMinimax
