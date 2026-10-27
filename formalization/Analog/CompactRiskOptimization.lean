import Mathlib

/-!
# Outer risk optimization from compactness and sequential local bounds

The lower bound is proved uniformly over the design set by contradiction,
selection below a threshold from the actual risk infimum, and extraction of
a convergent subsequence of designs. No uniform lower bound, continuity of
risk in the design, or existence of finite-noise optimizers is assumed.
-/

noncomputable section
namespace Analog.CompactRiskOptimization
open Set Filter Topology

/-- The actual infimum over every design at the specified noise index. -/
def infRisk {X : Type*} (r : X → ℕ → ℝ) (n : ℕ) : ℝ :=
  sInf (Set.range (fun p => r p n))

theorem risk_range_bddBelow {X : Type*} (r : X → ℕ → ℝ)
    (hnonneg : ∀ p n, 0 ≤ r p n) (n : ℕ) :
    BddBelow (Set.range (fun p => r p n)) :=
  ⟨0, fun _ ⟨p, hp⟩ => hp ▸ hnonneg p n⟩

/-- Nonnegativity also holds for the actual design infimum. -/
theorem infRisk_nonneg {X : Type*} [Nonempty X] (r : X → ℕ → ℝ)
    (hnonneg : ∀ p n, 0 ≤ r p n) (n : ℕ) : 0 ≤ infRisk r n := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨p, rfl⟩
  exact hnonneg p n

/-- Any one design gives an upper bound for the actual design infimum. -/
theorem infRisk_le {X : Type*} (r : X → ℕ → ℝ)
    (hnonneg : ∀ p n, 0 ≤ r p n) (p : X) (n : ℕ) :
    infRisk r n ≤ r p n :=
  csInf_le (risk_range_bddBelow r hnonneg n) ⟨p, rfl⟩

/-- An infimum strictly below a threshold supplies an actual design below
that threshold; attainment of the infimum is unnecessary. -/
theorem exists_risk_lt_of_infRisk_lt {X : Type*} [Nonempty X]
    (r : X → ℕ → ℝ) (n : ℕ) {a : ℝ} (ha : infRisk r n < a) :
    ∃ p, r p n < a := by
  obtain ⟨_, ⟨p, rfl⟩, hp⟩ := exists_lt_of_csInf_lt (Set.range_nonempty _) ha
  exact ⟨p, hp⟩

/-- Sequential lower bounds at every possible compact limit imply a lower
bound for the actual outer infimum. The displayed local hypothesis is not
an assumed uniform estimate: designs may vary arbitrarily with the index. -/
theorem eventual_infRisk_lower_of_compact_sequential
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (r : X → ℕ → ℝ) (m : ℝ)
    (hlocal : ∀ (p : ℕ → X) (p₀ : X) (idx : ℕ → ℕ),
      StrictMono idx → Tendsto p atTop (𝓝 p₀) →
      ∀ a < m, ∀ᶠ n in atTop, a ≤ r (p n) (idx n)) :
    ∀ a < m, ∀ᶠ n in atTop, a ≤ infRisk r n := by
  intro a ha
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, infRisk r n < a := by
    simpa only [Filter.Frequently, not_lt] using hnot
  obtain ⟨idx, hidx, hbad⟩ := extraction_of_frequently_atTop hfreq
  choose p hp using fun n => exists_risk_lt_of_infRisk_lt r (idx n) (hbad n)
  obtain ⟨p₀, σ, hσ, hconv⟩ := CompactSpace.tendsto_subseq p
  have hlow := hlocal (p ∘ σ) p₀ (idx ∘ σ) (hidx.comp hσ) hconv a ha
  obtain ⟨n, hn⟩ := hlow.exists
  exact (not_lt_of_ge hn) (hp (σ n))

/-- Regular-limit lower bounds and singular-limit divergence provide all
the sequential estimates needed for compact outer optimization. -/
theorem sequential_lower_of_regular_or_divergent
    {X : Type*} [TopologicalSpace X]
    (r : X → ℕ → ℝ) (good : X → Prop) (J : X → ℝ) (m : ℝ)
    (hmin : ∀ p, good p → m ≤ J p)
    (hregular : ∀ (p : ℕ → X) (p₀ : X) (idx : ℕ → ℕ),
      StrictMono idx → Tendsto p atTop (𝓝 p₀) → good p₀ →
      ∀ a < J p₀, ∀ᶠ n in atTop, a ≤ r (p n) (idx n))
    (hsingular : ∀ (p : ℕ → X) (p₀ : X) (idx : ℕ → ℕ),
      StrictMono idx → Tendsto p atTop (𝓝 p₀) → ¬ good p₀ →
      Tendsto (fun n => r (p n) (idx n)) atTop atTop) :
    ∀ (p : ℕ → X) (p₀ : X) (idx : ℕ → ℕ),
      StrictMono idx → Tendsto p atTop (𝓝 p₀) →
      ∀ a < m, ∀ᶠ n in atTop, a ≤ r (p n) (idx n) := by
  intro p p₀ idx hidx hp a ha
  by_cases hg : good p₀
  · exact hregular p p₀ idx hidx hp hg a (ha.trans_le (hmin p₀ hg))
  · exact (hsingular p p₀ idx hidx hp hg).eventually (eventually_ge_atTop a)

/-- Compactness turns the regular and singular sequential converse bounds
into convergence of the actual outer risk infimum, given a one-design
asymptotic upper bound. Only an upper bound, not fixed-design convergence,
is required of the designated design. -/
theorem outer_infimum_tendsto_of_eventual_upper
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (r : X → ℕ → ℝ) (good : X → Prop) (J : X → ℝ) (m : ℝ)
    (hnonneg : ∀ p n, 0 ≤ r p n)
    (hmin : ∀ p, good p → m ≤ J p)
    (pstar : X)
    (hupper : ∀ b > m, ∀ᶠ n in atTop, r pstar n < b)
    (hregular : ∀ (p : ℕ → X) (p₀ : X) (idx : ℕ → ℕ),
      StrictMono idx → Tendsto p atTop (𝓝 p₀) → good p₀ →
      ∀ a < J p₀, ∀ᶠ n in atTop, a ≤ r (p n) (idx n))
    (hsingular : ∀ (p : ℕ → X) (p₀ : X) (idx : ℕ → ℕ),
      StrictMono idx → Tendsto p atTop (𝓝 p₀) → ¬ good p₀ →
      Tendsto (fun n => r (p n) (idx n)) atTop atTop) :
    Tendsto (infRisk r) atTop (𝓝 m) := by
  have hlow := eventual_infRisk_lower_of_compact_sequential r m
    (sequential_lower_of_regular_or_divergent r good J m hmin hregular hsingular)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨b, hab, hbm⟩ := exists_between ha
    filter_upwards [hlow b hbm] with n hn
    exact hab.trans_le hn
  · intro b hb
    filter_upwards [hupper b hb] with n hn
    exact (infRisk_le r hnonneg pstar n).trans_lt hn

/-- Convenient attained-design form: convergence of the fixed design's risk
and the sequential converse bounds imply convergence of the outer infimum.
In applications `m = J pstar` and the minimizing good design is constructed
by a separate compactness theorem. -/
theorem outer_infimum_tendsto
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (r : X → ℕ → ℝ) (good : X → Prop) (J : X → ℝ) (m : ℝ)
    (hnonneg : ∀ p n, 0 ≤ r p n)
    (hmin : ∀ p, good p → m ≤ J p)
    (pstar : X) (hstar : Tendsto (r pstar) atTop (𝓝 m))
    (hregular : ∀ (p : ℕ → X) (p₀ : X) (idx : ℕ → ℕ),
      StrictMono idx → Tendsto p atTop (𝓝 p₀) → good p₀ →
      ∀ a < J p₀, ∀ᶠ n in atTop, a ≤ r (p n) (idx n))
    (hsingular : ∀ (p : ℕ → X) (p₀ : X) (idx : ℕ → ℕ),
      StrictMono idx → Tendsto p atTop (𝓝 p₀) → ¬ good p₀ →
      Tendsto (fun n => r (p n) (idx n)) atTop atTop) :
    Tendsto (infRisk r) atTop (𝓝 m) :=
  outer_infimum_tendsto_of_eventual_upper r good J m hnonneg hmin pstar
    (fun _ hb => hstar.eventually (gt_mem_nhds hb)) hregular hsingular

/-- The actual infimum over an admissible subset of the ambient compact
design space. The admissible subset need not itself be compact or closed. -/
def admissibleInfRisk {X : Type*} (r : X → ℕ → ℝ) (good : X → Prop) (n : ℕ) : ℝ :=
  sInf ((fun p => r p n) '' {p | good p})

/-- Any admissible design bounds the infimum over the admissible class. -/
theorem admissibleInfRisk_le {X : Type*} (r : X → ℕ → ℝ) (good : X → Prop)
    (hnonneg : ∀ p, good p → ∀ n, 0 ≤ r p n) (p : X) (hp : good p) (n : ℕ) :
    admissibleInfRisk r good n ≤ r p n := by
  change sInf ((fun p => r p n) '' {p | good p}) ≤ r p n
  refine csInf_le ?_ ⟨p, hp, rfl⟩
  refine ⟨0, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact hnonneg q hq n

/-- Selection below an infimum threshold stays inside the actual admissible
class; it does not introduce singular finite-stage designs. -/
theorem exists_admissible_risk_lt {X : Type*} (r : X → ℕ → ℝ) (good : X → Prop)
    (hne : ∃ p, good p) (n : ℕ) {a : ℝ} (ha : admissibleInfRisk r good n < a) :
    ∃ p, good p ∧ r p n < a := by
  have hne' : ((fun p => r p n) '' {p | good p}).Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨r p n, p, hp, rfl⟩
  obtain ⟨_, ⟨p, hp, rfl⟩, hpa⟩ := exists_lt_of_csInf_lt hne' ha
  exact ⟨p, hp, hpa⟩

/-- Compactness of the ambient closure upgrades sequential bounds along
admissible designs to a lower bound for the admissible-class infimum. -/
theorem eventual_admissibleInfRisk_lower
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (r : X → ℕ → ℝ) (good : X → Prop) (m : ℝ) (hne : ∃ p, good p)
    (hlocal : ∀ (p : ℕ → X) (p₀ : X) (idx : ℕ → ℕ),
      (∀ n, good (p n)) → StrictMono idx → Tendsto p atTop (𝓝 p₀) →
      ∀ a < m, ∀ᶠ n in atTop, a ≤ r (p n) (idx n)) :
    ∀ a < m, ∀ᶠ n in atTop, a ≤ admissibleInfRisk r good n := by
  intro a ha
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, admissibleInfRisk r good n < a := by
    simpa only [Filter.Frequently, not_lt] using hnot
  obtain ⟨idx, hidx, hbad⟩ := extraction_of_frequently_atTop hfreq
  choose p hpg hp using fun n => exists_admissible_risk_lt r good hne (idx n) (hbad n)
  obtain ⟨p₀, σ, hσ, hconv⟩ := CompactSpace.tendsto_subseq p
  have hlow := hlocal (p ∘ σ) p₀ (idx ∘ σ) (fun n => hpg (σ n))
    (hidx.comp hσ) hconv a ha
  obtain ⟨n, hn⟩ := hlow.exists
  exact (not_lt_of_ge hn) (hp (σ n))

/-- Outer optimization over the identifiable class inside its compact
closure. All selected finite-stage designs are identifiable. Singular
designs enter only as subsequential limits, where divergence excludes them.
No converse bound for singular finite-stage designs is required. -/
theorem admissible_outer_infimum_tendsto_of_eventual_upper
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (r : X → ℕ → ℝ) (good : X → Prop) (J : X → ℝ) (m : ℝ)
    (hnonneg : ∀ p, good p → ∀ n, 0 ≤ r p n)
    (hmin : ∀ p, good p → m ≤ J p)
    (pstar : X) (hpstar : good pstar)
    (hupper : ∀ b > m, ∀ᶠ n in atTop, r pstar n < b)
    (hregular : ∀ (p : ℕ → X) (p₀ : X) (idx : ℕ → ℕ),
      (∀ n, good (p n)) → StrictMono idx → Tendsto p atTop (𝓝 p₀) → good p₀ →
      ∀ a < J p₀, ∀ᶠ n in atTop, a ≤ r (p n) (idx n))
    (hsingular : ∀ (p : ℕ → X) (p₀ : X) (idx : ℕ → ℕ),
      (∀ n, good (p n)) → StrictMono idx → Tendsto p atTop (𝓝 p₀) → ¬ good p₀ →
      Tendsto (fun n => r (p n) (idx n)) atTop atTop) :
    Tendsto (admissibleInfRisk r good) atTop (𝓝 m) := by
  have hlow := eventual_admissibleInfRisk_lower r good m ⟨pstar, hpstar⟩ (by
    intro p p₀ idx hp hidx hconv a ha
    by_cases hg : good p₀
    · exact hregular p p₀ idx hp hidx hconv hg a (ha.trans_le (hmin p₀ hg))
    · exact (hsingular p p₀ idx hp hidx hconv hg).eventually (eventually_ge_atTop a))
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨b, hab, hbm⟩ := exists_between ha
    filter_upwards [hlow b hbm] with n hn
    exact hab.trans_le hn
  · intro b hb
    filter_upwards [hupper b hb] with n hn
    exact (admissibleInfRisk_le r good hnonneg pstar hpstar n).trans_lt hn

/-- Fixed-design convergence form of the admissible-class outer minimax
limit theorem. The actual admissible infimum converges, even if minimizers
for the positive-noise problems do not exist. -/
theorem admissible_outer_infimum_tendsto
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (r : X → ℕ → ℝ) (good : X → Prop) (J : X → ℝ) (m : ℝ)
    (hnonneg : ∀ p, good p → ∀ n, 0 ≤ r p n)
    (hmin : ∀ p, good p → m ≤ J p)
    (pstar : X) (hpstar : good pstar)
    (hstar : Tendsto (r pstar) atTop (𝓝 m))
    (hregular : ∀ (p : ℕ → X) (p₀ : X) (idx : ℕ → ℕ),
      (∀ n, good (p n)) → StrictMono idx → Tendsto p atTop (𝓝 p₀) → good p₀ →
      ∀ a < J p₀, ∀ᶠ n in atTop, a ≤ r (p n) (idx n))
    (hsingular : ∀ (p : ℕ → X) (p₀ : X) (idx : ℕ → ℕ),
      (∀ n, good (p n)) → StrictMono idx → Tendsto p atTop (𝓝 p₀) → ¬ good p₀ →
      Tendsto (fun n => r (p n) (idx n)) atTop atTop) :
    Tendsto (admissibleInfRisk r good) atTop (𝓝 m) :=
  admissible_outer_infimum_tendsto_of_eventual_upper r good J m hnonneg hmin pstar hpstar
    (fun _ hb => hstar.eventually (gt_mem_nhds hb)) hregular hsingular

end Analog.CompactRiskOptimization
