import Analog.AdditiveStatistics

/-!
# Common-completion identification for two prescribed additive statistics

This module verifies the collision step of the unified extension. Exact
computation and the stated local identification hypothesis imply that equal
encoded triple sums have equal prescribed triple statistics. The completion
is an actual valid K-input list, with an arbitrary common filler input.

The identification hypothesis is an explicit assumption. This module does
not derive it from analyticity, prove topological factorization, smooth a
continuous encoder, or establish the full encoder classification.
-/

noncomputable section

namespace Analog.CompletionIdentification

open Analog.ArbitraryEncoder Analog.AdditiveStatistics Set

/-- Evaluate the desired function after a common fourth input and a fixed
sum of filler statistics. Each coordinate is divided by the terminal count. -/
def completionValue (K : ℕ) (γ : ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (d p : ℝ × ℝ) (x : ℝ) : ℝ :=
  F ((p.1 + (γ x).1 + d.1) / (K : ℝ),
     (p.2 + (γ x).2 + d.2) / (K : ℝ))

/-- The common-completion identification condition on the prescribed set B.
Openness and density are needed later in the manuscript's rigidity proof,
but are not needed for this collision implication. -/
def IdentifiesOn (K : ℕ) (γ : ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (d : ℝ × ℝ) (B : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ B, ∀ p' ∈ B,
    (∀ x ∈ Ioo (-1 : ℝ) 1,
      completionValue K γ F d p x = completionValue K γ F d p' x) → p = p'

/-- Append a common fourth input and K-4 copies of a common filler. -/
def completeTripleAt (K : ℕ) (xs : List ℝ) (x filler : ℝ) : List ℝ :=
  xs ++ x :: List.replicate (K - 4) filler

lemma completeTripleAt_valid {K : ℕ} (hK : 4 ≤ K) {xs : List ℝ}
    (hxs : ValidInput 3 xs) {x filler : ℝ} (hx : InSource x)
    (hfiller : InSource filler) : ValidInput K (completeTripleAt K xs x filler) := by
  constructor
  · simp only [completeTripleAt, List.length_append, List.length_cons,
      List.length_replicate, hxs.1]
    omega
  · intro y hy
    simp only [completeTripleAt, List.mem_append, List.mem_cons,
      List.mem_replicate] at hy
    rcases hy with hy | hy | ⟨_, hy⟩
    · exact hxs.2 y hy
    · simpa [hy] using hx
    · simpa [hy] using hfiller

lemma statisticSum_completeTripleAt (K : ℕ) (γ : ℝ → ℝ × ℝ)
    (xs : List ℝ) (x filler : ℝ) :
    statisticSum γ (completeTripleAt K xs x filler) =
      statisticSum γ xs + γ x + (K - 4) • γ filler := by
  simp [statisticSum, completeTripleAt, add_assoc]

lemma received_completeTripleAt_collision (K : ℕ) (E : ℝ → ℝ × ℝ)
    (xs ys : List ℝ) (x filler : ℝ)
    (hcollision : received E xs = received E ys) :
    received E (completeTripleAt K xs x filler) =
      received E (completeTripleAt K ys x filler) := by
  simp only [received, completeTripleAt, List.map_append, List.sum_append]
  change received E xs + _ = received E ys + _
  rw [hcollision]

lemma desiredFunction_completeTripleAt (K : ℕ) (γ : ℝ → ℝ × ℝ)
    (F : ℝ × ℝ → ℝ) (xs : List ℝ) (x filler : ℝ) :
    desiredFunction K γ F (completeTripleAt K xs x filler) =
      completionValue K γ F ((K - 4) • γ filler) (statisticSum γ xs) x := by
  simp only [desiredFunction, meanStatistic, statisticSum_completeTripleAt,
    completionValue, Prod.fst_add, Prod.snd_add]

/-- Concrete bridge from an encoded triple collision to equality of all
common-completion function values. The completed lists are valid K-input
configurations, so the exactness assumption is used on its actual domain. -/
theorem exact_completion_values {K : ℕ} (hK : 4 ≤ K)
    (γ : ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ) (E : ℝ → ℝ × ℝ)
    (hexact : ExactComputation K γ F E)
    (xs ys : List ℝ) (hxs : ValidInput 3 xs) (hys : ValidInput 3 ys)
    (filler : ℝ) (hfiller : InSource filler)
    (hcollision : received E xs = received E ys)
    (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    completionValue K γ F ((K - 4) • γ filler) (statisticSum γ xs) x =
      completionValue K γ F ((K - 4) • γ filler) (statisticSum γ ys) x := by
  have hxsource : InSource x := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hh := hexact (completeTripleAt K xs x filler) (completeTripleAt K ys x filler)
    (completeTripleAt_valid hK hxs hxsource hfiller)
    (completeTripleAt_valid hK hys hxsource hfiller)
    (received_completeTripleAt_collision K E xs ys x filler hcollision)
  simpa only [desiredFunction_completeTripleAt] using hh

/-- The collision implication used in local factorization for the unified
extension. The triples may include endpoints; the common fourth inputs range
over the interior interval as in the manuscript's identification condition. -/
theorem triple_collision_preserves_statistics {K : ℕ} (hK : 4 ≤ K)
    (γ : ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ) (E : ℝ → ℝ × ℝ)
    (hexact : ExactComputation K γ F E)
    (filler : ℝ) (hfiller : InSource filler) (B : Set (ℝ × ℝ))
    (hidentify : IdentifiesOn K γ F ((K - 4) • γ filler) B)
    (xs ys : List ℝ) (hxs : ValidInput 3 xs) (hys : ValidInput 3 ys)
    (hxsB : statisticSum γ xs ∈ B) (hysB : statisticSum γ ys ∈ B)
    (hcollision : received E xs = received E ys) :
    statisticSum γ xs = statisticSum γ ys := by
  apply hidentify (statisticSum γ xs) hxsB (statisticSum γ ys) hysB
  intro x hx
  exact exact_completion_values hK γ F E hexact xs ys hxs hys filler hfiller
    hcollision x hx

/-- An injective scalar transformation preserves the completion
identification condition in both directions. -/
theorem identifiesOn_postcomp_iff (K : ℕ) (γ : ℝ → ℝ × ℝ)
    (F : ℝ × ℝ → ℝ) (d : ℝ × ℝ) (B : Set (ℝ × ℝ))
    (h : ℝ → ℝ) (hh : Function.Injective h) :
    IdentifiesOn K γ (h ∘ F) d B ↔ IdentifiesOn K γ F d B := by
  constructor
  · intro hidentify p hp p' hp' hequal
    apply hidentify p hp p' hp'
    intro x hx
    exact congrArg h (hequal x hx)
  · intro hidentify p hp p' hp' hequal
    apply hidentify p hp p' hp'
    intro x hx
    exact hh (hequal x hx)

end Analog.CompletionIdentification
