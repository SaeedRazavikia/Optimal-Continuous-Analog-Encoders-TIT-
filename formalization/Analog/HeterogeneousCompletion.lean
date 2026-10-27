import Analog.CompletionSeparation
import Analog.HeterogeneousAnalyticRigidity
import Analog.HeterogeneousScore

/-!
# Actual heterogeneous-node completion and local moment recovery

These definitions use actual finite source tuples and their two normalized
statistics. Three selected nodes vary, a fourth node supplies alternative
completions, and every remaining node keeps a fixed valid source value.
Exact scalar computation then yields local recovery of both partial moment
sums wherever two completion readouts are locally injective.
-/

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Analog.HeterogeneousCompletion
open HeterogeneousRegularity HeterogeneousScore

/-- Replace the three selected source inputs, then set the fourth completion. -/
def completeInput {K : ℕ} (base : Fin K → ℝ) (i j k l : Fin K)
    (p : RigidityAnalysis.Triple) (t : ℝ) : Fin K → ℝ :=
  Function.update (Function.update (Function.update (Function.update base i p.1) j p.2.1)
    k p.2.2) l t

/-- The unnormalized sum of the three selected feature vectors. -/
def partialStatistic {K : ℕ} (γ : Fin K → ℝ → Plane) (i j k : Fin K)
    (p : RigidityAnalysis.Triple) : Plane := γ i p.1 + γ j p.2.1 + γ k p.2.2

/-- The contribution of every node outside the three selected nodes and
fourth completion node. Distinctness makes this the actual remaining sum. -/
def background {K : ℕ} (γ : Fin K → ℝ → Plane) (base : Fin K → ℝ)
    (i j k l : Fin K) : Plane :=
  (∑ n, γ n (base n)) - γ i (base i) - γ j (base j) - γ k (base k) - γ l (base l)

private theorem sum_apply_update {K : ℕ} {V : Type*} [AddCommGroup V]
    (E : Fin K → ℝ → V) (s : Fin K → ℝ) (i : Fin K) (v : ℝ) :
    (∑ n, E n (Function.update s i v n)) = (∑ n, E n (s n)) - E i (s i) + E i v := by
  classical
  have he : (fun n => E n (Function.update s i v n)) =
      Function.update (fun n => E n (s n)) i (E i v) := by
    funext n
    by_cases hn : n = i
    · subst n; simp
    · simp [hn]
  rw [he, Finset.sum_update_of_mem (Finset.mem_univ i),
    Finset.sum_sdiff_eq_sub (Finset.subset_univ {i})]
  simp only [Finset.sum_singleton]
  abel

/-- The exact finite-node aggregate decomposition for the completed input. -/
theorem sum_completeInput {K : ℕ} (γ : Fin K → ℝ → Plane)
    (base : Fin K → ℝ) (i j k l : Fin K)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (p : RigidityAnalysis.Triple) (t : ℝ) :
    (∑ n, γ n (completeInput base i j k l p t n)) =
      partialStatistic γ i j k p + background γ base i j k l + γ l t := by
  simp only [completeInput, sum_apply_update]
  simp only [Function.update_of_ne (Ne.symm hkl), Function.update_of_ne (Ne.symm hjl),
    Function.update_of_ne (Ne.symm hil), Function.update_of_ne (Ne.symm hjk),
    Function.update_of_ne (Ne.symm hik), Function.update_of_ne (Ne.symm hij)]
  dsimp [partialStatistic, background]
  abel

/-- Updating one node with a valid input preserves validity of the full tuple. -/
theorem update_valid {K : ℕ} {s : Fin K → ℝ} (hs : s ∈ ValidInput K)
    (i : Fin K) {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 1) :
    Function.update s i v ∈ ValidInput K := by
  intro n
  by_cases hn : n = i
  · subst n; simpa using hv
  · simpa [hn] using hs n

/-- Every completed tuple is an admissible physical input. -/
theorem completeInput_valid {K : ℕ} {base : Fin K → ℝ} (hb : base ∈ ValidInput K)
    (i j k l : Fin K) {p : RigidityAnalysis.Triple} {t : ℝ}
    (hp : p ∈ Icc (-1 : ℝ) 1 ×ˢ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1))
    (ht : t ∈ Icc (-1 : ℝ) 1) : completeInput base i j k l p t ∈ ValidInput K :=
  update_valid (update_valid (update_valid (update_valid hb i hp.1) j hp.2.1) k hp.2.2) l ht

/-- Desired scalar readout of the actual partial sum with one completion. -/
def completionReadout {K : ℕ} (γ : Fin K → ℝ → Plane) (ψ₁ ψ₂ : ℝ → ℝ)
    (base : Fin K → ℝ) (i j k l : Fin K) (t : ℝ) (p : Plane) : ℝ :=
  ψ₁ ((p.1 + (background γ base i j k l).1 + (γ l t).1) / (K : ℝ)) +
  ψ₂ ((p.2 + (background γ base i j k l).2 + (γ l t).2) / (K : ℝ))

/-- The readout formula is exactly the desired function evaluated on the
completed finite-node input, with the true factor 1/K. -/
theorem desired_completeInput {K : ℕ} (γ : Fin K → ℝ → Plane) (ψ₁ ψ₂ : ℝ → ℝ)
    (base : Fin K → ℝ) (i j k l : Fin K)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (p : RigidityAnalysis.Triple) (t : ℝ) :
    ψ₁ (meanStatistic γ (completeInput base i j k l p t)).1 +
      ψ₂ (meanStatistic γ (completeInput base i j k l p t)).2 =
    completionReadout γ ψ₁ ψ₂ base i j k l t (partialStatistic γ i j k p) := by
  have hs := sum_completeInput γ base i j k l hij hik hil hjk hjl hkl p t
  have h₁ := congrArg Prod.fst hs
  have h₂ := congrArg Prod.snd hs
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.fst_add, Prod.snd_add] at h₁ h₂
  simp only [meanStatistic, completionReadout, h₁, h₂]

/-- Partial received collisions persist under the same physical completion. -/
theorem received_completeInput_collision {K : ℕ} (E : Fin K → ℝ → Plane)
    (base : Fin K → ℝ) (i j k l : Fin K)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (p q : RigidityAnalysis.Triple) (t : ℝ)
    (heq : partialStatistic E i j k p = partialStatistic E i j k q) :
    received E (completeInput base i j k l p t) =
      received E (completeInput base i j k l q t) := by
  have hsum : (∑ n, E n (completeInput base i j k l p t n)) =
      ∑ n, E n (completeInput base i j k l q t n) := by
    rw [sum_completeInput E base i j k l hij hik hil hjk hjl hkl,
      sum_completeInput E base i j k l hij hik hil hjk hjl hkl, heq]
  apply Prod.ext
  · simpa only [received, Prod.fst_sum] using congrArg Prod.fst hsum
  · simpa only [received, Prod.snd_sum] using congrArg Prod.snd hsum

/-- Exact computation identifies every scalar completion value from a
partial received collision. No regularity of the scalar decoder is used. -/
theorem collision_preserves_completion {K : ℕ}
    (γ E : Fin K → ℝ → Plane) (ψ₁ ψ₂ : ℝ → ℝ)
    (hexact : ExactComputation γ (fun m => ψ₁ m.1 + ψ₂ m.2) E)
    (base : Fin K → ℝ) (hb : base ∈ ValidInput K) (i j k l : Fin K)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (p q : RigidityAnalysis.Triple)
    (hp : p ∈ Icc (-1 : ℝ) 1 ×ˢ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1))
    (hq : q ∈ Icc (-1 : ℝ) 1 ×ˢ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1))
    (heq : partialStatistic E i j k p = partialStatistic E i j k q)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    completionReadout γ ψ₁ ψ₂ base i j k l t (partialStatistic γ i j k p) =
      completionReadout γ ψ₁ ψ₂ base i j k l t (partialStatistic γ i j k q) := by
  have hval := hexact _ (completeInput_valid hb i j k l hp ht)
    _ (completeInput_valid hb i j k l hq ht)
    (received_completeInput_collision E base i j k l hij hik hil hjk hjl hkl p q t heq)
  change ψ₁ (meanStatistic γ (completeInput base i j k l p t)).1 +
      ψ₂ (meanStatistic γ (completeInput base i j k l p t)).2 =
    ψ₁ (meanStatistic γ (completeInput base i j k l q t)).1 +
      ψ₂ (meanStatistic γ (completeInput base i j k l q t)).2 at hval
  simpa only [desired_completeInput γ ψ₁ ψ₂ base i j k l hij hik hil hjk hjl hkl] using hval

/-- The pair of alternative-completion scalar readouts. -/
def pairedReadout {K : ℕ} (γ : Fin K → ℝ → Plane) (ψ₁ ψ₂ : ℝ → ℝ)
    (base : Fin K → ℝ) (i j k l : Fin K) (t u : ℝ) (p : Plane) : Plane :=
  (completionReadout γ ψ₁ ψ₂ base i j k l t p,
   completionReadout γ ψ₁ ψ₂ base i j k l u p)

/-- Local moment recovery from exact computation and injectivity of the two
actual completion readouts, on arbitrary valid source triples. -/
theorem local_moment_recovery {K : ℕ}
    (γ E : Fin K → ℝ → Plane) (ψ₁ ψ₂ : ℝ → ℝ)
    (hexact : ExactComputation γ (fun m => ψ₁ m.1 + ψ₂ m.2) E)
    (base : Fin K → ℝ) (hb : base ∈ ValidInput K) (i j k l : Fin K)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    {t u : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (hu : u ∈ Icc (-1 : ℝ) 1)
    {B : Set Plane} (hinj : InjOn (pairedReadout γ ψ₁ ψ₂ base i j k l t u) B)
    (p q : RigidityAnalysis.Triple)
    (hp : p ∈ Icc (-1 : ℝ) 1 ×ˢ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1))
    (hq : q ∈ Icc (-1 : ℝ) 1 ×ˢ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1))
    (hpB : partialStatistic γ i j k p ∈ B) (hqB : partialStatistic γ i j k q ∈ B)
    (heq : partialStatistic E i j k p = partialStatistic E i j k q) :
    partialStatistic γ i j k p = partialStatistic γ i j k q := by
  apply hinj hpB hqB
  apply Prod.ext
  · exact collision_preserves_completion γ E ψ₁ ψ₂ hexact base hb i j k l
      hij hik hil hjk hjl hkl p q hp hq heq ht
  · exact collision_preserves_completion γ E ψ₁ ψ₂ hexact base hb i j k l
      hij hik hil hjk hjl hkl p q hp hq heq hu

/-- A point at which two valid physical completions identify nearby partial
moment sums. Every node outside the four selected indices is fixed at zero. -/
def localIdentifyingSet {K : ℕ} (γ : Fin K → ℝ → Plane) (ψ₁ ψ₂ : ℝ → ℝ)
    (i j k : Fin K) : Set Plane :=
  {p | ∃ l : Fin K, i ≠ l ∧ j ≠ l ∧ k ≠ l ∧
    ∃ t ∈ Icc (-1 : ℝ) 1, ∃ u ∈ Icc (-1 : ℝ) 1,
    ∃ B ∈ 𝓝 p, InjOn (pairedReadout γ ψ₁ ψ₂ (fun _ => 0) i j k l t u) B}

/-- On the actual identifying set, exact computation recovers partial
statistics from partial encoded sums in a full neighborhood. -/
theorem identifying_collision_neighborhood {K : ℕ}
    (γ E : Fin K → ℝ → Plane) (ψ₁ ψ₂ : ℝ → ℝ)
    (hexact : ExactComputation γ (fun m => ψ₁ m.1 + ψ₂ m.2) E)
    (i j k : Fin K) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {p : Plane} (hp : p ∈ localIdentifyingSet γ ψ₁ ψ₂ i j k) :
    ∃ B ∈ 𝓝 p, ∀ v ∈ Icc (-1 : ℝ) 1 ×ˢ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1),
      ∀ w ∈ Icc (-1 : ℝ) 1 ×ˢ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1),
      partialStatistic γ i j k v ∈ B → partialStatistic γ i j k w ∈ B →
      partialStatistic E i j k v = partialStatistic E i j k w →
      partialStatistic γ i j k v = partialStatistic γ i j k w := by
  obtain ⟨l, hil, hjl, hkl, t, ht, u, hu, B, hB, hinj⟩ := hp
  refine ⟨B, hB, ?_⟩
  intro v hv w hw hvB hwB heq
  exact local_moment_recovery γ E ψ₁ ψ₂ hexact (fun _ => 0)
    (fun _ => by norm_num) i j k l hij hik hil hjk hjl hkl ht hu hinj v w hv hw hvB hwB heq

private theorem scaled_receiver_deriv (ψ : ℝ → ℝ) {q r a K : ℝ}
    (hd : HasStrictDerivAt ψ a ((q + r) / K)) :
    HasStrictDerivAt (fun s => ψ ((s + r) / K)) (a / K) q := by
  convert hd.comp q (((hasStrictDerivAt_id q).add_const r).div_const K) using 1
  simp [div_eq_mul_inv]

/-- The genuine inverse-function theorem for the paired physical readout.
The determinant is evaluated at the actual normalized means and its 1/K²
scaling is proved explicitly. -/
theorem pairedReadout_locally_injective {K : ℕ} (hK : (K : ℝ) ≠ 0)
    (γ : Fin K → ℝ → Plane) (ψ₁ ψ₂ : ℝ → ℝ)
    (base : Fin K → ℝ) (i j k l : Fin K) (t u : ℝ) (p : Plane)
    {aₜ bt au bu : ℝ}
    (hat : HasStrictDerivAt ψ₁ aₜ
      ((p.1 + (background γ base i j k l).1 + (γ l t).1) / (K : ℝ)))
    (hbt : HasStrictDerivAt ψ₂ bt
      ((p.2 + (background γ base i j k l).2 + (γ l t).2) / (K : ℝ)))
    (hau : HasStrictDerivAt ψ₁ au
      ((p.1 + (background γ base i j k l).1 + (γ l u).1) / (K : ℝ)))
    (hbu : HasStrictDerivAt ψ₂ bu
      ((p.2 + (background γ base i j k l).2 + (γ l u).2) / (K : ℝ)))
    (hdet : aₜ * bu - au * bt ≠ 0) :
    ∃ B ∈ 𝓝 p, InjOn (pairedReadout γ ψ₁ ψ₂ base i j k l t u) B := by
  have hdet' : (aₜ / (K : ℝ)) * (bu / K) - (bt / K) * (au / K) ≠ 0 := by
    intro heq
    apply hdet
    field_simp [hK] at heq
    nlinarith
  have hat' := scaled_receiver_deriv ψ₁ (by simpa only [add_assoc] using hat)
  have hbt' := scaled_receiver_deriv ψ₂ (by simpa only [add_assoc] using hbt)
  have hau' := scaled_receiver_deriv ψ₁ (by simpa only [add_assoc] using hau)
  have hbu' := scaled_receiver_deriv ψ₂ (by simpa only [add_assoc] using hbu)
  have hd : HasStrictFDerivAt (pairedReadout γ ψ₁ ψ₂ base i j k l t u)
      (GeneralRigidity.pairDerivativeEquiv (aₜ / (K : ℝ)) (bt / K) (au / K) (bu / K) hdet' :
        Plane →L[ℝ] Plane) p := by
    rw [GeneralRigidity.pairDerivativeEquiv_coe]
    convert pairStatistic_hasStrictFDerivAt hat' hbt' hau' hbu' using 1
    · ext q <;> simp [pairedReadout, completionReadout, HeterogeneousRegularity.pairStatistic,
        add_assoc]
  let g := hd.localInverse _ _ p
  refine ⟨{q | g (pairedReadout γ ψ₁ ψ₂ base i j k l t u q) = q},
    hd.eventually_left_inverse, ?_⟩
  intro q hq r hr heq
  exact hq.symm.trans ((congrArg g heq).trans hr)

end Analog.HeterogeneousCompletion
