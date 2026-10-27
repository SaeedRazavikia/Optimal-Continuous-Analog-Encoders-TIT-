import Analog.HeterogeneousCompletion
import Analog.HeterogeneousMomentRanges

/-! # Dense physical completion identification

The normalized dense separation theorem is transferred back to actual
finite-node partial statistics. Receiver differentiability and local
invertibility are derived from the stated C¹ assumptions.
-/

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Analog.HeterogeneousCompletionDensity
open HeterogeneousRegularity HeterogeneousCompletion CompletionSeparation

/-- The affine change from actual partial sums to the normalized means
before adding the fourth node's contribution. -/
def normalization (K : ℝ) (hK : K ≠ 0) (b : Plane) : Plane ≃ₜ Plane where
  toFun p := ((p.1 + b.1) / K, (p.2 + b.2) / K)
  invFun p := (K * p.1 - b.1, K * p.2 - b.2)
  left_inv p := by ext <;> dsimp <;> field_simp <;> ring
  right_inv p := by ext <;> dsimp <;> field_simp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Receiver alternatives persist on every smaller interval. -/
theorem ReceiverAlternative.mono {D E : Set ℝ} {ψ : ℝ → ℝ}
    (h : ReceiverAlternative D ψ) (hED : E ⊆ D) : ReceiverAlternative E ψ := by
  rcases h with ⟨α, β, hβ, haff⟩ | hna
  · exact Or.inl ⟨α, β, hβ, fun s hs => haff s (hED hs)⟩
  · exact Or.inr (fun a b hab hsub => hna a b hab (hsub.trans hED))

/-- The nowhere-affine receiver condition persists under domain restriction. -/
theorem NoAffineInterval.mono {D E : Set ℝ} {ψ : ℝ → ℝ}
    (h : NoAffineInterval D ψ) (hED : E ⊆ D) : NoAffineInterval E ψ :=
  fun a b hab hsub => h a b hab (hsub.trans hED)

/-- Dense moment identification on any actual partial-statistic rectangle
whose completed coordinate intervals lie in the receiver domains. The
features and their ranges use the true normalization 1/K. -/
theorem dense_identifying_on_rectangle {K : ℕ} (hK : (K : ℝ) ≠ 0)
    (γ : Fin K → ℝ → Plane) (ψ₁ ψ₂ : ℝ → ℝ)
    (i j k l : Fin K) (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l)
    {a b c d e f g h : ℝ} (hcd : c < d) (hgh : g < h)
    (hx : MapsTo (fun t => (γ l t).1 / (K : ℝ)) (Icc (-1 : ℝ) 1) (Icc c d))
    (hy : MapsTo (fun t => (γ l t).2 / (K : ℝ)) (Icc (-1 : ℝ) 1) (Icc g h))
    (hsx : ∀ q ∈ Icc c d, ∃ t ∈ Icc (-1 : ℝ) 1, (γ l t).1 / (K : ℝ) = q)
    (hsy : ∀ q ∈ Icc g h, ∃ t ∈ Icc (-1 : ℝ) 1, (γ l t).2 / (K : ℝ) = q)
    (hC₁ : ContDiffOn ℝ 1 ψ₁ (Ioo (a + c) (b + d)))
    (hC₂ : ContDiffOn ℝ 1 ψ₂ (Ioo (e + g) (f + h)))
    (halt₁ : ReceiverAlternative (Ioo (a + c) (b + d)) ψ₁)
    (halt₂ : ReceiverAlternative (Ioo (e + g) (f + h)) ψ₂)
    (hna : NoAffineInterval (Ioo (a + c) (b + d)) ψ₁ ∨
      NoAffineInterval (Ioo (e + g) (f + h)) ψ₂)
    (hind : GeneralRigidity.NotInAffineLine (Icc (-1 : ℝ) 1)
      (fun t => (γ l t).1) (fun t => (γ l t).2))
    {p : Plane}
    (hp : normalization (K : ℝ) hK (background γ (fun _ => 0) i j k l) p ∈
      Ioo a b ×ˢ Ioo e f) :
    p ∈ closure (localIdentifyingSet γ ψ₁ ψ₂ i j k) := by
  let N := normalization (K : ℝ) hK (background γ (fun _ => 0) i j k l)
  let L := separatingLocus (Icc (-1 : ℝ) 1)
    (fun t => (γ l t).1 / (K : ℝ)) (fun t => (γ l t).2 / (K : ℝ))
    (deriv ψ₁) (deriv ψ₂) ∩ (Ioo a b ×ˢ Ioo e f)
  have hd₁ : ∀ z ∈ Ioo (a + c) (b + d), HasDerivAt ψ₁ (deriv ψ₁ z) z :=
    fun z hz => ((hC₁ z hz).contDiffAt (Ioo_mem_nhds hz.1 hz.2)).differentiableAt le_rfl |>.hasDerivAt
  have hd₂ : ∀ z ∈ Ioo (e + g) (f + h), HasDerivAt ψ₂ (deriv ψ₂ z) z :=
    fun z hz => ((hC₂ z hz).contDiffAt (Ioo_mem_nhds hz.1 hz.2)).differentiableAt le_rfl |>.hasDerivAt
  have hdense := (dense_open_separation_of_receiver_alternatives hcd hgh
    (Icc (-1 : ℝ) 1) (fun t => (γ l t).1 / (K : ℝ)) (fun t => (γ l t).2 / (K : ℝ))
    ψ₁ ψ₂ (deriv ψ₁) (deriv ψ₂) (u := 0) (by norm_num) hx hy hsx hsy
    (hC₁.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl)
    (hC₂.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl)
    hd₁ hd₂ halt₁ halt₂ hna (independent_div _ _ hK hind)).2
  have hp' : p ∈ closure (N ⁻¹' L) := by
    rw [← N.preimage_closure]
    exact hdense hp
  apply closure_mono (t := localIdentifyingSet γ ψ₁ ψ₂ i j k) ?_ hp'
  intro q hq
  obtain ⟨⟨t, ht, u, hu, hdet⟩, hqr⟩ := hq
  have ht₁ : (N q).1 + (γ l t).1 / (K : ℝ) ∈ Ioo (a + c) (b + d) :=
    ⟨add_lt_add_of_lt_of_le hqr.1.1 (hx ht).1,
      add_lt_add_of_lt_of_le hqr.1.2 (hx ht).2⟩
  have hu₁ : (N q).1 + (γ l u).1 / (K : ℝ) ∈ Ioo (a + c) (b + d) :=
    ⟨add_lt_add_of_lt_of_le hqr.1.1 (hx hu).1,
      add_lt_add_of_lt_of_le hqr.1.2 (hx hu).2⟩
  have ht₂ : (N q).2 + (γ l t).2 / (K : ℝ) ∈ Ioo (e + g) (f + h) :=
    ⟨add_lt_add_of_lt_of_le hqr.2.1 (hy ht).1,
      add_lt_add_of_lt_of_le hqr.2.2 (hy ht).2⟩
  have hu₂ : (N q).2 + (γ l u).2 / (K : ℝ) ∈ Ioo (e + g) (f + h) :=
    ⟨add_lt_add_of_lt_of_le hqr.2.1 (hy hu).1,
      add_lt_add_of_lt_of_le hqr.2.2 (hy hu).2⟩
  refine ⟨l, hil, hjl, hkl, t, ht, u, hu, ?_⟩
  apply pairedReadout_locally_injective hK γ ψ₁ ψ₂ (fun _ => 0) i j k l t u q
  · simpa [N, normalization, ← add_div] using
      ((hC₁ _ ht₁).contDiffAt (Ioo_mem_nhds ht₁.1 ht₁.2)).hasStrictDerivAt le_rfl
  · simpa [N, normalization, ← add_div] using
      ((hC₂ _ ht₂).contDiffAt (Ioo_mem_nhds ht₂.1 ht₂.2)).hasStrictDerivAt le_rfl
  · simpa [N, normalization, ← add_div] using
      ((hC₁ _ hu₁).contDiffAt (Ioo_mem_nhds hu₁.1 hu₁.2)).hasStrictDerivAt le_rfl
  · simpa [N, normalization, ← add_div] using
      ((hC₂ _ hu₂).contDiffAt (Ioo_mem_nhds hu₂.1 hu₂.2)).hasStrictDerivAt le_rfl
  · simpa [N, normalization, ← add_div] using sub_ne_zero.mpr hdet

/-- The exact lower endpoint of a feature's attainable coordinate range. -/
def featureLower (φ : ℝ → ℝ) : ℝ := sInf (φ '' Icc (-1 : ℝ) 1)

/-- The exact upper endpoint of a feature's attainable coordinate range. -/
def featureUpper (φ : ℝ → ℝ) : ℝ := sSup (φ '' Icc (-1 : ℝ) 1)

/-- The open attainable coordinate interval of the normalized aggregate. -/
def meanDomain {K : ℕ} (φ : Fin K → ℝ → ℝ) : Set ℝ :=
  Ioo ((∑ i, featureLower (φ i)) / (K : ℝ)) ((∑ i, featureUpper (φ i)) / (K : ℝ))

/-- The infimum/supremum definitions are actual attained interval endpoints,
and both feature coordinate intervals are nondegenerate. -/
theorem exact_feature_ranges (φ₁ φ₂ : ℝ → ℝ)
    (h₁ : ContinuousOn φ₁ (Icc (-1 : ℝ) 1))
    (h₂ : ContinuousOn φ₂ (Icc (-1 : ℝ) 1))
    (hind : GeneralRigidity.NotInAffineLine (Icc (-1 : ℝ) 1) φ₁ φ₂) :
    featureLower φ₁ < featureUpper φ₁ ∧ featureLower φ₂ < featureUpper φ₂ ∧
    MapsTo φ₁ (Icc (-1 : ℝ) 1) (Icc (featureLower φ₁) (featureUpper φ₁)) ∧
    MapsTo φ₂ (Icc (-1 : ℝ) 1) (Icc (featureLower φ₂) (featureUpper φ₂)) ∧
    (∀ q ∈ Icc (featureLower φ₁) (featureUpper φ₁), ∃ t ∈ Icc (-1 : ℝ) 1, φ₁ t = q) ∧
    (∀ q ∈ Icc (featureLower φ₂) (featureUpper φ₂), ∃ t ∈ Icc (-1 : ℝ) 1, φ₂ t = q) := by
  obtain ⟨c, d, g, h, hcd, hgh, hx, hy, hsx, hsy⟩ :=
    independent_coordinate_ranges (by norm_num : (-1 : ℝ) ≤ 1) φ₁ φ₂ h₁ h₂ hind
  have hix : φ₁ '' Icc (-1 : ℝ) 1 = Icc c d := by
    ext q
    exact ⟨by rintro ⟨t, ht, rfl⟩; exact hx ht, fun hq => hsx q hq⟩
  have hiy : φ₂ '' Icc (-1 : ℝ) 1 = Icc g h := by
    ext q
    exact ⟨by rintro ⟨t, ht, rfl⟩; exact hy ht, fun hq => hsy q hq⟩
  simpa [featureLower, featureUpper, hix, hiy, csInf_Icc hcd.le,
    csSup_Icc hcd.le, csInf_Icc hgh.le, csSup_Icc hgh.le] using
    And.intro hcd (And.intro hgh (And.intro hx (And.intro hy (And.intro hsx hsy))))

/-- Four nodes provide a completion index outside any three selected nodes. -/
theorem exists_fourth_node {K : ℕ} (hK : 4 ≤ K) (i j k : Fin K) :
    ∃ l : Fin K, i ≠ l ∧ j ≠ l ∧ k ≠ l := by
  classical
  have hcard : ({i, j, k} : Finset (Fin K)).card < Fintype.card (Fin K) := by
    have hh := Finset.card_le_three (a := i) (b := j) (c := k)
    simpa only [Fintype.card_fin] using lt_of_le_of_lt hh hK
  by_contra hn
  have hs : (Finset.univ : Finset (Fin K)) ⊆ {i, j, k} := by
    intro l _
    by_contra hl
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    exact hn ⟨l, Ne.symm hl.1, Ne.symm hl.2.1, Ne.symm hl.2.2⟩
  have hc := Finset.card_le_card hs
  simp only [Finset.card_univ] at hc
  omega

/-- A positive normalization preserves exact scalar interval ranges. -/
theorem normalized_scalar_range (φ : ℝ → ℝ) {K c d : ℝ} (hK : 0 < K)
    (hb : MapsTo φ (Icc (-1 : ℝ) 1) (Icc c d))
    (hs : ∀ q ∈ Icc c d, ∃ t ∈ Icc (-1 : ℝ) 1, φ t = q) :
    MapsTo (fun t => φ t / K) (Icc (-1 : ℝ) 1) (Icc (c / K) (d / K)) ∧
    ∀ q ∈ Icc (c / K) (d / K), ∃ t ∈ Icc (-1 : ℝ) 1, φ t / K = q := by
  constructor
  · intro t ht
    exact ⟨div_le_div_of_nonneg_right (hb ht).1 hK.le,
      div_le_div_of_nonneg_right (hb ht).2 hK.le⟩
  · intro q hq
    obtain ⟨t, ht, heq⟩ := hs (q * K)
      ⟨(div_le_iff₀ hK).mp hq.1, (le_div_iff₀ hK).mp hq.2⟩
    exact ⟨t, ht, by rw [heq, mul_div_cancel_right₀ _ hK.ne']⟩

/-- The actual heterogeneous identifying set is dense at every regular
three-node statistic. Exact feature ranges, strict interior of regular
statistics, all fixed-node contributions, and the factor 1/K are derived;
no density, chart, completion, or extra differentiability premise is used. -/
theorem dense_identification {K : ℕ} (hK : 4 ≤ K)
    (φ₁ φ₂ : Fin K → ℝ → ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (h₁ : ∀ i, ContinuousOn (φ₁ i) (Icc (-1 : ℝ) 1))
    (h₂ : ∀ i, ContinuousOn (φ₂ i) (Icc (-1 : ℝ) 1))
    (hind : ∀ i, GeneralRigidity.NotInAffineLine (Icc (-1 : ℝ) 1) (φ₁ i) (φ₂ i))
    (hC₁ : ContDiffOn ℝ 1 ψ₁ (meanDomain φ₁))
    (hC₂ : ContDiffOn ℝ 1 ψ₂ (meanDomain φ₂))
    (halt₁ : ReceiverAlternative (meanDomain φ₁) ψ₁)
    (halt₂ : ReceiverAlternative (meanDomain φ₂) ψ₂)
    (hna : NoAffineInterval (meanDomain φ₁) ψ₁ ∨ NoAffineInterval (meanDomain φ₂) ψ₂) :
    HeterogeneousAnalyticRigidity.DenseIdentification φ₁ φ₂
      (localIdentifyingSet (fun i t => (φ₁ i t, φ₂ i t)) ψ₁ ψ₂) := by
  classical
  let γ : Fin K → ℝ → Plane := fun i t => (φ₁ i t, φ₂ i t)
  let lo₁ : Fin K → ℝ := fun i => featureLower (φ₁ i)
  let hi₁ : Fin K → ℝ := fun i => featureUpper (φ₁ i)
  let lo₂ : Fin K → ℝ := fun i => featureLower (φ₂ i)
  let hi₂ : Fin K → ℝ := fun i => featureUpper (φ₂ i)
  have hr (i : Fin K) := exact_feature_ranges (φ₁ i) (φ₂ i) (h₁ i) (h₂ i) (hind i)
  have hb₁ : ∀ i t, t ∈ Icc (-1 : ℝ) 1 → φ₁ i t ∈ Icc (lo₁ i) (hi₁ i) :=
    fun i _ ht => (hr i).2.2.1 ht
  have hb₂ : ∀ i t, t ∈ Icc (-1 : ℝ) 1 → φ₂ i t ∈ Icc (lo₂ i) (hi₂ i) :=
    fun i _ ht => (hr i).2.2.2.1 ht
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  intro i j k hij hik hjk x hx y hy z hz hd
  obtain ⟨l, hil, hjl, hkl⟩ := exists_fourth_node hK i j k
  let β := background γ (fun _ => 0) i j k l
  let a := (lo₁ i + lo₁ j + lo₁ k + β.1) / (K : ℝ)
  let b := (hi₁ i + hi₁ j + hi₁ k + β.1) / (K : ℝ)
  let e := (lo₂ i + lo₂ j + lo₂ k + β.2) / (K : ℝ)
  let f := (hi₂ i + hi₂ j + hi₂ k + β.2) / (K : ℝ)
  have hbg₁ := HeterogeneousMomentRanges.background_bounds (fun n => φ₁ n 0) lo₁ hi₁
    (fun n => hb₁ n 0 (by norm_num)) i j k l hij hik hil hjk hjl hkl
  have hbg₂ := HeterogeneousMomentRanges.background_bounds (fun n => φ₂ n 0) lo₂ hi₂
    (fun n => hb₂ n 0 (by norm_num)) i j k l hij hik hil hjk hjl hkl
  have hsub₁ : Ioo (a + lo₁ l / (K : ℝ)) (b + hi₁ l / (K : ℝ)) ⊆ meanDomain φ₁ := by
    simpa [a, b, β, background, γ, lo₁, hi₁, meanDomain, Prod.fst_sum] using
      HeterogeneousMomentRanges.normalized_completion_interval_subset hKpos hbg₁.1 hbg₁.2
  have hsub₂ : Ioo (e + lo₂ l / (K : ℝ)) (f + hi₂ l / (K : ℝ)) ⊆ meanDomain φ₂ := by
    simpa [e, f, β, background, γ, lo₂, hi₂, meanDomain, Prod.snd_sum] using
      HeterogeneousMomentRanges.normalized_completion_interval_subset hKpos hbg₂.1 hbg₂.2
  have hn₁ := normalized_scalar_range (φ₁ l) hKpos (hr l).2.2.1 (hr l).2.2.2.2.1
  have hn₂ := normalized_scalar_range (φ₂ l) hKpos (hr l).2.2.2.1 (hr l).2.2.2.2.2
  have hstrict := HeterogeneousMomentRanges.regular_triple_sum_strict φ₁ φ₂ lo₁ hi₁ lo₂ hi₂
    hb₁ hb₂ i j k hx hy hz hd
  apply dense_identifying_on_rectangle hKpos.ne' γ ψ₁ ψ₂ i j k l hil hjl hkl
    (a := a) (b := b) (e := e) (f := f)
    (div_lt_div_of_pos_right (hr l).1 hKpos)
    (div_lt_div_of_pos_right (hr l).2.1 hKpos) hn₁.1 hn₂.1 hn₁.2 hn₂.2
    (hC₁.mono hsub₁) (hC₂.mono hsub₂)
    (ReceiverAlternative.mono halt₁ hsub₁) (ReceiverAlternative.mono halt₂ hsub₂)
    (hna.elim (fun h => Or.inl (NoAffineInterval.mono h hsub₁))
      (fun h => Or.inr (NoAffineInterval.mono h hsub₂))) (hind l)
  change ((φ₁ i x + φ₁ j y + φ₁ k z + β.1) / (K : ℝ) ∈ Ioo a b) ∧
    ((φ₂ i x + φ₂ j y + φ₂ k z + β.2) / (K : ℝ) ∈ Ioo e f)
  constructor
  · exact ⟨div_lt_div_of_pos_right (add_lt_add_right hstrict.1.1 β.1) hKpos,
      div_lt_div_of_pos_right (add_lt_add_right hstrict.1.2 β.1) hKpos⟩
  · exact ⟨div_lt_div_of_pos_right (add_lt_add_right hstrict.2.1 β.2) hKpos,
      div_lt_div_of_pos_right (add_lt_add_right hstrict.2.2 β.2) hKpos⟩

/-- Both global mean intervals have distinct endpoints; this follows from
per-node independence and the positive node count. -/
theorem mean_endpoints_lt {K : ℕ} (hK : 0 < K)
    (φ₁ φ₂ : Fin K → ℝ → ℝ)
    (h₁ : ∀ i, ContinuousOn (φ₁ i) (Icc (-1 : ℝ) 1))
    (h₂ : ∀ i, ContinuousOn (φ₂ i) (Icc (-1 : ℝ) 1))
    (hind : ∀ i, GeneralRigidity.NotInAffineLine (Icc (-1 : ℝ) 1) (φ₁ i) (φ₂ i)) :
    (∑ i, featureLower (φ₁ i)) / (K : ℝ) < (∑ i, featureUpper (φ₁ i)) / (K : ℝ) ∧
    (∑ i, featureLower (φ₂ i)) / (K : ℝ) < (∑ i, featureUpper (φ₂ i)) / (K : ℝ) := by
  have hr (i : Fin K) := exact_feature_ranges (φ₁ i) (φ₂ i) (h₁ i) (h₂ i) (hind i)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hne : (Finset.univ : Finset (Fin K)).Nonempty := ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  constructor
  · apply div_lt_div_of_pos_right _ hKr
    exact Finset.sum_lt_sum_of_nonempty hne (fun i _ => (hr i).1)
  · apply div_lt_div_of_pos_right _ hKr
    exact Finset.sum_lt_sum_of_nonempty hne (fun i _ => (hr i).2.1)

end Analog.HeterogeneousCompletionDensity
