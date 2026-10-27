import Analog.HeterogeneousSynthesis
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Attainment without independence of the local features

The image of the finite coefficient space is finite-dimensional even when its
parameterization has a kernel. We put the uniform norm on the actual encoder
functions. Peak constraints give a closed bounded set in this image, so its
compactness does not require independent preprocessing functions.
-/

noncomputable section
namespace Analog.HeterogeneousAttainment
open Set GramSynthesis ArbitraryEncoder
open scoped BigOperators NNReal

section FunctionSpace
variable {K : ℕ} {S : Type*} [TopologicalSpace S] [CompactSpace S]

abbrev EncoderSpace (K : ℕ) (S : Type*) [TopologicalSpace S] := Fin K → C(S, ℝ × ℝ)

def peakSet (V : Submodule ℝ (EncoderSpace K S)) (P : ℝ) : Set V :=
  {E | ∀ k s, (E.1 k s).1 ^ 2 + (E.1 k s).2 ^ 2 ≤ P}

omit [CompactSpace S] in
private theorem evaluation_continuous (V : Submodule ℝ (EncoderSpace K S))
    (k : Fin K) (s : S) : Continuous (fun E : V => E.1 k s) :=
  (continuous_eval_const s).comp
    ((continuous_apply k).comp continuous_subtype_val)

omit [CompactSpace S] in
theorem peakSet_isClosed (V : Submodule ℝ (EncoderSpace K S)) (P : ℝ) :
    IsClosed (peakSet V P) := by
  change IsClosed {E : V | ∀ k s, (E.1 k s).1 ^ 2 + (E.1 k s).2 ^ 2 ≤ P}
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro s
  exact isClosed_le (((evaluation_continuous V k s).fst.pow 2).add
    ((evaluation_continuous V k s).snd.pow 2)) continuous_const

theorem peakSet_norm_bound (V : Submodule ℝ (EncoderSpace K S))
    {P : ℝ} (hP : 0 ≤ P) {E : V} (hE : E ∈ peakSet V P) :
    ‖E‖ ≤ Real.sqrt P := by
  change ‖E.1‖ ≤ Real.sqrt P
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg P)).mpr
  intro k
  apply (ContinuousMap.norm_le _ (Real.sqrt_nonneg P)).mpr
  intro s
  rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
  have hh := hE k s
  constructor <;> apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg P)).mp <;>
    rw [sq_abs, Real.sq_sqrt hP] <;> nlinarith [sq_nonneg (E.1 k s).1,
      sq_nonneg (E.1 k s).2]

/-- Finite-dimensionality of the function image, not independence of its
coefficient representation, is sufficient for compact peak-feasible classes. -/
theorem peakSet_isCompact (V : Submodule ℝ (EncoderSpace K S))
    [FiniteDimensional ℝ V] {P : ℝ} (hP : 0 ≤ P) : IsCompact (peakSet V P) := by
  apply (isCompact_closedBall (0 : V) (Real.sqrt P)).of_isClosed_subset
    (peakSet_isClosed V P)
  intro E hE
  simpa only [Metric.mem_closedBall, dist_zero_right] using peakSet_norm_bound V hP hE

def receivedMap (V : Submodule ℝ (EncoderSpace K S)) (E : V) (s : Fin K → S) : ℝ × ℝ :=
  (∑ k, (E.1 k (s k)).1, ∑ k, (E.1 k (s k)).2)

def pairCost (V : Submodule ℝ (EncoderSpace K S)) (E : V) (s t : Fin K → S) : ℝ :=
  squaredDistance (receivedMap V E s) (receivedMap V E t)

omit [CompactSpace S] in
private theorem pairCost_continuous (V : Submodule ℝ (EncoderSpace K S))
    (s t : Fin K → S) : Continuous (fun E : V => pairCost V E s t) := by
  unfold pairCost squaredDistance receivedMap
  have h (s : Fin K → S) : Continuous (fun E : V => ∑ k, (E.1 k (s k)).1) :=
    continuous_finset_sum _ (fun k _ => (evaluation_continuous V k (s k)).fst)
  have h' (s : Fin K → S) : Continuous (fun E : V => ∑ k, (E.1 k (s k)).2) :=
    continuous_finset_sum _ (fun k _ => (evaluation_continuous V k (s k)).snd)
  exact ((h s).sub (h t)).pow 2 |>.add (((h' s).sub (h' t)).pow 2)

def feasibleSet (V : Submodule ℝ (EncoderSpace K S)) (f : (Fin K → S) → ℝ)
    (P : ℝ) : Set (V × ℝ) :=
  {q | q.1 ∈ peakSet V P ∧ 0 ≤ q.2 ∧
    ∀ s t, q.2 * (f s - f t)^2 ≤ pairCost V q.1 s t}

omit [CompactSpace S] in
private theorem feasibleSet_isClosed (V : Submodule ℝ (EncoderSpace K S))
    (f : (Fin K → S) → ℝ) (P : ℝ) : IsClosed (feasibleSet V f P) := by
  apply IsClosed.inter ((peakSet_isClosed V P).preimage continuous_fst)
  apply IsClosed.inter (isClosed_le continuous_const continuous_snd)
  change IsClosed {q : V × ℝ | ∀ s t, q.2 * (f s - f t)^2 ≤ pairCost V q.1 s t}
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro t
  exact isClosed_le (continuous_snd.mul continuous_const)
    ((pairCost_continuous V s t).comp continuous_fst)

/-- Actual pair constraints are compact after passing to the finite-dimensional
space of encoder functions; zero separation is retained. -/
theorem feasibleSet_isCompact (V : Submodule ℝ (EncoderSpace K S))
    [FiniteDimensional ℝ V] (f : (Fin K → S) → ℝ)
    (hn : ∃ s t, f s ≠ f t) {P : ℝ} (hP : 0 ≤ P) :
    IsCompact (feasibleSet V f P) := by
  obtain ⟨s, t, hst⟩ := hn
  have hc := peakSet_isCompact V hP
  have hb := (hc.image (pairCost_continuous V s t)).bddAbove
  obtain ⟨B, hB⟩ := hb
  let R := B / (f s - f t)^2
  apply (hc.prod isCompact_Icc).of_isClosed_subset (feasibleSet_isClosed V f P)
  intro q hq
  refine ⟨hq.1, hq.2.1, ?_⟩
  change q.2 ≤ R
  apply (le_div_iff₀ (sq_pos_of_ne_zero (sub_ne_zero.mpr hst))).mpr
  exact (hq.2.2 s t).trans (hB ⟨q.1, hq.1, rfl⟩)

/-- Every finite-dimensional linear encoder family attains its operational
separation optimum under peak power, even when the optimum is zero. -/
theorem operational_maximum_attained (V : Submodule ℝ (EncoderSpace K S))
    [FiniteDimensional ℝ V] (f : (Fin K → S) → ℝ)
    (hn : ∃ s t, f s ≠ f t) {P : ℝ} (hP : 0 ≤ P) :
    ∃ E : V, E ∈ peakSet V P ∧
      ∀ E' : V, E' ∈ peakSet V P →
        Operational.score Set.univ f (pairCost V E') ≤
          Operational.score Set.univ f (pairCost V E) := by
  have hnon : Operational.NonconstantOn Set.univ f := by
    obtain ⟨s, t, hst⟩ := hn
    exact ⟨s, mem_univ _, t, mem_univ _, hst⟩
  have costNonneg (E : V) (s t : Fin K → S) : 0 ≤ pairCost V E s t :=
    squaredDistance_nonnegative _ _
  have hzero : ((0 : V), (0 : ℝ)) ∈ feasibleSet V f P := by
    refine ⟨?_, le_rfl, ?_⟩
    · intro k s
      simpa using hP
    · intro s t
      simpa using costNonneg 0 s t
  obtain ⟨q, hq, hmax⟩ := (feasibleSet_isCompact V f hn hP).exists_isMaxOn
    ⟨_, hzero⟩ continuous_snd.continuousOn
  refine ⟨q.1, hq.1, ?_⟩
  intro E' hE'
  have hscore : (E', Operational.score Set.univ f (pairCost V E')) ∈ feasibleSet V f P := by
    refine ⟨hE', Operational.score_nonnegative hnon (fun s _ t _ => costNonneg E' s t), ?_⟩
    intro s t
    exact Operational.score_is_lowerBound hnon (fun s _ t _ => costNonneg E' s t)
      s (mem_univ _) t (mem_univ _)
  have hmax' : Operational.score Set.univ f (pairCost V E') ≤ q.2 := hmax hscore
  apply hmax'.trans
  apply (Operational.le_score_iff hnon (fun s _ t _ => costNonneg q.1 s t) q.2).mpr
  intro s _ t _
  exact hq.2.2 s t


/-- Finite coefficient parameters: node offsets followed by the shared columns. -/
abbrev Parameters (K : ℕ) := (Fin K → ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)

/-- The linear map into actual continuous encoder functions. Its range is
finite-dimensional even when preprocessing functions are linearly dependent. -/
def coefficientMap (γ : Fin K → C(S, ℝ × ℝ)) :
    Parameters K →ₗ[ℝ] EncoderSpace K S where
  toFun p k := ⟨fun s =>
    ((p.1 k).1 + p.2.1.1 * (γ k s).1 + p.2.2.1 * (γ k s).2,
     (p.1 k).2 + p.2.1.2 * (γ k s).1 + p.2.2.2 * (γ k s).2), by fun_prop⟩
  map_add' p q := by
    ext k s <;> simp <;> ring
  map_smul' a p := by
    ext k s <;> simp <;> ring

/-- Unconditional coefficient-class operational attainment for arbitrary
continuous node features on a compact source. Independence is not assumed. -/
theorem coefficient_maximum_attained (γ : Fin K → C(S, ℝ × ℝ))
    (f : (Fin K → S) → ℝ) (hn : ∃ s t, f s ≠ f t)
    {P : ℝ} (hP : 0 ≤ P) :
    ∃ p : Parameters K,
      (∀ k s, ((coefficientMap γ p) k s).1 ^ 2 +
        ((coefficientMap γ p) k s).2 ^ 2 ≤ P) ∧
      ∀ p' : Parameters K,
        (∀ k s, ((coefficientMap γ p') k s).1 ^ 2 +
          ((coefficientMap γ p') k s).2 ^ 2 ≤ P) →
        Operational.score Set.univ f (fun s t =>
          squaredDistance
            (∑ k, ((coefficientMap γ p') k (s k)).1,
             ∑ k, ((coefficientMap γ p') k (s k)).2)
            (∑ k, ((coefficientMap γ p') k (t k)).1,
             ∑ k, ((coefficientMap γ p') k (t k)).2)) ≤
        Operational.score Set.univ f (fun s t =>
          squaredDistance
            (∑ k, ((coefficientMap γ p) k (s k)).1,
             ∑ k, ((coefficientMap γ p) k (s k)).2)
            (∑ k, ((coefficientMap γ p) k (t k)).1,
             ∑ k, ((coefficientMap γ p) k (t k)).2)) := by
  let V := LinearMap.range (coefficientMap γ)
  obtain ⟨E, hE, hmax⟩ := operational_maximum_attained V f hn hP
  obtain ⟨p, hp⟩ := E.property
  refine ⟨p, ?_, ?_⟩
  · simpa only [hp] using hE
  · intro p' hp'
    let E' : V := ⟨coefficientMap γ p', ⟨p', rfl⟩⟩
    have hh := hmax E' hp'
    simpa only [pairCost, receivedMap, E', hp] using hh

end FunctionSpace

section CurrentModel

abbrev Source := Set.Icc (-1 : ℝ) 1

private def sourceCoe {K : ℕ} (s : Fin K → Source) : Fin K → ℝ := fun k => s k

private theorem sourceCoe_image (K : ℕ) :
    sourceCoe '' (Set.univ : Set (Fin K → Source)) = HeterogeneousScore.ValidInput K := by
  ext s
  constructor
  · rintro ⟨t, _, rfl⟩
    exact fun k => (t k).property
  · intro hs
    exact ⟨fun k => ⟨s k, hs k⟩, mem_univ _, rfl⟩

private def compactFeatures {K : ℕ} (γ : Fin K → ℝ → ℝ × ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Set.Icc (-1 : ℝ) 1)) :
    Fin K → C(Source, ℝ × ℝ) := fun k => ⟨fun s => γ k s, (hγ k).restrict⟩

def parameterPlanar {K : ℕ} (p : Parameters K) : Planar :=
  ⟨0, 0, p.2.1.1, p.2.1.2, p.2.2.1, p.2.2.2⟩

private theorem current_score_bridge {K : ℕ} (γ : Fin K → ℝ → ℝ × ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Set.Icc (-1 : ℝ) 1))
    (F : ℝ × ℝ → ℝ) (p : Parameters K) :
    Operational.score Set.univ
      (fun s : Fin K → Source => F (HeterogeneousScore.meanStatistic γ (sourceCoe s)))
      (fun s t => squaredDistance
        (∑ k, ((coefficientMap (compactFeatures γ hγ) p) k (s k)).1,
         ∑ k, ((coefficientMap (compactFeatures γ hγ) p) k (s k)).2)
        (∑ k, ((coefficientMap (compactFeatures γ hγ) p) k (t k)).1,
         ∑ k, ((coefficientMap (compactFeatures γ hγ) p) k (t k)).2)) =
      HeterogeneousScore.score γ F (HeterogeneousScore.encoder (parameterPlanar p) p.1 γ) := by
  have h := Operational.score_stat_image Set.univ (@sourceCoe K)
    (F ∘ HeterogeneousScore.meanStatistic γ)
    (fun s t => squaredDistance
      (HeterogeneousScore.received (HeterogeneousScore.encoder (parameterPlanar p) p.1 γ) s)
      (HeterogeneousScore.received (HeterogeneousScore.encoder (parameterPlanar p) p.1 γ) t))
  rw [sourceCoe_image] at h
  exact h

/-- The current heterogeneous coefficient class attains its actual operational
maximum, with no independence, Lipschitz, or positive-score assumption. -/
theorem heterogeneous_operational_maximum_attained {K : ℕ}
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Set.Icc (-1 : ℝ) 1))
    (hn : Operational.NonconstantOn (HeterogeneousScore.attainable γ) F)
    {P : ℝ} (hP : 0 ≤ P) :
    ∃ (e : Planar) (c : Fin K → ℝ × ℝ),
      (∀ k s, s ∈ Set.Icc (-1 : ℝ) 1 →
        squaredDistance (HeterogeneousScore.encoder e c γ k s) 0 ≤ P) ∧
      ∀ (e' : Planar) (c' : Fin K → ℝ × ℝ),
        (∀ k s, s ∈ Set.Icc (-1 : ℝ) 1 →
          squaredDistance (HeterogeneousScore.encoder e' c' γ k s) 0 ≤ P) →
        HeterogeneousScore.score γ F (HeterogeneousScore.encoder e' c' γ) ≤
          HeterogeneousScore.score γ F (HeterogeneousScore.encoder e c γ) := by
  let f : (Fin K → Source) → ℝ :=
    fun s => F (HeterogeneousScore.meanStatistic γ (sourceCoe s))
  have hnon : ∃ s t, f s ≠ f t := by
    obtain ⟨μ, ⟨s, hs, rfl⟩, ν, ⟨t, ht, rfl⟩, hne⟩ := hn
    exact ⟨fun k => ⟨s k, hs k⟩, fun k => ⟨t k, ht k⟩, hne⟩
  obtain ⟨p, hp, hmax⟩ := coefficient_maximum_attained (compactFeatures γ hγ) f hnon hP
  refine ⟨parameterPlanar p, p.1, ?_, ?_⟩
  · intro k s hs
    simpa only [coefficientMap, compactFeatures, HeterogeneousScore.encoder,
      parameterPlanar, squaredDistance, Prod.fst_zero, Prod.snd_zero, sub_zero] using hp k ⟨s, hs⟩
  · intro e' c' hp'
    let p' : Parameters K := ⟨c', (e'.ux, e'.uy), (e'.vx, e'.vy)⟩
    have hpeak : ∀ k s, ((coefficientMap (compactFeatures γ hγ) p') k s).1 ^ 2 +
        ((coefficientMap (compactFeatures γ hγ) p') k s).2 ^ 2 ≤ P := by
      intro k s
      simpa only [coefficientMap, compactFeatures, HeterogeneousScore.encoder,
        p', squaredDistance, Prod.fst_zero, Prod.snd_zero, sub_zero] using hp' k s s.property
    have hh := hmax p' hpeak
    rw [current_score_bridge γ hγ F p', current_score_bridge γ hγ F p] at hh
    exact hh


/-- The current semi-infinite program, in scalar symmetric-matrix coordinates. -/
structure SDPPoint (K : ℕ) where
  lam : ℝ
  h : Fin K → ℝ
  l₁ : Fin K → ℝ
  l₂ : Fin K → ℝ
  A : ℝ
  B : ℝ
  C : ℝ

def SDPFeasible {K : ℕ} (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (P : ℝ) (q : SDPPoint K) : Prop :=
  0 ≤ q.lam ∧
  (∀ k, PSD3 (q.h k) (q.l₁ k) (q.l₂ k) q.A q.B q.C) ∧
  (∀ k s, s ∈ Set.Icc (-1 : ℝ) 1 →
    form3 (q.h k) (q.l₁ k) (q.l₂ k) q.A q.B q.C 1 (γ k s).1 (γ k s).2 ≤ P) ∧
  (∀ μ ∈ HeterogeneousScore.attainable γ, ∀ ν ∈ HeterogeneousScore.attainable γ,
    q.lam * (F μ - F ν)^2 ≤ form2 q.A q.B q.C (μ.1 - ν.1) (μ.2 - ν.2))

private def offsetPlanar (e : Planar) (c : ℝ × ℝ) : Planar :=
  {e with cx := c.1, cy := c.2}

private theorem encoder_to_sdp {K : ℕ} (hK : 0 < K)
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (hn : Operational.NonconstantOn (HeterogeneousScore.attainable γ) F)
    (e : Planar) (c : Fin K → ℝ × ℝ) (P : ℝ)
    (hp : ∀ k s, s ∈ Set.Icc (-1 : ℝ) 1 →
      squaredDistance (HeterogeneousScore.encoder e c γ k s) 0 ≤ P) :
    ∃ q : SDPPoint K, SDPFeasible γ F P q ∧
      (K : ℝ)^2 * q.lam = HeterogeneousScore.score γ F (HeterogeneousScore.encoder e c γ) := by
  let S := HeterogeneousScore.score γ F (HeterogeneousScore.encoder e c γ)
  let q : SDPPoint K := ⟨S / (K : ℝ)^2, (fun k => (offsetPlanar e (c k)).h),
    (fun k => (offsetPlanar e (c k)).l₁), (fun k => (offsetPlanar e (c k)).l₂),
    e.A, e.B, e.C⟩
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  have hSn : 0 ≤ S := by
    apply Operational.score_nonnegative
    · exact (Operational.nonconstantOn_stat_image_iff
        (HeterogeneousScore.ValidInput K) (HeterogeneousScore.meanStatistic γ) F).mpr hn
    · intro s _ t _
      exact squaredDistance_nonnegative _ _
  have heq : (K : ℝ)^2 * q.lam = S := by dsimp [q]; field_simp
  refine ⟨q, ⟨div_nonneg hSn (sq_nonneg _), ?_, ?_, ?_⟩, heq⟩
  · intro k
    exact (offsetPlanar e (c k)).gram_psd
  · intro k s hs
    have he : form3 (q.h k) (q.l₁ k) (q.l₂ k) q.A q.B q.C 1 (γ k s).1 (γ k s).2 =
        squaredDistance (HeterogeneousScore.encoder e c γ k s) 0 := by
      change form3 (offsetPlanar e (c k)).h (offsetPlanar e (c k)).l₁
        (offsetPlanar e (c k)).l₂ (offsetPlanar e (c k)).A (offsetPlanar e (c k)).B
        (offsetPlanar e (c k)).C 1 (γ k s).1 (γ k s).2 = _
      rw [← Planar.energy_eq_form3]
      dsimp [Planar.energy, offsetPlanar, HeterogeneousScore.encoder, squaredDistance]
      ring
    rw [he]
    exact hp k s hs
  · apply (HeterogeneousScore.affine_score_bound_iff hK e c γ F hn q.lam).mp
    rw [heq]

/-- Full attainment and zero relaxation gap for the current heterogeneous SDP.
There is no independence assumption, and both singular matrices and the zero
optimum are allowed. The actual optimal encoder is exhibited alongside the
optimal matrix family. -/
theorem heterogeneous_sdp_attained {K : ℕ} (hK : 0 < K)
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Set.Icc (-1 : ℝ) 1))
    (hn : Operational.NonconstantOn (HeterogeneousScore.attainable γ) F)
    {P : ℝ} (hP : 0 ≤ P) :
    ∃ (q : SDPPoint K) (e : Planar) (c : Fin K → ℝ × ℝ),
      SDPFeasible γ F P q ∧
      (∀ q' : SDPPoint K, SDPFeasible γ F P q' → q'.lam ≤ q.lam) ∧
      (∀ k s, s ∈ Set.Icc (-1 : ℝ) 1 →
        squaredDistance (HeterogeneousScore.encoder e c γ k s) 0 ≤ P) ∧
      HeterogeneousScore.score γ F (HeterogeneousScore.encoder e c γ) = (K : ℝ)^2 * q.lam ∧
      (∀ (e' : Planar) (c' : Fin K → ℝ × ℝ),
        (∀ k s, s ∈ Set.Icc (-1 : ℝ) 1 →
          squaredDistance (HeterogeneousScore.encoder e' c' γ k s) 0 ≤ P) →
        HeterogeneousScore.score γ F (HeterogeneousScore.encoder e' c' γ) ≤
          HeterogeneousScore.score γ F (HeterogeneousScore.encoder e c γ)) := by
  obtain ⟨e, c, hp, hmax⟩ := heterogeneous_operational_maximum_attained γ F hγ hn hP
  obtain ⟨q, hq, heq⟩ := encoder_to_sdp hK γ F hn e c P hp
  refine ⟨q, e, c, hq, ?_, hp, heq.symm, hmax⟩
  intro q' hq'
  obtain ⟨e', c', _, _, _, _, hp', hs', _⟩ :=
    HeterogeneousSynthesis.feasible_operational_synthesis hK γ F hγ hn
      q'.h q'.l₁ q'.l₂ q'.A q'.B q'.C P q'.lam hq'.2.1 hq'.2.2.1 hq'.2.2.2
  have hh := hs'.trans (hmax e' c' hp')
  rw [← heq] at hh
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hk)).mp hh


private theorem form2_dist_bound (A B C : ℝ) (μ ν : ℝ × ℝ) :
    form2 A B C (μ.1 - ν.1) (μ.2 - ν.2) ≤
      (|A| + 2 * |C| + |B|) * dist μ ν ^ 2 := by
  have hx : |μ.1 - ν.1| ≤ dist μ ν := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have hy : |μ.2 - ν.2| ≤ dist μ ν := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  have hx2 : (μ.1 - ν.1)^2 ≤ dist μ ν ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) dist_nonneg).mpr hx
  have hy2 : (μ.2 - ν.2)^2 ≤ dist μ ν ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) dist_nonneg).mpr hy
  have hxy : |(μ.1 - ν.1) * (μ.2 - ν.2)| ≤ dist μ ν ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hx hy (abs_nonneg _) dist_nonneg
  have hA := mul_le_mul_of_nonneg_right (le_abs_self A) (sq_nonneg (μ.1 - ν.1))
  have hA' := mul_le_mul_of_nonneg_left hx2 (abs_nonneg A)
  have hB := mul_le_mul_of_nonneg_right (le_abs_self B) (sq_nonneg (μ.2 - ν.2))
  have hB' := mul_le_mul_of_nonneg_left hy2 (abs_nonneg B)
  have hC : C * ((μ.1 - ν.1) * (μ.2 - ν.2)) ≤ |C| * dist μ ν ^ 2 := by
    calc
      _ ≤ |C * ((μ.1 - ν.1) * (μ.2 - ν.2))| := le_abs_self _
      _ = |C| * |(μ.1 - ν.1) * (μ.2 - ν.2)| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hxy (abs_nonneg C)
  dsimp [form2]
  nlinarith

/-- Any positive feasible secant coefficient forces the desired readout to
be Lipschitz on the actual attainable set, regardless of its geometry. -/
theorem positive_feasible_implies_lipschitz {K : ℕ}
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ) {P : ℝ} {q : SDPPoint K}
    (hq : SDPFeasible γ F P q) (hlam : 0 < q.lam) :
    ∃ L : ℝ≥0, LipschitzOnWith L F (HeterogeneousScore.attainable γ) := by
  let T := |q.A| + 2 * |q.C| + |q.B|
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let L : ℝ≥0 := ⟨Real.sqrt (T / q.lam), Real.sqrt_nonneg _⟩
  refine ⟨L, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro μ hμ ν hν
  have hh := (hq.2.2.2 μ hμ ν hν).trans (form2_dist_bound q.A q.B q.C μ ν)
  have hs : (F μ - F ν)^2 ≤ (T / q.lam) * dist μ ν ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hlam).mpr
    nlinarith [hh]
  rw [Real.dist_eq]
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg L.coe_nonneg dist_nonneg)).mp
  change |F μ - F ν|^2 ≤ (Real.sqrt (T / q.lam) * dist μ ν)^2
  rw [sq_abs, mul_pow, Real.sq_sqrt (div_nonneg hT hlam.le)]
  exact hs


private theorem dist_sq_le_coordinate_sum (μ ν : ℝ × ℝ) :
    dist μ ν ^ 2 ≤ (μ.1 - ν.1)^2 + (μ.2 - ν.2)^2 := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  rcases le_total |μ.1 - ν.1| |μ.2 - ν.2| with h | h
  · rw [max_eq_right h, sq_abs]
    nlinarith [sq_nonneg (μ.1 - ν.1)]
  · rw [max_eq_left h, sq_abs]
    nlinarith [sq_nonneg (μ.2 - ν.2)]

/-- A Lipschitz readout yields a strictly positive feasible point by a scaled
identity moment embedding, for any positive power and continuous local features. -/
theorem lipschitz_implies_positive_feasible {K : ℕ}
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Set.Icc (-1 : ℝ) 1))
    {P : ℝ} (hP : 0 < P) {L : ℝ≥0}
    (hL : LipschitzOnWith L F (HeterogeneousScore.attainable γ)) :
    ∃ q : SDPPoint K, SDPFeasible γ F P q ∧ 0 < q.lam := by
  let B := ‖compactFeatures γ hγ‖
  have hB : 0 ≤ B := norm_nonneg _
  let a := P / (1 + 2 * B^2)
  have hden : 0 < 1 + 2 * B^2 := by positivity
  have ha : 0 < a := div_pos hP hden
  have hld : 0 < (L : ℝ)^2 + 1 := by positivity
  let q : SDPPoint K := ⟨a / ((L : ℝ)^2 + 1), 0, 0, 0, a, a, 0⟩
  have hpositive : 0 < q.lam := div_pos ha hld
  refine ⟨q, ⟨hpositive.le, ?_, ?_, ?_⟩, hpositive⟩
  · intro k t x y
    change 0 ≤ form3 0 0 0 a a 0 t x y
    dsimp [form3, form2]
    nlinarith [mul_nonneg ha.le (sq_nonneg x), mul_nonneg ha.le (sq_nonneg y)]
  · intro k s hs
    have hn : ‖γ k s‖ ≤ B :=
      ((compactFeatures γ hγ k).norm_coe_le_norm ⟨s, hs⟩).trans
        (norm_le_pi_norm (compactFeatures γ hγ) k)
    have hx : |(γ k s).1| ≤ B := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hn
      exact (le_max_left _ _).trans hn
    have hy : |(γ k s).2| ≤ B := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hn
      exact (le_max_right _ _).trans hn
    have hx2 : (γ k s).1^2 ≤ B^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr hx
    have hy2 : (γ k s).2^2 ≤ B^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr hy
    change form3 0 0 0 a a 0 1 (γ k s).1 (γ k s).2 ≤ P
    have hm := mul_le_mul_of_nonneg_left (show (γ k s).1^2 + (γ k s).2^2 ≤
      1 + 2*B^2 by linarith) ha.le
    have he : a * (1 + 2 * B^2) = P := by dsimp [a]; field_simp
    dsimp [form3, form2]
    nlinarith [hm, he]
  · intro μ hμ ν hν
    have hl := hL.dist_le_mul μ hμ ν hν
    have hf : (F μ - F ν)^2 ≤ (L : ℝ)^2 * dist μ ν ^ 2 := by
      have hs := (sq_le_sq₀ dist_nonneg (mul_nonneg L.coe_nonneg dist_nonneg)).mpr hl
      simpa only [Real.dist_eq, sq_abs, mul_pow] using hs
    have hd := dist_sq_le_coordinate_sum μ ν
    have hmul := mul_le_mul_of_nonneg_left hd (sq_nonneg (L : ℝ))
    have hs : (F μ - F ν)^2 ≤ ((L : ℝ)^2 + 1) *
        ((μ.1 - ν.1)^2 + (μ.2 - ν.2)^2) := by
      nlinarith [sq_nonneg (μ.1 - ν.1), sq_nonneg (μ.2 - ν.2)]
    have hscale := mul_le_mul_of_nonneg_left hs ha.le
    change (a / ((L : ℝ)^2 + 1)) * (F μ - F ν)^2 ≤
      form2 a a 0 (μ.1 - ν.1) (μ.2 - ν.2)
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hld).mpr
    dsimp [form2]
    nlinarith

/-- Exact positivity characterization for the current program. -/
theorem positive_feasible_iff_lipschitz {K : ℕ}
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Set.Icc (-1 : ℝ) 1))
    {P : ℝ} (hP : 0 < P) :
    (∃ q : SDPPoint K, SDPFeasible γ F P q ∧ 0 < q.lam) ↔
      ∃ L : ℝ≥0, LipschitzOnWith L F (HeterogeneousScore.attainable γ) := by
  constructor
  · rintro ⟨q, hq, hpos⟩
    exact positive_feasible_implies_lipschitz γ F hq hpos
  · rintro ⟨L, hL⟩
    exact lipschitz_implies_positive_feasible γ F hγ hP hL

/-- At every attained optimum the objective is positive exactly for Lipschitz
readouts; no differentiability or convexity of the moment set is assumed. -/
theorem optimal_positive_iff_lipschitz {K : ℕ}
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Set.Icc (-1 : ℝ) 1))
    {P : ℝ} (hP : 0 < P) {q : SDPPoint K} (hq : SDPFeasible γ F P q)
    (hmax : ∀ q' : SDPPoint K, SDPFeasible γ F P q' → q'.lam ≤ q.lam) :
    0 < q.lam ↔ ∃ L : ℝ≥0, LipschitzOnWith L F (HeterogeneousScore.attainable γ) := by
  constructor
  · exact positive_feasible_implies_lipschitz γ F hq
  · intro hl
    obtain ⟨q', hq', hpos⟩ := (positive_feasible_iff_lipschitz γ F hγ hP).mpr hl
    exact hpos.trans_le (hmax q' hq')


/-- The manuscript's Euclidean Lipschitz condition, with its explicit norm. -/
def EuclideanLipschitzOn (F : ℝ × ℝ → ℝ) (M : Set (ℝ × ℝ)) : Prop :=
  ∃ L : ℝ, 0 ≤ L ∧ ∀ μ ∈ M, ∀ ν ∈ M,
    |F μ - F ν| ≤ L * Real.sqrt ((μ.1 - ν.1)^2 + (μ.2 - ν.2)^2)

/-- Existence of a Lipschitz constant agrees for the library's product metric
and the exact Euclidean norm written in the manuscript. -/
theorem product_lipschitz_iff_euclidean (F : ℝ × ℝ → ℝ) (M : Set (ℝ × ℝ)) :
    (∃ L : ℝ≥0, LipschitzOnWith L F M) ↔ EuclideanLipschitzOn F M := by
  have hnon (μ ν : ℝ × ℝ) : 0 ≤ (μ.1 - ν.1)^2 + (μ.2 - ν.2)^2 := by positivity
  have hlo (μ ν : ℝ × ℝ) : dist μ ν ≤
      Real.sqrt ((μ.1 - ν.1)^2 + (μ.2 - ν.2)^2) := by
    apply (sq_le_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (hnon μ ν)]
    exact dist_sq_le_coordinate_sum μ ν
  have hup (μ ν : ℝ × ℝ) : Real.sqrt ((μ.1 - ν.1)^2 + (μ.2 - ν.2)^2) ≤
      2 * dist μ ν := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (hnon μ ν)]
    have hbound := form2_dist_bound 1 1 0 μ ν
    norm_num [form2] at hbound
    nlinarith [sq_nonneg (dist μ ν)]
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L, L.coe_nonneg, ?_⟩
    intro μ hμ ν hν
    have hh := hL.dist_le_mul μ hμ ν hν
    rw [Real.dist_eq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hlo μ ν) L.coe_nonneg)
  · rintro ⟨L, hL, hf⟩
    refine ⟨⟨2 * L, by positivity⟩, LipschitzOnWith.of_dist_le_mul ?_⟩
    intro μ hμ ν hν
    rw [Real.dist_eq]
    have hh := (hf μ hμ ν hν).trans (mul_le_mul_of_nonneg_left (hup μ ν) hL)
    change |F μ - F ν| ≤ 2 * L * dist μ ν
    nlinarith

/-- Positivity of the attained optimum in the exact Euclidean convention of
the manuscript, with all compactness and attainment hypotheses supplied by
`heterogeneous_sdp_attained`. -/
theorem optimal_positive_iff_euclidean_lipschitz {K : ℕ}
    (γ : Fin K → ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (hγ : ∀ k, ContinuousOn (γ k) (Set.Icc (-1 : ℝ) 1))
    {P : ℝ} (hP : 0 < P) {q : SDPPoint K} (hq : SDPFeasible γ F P q)
    (hmax : ∀ q' : SDPPoint K, SDPFeasible γ F P q' → q'.lam ≤ q.lam) :
    0 < q.lam ↔ EuclideanLipschitzOn F (HeterogeneousScore.attainable γ) :=
  (optimal_positive_iff_lipschitz γ F hγ hP hq hmax).trans
    (product_lipschitz_iff_euclidean F (HeterogeneousScore.attainable γ))

end CurrentModel
end Analog.HeterogeneousAttainment
