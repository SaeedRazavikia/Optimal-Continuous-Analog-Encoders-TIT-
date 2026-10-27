import Analog.GeneralScore
import Analog.EuclideanBridge
import Analog.GeneralDesign
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Transfer of the actual operational score to other dissimilarities

The infimum is over actual admissible input pairs. A general transfer theorem
uses shrinking sharp pairs, and the moment-encoder specialization derives
these pairs from `GeneralScore.general_score_small_distance_sharpness`.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace Analog.CriterionTransfer
open Operational ArbitraryEncoder GeneralCollision GeneralScore GramSynthesis

/-- The dissimilarity score uses the same unequal-function-value pairs as the
squared-separation score, with numerator `D(distance x y)`. -/
def dissimilarityScore {X : Type*} (S : Set X) (f : X → ℝ)
    (distance : X → X → ℝ) (D : ℝ → ℝ) : ℝ :=
  Operational.score S f (fun x y => D (distance x y))

/-- A right-hand quadratic ratio limit supplies a local quadratic envelope. -/
theorem local_quadratic_upper (D : ℝ → ℝ) (c ε : ℝ) (hε : 0 < ε)
    (hlim : Tendsto (fun d : ℝ => D d / d ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    ∃ δ > 0, ∀ d : ℝ, 0 < d → d < δ → D d ≤ (c + ε) * d ^ 2 := by
  obtain ⟨δ, hδ, hh⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim ε hε
  refine ⟨δ, hδ, ?_⟩
  intro d hd hdδ
  have he := hh (show d ∈ Ioi (0 : ℝ) from hd)
    (show dist d 0 < δ by simpa [Real.dist_eq, abs_of_pos hd] using hdδ)
  have hu : D d / d ^ 2 < c + ε := by
    rw [Real.dist_eq] at he
    have := (abs_lt.mp he).2
    linarith
  exact ((div_le_iff₀ (sq_pos_of_pos hd)).mp hu.le)

/-- A positive operational score with arbitrarily short sharp pairs transfers
exactly to every dissimilarity with the indicated global and local envelopes.
No received moment region is substituted for the actual input domain. -/
theorem score_transfer {X : Type*} (S : Set X) (f : X → ℝ)
    (distance : X → X → ℝ) (D : ℝ → ℝ) (c : ℝ)
    (hn : NonconstantOn S f) (hc : 0 < c)
    (hd : ∀ x ∈ S, ∀ y ∈ S, 0 ≤ distance x y)
    (hpos : 0 < Operational.score S f (fun x y => distance x y ^ 2))
    (hlower : ∀ x ∈ S, ∀ y ∈ S, c * distance x y ^ 2 ≤ D (distance x y))
    (hlim : Tendsto (fun d : ℝ => D d / d ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 c))
    (hsharp : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∃ x ∈ S, ∃ y ∈ S, f x ≠ f y ∧ distance x y < δ ∧
        distance x y ^ 2 / (f x - f y) ^ 2 <
          Operational.score S f (fun x y => distance x y ^ 2) + ε) :
    dissimilarityScore S f distance D =
      c * Operational.score S f (fun x y => distance x y ^ 2) := by
  let L := Operational.score S f (fun x y => distance x y ^ 2)
  have hsq : ∀ x ∈ S, ∀ y ∈ S, 0 ≤ distance x y ^ 2 :=
    fun x _ y _ => sq_nonneg _
  have hD : ∀ x ∈ S, ∀ y ∈ S, 0 ≤ D (distance x y) := by
    intro x hx y hy
    exact (mul_nonneg hc.le (sq_nonneg _)).trans (hlower x hx y hy)
  have hbase := score_is_lowerBound hn hsq
  apply le_antisymm
  · have hup (ε : ℝ) (hε : 0 < ε) :
        dissimilarityScore S f distance D ≤ (c + ε) * (L + ε) := by
      obtain ⟨δ, hδ, hloc⟩ := local_quadratic_upper D c ε hε hlim
      obtain ⟨x, hx, y, hy, hne, hsmall, hquot⟩ := hsharp ε δ hε hδ
      have hdpos : 0 < distance x y := by
        have ht := hbase x hx y hy
        have hprod := mul_pos hpos (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
        have hdsq : 0 < distance x y ^ 2 := hprod.trans_le ht
        have hdnonneg := hd x hx y hy
        nlinarith
      have hmember : D (distance x y) / (f x - f y) ^ 2 ∈
          Quotients S f (fun x y => D (distance x y)) :=
        ⟨x, hx, y, hy, hne, rfl⟩
      have hscore := csInf_le (quotients_bddBelow hD) hmember
      change dissimilarityScore S f distance D ≤ _ at hscore
      calc
        dissimilarityScore S f distance D ≤
            D (distance x y) / (f x - f y) ^ 2 := hscore
        _ ≤ ((c + ε) * distance x y ^ 2) / (f x - f y) ^ 2 :=
          div_le_div_of_nonneg_right (hloc _ hdpos hsmall) (sq_nonneg _)
        _ = (c + ε) * (distance x y ^ 2 / (f x - f y) ^ 2) := by ring
        _ ≤ (c + ε) * (L + ε) :=
          mul_le_mul_of_nonneg_left hquot.le (by linarith)
    have ht : Tendsto (fun ε : ℝ => (c + ε) * (L + ε))
        (𝓝[>] (0 : ℝ)) (𝓝 (c * L)) := by
      have h : ContinuousAt (fun ε : ℝ => (c + ε) * (L + ε)) 0 := by fun_prop
      simpa using h.tendsto.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto ht (by
      filter_upwards [eventually_mem_nhdsWithin] with ε hε
      exact hup ε hε)
  · apply (le_score_iff hn hD _).mpr
    intro x hx y hy
    have hh := mul_le_mul_of_nonneg_left (hbase x hx y hy) hc.le
    calc
      (c * Operational.score S f (fun x y => distance x y ^ 2)) * (f x - f y) ^ 2 =
          c * (Operational.score S f (fun x y => distance x y ^ 2) * (f x - f y) ^ 2) := by ring
      _ ≤ c * distance x y ^ 2 := hh
      _ ≤ D (distance x y) := hlower x hx y hy

/-- A nonexact collision forces zero dissimilarity score when `D(0)=0`. -/
theorem collision_score_zero {X : Type*} (S : Set X) (f : X → ℝ)
    (distance : X → X → ℝ) (D : ℝ → ℝ)
    (hD : ∀ x ∈ S, ∀ y ∈ S, 0 ≤ D (distance x y)) (hzero : D 0 = 0)
    (x y : X) (hx : x ∈ S) (hy : y ∈ S)
    (hne : f x ≠ f y) (hcol : distance x y = 0) :
    dissimilarityScore S f distance D = 0 := by
  have hn : NonconstantOn S f := ⟨x, hx, y, hy, hne⟩
  apply le_antisymm
  · apply csInf_le (quotients_bddBelow hD)
    exact ⟨x, hx, y, hy, hne, by simp [hcol, hzero]⟩
  · exact score_nonnegative hn hD

/-- Euclidean received distance for the actual complex multiple-access sum. -/
def receivedDistance (E : ℝ → ℝ × ℝ) (xs ys : List ℝ) : ℝ :=
  dist (asComplex (received E xs)) (asComplex (received E ys))

lemma received_norm_bound (E : ℝ → ℝ × ℝ) (R : ℝ) (xs : List ℝ)
    (hpeak : ∀ s ∈ xs, ‖asComplex (E s)‖ ≤ R) :
    ‖asComplex (received E xs)‖ ≤ (xs.length : ℝ) * R := by
  rw [asComplex_received]
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hpeak x (List.mem_cons_self ..)
    have ht := ih (fun s hs => hpeak s (List.mem_cons_of_mem x hs))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      ‖asComplex (E x) + (xs.map (fun s => asComplex (E s))).sum‖ ≤
          ‖asComplex (E x)‖ + ‖(xs.map (fun s => asComplex (E s))).sum‖ := norm_add_le _ _
      _ ≤ R + (xs.length : ℝ) * R := add_le_add hx ht
      _ = ((xs.length : ℝ) + 1) * R := by ring

/-- Pointwise peak power bounds every actual received-pair distance by
`2 K sqrt(P)`, exactly the interval in the manuscript's transfer condition. -/
theorem received_distance_peak_bound (E : ℝ → ℝ × ℝ) {K : ℕ}
    (P : ℝ) (hP : 0 ≤ P)
    (hpeak : ∀ s ∈ Icc (-1 : ℝ) 1, squaredDistance (E s) 0 ≤ P)
    (xs ys : List ℝ) (hxs : ValidInput K xs) (hys : ValidInput K ys) :
    receivedDistance E xs ys ≤ 2 * (K : ℝ) * Real.sqrt P := by
  have hp (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) : ‖asComplex (E s)‖ ≤ Real.sqrt P := by
    have he : ‖asComplex (E s)‖ ^ 2 = squaredDistance (E s) 0 := by
      have hz : asComplex (0 : ℝ × ℝ) = 0 := rfl
      simpa only [hz, dist_zero_right] using asComplex_squared_distance (E s) 0
    have hh := hpeak s hs
    nlinarith [Real.sq_sqrt hP, Real.sqrt_nonneg P, norm_nonneg (asComplex (E s))]
  have hx := received_norm_bound E (Real.sqrt P) xs (fun s hs => hp s (hxs.2 s hs))
  have hy := received_norm_bound E (Real.sqrt P) ys (fun s hs => hp s (hys.2 s hs))
  rw [hxs.1] at hx
  rw [hys.1] at hy
  dsimp [receivedDistance]
  rw [dist_eq_norm]
  have ht := norm_sub_le (asComplex (received E xs)) (asComplex (received E ys))
  linarith

/-- The moment-encoder transfer theorem derives its shrinking sharp pairs
from the already verified operational score theorem. -/
theorem moment_score_transfer (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (φ ψ D : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hdet : 0 < det e.A e.B e.C)
    (hφ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ)
    (hdφ : ∀ z ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ φ z)
    (hψ : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (hdψ : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hcψ : ContinuousOn (readoutSlope ψ) (Icc (-1 : ℝ) 1))
    (hlower : ∀ xs ys : List ℝ, ValidInput K xs → ValidInput K ys →
      c * receivedDistance (encoder e φ) xs ys ^ 2 ≤
        D (receivedDistance (encoder e φ) xs ys))
    (hlim : Tendsto (fun d : ℝ => D d / d ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    dissimilarityScore {xs | ValidInput K xs} (target K φ ψ)
      (receivedDistance (encoder e φ)) D = c * GeneralScore.score K φ ψ e := by
  have hcost : (fun xs ys => receivedDistance (encoder e φ) xs ys ^ 2) =
      (fun xs ys => squaredDistance (received (encoder e φ) xs)
        (received (encoder e φ) ys)) := by
    funext xs ys
    exact asComplex_squared_distance _ _
  have hscore : Operational.score {xs | ValidInput K xs} (target K φ ψ)
      (fun xs ys => receivedDistance (encoder e φ) xs ys ^ 2) =
        GeneralScore.score K φ ψ e := by rw [hcost]; rfl
  rw [← hscore]
  apply score_transfer _ _ _ _ c (target_nonconstant_of_strict_feature hK φ ψ hφ) hc
    (fun xs _ ys _ => dist_nonneg)
  · change 0 < Operational.score {xs | ValidInput K xs} (target K φ ψ)
      (fun xs ys => receivedDistance (encoder e φ) xs ys ^ 2)
    rw [hscore, general_operational_score e hK φ ψ hdet hφ hdφ hψ hdψ hcψ]
    have hk : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
    exact div_pos (sq_pos_of_pos hk) (endpointDual_pos e ψ hdet)
  · exact fun xs hxs ys hys => hlower xs ys hxs hys
  · exact hlim
  · intro ε δ hε hδ
    obtain ⟨xs, ys, hxs, hys, hne, hsmall, hquot⟩ :=
      general_score_small_distance_sharpness e hK φ ψ hdet hφ hdφ hψ hdψ hcψ ε δ hε hδ
    refine ⟨xs, hxs, ys, hys, hne, ?_, ?_⟩
    · change dist _ _ < δ
      have hs := asComplex_squared_distance (received (encoder e φ) xs)
        (received (encoder e φ) ys)
      nlinarith [dist_nonneg (x := asComplex (received (encoder e φ) xs))
        (y := asComplex (received (encoder e φ) ys))]
    · simpa only [receivedDistance, asComplex_squared_distance, hscore] using hquot

/-- The coefficient-class corollary with the manuscript's finite peak-power
interval hypothesis. The operational shrinking-pair condition is derived,
not assumed. -/
theorem peak_constrained_moment_transfer (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (φ ψ D : ℝ → ℝ) (c P : ℝ) (hc : 0 < c) (hP : 0 < P)
    (hdet : 0 < det e.A e.B e.C)
    (hφ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ)
    (hdφ : ∀ z ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ φ z)
    (hψ : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (hdψ : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hcψ : ContinuousOn (readoutSlope ψ) (Icc (-1 : ℝ) 1))
    (hpeak : GeneralDesign.PeakFeasible e φ P)
    (hlower : ∀ d ∈ Icc (0 : ℝ) (2 * (K : ℝ) * Real.sqrt P), c * d ^ 2 ≤ D d)
    (hlim : Tendsto (fun d : ℝ => D d / d ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    dissimilarityScore {xs | ValidInput K xs} (target K φ ψ)
      (receivedDistance (encoder e φ)) D = c * GeneralScore.score K φ ψ e := by
  apply moment_score_transfer e hK φ ψ D c hc hdet hφ hdφ hψ hdψ hcψ
  · intro xs ys hxs hys
    apply hlower
    exact ⟨dist_nonneg, received_distance_peak_bound (encoder e φ) P hP.le hpeak xs ys hxs hys⟩
  · exact hlim

end Analog.CriterionTransfer
