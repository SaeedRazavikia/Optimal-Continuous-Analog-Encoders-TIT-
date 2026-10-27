import Analog.GeneralDesign
import Analog.QuarticPower
import Analog.HeterogeneousGlobalOptimum
import Mathlib.Algebra.Order.Chebyshev
import Analog.FiniteNodeScore
import Analog.EvenReadout
import Analog.PolynomialRigidity
import Analog.PolynomialOptimizerFacts
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-! Operational polynomial optimization: the peak-feasible averaging bridge
and the assembly of the explicit coefficient optima with finite-node rigidity. -/

noncomputable section
namespace Analog.PolynomialGlobalOptima
open Set GramSynthesis HeterogeneousScore
open scoped BigOperators

/-- Coordinate-preserving passage from the polynomial coefficient record. -/
def planarOfCurve (e : Curve) : Planar :=
  ⟨e.cx, e.cy, e.ux, e.uy, e.vx, e.vy⟩

/-- The shared offset is the arithmetic average of the physical node offsets. -/
def averageCurve {K : ℕ} (e : Planar) (c : Fin K → ℝ × ℝ) : Curve :=
  ⟨(∑ i, (c i).1) / K, (∑ i, (c i).2) / K, e.ux, e.uy, e.vx, e.vy⟩

lemma averageCurve_gram {K : ℕ} (e : Planar) (c : Fin K → ℝ × ℝ) :
    (averageCurve e c).A = e.A ∧ (averageCurve e c).B = e.B ∧
      (averageCurve e c).C = e.C := ⟨rfl, rfl, rfl⟩

lemma average_encoder {K : ℕ} (hK : 0 < K) (e : Planar)
    (c : Fin K → ℝ × ℝ) (φ : ℝ → ℝ) (s : ℝ) :
    GeneralScore.encoder (averageCurve e c) φ s =
      ((∑ i, (encoder e c (fun _ t => (t, φ t)) i s).1) / K,
       (∑ i, (encoder e c (fun _ t => (t, φ t)) i s).2) / K) := by
  have hk : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  ext <;> simp [GeneralScore.encoder, averageCurve, encoder, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul] <;> field_simp

/-- Averaging the node offsets preserves the continuum peak constraint. -/
theorem average_peak {K : ℕ} (hK : 0 < K) (e : Planar)
    (c : Fin K → ℝ × ℝ) (φ : ℝ → ℝ) (P : ℝ)
    (hp : ∀ i s, s ∈ Icc (-1 : ℝ) 1 →
      ArbitraryEncoder.squaredDistance (encoder e c (fun _ t => (t, φ t)) i s) 0 ≤ P) :
    GeneralDesign.PeakFeasible (averageCurve e c) φ P := by
  intro s hs
  rw [average_encoder hK]
  let x := fun i => (encoder e c (fun _ t => (t, φ t)) i s).1
  let y := fun i => (encoder e c (fun _ t => (t, φ t)) i s).2
  have hx : (∑ i, x i)^2 ≤ (K : ℝ) * ∑ i, (x i)^2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x))
  have hy : (∑ i, y i)^2 ≤ (K : ℝ) * ∑ i, (y i)^2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := y))
  have hsum : (∑ i, ((x i)^2 + (y i)^2)) ≤ (K : ℝ) * P := by
    calc
      _ ≤ ∑ i : Fin K, P := Finset.sum_le_sum (fun i _ => by
        simpa [ArbitraryEncoder.squaredDistance, x, y] using hp i s hs)
      _ = _ := by simp
  rw [Finset.sum_add_distrib] at hsum
  have hk : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  change ((∑ i, x i) / K - 0)^2 + ((∑ i, y i) / K - 0)^2 ≤ P
  simp only [sub_zero, div_pow, ← add_div]
  apply (div_le_iff₀ (sq_pos_of_pos hk)).2
  have hh := mul_le_mul_of_nonneg_left hsum hk.le
  nlinarith [hx, hy]

/-- Averaging the offsets preserves the exact received aggregate for every
input tuple, and consequently preserves any fixed decoder's error. -/
theorem average_received {K : ℕ} (hK : 0 < K) (e : Planar)
    (c : Fin K → ℝ × ℝ) (φ : ℝ → ℝ) (s : Fin K → ℝ) :
    received (encoder e c (fun _ t => (t, φ t))) s =
      received (fun _ => GeneralScore.encoder (averageCurve e c) φ) s := by
  have hk : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  have heq : (fun (_ : Fin K) => GeneralScore.encoder (averageCurve e c) φ) =
      encoder (planarOfCurve (averageCurve e c))
        (fun _ => ((averageCurve e c).cx, (averageCurve e c).cy))
        (fun _ t => (t, φ t)) := rfl
  rw [heq, received_encoder, received_encoder]
  ext <;> simp [planarOfCurve, averageCurve, Finset.sum_const, nsmul_eq_mul] <;> field_simp

/-- Both polynomial conventions use the same Euclidean energy as the channel. -/
lemma quadratic_peak_iff (e : Curve) (P : ℝ) :
    GeneralDesign.PeakFeasible e (fun s => s^2) P ↔ e.PeakFeasibleAt P := by
  constructor
  · intro h s hlo hhi
    simpa [GeneralScore.encoder, Curve.energy, ArbitraryEncoder.squaredDistance] using h s ⟨hlo, hhi⟩
  · intro h s hs
    simpa [GeneralScore.encoder, Curve.energy, ArbitraryEncoder.squaredDistance] using h s hs.1 hs.2

lemma quartic_peak_iff (e : Curve) (P : ℝ) :
    GeneralDesign.PeakFeasible e (fun s => s^4) P ↔ Quartic.CurvePeakFeasibleAt e P := by
  constructor
  · intro h s hlo hhi
    simpa [GeneralScore.encoder, Quartic.curveEnergy, ArbitraryEncoder.squaredDistance] using h s ⟨hlo, hhi⟩
  · intro h s hs
    simpa [GeneralScore.encoder, Quartic.curveEnergy, ArbitraryEncoder.squaredDistance] using h s hs.1 hs.2

/-- The two polynomial feature functions are strictly convex on the source interval. -/
theorem polynomial_strict (p : ℕ) (hp : p = 2 ∨ p = 4) :
    StrictConvexOn ℝ (Icc (-1 : ℝ) 1) (fun s : ℝ => s^p) := by
  have he : Even p := by rcases hp with rfl | rfl <;> decide
  have hn : p ≠ 0 := by omega
  exact (he.strictConvexOn_pow hn).subset (subset_univ _) (convex_Icc _ _)

/-- The operational score of any nonsingular polynomial encoder, retaining
arbitrary per-node offsets, is its exact even-readout Gram objective. -/
theorem polynomial_score {K : ℕ} (hK : 4 ≤ K) (p : ℕ) (hp : p = 2 ∨ p = 4)
    (ψ : ℝ → ℝ) (hψ : ContDiffOn ℝ 1 ψ (Icc (-1 : ℝ) 1))
    (heven : ∀ x ∈ Icc (-1 : ℝ) 1, ψ (-x) = ψ x)
    (hshape : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (e : Planar) (c : Fin K → ℝ × ℝ) (hD : 0 < det e.A e.B e.C) :
    score (fun _ s => (s, s^p)) (fun m => m.2 - ψ m.1)
      (encoder e c (fun _ s => (s, s^p))) =
      (K : ℝ)^2 * GeneralQuadratic.gramScore (averageCurve e c)
        |GeneralScore.readoutSlope ψ 1| := by
  change score (FiniteNodeScore.sharedFeatures (fun s => s^p)) (FiniteNodeScore.readout ψ)
    (encoder e c (FiniteNodeScore.sharedFeatures (fun s => s^p))) = _
  rw [FiniteNodeScore.lemma_one_score hK e c (fun s => s^p) ψ hD
    (Or.inl (polynomial_strict p hp)) (contDiffOn_id.pow p) hshape hψ]
  exact EvenReadout.endpoint_score_eq_gramScore K (averageCurve e c) ψ heven hD

/-- The explicit shared polynomial encoder, as an actual node-indexed collection. -/
def sharedEncoder {K : ℕ} (p : ℕ) (e : Curve) : Fin K → ℝ → ℝ × ℝ :=
  fun _ => GeneralScore.encoder e (fun s => s^p)

/-- Every explicit polynomial optimizer belongs to the continuous competitor class. -/
theorem sharedEncoder_continuous {K : ℕ} (p : ℕ) (e : Curve) (i : Fin K) :
    Continuous (sharedEncoder p e i) := by
  unfold sharedEncoder GeneralScore.encoder
  fun_prop

lemma sharedEncoder_eq {K : ℕ} (p : ℕ) (e : Curve) :
    sharedEncoder (K := K) p e = encoder (planarOfCurve e)
      (fun _ => (e.cx, e.cy)) (fun _ s => (s, s^p)) := rfl

theorem shared_score {K : ℕ} (hK : 4 ≤ K) (p : ℕ) (hp : p = 2 ∨ p = 4)
    (ψ : ℝ → ℝ) (hψ : ContDiffOn ℝ 1 ψ (Icc (-1 : ℝ) 1))
    (heven : ∀ x ∈ Icc (-1 : ℝ) 1, ψ (-x) = ψ x)
    (hshape : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (e : Curve) (hD : 0 < det e.A e.B e.C) :
    score (fun _ s => (s, s^p)) (fun m => m.2 - ψ m.1) (sharedEncoder (K := K) p e) =
      (K : ℝ)^2 * GeneralQuadratic.gramScore e |GeneralScore.readoutSlope ψ 1| := by
  rw [sharedEncoder_eq]
  exact polynomial_score hK p hp ψ hψ heven hshape (planarOfCurve e)
    (fun _ => (e.cx, e.cy)) hD

/-- Coefficient optimization becomes optimization over every continuous
encoder collection. Positive-score competitors satisfy proved rigidity; all
other competitors have score at most the nonnegative attained value. -/
theorem unrestricted_polynomial_optimal {K : ℕ} (hK : 4 ≤ K)
    (p : ℕ) (hp : p = 2 ∨ p = 4) (ψ : ℝ → ℝ)
    (hψ : ContDiffOn ℝ 1 ψ (Icc (-1 : ℝ) 1))
    (heven : ∀ x ∈ Icc (-1 : ℝ) 1, ψ (-x) = ψ x)
    (hshape : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (P : ℝ) (opt : Curve) (hD : 0 < det opt.A opt.B opt.C)
    (hmax : ∀ e : Curve, GeneralDesign.PeakFeasible e (fun s => s^p) P →
      GeneralQuadratic.gramScore e |GeneralScore.readoutSlope ψ 1| ≤
        GeneralQuadratic.gramScore opt |GeneralScore.readoutSlope ψ 1|) :
    ∀ E : Fin K → ℝ → ℝ × ℝ,
      (∀ i, ContinuousOn (E i) (Icc (-1 : ℝ) 1)) →
      (∀ i s, s ∈ Icc (-1 : ℝ) 1 → ArbitraryEncoder.squaredDistance (E i s) 0 ≤ P) →
      score (fun _ s => (s, s^p)) (fun m => m.2 - ψ m.1) E ≤
        score (fun _ s => (s, s^p)) (fun m => m.2 - ψ m.1) (sharedEncoder (K := K) p opt) := by
  intro E hE hpeak
  by_cases hpos : 0 < score (fun _ s => (s, s^p)) (fun m => m.2 - ψ m.1) E
  · obtain ⟨u, v, c, hdet, haff⟩ :=
      PolynomialRigidity.polynomial_positive_score_rigidity hK p hp ψ hψ hshape E hE hpos
    let e : Planar := ⟨0, 0, u.1, u.2, v.1, v.2⟩
    have heq : ∀ i s, s ∈ Icc (-1 : ℝ) 1 →
        E i s = encoder e c (fun _ t => (t, t^p)) i s := by
      intro i s hs
      rw [haff i s hs]
      ext <;> simp [encoder, e, mul_comm]
    have hpeak' : ∀ i s, s ∈ Icc (-1 : ℝ) 1 →
        ArbitraryEncoder.squaredDistance (encoder e c (fun _ t => (t,t^p)) i s) 0 ≤ P := by
      intro i s hs
      rw [← heq i s hs]
      exact hpeak i s hs
    have hDe : 0 < det e.A e.B e.C := by
      have hid : det e.A e.B e.C = (u.1*v.2 - v.1*u.2)^2 := by
        dsimp [det, Planar.A, Planar.B, Planar.C, e]
        ring
      rw [hid]
      exact sq_pos_of_ne_zero hdet
    rw [HeterogeneousGlobalOptimum.score_eq_of_source_eq _ E _ _ heq,
      polynomial_score hK p hp ψ hψ heven hshape e c hDe,
      shared_score hK p hp ψ hψ heven hshape opt hD]
    exact mul_le_mul_of_nonneg_left
      (hmax (averageCurve e c) (average_peak (by omega) e c (fun s => s^p) P hpeak'))
      (sq_nonneg _)
  · apply (le_of_not_gt hpos).trans
    exact Operational.score_nonnegative
      (FiniteNodeScore.finite_target_nonconstant (by omega) (fun s => s^p) ψ
        (Or.inl (polynomial_strict p hp)))
      (fun _ _ _ _ => ArbitraryEncoder.squaredDistance_nonnegative _ _)

/-- Proposition 4, quadratic case: the displayed optimizer is peak feasible,
has the exact operational value, and dominates every continuous encoder
collection, without assuming that its competitors compute the target exactly. -/
theorem quadratic_global_optimal {K : ℕ} (hK : 4 ≤ K)
    (P : ℝ) (hP : 0 < P) (ψ : ℝ → ℝ)
    (hψ : ContDiffOn ℝ 1 ψ (Icc (-1 : ℝ) 1))
    (heven : ∀ x ∈ Icc (-1 : ℝ) 1, ψ (-x) = ψ x)
    (hshape : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ) :
    let M := |GeneralScore.readoutSlope ψ 1|
    let b := GeneralQuadratic.optimalParameter M
    let e := (GeneralQuadratic.optimalCurve b).scale (Real.sqrt P)
    (∀ i : Fin K, ∀ s ∈ Icc (-1 : ℝ) 1,
      ArbitraryEncoder.squaredDistance (sharedEncoder 2 e i s) 0 ≤ P) ∧
    score (fun _ s => (s,s^2)) (fun m => m.2 - ψ m.1)
      (sharedEncoder (K := K) 2 e) = (K : ℝ)^2 * P * b^2 * (b-1) ∧
    ∀ E : Fin K → ℝ → ℝ × ℝ,
      (∀ i, ContinuousOn (E i) (Icc (-1 : ℝ) 1)) →
      (∀ i s, s ∈ Icc (-1 : ℝ) 1 → ArbitraryEncoder.squaredDistance (E i s) 0 ≤ P) →
      score (fun _ s => (s,s^2)) (fun m => m.2 - ψ m.1) E ≤
        score (fun _ s => (s,s^2)) (fun m => m.2 - ψ m.1)
          (sharedEncoder (K := K) 2 e) := by
  dsimp only
  have hM := EvenReadout.endpoint_magnitude_pos ψ heven
    (hψ.differentiableOn (by norm_num)) hshape
  have hopt := quadratic_optimal_all_power |GeneralScore.readoutSlope ψ 1| P hM hP
  have hdet := PolynomialOptimizerFacts.quadratic_det_pos
    |GeneralScore.readoutSlope ψ 1| P hM hP
  refine ⟨?_, ?_, ?_⟩
  · intro i s hs
    exact (quadratic_peak_iff _ P).mpr hopt.1 s hs
  · rw [shared_score hK 2 (Or.inl rfl) ψ hψ heven hshape _ hdet, hopt.2.1]
    ring
  · apply unrestricted_polynomial_optimal hK 2 (Or.inl rfl) ψ hψ heven hshape P _ hdet
    intro e he
    exact hopt.2.2 e ((quadratic_peak_iff e P).mp he)

/-- Proposition 4, quartic case: the root is unique, the displayed encoder
is feasible, and its exact operational score is globally optimal over every
continuous peak-feasible collection. -/
theorem quartic_global_optimal {K : ℕ} (hK : 4 ≤ K)
    (P : ℝ) (hP : 0 < P) (ψ : ℝ → ℝ)
    (hψ : ContDiffOn ℝ 1 ψ (Icc (-1 : ℝ) 1))
    (heven : ∀ x ∈ Icc (-1 : ℝ) 1, ψ (-x) = ψ x)
    (hshape : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ) :
    let M := |GeneralScore.readoutSlope ψ 1|
    ∃ r : ℝ, (0 < r ∧ r < 1/3 ∧ Quartic.RootEquation M r) ∧
      (∀ r' : ℝ, 0 < r' → r' < 1/3 → Quartic.RootEquation M r' → r' = r) ∧
      let e := (Quartic.optimalPlanarCurve r).scale (Real.sqrt P)
      (∀ i : Fin K, ∀ s ∈ Icc (-1 : ℝ) 1,
        ArbitraryEncoder.squaredDistance (sharedEncoder 4 e i s) 0 ≤ P) ∧
      score (fun _ s => (s,s^4)) (fun m => m.2 - ψ m.1)
        (sharedEncoder (K := K) 4 e) =
          (K : ℝ)^2 * P /
            (M^2 / (Real.sqrt (Quartic.optA r))^2 + 1 / (Quartic.optb r)^2) ∧
      ∀ E : Fin K → ℝ → ℝ × ℝ,
        (∀ i, ContinuousOn (E i) (Icc (-1 : ℝ) 1)) →
        (∀ i s, s ∈ Icc (-1 : ℝ) 1 → ArbitraryEncoder.squaredDistance (E i s) 0 ≤ P) →
        score (fun _ s => (s,s^4)) (fun m => m.2 - ψ m.1) E ≤
          score (fun _ s => (s,s^4)) (fun m => m.2 - ψ m.1)
            (sharedEncoder (K := K) 4 e) := by
  dsimp only
  have hM := EvenReadout.endpoint_magnitude_pos ψ heven
    (hψ.differentiableOn (by norm_num)) hshape
  obtain ⟨r, hr, hopt⟩ := Quartic.quartic_optimal_all_power
    |GeneralScore.readoutSlope ψ 1| P hM hP
  have hdet := PolynomialOptimizerFacts.quartic_det_pos P r hP hr.1
  refine ⟨r, hr, ?_, ?_, ?_, ?_⟩
  · intro r' hr' _ hroot
    exact Quartic.root_unique _ r' r hM hr'.le hr.1.le hroot hr.2.2
  · intro i s hs
    exact (quartic_peak_iff _ P).mpr hopt.1 s hs
  · rw [shared_score hK 4 (Or.inr rfl) ψ hψ heven hshape _ hdet,
      PolynomialOptimizerFacts.quartic_score_formula _ P r hP hr.1]
    ring
  · apply unrestricted_polynomial_optimal hK 4 (Or.inr rfl) ψ hψ heven hshape P _ hdet
    intro e he
    exact hopt.2.2 e ((quartic_peak_iff e P).mp he)

end Analog.PolynomialGlobalOptima
