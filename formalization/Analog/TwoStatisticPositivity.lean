import Analog.TwoStatisticAttainment
import Analog.CompletionIdentification
import Analog.GeneralRigidity

/-!
# Positive definite design from common-completion identification

An open identifying neighborhood rules out a nonzero zero-cost direction of
any positive-score feasible Gram matrix. The proof uses actual completed
input tuples and elementary continuity of a line through the neighborhood.
-/

noncomputable section
open Set
open scoped NNReal
namespace Analog.TwoStatisticPositivity
open GramSynthesis ArbitraryEncoder AdditiveStatistics CompletionIdentification
open TwoStatisticAttainment

/-- Actual sums of valid triples, before division by the user count. -/
def tripleStatistics (γ : ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  statisticSum γ '' {xs | ValidInput 3 xs}

def completedPoint (K : ℕ) (γ : ℝ → ℝ × ℝ) (d p : ℝ × ℝ) (x : ℝ) : ℝ × ℝ :=
  ((p.1+(γ x).1+d.1)/(K : ℝ), (p.2+(γ x).2+d.2)/(K : ℝ))

/-- Every completion used in the identification argument is actually attainable. -/
lemma completedPoint_mem_attainable {K : ℕ} (hK : 4 ≤ K)
    (γ : ℝ → ℝ × ℝ) {p : ℝ × ℝ} (hp : p ∈ tripleStatistics γ)
    {filler x : ℝ} (hfiller : InSource filler) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    completedPoint K γ ((K-4) • γ filler) p x ∈ attainable K γ := by
  obtain ⟨xs, hxs, rfl⟩ := hp
  refine ⟨completeTripleAt K xs x filler,
    completeTripleAt_valid hK hxs ⟨hx.1.le, hx.2.le⟩ hfiller, ?_⟩
  simp only [meanStatistic, statisticSum_completeTripleAt, completedPoint,
    Prod.fst_add, Prod.snd_add]

/-- One nonempty open identifying neighborhood suffices for design positivity.
The manuscript's dense-open identification hypothesis supplies such a
neighborhood; density is needed for its separate rigidity argument. -/
def LocalIdentification (K : ℕ) (γ : ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (filler : ℝ) : Prop :=
  ∃ B : Set (ℝ × ℝ), IsOpen B ∧ B.Nonempty ∧ B ⊆ tripleStatistics γ ∧
    IdentifiesOn K γ F ((K-4) • γ filler) B

/-- A nonzero direction has a distinct nearby point inside any open planar set. -/
lemma exists_line_point {B : Set (ℝ × ℝ)} (hB : IsOpen B)
    {p : ℝ × ℝ} (hp : p ∈ B) (x y : ℝ) (hxy : x ≠ 0 ∨ y ≠ 0) :
    ∃ t : ℝ, t ≠ 0 ∧ (p.1+t*x,p.2+t*y) ∈ B ∧ (p.1+t*x,p.2+t*y) ≠ p := by
  let line : ℝ → ℝ × ℝ := fun t => (p.1+t*x,p.2+t*y)
  have hline : Continuous line := by dsimp [line]; fun_prop
  have hopen : IsOpen (line ⁻¹' B) := hB.preimage hline
  have hzero : (0 : ℝ) ∈ line ⁻¹' B := by simpa [line] using hp
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  have ht : 0 < ε/2 := by linarith
  have hmem : ε/2 ∈ Metric.ball (0 : ℝ) ε := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    linarith
  refine ⟨ε/2, ht.ne', hb hmem, ?_⟩
  intro heq
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  dsimp only at hx hy
  have htx : ε/2*x = 0 := by linarith
  have hty : ε/2*y = 0 := by linarith
  rcases hxy with hx0 | hy0
  · exact hx0 ((mul_eq_zero.mp htx).resolve_left ht.ne')
  · exact hy0 ((mul_eq_zero.mp hty).resolve_left ht.ne')

/-- The exact pair constraints and identification exclude every nonzero
zero-cost direction, without assuming an encoder rigidity theorem. -/
theorem positive_pair_constraints_strict {K : ℕ} (hK : 4 ≤ K)
    (γ : ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ) (filler : ℝ)
    (hfiller : InSource filler) (hid : LocalIdentification K γ F filler)
    (A B C lam : ℝ) (hlam : 0 < lam)
    (hpsd : ∀ x y : ℝ, 0 ≤ form2 A B C x y)
    (hpairs : ∀ μ ∈ attainable K γ, ∀ ν ∈ attainable K γ,
      lam * (F μ-F ν)^2 ≤ form2 A B C (μ.1-ν.1) (μ.2-ν.2)) :
    ∀ x y : ℝ, x ≠ 0 ∨ y ≠ 0 → 0 < form2 A B C x y := by
  intro x y hxy
  by_contra hnot
  have hzero : form2 A B C x y = 0 := le_antisymm (le_of_not_gt hnot) (hpsd x y)
  obtain ⟨U, hU, ⟨p, hp⟩, hsub, hidentify⟩ := hid
  obtain ⟨t, _, hp', hne⟩ := exists_line_point hU hp x y hxy
  apply hne
  symm
  apply hidentify p hp (p.1+t*x,p.2+t*y) hp'
  intro s hs
  let μ := completedPoint K γ ((K-4) • γ filler) p s
  let ν := completedPoint K γ ((K-4) • γ filler) (p.1+t*x,p.2+t*y) s
  have hμ := completedPoint_mem_attainable hK γ (hsub hp) hfiller hs
  have hν := completedPoint_mem_attainable hK γ (hsub hp') hfiller hs
  have h := hpairs μ hμ ν hν
  have he : form2 A B C (μ.1-ν.1) (μ.2-ν.2) =
      (t/(K : ℝ))^2 * form2 A B C x y := by
    dsimp [μ, ν, completedPoint, form2]
    ring
  rw [he, hzero, mul_zero] at h
  have hs0 : (F μ-F ν)^2 = 0 := by nlinarith [sq_nonneg (F μ-F ν)]
  have heq : F μ = F ν := sub_eq_zero.mp (sq_eq_zero_iff.mp hs0)
  exact heq

/-- Positive SDP score forces an invertible lower Gram block from the stated
common-completion condition; it is no longer a separate definiteness premise. -/
theorem positive_feasible_gram {K : ℕ} (hK : 4 ≤ K)
    {γ : ℝ → ℝ × ℝ} {F : ℝ × ℝ → ℝ} {filler P : ℝ}
    (hfiller : InSource filler) (hid : LocalIdentification K γ F filler)
    {q : Coordinates} (hq : Feasible γ (attainable K γ) F P q) (hpos : 0 < q 6) :
    0 < q 3 ∧ 0 < det (q 3) (q 4) (q 5) := by
  have hpsd (x y : ℝ) : 0 ≤ form2 (q 3) (q 4) (q 5) x y := by
    simpa [form3] using hq.2.1 0 x y
  have hstrict := positive_pair_constraints_strict hK γ F filler hfiller hid
    (q 3) (q 4) (q 5) (q 6) hpos hpsd hq.2.2.2
  have hA : 0 < q 3 := by simpa [form2] using hstrict 1 0 (Or.inl one_ne_zero)
  refine ⟨hA, ?_⟩
  have ht := hstrict (-(q 5)) (q 3) (Or.inr hA.ne')
  have he : form2 (q 3) (q 4) (q 5) (-(q 5)) (q 3) =
      q 3 * det (q 3) (q 4) (q 5) := by unfold form2 det; ring
  rw [he] at ht
  exact (mul_pos_iff_of_pos_left hA).mp ht


/-- The dense identifying family in the manuscript supplies the single open
neighborhood needed by positivity. The regular triple-image set Ω may be used
here because each of its points is an actual triple statistic. -/
theorem localIdentification_of_dense_family {K : ℕ} {γ : ℝ → ℝ × ℝ}
    {F : ℝ × ℝ → ℝ} {filler : ℝ} {Ω O : Set (ℝ × ℝ)}
    (hΩ : Ω.Nonempty) (hactual : Ω ⊆ tripleStatistics γ)
    (hdense : Ω ⊆ closure O)
    (hlocal : ∀ p ∈ O, ∃ B : Set (ℝ × ℝ), IsOpen B ∧ p ∈ B ∧ B ⊆ Ω ∧
      IdentifiesOn K γ F ((K-4) • γ filler) B) :
    LocalIdentification K γ F filler := by
  have hO : O.Nonempty := by
    by_contra hn
    have he : O = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    rw [he, closure_empty] at hdense
    obtain ⟨p, hp⟩ := hΩ
    exact hdense hp
  obtain ⟨p, hp⟩ := hO
  obtain ⟨B, hB, hpB, hBΩ, hid⟩ := hlocal p hp
  exact ⟨B, hB, ⟨p, hpB⟩, hBΩ.trans hactual, hid⟩

/-- Positive feasible matrices now reconstruct operational exact encoders
without a separate positive-definiteness hypothesis. -/
theorem positive_sdp_operational_synthesis {K : ℕ} (hK : 4 ≤ K)
    {γ : ℝ → ℝ × ℝ} {F : ℝ × ℝ → ℝ} {filler P : ℝ}
    (hγ : ContinuousOn γ (Icc (-1 : ℝ) 1))
    (hn : Operational.NonconstantOn (attainable K γ) F)
    (hfiller : InSource filler) (hid : LocalIdentification K γ F filler)
    {q : Coordinates} (hq : Feasible γ (attainable K γ) F P q) (hpos : 0 < q 6) :
    ∃ e : Planar, e.A = q 3 ∧ e.B = q 4 ∧ e.C = q 5 ∧
      0 < det e.A e.B e.C ∧
      ContinuousOn (encoder e γ) (Icc (-1 : ℝ) 1) ∧
      ExactComputation K γ F (encoder e γ) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, squaredDistance (encoder e γ s) 0 ≤ P) ∧
      (K : ℝ)^2*q 6 ≤ TwoStatisticDesign.score K γ F (encoder e γ) := by
  have hpd := positive_feasible_gram hK hfiller hid hq hpos
  obtain ⟨e, hA, hB, hC, hcont, hexact, hpeak, hscore⟩ :=
    TwoStatisticDesign.positive_definite_operational_synthesis (by omega : 0 < K)
      γ F hγ hn (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) P (q 6)
      hpd.1 hpd.2 hq.2.1 hq.2.2.1 hq.2.2.2
  refine ⟨e, hA, hB, hC, ?_, hcont, hexact, hpeak, hscore⟩
  simpa [hA, hB, hC] using hpd.2

/-- A physical coefficient curve supplies its Gram coordinates and its
actual attained-pair objective, including degenerate curves. -/
def coordinatesOfCurve (K : ℕ) (γ : ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (e : Planar) : Coordinates :=
  ![e.h, e.l₁, e.l₂, e.A, e.B, e.C,
    Operational.score (attainable K γ) F (TwoStatisticDesign.gramCost e)]

lemma coordinatesOfCurve_feasible {K : ℕ} {γ : ℝ → ℝ × ℝ}
    {F : ℝ × ℝ → ℝ} {P : ℝ} (e : Planar)
    (hn : Operational.NonconstantOn (attainable K γ) F)
    (hpeak : ∀ s ∈ Icc (-1 : ℝ) 1, squaredDistance (encoder e γ s) 0 ≤ P) :
    Feasible γ (attainable K γ) F P (coordinatesOfCurve K γ F e) := by
  have hcost := fun μ (_ : μ ∈ attainable K γ) ν (_ : ν ∈ attainable K γ) =>
    TwoStatisticDesign.gramCost_nonnegative e μ ν
  refine ⟨Operational.score_nonnegative hn hcost, e.gram_psd, ?_,
    Operational.score_is_lowerBound hn hcost⟩
  intro s hs
  change form3 e.h e.l₁ e.l₂ e.A e.B e.C 1 (γ s).1 (γ s).2 ≤ P
  rw [← Planar.energy_eq_form3, ← encoder_energy]
  exact hpeak s hs

/-- The general SDP optimum is attained by a continuous exact planar encoder,
and is globally optimal over every affine coefficient curve, including
singular competitors. This is the complete operational coefficient-class
design result; reduction of arbitrary continuous encoders is a separate
rigidity theorem. -/
theorem operational_maximum_attained {K : ℕ} (hK : 4 ≤ K)
    {γ : ℝ → ℝ × ℝ} {F : ℝ × ℝ → ℝ} {P filler : ℝ} {L : ℝ≥0}
    (hP : 0 < P) (hγ : ContinuousOn γ (Icc (-1 : ℝ) 1))
    (hind : IndependentStatistics γ)
    (hn : Operational.NonconstantOn (attainable K γ) F)
    (hL : LipschitzOnWith L F (attainable K γ))
    (hfiller : InSource filler) (hid : LocalIdentification K γ F filler) :
    ∃ e : Planar, 0 < det e.A e.B e.C ∧
      ContinuousOn (encoder e γ) (Icc (-1 : ℝ) 1) ∧
      ExactComputation K γ F (encoder e γ) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, squaredDistance (encoder e γ s) 0 ≤ P) ∧
      0 < TwoStatisticDesign.score K γ F (encoder e γ) ∧
      ∀ e' : Planar,
        (∀ s ∈ Icc (-1 : ℝ) 1, squaredDistance (encoder e' γ s) 0 ≤ P) →
        TwoStatisticDesign.score K γ F (encoder e' γ) ≤
          TwoStatisticDesign.score K γ F (encoder e γ) := by
  obtain ⟨q, hq, hqpos, hmax⟩ := attained_statistic_maximum hP hγ hind hn hL
  obtain ⟨e, _, _, _, hdet, hcont, hexact, hpeak, hscore⟩ :=
    positive_sdp_operational_synthesis hK hγ hn hfiller hid hq hqpos
  have hk : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hp : 0 < (K : ℝ)^2*q 6 := mul_pos (sq_pos_of_pos hk) hqpos
  refine ⟨e, hdet, hcont, hexact, hpeak, hp.trans_le hscore, ?_⟩
  intro e' hpeak'
  have hb := hmax (coordinatesOfCurve K γ F e') (coordinatesOfCurve_feasible e' hn hpeak')
  change Operational.score (attainable K γ) F (TwoStatisticDesign.gramCost e') ≤ q 6 at hb
  rw [TwoStatisticDesign.affine_operational_score e' (by omega : 0 < K) γ F hn]
  exact (mul_le_mul_of_nonneg_left hb (sq_nonneg (K : ℝ))).trans hscore


/-- The operational optimum has exactly the K² normalization of the attained
SDP maximum, rather than only a one-sided implementation guarantee. -/
theorem operational_score_eq_sdp_maximum {K : ℕ} (hK : 4 ≤ K)
    {γ : ℝ → ℝ × ℝ} {F : ℝ × ℝ → ℝ} {P filler : ℝ}
    (hγ : ContinuousOn γ (Icc (-1 : ℝ) 1))
    (hn : Operational.NonconstantOn (attainable K γ) F)
    (hfiller : InSource filler) (hid : LocalIdentification K γ F filler)
    {q : Coordinates} (hq : Feasible γ (attainable K γ) F P q) (hpos : 0 < q 6)
    (hmax : ∀ r : Coordinates, Feasible γ (attainable K γ) F P r → r 6 ≤ q 6) :
    ∃ e : Planar, 0 < det e.A e.B e.C ∧
      ContinuousOn (encoder e γ) (Icc (-1 : ℝ) 1) ∧
      ExactComputation K γ F (encoder e γ) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, squaredDistance (encoder e γ s) 0 ≤ P) ∧
      TwoStatisticDesign.score K γ F (encoder e γ) = (K : ℝ)^2*q 6 := by
  obtain ⟨e, _, _, _, hdet, hcont, hexact, hpeak, hscore⟩ :=
    positive_sdp_operational_synthesis hK hγ hn hfiller hid hq hpos
  refine ⟨e, hdet, hcont, hexact, hpeak, le_antisymm ?_ hscore⟩
  have hb := hmax (coordinatesOfCurve K γ F e) (coordinatesOfCurve_feasible e hn hpeak)
  change Operational.score (attainable K γ) F (TwoStatisticDesign.gramCost e) ≤ q 6 at hb
  rw [TwoStatisticDesign.affine_operational_score e (by omega : 0 < K) γ F hn]
  exact mul_le_mul_of_nonneg_left hb (sq_nonneg (K : ℝ))


/-- The manuscript's common-completion condition on the regular triple image:
a dense open family, with an open identifying neighborhood at each point. -/
def CommonCompletionCondition (K : ℕ) (γ : ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ)
    (filler : ℝ) : Prop :=
  let Ω := GeneralRigidity.regularTripleImage (fun s => (γ s).1) (fun s => (γ s).2)
  ∃ O : Set (ℝ × ℝ), IsOpen O ∧ O ⊆ Ω ∧ Ω ⊆ closure O ∧
    ∀ p ∈ O, ∃ B : Set (ℝ × ℝ), IsOpen B ∧ p ∈ B ∧ B ⊆ Ω ∧
      IdentifiesOn K γ F ((K-4) • γ filler) B

/-- The required open identifying set is derived directly from the manuscript
regularity, independence, and dense common-completion hypotheses. Nonemptiness
of the regular image and its actual-input witnesses are proved, not assumed. -/
theorem localIdentification_of_commonCompletion {K : ℕ} {γ : ℝ → ℝ × ℝ}
    {F : ℝ × ℝ → ℝ} {filler : ℝ}
    (hγ : ContinuousOn γ (Icc (-1 : ℝ) 1))
    (hdγ : DifferentiableOn ℝ γ (Ioo (-1 : ℝ) 1))
    (hind : IndependentStatistics γ)
    (hci : CommonCompletionCondition K γ F filler) :
    LocalIdentification K γ F filler := by
  have hline := GeneralRigidity.notInAffineLine_of_independent hind
  have hΩ := GeneralRigidity.regularTripleImage_nonempty hγ.fst hγ.snd hdγ.fst hdγ.snd hline
  obtain ⟨O, _, _, hdense, hlocal⟩ := hci
  apply localIdentification_of_dense_family hΩ ?_ hdense hlocal
  intro p hp
  obtain ⟨xs, hxs, he⟩ := GeneralRigidity.regularTripleImage_valid hp
  exact ⟨xs, hxs, he⟩

/-- Operational attainment for arbitrary prescribed additive statistics under
the manuscript's common-completion condition. The conclusion optimizes over
all coefficient curves; the unrestricted continuous-encoder converse is the
only separate reduction needed to enlarge that competitor class. -/
theorem general_operational_maximum_attained {K : ℕ} (hK : 4 ≤ K)
    {γ : ℝ → ℝ × ℝ} {F : ℝ × ℝ → ℝ} {P filler : ℝ} {L : ℝ≥0}
    (hP : 0 < P) (hγ : ContinuousOn γ (Icc (-1 : ℝ) 1))
    (hdγ : DifferentiableOn ℝ γ (Ioo (-1 : ℝ) 1))
    (hind : IndependentStatistics γ)
    (hn : Operational.NonconstantOn (attainable K γ) F)
    (hL : LipschitzOnWith L F (attainable K γ))
    (hfiller : InSource filler) (hci : CommonCompletionCondition K γ F filler) :
    ∃ e : Planar, 0 < det e.A e.B e.C ∧
      ContinuousOn (encoder e γ) (Icc (-1 : ℝ) 1) ∧
      ExactComputation K γ F (encoder e γ) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, squaredDistance (encoder e γ s) 0 ≤ P) ∧
      0 < TwoStatisticDesign.score K γ F (encoder e γ) ∧
      ∀ e' : Planar,
        (∀ s ∈ Icc (-1 : ℝ) 1, squaredDistance (encoder e' γ s) 0 ≤ P) →
        TwoStatisticDesign.score K γ F (encoder e' γ) ≤
          TwoStatisticDesign.score K γ F (encoder e γ) :=
  operational_maximum_attained hK hP hγ hind hn hL hfiller
    (localIdentification_of_commonCompletion hγ hdγ hind hci)


/-- Joint attainment of the general SDP and its exact operational realization
under the manuscript assumptions, with neither optimum supplied as a premise. -/
theorem general_sdp_operational_attainment {K : ℕ} (hK : 4 ≤ K)
    {γ : ℝ → ℝ × ℝ} {F : ℝ × ℝ → ℝ} {P filler : ℝ} {L : ℝ≥0}
    (hP : 0 < P) (hγ : ContinuousOn γ (Icc (-1 : ℝ) 1))
    (hdγ : DifferentiableOn ℝ γ (Ioo (-1 : ℝ) 1))
    (hind : IndependentStatistics γ)
    (hn : Operational.NonconstantOn (attainable K γ) F)
    (hL : LipschitzOnWith L F (attainable K γ))
    (hfiller : InSource filler) (hci : CommonCompletionCondition K γ F filler) :
    ∃ q : Coordinates, Feasible γ (attainable K γ) F P q ∧ 0 < q 6 ∧
      (∀ r : Coordinates, Feasible γ (attainable K γ) F P r → r 6 ≤ q 6) ∧
      ∃ e : Planar, 0 < det e.A e.B e.C ∧
        ContinuousOn (encoder e γ) (Icc (-1 : ℝ) 1) ∧
        ExactComputation K γ F (encoder e γ) ∧
        (∀ s ∈ Icc (-1 : ℝ) 1, squaredDistance (encoder e γ s) 0 ≤ P) ∧
        TwoStatisticDesign.score K γ F (encoder e γ) = (K : ℝ)^2*q 6 := by
  obtain ⟨q, hq, hqpos, hmax⟩ := attained_statistic_maximum hP hγ hind hn hL
  refine ⟨q, hq, hqpos, hmax, ?_⟩
  exact operational_score_eq_sdp_maximum hK hγ hn hfiller
    (localIdentification_of_commonCompletion hγ hdγ hind hci) hq hqpos hmax

end Analog.TwoStatisticPositivity
