import Analog.GeneralScore

/-!
# Operational guarantees from general semidefinite designs

This file joins the checked Gram reconstruction to the actual general
operational score. A positive feasible point of the seven-variable continuum
SDP produces a continuous planar transmitter encoder satisfying every peak
constraint, with exact computation and operational score at least K²λ.
The theorem does not assert global continuous-encoder rigidity or attainment
of the SDP; those are separate mathematical steps.
-/

noncomputable section
open Set
namespace Analog.GeneralDesign
open ArbitraryEncoder GeneralCollision GramSynthesis GeneralScore

def curveOfPlanar (e : Planar) : Curve :=
  ⟨e.cx, e.cy, e.ux, e.uy, e.vx, e.vy⟩

lemma curveOfPlanar_gram (e : Planar) :
    (curveOfPlanar e).A = e.A ∧ (curveOfPlanar e).B = e.B ∧
      (curveOfPlanar e).C = e.C := by
  exact ⟨rfl, rfl, rfl⟩

lemma curveOfPlanar_energy (e : Planar) (φ : ℝ → ℝ) (s : ℝ) :
    squaredDistance (encoder (curveOfPlanar e) φ s) 0 = e.energy 1 s (φ s) := by
  dsimp [squaredDistance, encoder, curveOfPlanar, Planar.energy]
  ring

def PeakFeasible (e : Curve) (φ : ℝ → ℝ) (P : ℝ) : Prop :=
  ∀ s ∈ Icc (-1 : ℝ) 1, squaredDistance (encoder e φ s) 0 ≤ P

lemma encoder_continuousOn (e : Curve) (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (Icc (-1 : ℝ) 1)) :
    ContinuousOn (encoder e φ) (Icc (-1 : ℝ) 1) := by
  unfold encoder
  fun_prop

lemma strict_readout_endpoint_slopes (ψ : ℝ → ℝ)
    (hψ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (hdψ : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1)) :
    readoutSlope ψ (-1) ≠ readoutSlope ψ 1 := by
  rcases hψ with hc | hc
  · exact ne_of_lt (hc.strictMonoOn_derivWithin hdψ
      (by norm_num) (by norm_num) (by norm_num))
  · exact ne_of_gt (hc.strictAntiOn_derivWithin hdψ
      (by norm_num) (by norm_num) (by norm_num))

/-- Two endpoint rank-one semidefinite constraints are exactly the bound on
the maximum endpoint dual norm, with all signs and normalizations explicit. -/
theorem endpoint_constraints_iff (e : Curve) (ψ : ℝ → ℝ) (lam : ℝ)
    (hD : 0 < det e.A e.B e.C) (hlam : 0 ≤ lam) :
    (RankOnePSD e.A e.B e.C lam (-readoutSlope ψ (-1)) 1 ∧
      RankOnePSD e.A e.B e.C lam (-readoutSlope ψ 1) 1) ↔
      lam ≤ 1 / endpointDual e ψ := by
  have hA := coefficient_A_pos e hD
  have h1 := rank_one_psd_iff e.A e.B e.C lam (-readoutSlope ψ (-1)) 1
    hA hD hlam (Or.inr one_ne_zero)
  have h2 := rank_one_psd_iff e.A e.B e.C lam (-readoutSlope ψ 1) 1
    hA hD hlam (Or.inr one_ne_zero)
  have hd1 := dual_pos e.A e.B e.C (-readoutSlope ψ (-1)) 1 hA hD (Or.inr one_ne_zero)
  have hd2 := dual_pos e.A e.B e.C (-readoutSlope ψ 1) 1 hA hD (Or.inr one_ne_zero)
  rw [h1, h2]
  constructor
  · intro h
    rcases le_total (dual e.A e.B e.C (-readoutSlope ψ (-1)) 1)
      (dual e.A e.B e.C (-readoutSlope ψ 1) 1) with hle | hge
    · simpa [endpointDual, max_eq_right hle] using h.2
    · simpa [endpointDual, max_eq_left hge] using h.1
  · intro h
    constructor
    · exact h.trans (one_div_le_one_div_of_le hd1 (le_max_left _ _))
    · exact h.trans (one_div_le_one_div_of_le hd2 (le_max_right _ _))

/-- A positive feasible SDP point yields an actual continuous peak-feasible
encoder with exact computation and the asserted operational score. Endpoint
independence and Gram positive definiteness are proved from strict readout
curvature and the two semidefinite constraints. -/
theorem positive_sdp_operational_synthesis {K : ℕ} (hK : 2 ≤ K)
    (φ ψ : ℝ → ℝ) (h l₁ l₂ A B C P lam : ℝ)
    (hcφ : ContinuousOn φ (Icc (-1 : ℝ) 1))
    (hφ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ)
    (hdφ : ∀ z ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ φ z)
    (hψ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (hdψ : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hcψ : ContinuousOn (readoutSlope ψ) (Icc (-1 : ℝ) 1))
    (hlam : 0 < lam) (hpsd : PSD3 h l₁ l₂ A B C)
    (hfirst : RankOnePSD A B C lam (-readoutSlope ψ (-1)) 1)
    (hsecond : RankOnePSD A B C lam (-readoutSlope ψ 1) 1)
    (hpeak : ∀ s : ℝ, -1 ≤ s → s ≤ 1 → form3 h l₁ l₂ A B C 1 s (φ s) ≤ P) :
    ∃ e : Curve, e.A = A ∧ e.B = B ∧ e.C = C ∧
      0 < det e.A e.B e.C ∧ PeakFeasible e φ P ∧
      ContinuousOn (encoder e φ) (Icc (-1 : ℝ) 1) ∧
      GeneralCollision.ExactTarget K φ ψ (encoder e φ) ∧
      (K : ℝ) ^ 2 * lam ≤ GeneralScore.score K φ ψ e := by
  have hind : (-readoutSlope ψ (-1)) * 1 - 1 * (-readoutSlope ψ 1) ≠ 0 := by
    have hh := strict_readout_endpoint_slopes ψ hψ hdψ
    intro heq
    apply hh
    linarith
  obtain ⟨p, _, _, _, hpA, hpB, hpC, hpApos, hpD, hpfirst, hpsecond, hppeak⟩ :=
    positive_sdp_synthesis h l₁ l₂ A B C P lam (-readoutSlope ψ (-1)) 1
      (-readoutSlope ψ 1) 1 φ hlam hind hpsd hfirst hsecond hpeak
  let e := curveOfPlanar p
  have hD : 0 < det e.A e.B e.C := hpD
  have hend : lam ≤ 1 / endpointDual e ψ :=
    (endpoint_constraints_iff e ψ lam hD hlam.le).mp ⟨hpfirst, hpsecond⟩
  have hshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ := by
    rcases hψ with hc | hc
    · exact Or.inl hc.convexOn
    · exact Or.inr hc.concaveOn
  have hscore : (K : ℝ) ^ 2 * lam ≤ GeneralScore.score K φ ψ e := by
    rw [general_operational_score e hK φ ψ hD hφ hdφ hshape hdψ hcψ]
    have hh := mul_le_mul_of_nonneg_left hend (sq_nonneg (K : ℝ))
    simpa only [mul_one_div] using hh
  have hsep : GeneralCollision.SeparationLowerBound K φ ψ (encoder e φ)
      ((K : ℝ) ^ 2 * lam) := by
    have hb := (Operational.le_score_iff
      (target_nonconstant_of_strict_feature hK φ ψ hφ)
      (fun xs _ ys _ => squaredDistance_nonnegative
        (received (encoder e φ) xs) (received (encoder e φ) ys)) _).mp hscore
    exact fun xs ys hxs hys => hb xs hxs ys hys
  have hk : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  refine ⟨e, hpA, hpB, hpC, hD, ?_, encoder_continuousOn e φ hcφ,
    GeneralCollision.positive_separation_implies_exact (mul_pos (sq_pos_of_pos hk) hlam) hsep,
    hscore⟩
  intro s hs
  rw [curveOfPlanar_energy]
  exact hppeak s hs.1 hs.2

end Analog.GeneralDesign
