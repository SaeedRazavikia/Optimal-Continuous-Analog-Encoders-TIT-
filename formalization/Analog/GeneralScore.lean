import Analog.VarianceScore
import Analog.GeneralCollision
import Analog.GramSynthesis
import Analog.MomentPaths
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Operational separation for general moment targets

The score is the actual infimum over pairs of finite source lists. The lower
bound applies to arbitrary local features. The exact formula and small-distance
sharpness apply to strictly convex or concave features differentiable in the
interior, with convex or concave C¹ mean readouts. Actual two-input paths prove
the converse, without a postulated attainable neighborhood or a rigidity
assumption. Endpoint slopes are derivatives within the closed source interval,
so only one-sided endpoint differentiability is required.
-/

noncomputable section

open Set
namespace Analog.GeneralScore
open ArbitraryEncoder GeneralCollision GramSynthesis

def encoder (e : Curve) (φ : ℝ → ℝ) (s : ℝ) : ℝ × ℝ :=
  (e.cx + e.ux * s + e.vx * φ s, e.cy + e.uy * s + e.vy * φ s)

def score (K : ℕ) (φ ψ : ℝ → ℝ) (e : Curve) : ℝ :=
  Operational.score {xs | ValidInput K xs} (target K φ ψ)
    (fun xs ys => squaredDistance (received (encoder e φ) xs) (received (encoder e φ) ys))

def readoutSlope (ψ : ℝ → ℝ) (s : ℝ) : ℝ := derivWithin ψ (Icc (-1 : ℝ) 1) s

def endpointDual (e : Curve) (ψ : ℝ → ℝ) : ℝ :=
  max (dual e.A e.B e.C (-readoutSlope ψ (-1)) 1)
    (dual e.A e.B e.C (-readoutSlope ψ 1) 1)

lemma received_encoder (e : Curve) (φ : ℝ → ℝ) (xs : List ℝ) :
    received (encoder e φ) xs =
      ((xs.length : ℝ) * e.cx + e.ux * firstMoment xs + e.vx * featureMoment φ xs,
       (xs.length : ℝ) * e.cy + e.uy * firstMoment xs + e.vy * featureMoment φ xs) := by
  induction xs with
  | nil => simp [received, firstMoment, featureMoment]; rfl
  | cons x xs ih =>
    simp only [received, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    apply Prod.ext <;>
      simp [encoder, firstMoment, featureMoment, Nat.cast_add, Nat.cast_one] <;> ring

lemma received_squaredDistance (e : Curve) (φ : ℝ → ℝ) {K : ℕ}
    (xs ys : List ℝ) (hx : ValidInput K xs) (hy : ValidInput K ys) :
    squaredDistance (received (encoder e φ) xs) (received (encoder e φ) ys) =
      form2 e.A e.B e.C (firstMoment xs - firstMoment ys)
        (featureMoment φ xs - featureMoment φ ys) := by
  rw [received_encoder, received_encoder, hx.1, hy.1]
  dsimp [squaredDistance, form2, Curve.A, Curve.B, Curve.C]
  ring

lemma mean_in_source {K : ℕ} (hK : 0 < K) (xs : List ℝ) (hx : ValidInput K xs) :
    firstMoment xs / (K : ℝ) ∈ Icc (-1 : ℝ) 1 := by
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hb := GeneralCollision.firstMoment_bounds xs hx.2
  rw [hx.1] at hb
  constructor
  · apply (le_div_iff₀ hk).2
    simpa using hb.1
  · apply (div_le_iff₀ hk).2
    simpa using hb.2

/-- The maximum of a convex quadratic on a real interval is at an endpoint. -/
lemma quadratic_endpoint_bound (A B C a b q : ℝ) (hB : 0 ≤ B)
    (ha : a ≤ q) (hb : q ≤ b) :
    A + 2 * C * q + B * q ^ 2 ≤
      max (A + 2 * C * a + B * a ^ 2) (A + 2 * C * b + B * b ^ 2) := by
  by_cases hab : a = b
  · have hq : q = a := by linarith
    simp [hq, hab]
  · have hlen : 0 < b - a := by
      have : a < b := lt_of_le_of_ne (ha.trans hb) hab
      linarith
    let D := max (A + 2 * C * a + B * a ^ 2) (A + 2 * C * b + B * b ^ 2)
    have h1 := mul_le_mul_of_nonneg_left (le_max_left
      (A + 2 * C * a + B * a ^ 2) (A + 2 * C * b + B * b ^ 2)) (sub_nonneg.mpr hb)
    have h2 := mul_le_mul_of_nonneg_left (le_max_right
      (A + 2 * C * a + B * a ^ 2) (A + 2 * C * b + B * b ^ 2)) (sub_nonneg.mpr ha)
    have hn := mul_nonneg (mul_nonneg hB (sub_nonneg.mpr ha)) (sub_nonneg.mpr hb)
    have hid : (b - q) * (A + 2 * C * a + B * a ^ 2) +
        (q - a) * (A + 2 * C * b + B * b ^ 2) =
        (b - a) * (A + 2 * C * q + B * q ^ 2) +
          (b - a) * (B * (q - a) * (b - q)) := by ring
    have hh : (b - a) * (A + 2 * C * q + B * q ^ 2) ≤ (b - a) * D := by
      dsimp [D] at *
      nlinarith only [h1, h2, hid, mul_nonneg hlen.le hn]
    exact (mul_le_mul_iff_right₀ hlen).mp hh

lemma dual_endpoint_bound (e : Curve) (hD : 0 < det e.A e.B e.C)
    (a b q : ℝ) (hq : min a b ≤ q ∧ q ≤ max a b) :
    dual e.A e.B e.C (-q) 1 ≤
      max (dual e.A e.B e.C (-a) 1) (dual e.A e.B e.C (-b) 1) := by
  have hB : 0 ≤ e.B := by dsimp [Curve.B]; positivity
  have step (x y : ℝ) (hlo : x ≤ q) (hhi : q ≤ y) :
      dual e.A e.B e.C (-q) 1 ≤
        max (dual e.A e.B e.C (-x) 1) (dual e.A e.B e.C (-y) 1) := by
    simp only [dual_formula]
    have h := quadratic_endpoint_bound e.A e.B e.C x y q hB hlo hhi
    have hh := div_le_div_of_nonneg_right h hD.le
    rw [← max_div_div_right (le_of_lt hD)] at hh
    convert hh using 1 <;> congr 1 <;> ring
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab] at hq
    exact step a b hq.1 hq.2
  · rw [min_eq_right hba, max_eq_left hba] at hq
    simpa only [max_comm] using step b a hq.1 hq.2

/-- A secant of a differentiable convex or concave readout uses a slope between
its two endpoint derivatives. The statement also covers coincident arguments. -/
lemma secant_slope_between_endpoints (ψ : ℝ → ℝ)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (a b : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1) (hb : b ∈ Icc (-1 : ℝ) 1) :
    ∃ q : ℝ, min (readoutSlope ψ (-1)) (readoutSlope ψ 1) ≤ q ∧
      q ≤ max (readoutSlope ψ (-1)) (readoutSlope ψ 1) ∧ ψ a - ψ b = q * (a - b) := by
  have hslope (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
      min (readoutSlope ψ (-1)) (readoutSlope ψ 1) ≤ readoutSlope ψ x ∧
        readoutSlope ψ x ≤ max (readoutSlope ψ (-1)) (readoutSlope ψ 1) := by
    rcases hshape with hc | hc
    · have hm := hc.monotoneOn_derivWithin hd
      exact ⟨(min_le_left _ _).trans (hm (by norm_num) hx hx.1),
        (hm hx (by norm_num) hx.2).trans (le_max_right _ _)⟩
    · have hm := hc.antitoneOn_derivWithin hd
      exact ⟨(min_le_right _ _).trans (hm hx (by norm_num) hx.2),
        (hm (by norm_num) hx hx.1).trans (le_max_left _ _)⟩
  have step (x y : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1)
      (hxy : x < y) : ∃ q : ℝ, min (readoutSlope ψ (-1)) (readoutSlope ψ 1) ≤ q ∧
      q ≤ max (readoutSlope ψ (-1)) (readoutSlope ψ 1) ∧ ψ y - ψ x = q * (y - x) := by
    have hsub : Icc x y ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc hx.1 hy.2
    obtain ⟨c, hc, heq⟩ := exists_deriv_eq_slope ψ hxy
      (hd.continuousOn.mono hsub)
      (hd.mono (Ioo_subset_Icc_self.trans hsub))
    have hcs := hslope c (hsub ⟨hc.1.le, hc.2.le⟩)
    refine ⟨readoutSlope ψ c, hcs.1, hcs.2, ?_⟩
    dsimp [readoutSlope]
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds (lt_of_le_of_lt hx.1 hc.1)
      (lt_of_lt_of_le hc.2 hy.2))]
    exact ((eq_div_iff (sub_ne_zero.mpr (ne_of_gt hxy))).mp heq).symm
  rcases lt_trichotomy a b with hab | hab | hab
  · obtain ⟨q, hq1, hq2, heq⟩ := step a b ha hb hab
    exact ⟨q, hq1, hq2, by nlinarith only [heq]⟩
  · subst b
    exact ⟨readoutSlope ψ (-1), min_le_left _ _, le_max_left _ _, by simp⟩
  · exact step b a hb ha hab

lemma target_nonconstant_of_midpoint {K : ℕ} (hK : 2 ≤ K) (φ ψ : ℝ → ℝ)
    (hφ : φ (-1) + φ 1 ≠ 2 * φ 0) :
    Operational.NonconstantOn {xs | ValidInput K xs} (target K φ ψ) := by
  let xs : List ℝ := (-1) :: 1 :: List.replicate (K - 2) 0
  let ys : List ℝ := List.replicate K 0
  have hk : ((K - 2 : ℕ) : ℝ) + 2 = (K : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hK
  have hk0 : (K : ℝ) ≠ 0 := by
    have : K ≠ 0 := by omega
    exact_mod_cast this
  have hx : ValidInput K xs := by
    constructor
    · dsimp [xs]; simp only [List.length_replicate]; omega
    · intro t ht
      simp only [xs, List.mem_cons, List.mem_replicate] at ht
      rcases ht with rfl | rfl | ⟨_, rfl⟩ <;> norm_num [InSource]
  have hy : ValidInput K ys := by
    constructor
    · simp [ys]
    · intro t ht
      have ht0 : t = 0 := (List.mem_replicate.mp ht).2
      subst t
      norm_num [InSource]
  refine ⟨xs, hx, ys, hy, ?_⟩
  intro heq
  have hh : φ (-1) + φ 1 + ((K - 2 : ℕ) : ℝ) * φ 0 = (K : ℝ) * φ 0 := by
    have hmeanx : firstMoment xs = 0 := by simp [xs, firstMoment]
    have hmeany : firstMoment ys = 0 := by simp [ys, firstMoment]
    simp only [target, hmeanx, hmeany, zero_div] at heq
    have heq' : featureMoment φ xs / (K : ℝ) = featureMoment φ ys / (K : ℝ) := by
      linarith only [heq]
    have hmom := (div_left_inj' hk0).mp heq'
    simpa [xs, ys, featureMoment, List.sum_replicate, nsmul_eq_mul, add_assoc] using hmom
  apply hφ
  nlinarith only [hh, congrArg (fun z : ℝ => z * φ 0) hk]

/-- Strict curvature of the feature makes the general target nonconstant,
regardless of the mean readout. Two tuples with the same mean witness this. -/
theorem target_nonconstant_of_strict_feature {K : ℕ} (hK : 2 ≤ K) (φ ψ : ℝ → ℝ)
    (hφ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ) :
    Operational.NonconstantOn {xs | ValidInput K xs} (target K φ ψ) := by
  apply target_nonconstant_of_midpoint hK φ ψ
  rcases hφ with hc | hc
  · have hstrict := hc.2
    have hh := hstrict (x := (-1 : ℝ)) (by norm_num) (y := 1) (by norm_num)
      (by norm_num) (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    norm_num [smul_eq_mul] at hh
    intro heq
    nlinarith
  · have hstrict := hc.2
    have hh := hstrict (x := (-1 : ℝ)) (by norm_num) (y := 1) (by norm_num)
      (by norm_num) (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    norm_num [smul_eq_mul] at hh
    intro heq
    nlinarith

lemma coefficient_A_pos (e : Curve) (hD : 0 < det e.A e.B e.C) : 0 < e.A := by
  have ha : 0 ≤ e.A := by dsimp [Curve.A]; positivity
  have hb : 0 ≤ e.B := by dsimp [Curve.B]; positivity
  dsimp [det] at hD
  by_contra hn
  have haz : e.A = 0 := le_antisymm (le_of_not_gt hn) ha
  rw [haz, zero_mul] at hD
  nlinarith [sq_nonneg e.C]

lemma endpointDual_pos (e : Curve) (ψ : ℝ → ℝ)
    (hD : 0 < det e.A e.B e.C) : 0 < endpointDual e ψ := by
  exact lt_of_lt_of_le
    (dual_pos e.A e.B e.C (-readoutSlope ψ (-1)) 1 (coefficient_A_pos e hD) hD
      (Or.inr one_ne_zero)) (le_max_left _ _)

/-- Every valid pair of actual inputs obeys the endpoint-dual Gram bound.
The local feature is arbitrary; no injectivity or regularity is needed for it. -/
theorem general_separation_lower_bound (e : Curve) {K : ℕ} (hK : 0 < K)
    (φ ψ : ℝ → ℝ) (hD : 0 < det e.A e.B e.C)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ) :
    GeneralCollision.SeparationLowerBound K φ ψ (encoder e φ)
      ((K : ℝ) ^ 2 / endpointDual e ψ) := by
  intro xs ys hxs hys
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hk0 : (K : ℝ) ≠ 0 := ne_of_gt hk
  obtain ⟨q, hq1, hq2, heq⟩ := secant_slope_between_endpoints ψ hd hshape
    (firstMoment xs / (K : ℝ)) (firstMoment ys / (K : ℝ))
    (mean_in_source hK xs hxs) (mean_in_source hK ys hys)
  let x := firstMoment xs - firstMoment ys
  let y := featureMoment φ xs - featureMoment φ ys
  have hf : target K φ ψ xs - target K φ ψ ys = (y - q * x) / (K : ℝ) := by
    dsimp [target]
    calc
      _ = (featureMoment φ xs - featureMoment φ ys) / (K : ℝ) -
          (ψ (firstMoment xs / (K : ℝ)) - ψ (firstMoment ys / (K : ℝ))) := by ring
      _ = _ := by rw [heq]; dsimp [x, y]; ring
  have hcost : 0 ≤ form2 e.A e.B e.C x y :=
    form2_nonneg e.A e.B e.C (coefficient_A_pos e hD) hD x y
  have hdual := dual_endpoint_bound e hD (readoutSlope ψ (-1)) (readoutSlope ψ 1) q ⟨hq1, hq2⟩
  have hc := dual_cauchy e.A e.B e.C (-q) 1 x y hD
  have hm := mul_le_mul_of_nonneg_right hdual hcost
  have hs : (y - q * x) ^ 2 ≤ endpointDual e ψ * form2 e.A e.B e.C x y := by
    dsimp [endpointDual]
    nlinarith only [hc, hm]
  rw [hf, received_squaredDistance e φ xs ys hxs hys]
  change (K : ℝ) ^ 2 / endpointDual e ψ * ((y - q * x) / (K : ℝ)) ^ 2 ≤
    form2 e.A e.B e.C x y
  have halg : (K : ℝ) ^ 2 / endpointDual e ψ * ((y - q * x) / (K : ℝ)) ^ 2 =
      (y - q * x) ^ 2 / endpointDual e ψ := by field_simp
  rw [halg]
  exact (div_le_iff₀ (endpointDual_pos e ψ hD)).mpr (by nlinarith only [hs])

/-- The general endpoint expression is a lower bound for the actual operational
infimum, not merely for an independently defined matrix objective. -/
theorem general_operational_lower_bound (e : Curve) {K : ℕ} (hK : 0 < K)
    (φ ψ : ℝ → ℝ) (hD : 0 < det e.A e.B e.C)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (hn : Operational.NonconstantOn {xs | ValidInput K xs} (target K φ ψ)) :
    (K : ℝ) ^ 2 / endpointDual e ψ ≤ score K φ ψ e := by
  apply (Operational.le_score_iff hn
    (fun xs _ ys _ => squaredDistance_nonnegative
      (received (encoder e φ) xs) (received (encoder e φ) ys)) _).mpr
  intro xs hxs ys hys
  exact general_separation_lower_bound e hK φ ψ hD hd hshape xs ys hxs hys

/-- The general proposition's lower bound with nonconstancy discharged from
the paper's strict feature curvature, for every number of transmitters K ≥ 2. -/
theorem strict_feature_operational_lower_bound (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (φ ψ : ℝ → ℝ) (hD : 0 < det e.A e.B e.C)
    (hφ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hshape : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ) :
    (K : ℝ) ^ 2 / endpointDual e ψ ≤ score K φ ψ e :=
  general_operational_lower_bound e (by omega) φ ψ hD hd hshape
    (target_nonconstant_of_strict_feature hK φ ψ hφ)

open Filter Topology

/-- Differentiating an inequality along an actual admissible source path gives
the local Gram converse. The hypotheses are derivatives of its two moments,
not a postulated open attainable set. -/
theorem path_direction_bound_of_eventually (e : Curve) {K : ℕ} (hK : 0 < K)
    (φ ψ : ℝ → ℝ) (lam : ℝ)
    (p : ℝ → List ℝ)
    (hsep : ∀ᶠ t in 𝓝 (0 : ℝ), lam * (target K φ ψ (p t) - target K φ ψ (p 0)) ^ 2 ≤
      squaredDistance (received (encoder e φ) (p t)) (received (encoder e φ) (p 0)))
    (h0 : ValidInput K (p 0))
    (hvalid : ∀ᶠ t in 𝓝 (0 : ℝ), ValidInput K (p t))
    (x y q : ℝ)
    (hS : HasDerivAt (fun t => firstMoment (p t)) x 0)
    (hT : HasDerivAt (fun t => featureMoment φ (p t)) y 0)
    (hψ : HasDerivAt ψ q (firstMoment (p 0) / (K : ℝ))) :
    lam * (y - q * x) ^ 2 ≤ (K : ℝ) ^ 2 * form2 e.A e.B e.C x y := by
  have hk0 : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  have hF : HasDerivAt (fun t => target K φ ψ (p t))
      ((y - q * x) / (K : ℝ)) 0 := by
    convert (hT.div_const (K : ℝ)).sub (hψ.comp 0 (hS.div_const (K : ℝ))) using 1
    dsimp [target]
    ring
  have slope_limit (g : ℝ → ℝ) (v : ℝ) (hg : HasDerivAt g v 0) :
      Tendsto (fun t => (g t - g 0) / t) (𝓝[≠] (0 : ℝ)) (𝓝 v) := by
    convert hg.tendsto_slope_zero using 1
    ext t
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hSl := slope_limit _ _ hS
  have hTl := slope_limit _ _ hT
  have hFl := slope_limit _ _ hF
  have hleft := (hFl.pow 2).const_mul lam
  have hright : Tendsto (fun t => form2 e.A e.B e.C
      ((firstMoment (p t) - firstMoment (p 0)) / t)
      ((featureMoment φ (p t) - featureMoment φ (p 0)) / t))
      (𝓝[≠] (0 : ℝ)) (𝓝 (form2 e.A e.B e.C x y)) := by
    exact (((hSl.pow 2).const_mul e.A).add
      ((hSl.const_mul (2 * e.C)).mul hTl)).add ((hTl.pow 2).const_mul e.B)
  have hbound : lam * ((y - q * x) / (K : ℝ)) ^ 2 ≤ form2 e.A e.B e.C x y := by
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [hvalid.filter_mono nhdsWithin_le_nhds,
      hsep.filter_mono nhdsWithin_le_nhds] with t ht hbt
    have hh := div_le_div_of_nonneg_right hbt (sq_nonneg t)
    rw [received_squaredDistance e φ (p t) (p 0) ht h0] at hh
    convert hh using 1 <;> dsimp [form2] <;> ring
  have hh := mul_le_mul_of_nonneg_right hbound (sq_nonneg (K : ℝ))
  have halg : lam * ((y - q * x) / (K : ℝ)) ^ 2 * (K : ℝ) ^ 2 =
      lam * (y - q * x) ^ 2 := by field_simp
  rw [halg] at hh
  nlinarith only [hh]

/-- A global separation bound can be differentiated along each actual source path. -/
theorem separation_path_direction_bound (e : Curve) {K : ℕ} (hK : 0 < K)
    (φ ψ : ℝ → ℝ) (lam : ℝ)
    (hsep : GeneralCollision.SeparationLowerBound K φ ψ (encoder e φ) lam)
    (p : ℝ → List ℝ) (h0 : ValidInput K (p 0))
    (hvalid : ∀ᶠ t in 𝓝 (0 : ℝ), ValidInput K (p t))
    (x y q : ℝ)
    (hS : HasDerivAt (fun t => firstMoment (p t)) x 0)
    (hT : HasDerivAt (fun t => featureMoment φ (p t)) y 0)
    (hψ : HasDerivAt ψ q (firstMoment (p 0) / (K : ℝ))) :
    lam * (y - q * x) ^ 2 ≤ (K : ℝ) ^ 2 * form2 e.A e.B e.C x y := by
  apply path_direction_bound_of_eventually e hK φ ψ lam p _ h0 hvalid x y q hS hT hψ
  filter_upwards [hvalid] with t ht
  exact hsep (p t) (p 0) ht h0

/-- A separation bound restricted to sufficiently small received distances.
This uses the same actual source tuples and Euclidean squared channel distance. -/
def LocalSeparation (K : ℕ) (φ ψ : ℝ → ℝ) (e : Curve) (δ lam : ℝ) : Prop :=
  ∀ xs ys : List ℝ, ValidInput K xs → ValidInput K ys →
    squaredDistance (received (encoder e φ) xs) (received (encoder e φ) ys) < δ ^ 2 →
    lam * (target K φ ψ xs - target K φ ψ ys) ^ 2 ≤
      squaredDistance (received (encoder e φ) xs) (received (encoder e φ) ys)

/-- The same converse follows even when the pairwise bound is assumed only
inside an arbitrarily small received-distance neighborhood. -/
theorem local_separation_path_direction_bound (e : Curve) {K : ℕ} (hK : 0 < K)
    (φ ψ : ℝ → ℝ) (δ lam : ℝ) (hδ : 0 < δ)
    (hsep : LocalSeparation K φ ψ e δ lam)
    (p : ℝ → List ℝ) (h0 : ValidInput K (p 0))
    (hvalid : ∀ᶠ t in 𝓝 (0 : ℝ), ValidInput K (p t))
    (x y q : ℝ)
    (hS : HasDerivAt (fun t => firstMoment (p t)) x 0)
    (hT : HasDerivAt (fun t => featureMoment φ (p t)) y 0)
    (hψ : HasDerivAt ψ q (firstMoment (p 0) / (K : ℝ))) :
    lam * (y - q * x) ^ 2 ≤ (K : ℝ) ^ 2 * form2 e.A e.B e.C x y := by
  apply path_direction_bound_of_eventually e hK φ ψ lam p _ h0 hvalid x y q hS hT hψ
  have hSc := hS.continuousAt
  have hTc := hT.continuousAt
  have hc : ContinuousAt (fun t => form2 e.A e.B e.C
      (firstMoment (p t) - firstMoment (p 0))
      (featureMoment φ (p t) - featureMoment φ (p 0))) 0 := by
    unfold form2
    fun_prop
  have hc0 : Tendsto (fun t => form2 e.A e.B e.C
      (firstMoment (p t) - firstMoment (p 0))
      (featureMoment φ (p t) - featureMoment φ (p 0))) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa [form2] using hc.tendsto
  have hsmall := hc0.eventually (gt_mem_nhds (sq_pos_of_pos hδ))
  filter_upwards [hvalid, hsmall] with t ht hsmallt
  apply hsep (p t) (p 0) ht h0
  rw [received_squaredDistance e φ (p t) (p 0) ht h0]
  exact hsmallt

lemma readoutSlope_hasDerivAt (ψ : ℝ → ℝ)
    (hd : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (m : ℝ) (hm : m ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt ψ (readoutSlope ψ m) m := by
  exact ((hd m ⟨hm.1.le, hm.2.le⟩).hasDerivWithinAt).hasDerivAt
    (Icc_mem_nhds hm.1 hm.2)

/-- The local converse holds for every direction at every interior mean;
the source paths are explicitly constructed using only two moving inputs. -/
theorem local_separation_direction_bound (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (φ ψ : ℝ → ℝ) (δ lam : ℝ) (hδ : 0 < δ)
    (hsep : LocalSeparation K φ ψ e δ lam)
    (hφ : StrictConvexOn ℝ (Ioo (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Ioo (-1 : ℝ) 1) φ)
    (hdφ : ∀ z ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ φ z)
    (hdψ : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (m x y : ℝ) (hm : m ∈ Ioo (-1 : ℝ) 1) :
    lam * (y - readoutSlope ψ m * x) ^ 2 ≤
      (K : ℝ) ^ 2 * form2 e.A e.B e.C x y := by
  obtain ⟨p, hp0, hp, hmean, hS, hT⟩ :=
    MomentPaths.exists_source_path_at_mean hK φ hφ hdφ m x y hm
  have hk0 : (K : ℝ) ≠ 0 := by
    have : K ≠ 0 := by omega
    exact_mod_cast this
  have hψ : HasDerivAt ψ (readoutSlope ψ m) (firstMoment (p 0) / (K : ℝ)) := by
    rw [hmean, mul_div_cancel_left₀ m hk0]
    exact readoutSlope_hasDerivAt ψ hdψ m hm
  exact local_separation_path_direction_bound e (by omega) φ ψ δ lam hδ hsep
    p hp0 hp x y (readoutSlope ψ m) hS hT hψ

/-- Continuity of the one-sided endpoint slopes closes the interior directional
inequality at both consensus endpoints. -/
theorem local_separation_direction_bound_closed (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (φ ψ : ℝ → ℝ) (δ lam : ℝ) (hδ : 0 < δ)
    (hsep : LocalSeparation K φ ψ e δ lam)
    (hφ : StrictConvexOn ℝ (Ioo (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Ioo (-1 : ℝ) 1) φ)
    (hdφ : ∀ z ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ φ z)
    (hdψ : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hcψ : ContinuousOn (readoutSlope ψ) (Icc (-1 : ℝ) 1))
    (m x y : ℝ) (hm : m ∈ Icc (-1 : ℝ) 1) :
    lam * (y - readoutSlope ψ m * x) ^ 2 ≤
      (K : ℝ) ^ 2 * form2 e.A e.B e.C x y := by
  have hcl : m ∈ closure (Ioo (-1 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    exact hm
  apply le_on_closure
    (fun z hz => local_separation_direction_bound e hK φ ψ δ lam hδ hsep hφ hdφ hdψ z x y hz)
    (x := m) (s := Ioo (-1 : ℝ) 1) _ _ hcl
  · rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    exact (continuousOn_const.mul ((continuousOn_const.sub (hcψ.mul continuousOn_const)).pow 2))
  · exact continuousOn_const

/-- Every local pairwise lower bound is at most the endpoint-dual expression.
Thus restricting the received distance to any positive radius cannot improve
the sharp constant. -/
theorem local_separation_upper_bound (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (φ ψ : ℝ → ℝ) (δ lam : ℝ) (hδ : 0 < δ)
    (hsep : LocalSeparation K φ ψ e δ lam)
    (hD : 0 < det e.A e.B e.C)
    (hφ : StrictConvexOn ℝ (Ioo (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Ioo (-1 : ℝ) 1) φ)
    (hdφ : ∀ z ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ φ z)
    (hdψ : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hcψ : ContinuousOn (readoutSlope ψ) (Icc (-1 : ℝ) 1)) :
    lam ≤ (K : ℝ) ^ 2 / endpointDual e ψ := by
  have hpoint (m : ℝ) (hm : m ∈ Icc (-1 : ℝ) 1) :
      lam ≤ (K : ℝ) ^ 2 / dual e.A e.B e.C (-readoutSlope ψ m) 1 := by
    let q := readoutSlope ψ m
    let d := dual e.A e.B e.C (-q) 1
    have hd : 0 < d := dual_pos e.A e.B e.C (-q) 1
      (coefficient_A_pos e hD) hD (Or.inr one_ne_zero)
    have hh := local_separation_direction_bound_closed e hK φ ψ δ lam hδ hsep
      hφ hdφ hdψ hcψ m (invX e.A e.B e.C (-q) 1) (invY e.A e.B e.C (-q) 1) hm
    rw [form2_inverse e.A e.B e.C (-q) 1 (ne_of_gt hD)] at hh
    have he : invY e.A e.B e.C (-q) 1 - q * invX e.A e.B e.C (-q) 1 = d := by
      dsimp [d, dual]; ring
    change lam * (invY e.A e.B e.C (-q) 1 - q * invX e.A e.B e.C (-q) 1) ^ 2 ≤
      (K : ℝ) ^ 2 * d at hh
    rw [he] at hh
    have hm' : (lam * d) * d ≤ (K : ℝ) ^ 2 * d := by nlinarith only [hh]
    have hb := (mul_le_mul_iff_left₀ hd).mp hm'
    exact (le_div_iff₀ hd).mpr hb
  rcases le_total (dual e.A e.B e.C (-readoutSlope ψ (-1)) 1)
    (dual e.A e.B e.C (-readoutSlope ψ 1) 1) with hle | hge
  · rw [endpointDual, max_eq_right hle]
    exact hpoint 1 (by norm_num)
  · rw [endpointDual, max_eq_left hge]
    exact hpoint (-1) (by norm_num)

/-- The exact operational score for general strictly curved moment features
and convex or concave C¹ mean readouts, including one-sided endpoint slopes.
Both bounds refer to the infimum over actual valid input lists. -/
theorem general_operational_score (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (φ ψ : ℝ → ℝ) (hD : 0 < det e.A e.B e.C)
    (hφ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ)
    (hdφ : ∀ z ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ φ z)
    (hψ : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (hdψ : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hcψ : ContinuousOn (readoutSlope ψ) (Icc (-1 : ℝ) 1)) :
    score K φ ψ e = (K : ℝ) ^ 2 / endpointDual e ψ := by
  have hn := target_nonconstant_of_strict_feature hK φ ψ hφ
  apply le_antisymm
  · have hbound := Operational.score_is_lowerBound hn
      (fun xs _ ys _ => squaredDistance_nonnegative
        (received (encoder e φ) xs) (received (encoder e φ) ys))
    have hlocal : LocalSeparation K φ ψ e 1 (score K φ ψ e) := by
      intro xs ys hxs hys _
      exact hbound xs hxs ys hys
    apply local_separation_upper_bound e hK φ ψ 1 (score K φ ψ e) (by norm_num)
      hlocal hD _ hdφ hdψ hcψ
    rcases hφ with hφ | hφ
    · exact Or.inl (hφ.subset Ioo_subset_Icc_self (convex_Ioo (-1) 1))
    · exact Or.inr (hφ.subset Ioo_subset_Icc_self (convex_Ioo (-1) 1))
  · exact general_operational_lower_bound e (by omega) φ ψ hD hdψ hψ hn

/-- Arbitrarily short received-distance pairs approach the exact operational
score. Both the numerator and target difference are evaluated on actual valid
source tuples, not on potentially unattainable moment points. -/
theorem general_score_small_distance_sharpness (e : Curve) {K : ℕ} (hK : 2 ≤ K)
    (φ ψ : ℝ → ℝ) (hD : 0 < det e.A e.B e.C)
    (hφ : StrictConvexOn ℝ (Icc (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Icc (-1 : ℝ) 1) φ)
    (hdφ : ∀ z ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ φ z)
    (hψ : ConvexOn ℝ (Icc (-1 : ℝ) 1) ψ ∨ ConcaveOn ℝ (Icc (-1 : ℝ) 1) ψ)
    (hdψ : DifferentiableOn ℝ ψ (Icc (-1 : ℝ) 1))
    (hcψ : ContinuousOn (readoutSlope ψ) (Icc (-1 : ℝ) 1))
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ xs ys : List ℝ, ValidInput K xs ∧ ValidInput K ys ∧
      target K φ ψ xs ≠ target K φ ψ ys ∧
      squaredDistance (received (encoder e φ) xs) (received (encoder e φ) ys) < δ ^ 2 ∧
      squaredDistance (received (encoder e φ) xs) (received (encoder e φ) ys) /
        (target K φ ψ xs - target K φ ψ ys) ^ 2 < score K φ ψ e + ε := by
  by_contra hnone
  have hlocal : LocalSeparation K φ ψ e δ (score K φ ψ e + ε) := by
    intro xs ys hxs hys hsmall
    by_cases hsame : target K φ ψ xs = target K φ ψ ys
    · simpa only [hsame, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero] using
        squaredDistance_nonnegative (received (encoder e φ) xs) (received (encoder e φ) ys)
    · have hquot : score K φ ψ e + ε ≤
          squaredDistance (received (encoder e φ) xs) (received (encoder e φ) ys) /
            (target K φ ψ xs - target K φ ψ ys) ^ 2 := by
        by_contra hlt
        exact hnone ⟨xs, ys, hxs, hys, hsame, hsmall, lt_of_not_ge hlt⟩
      exact (le_div_iff₀ (sq_pos_of_ne_zero (sub_ne_zero.mpr hsame))).mp hquot
  have hφ' : StrictConvexOn ℝ (Ioo (-1 : ℝ) 1) φ ∨
      StrictConcaveOn ℝ (Ioo (-1 : ℝ) 1) φ := by
    rcases hφ with hφ | hφ
    · exact Or.inl (hφ.subset Ioo_subset_Icc_self (convex_Ioo (-1) 1))
    · exact Or.inr (hφ.subset Ioo_subset_Icc_self (convex_Ioo (-1) 1))
  have hb := local_separation_upper_bound e hK φ ψ δ (score K φ ψ e + ε)
    hδ hlocal hD hφ' hdφ hdψ hcψ
  rw [← general_operational_score e hK φ ψ hD hφ hdφ hψ hdψ hcψ] at hb
  linarith

end Analog.GeneralScore
