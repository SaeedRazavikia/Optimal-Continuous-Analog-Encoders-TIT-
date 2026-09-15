import Analog.PowerScaling
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.IntermediateValue

/-!
# The constrained quadratic frontier

The upper robustness root is constructed from the actual scalar separation
function. The supporting peak inequality supplies certificates against all
feasible planar quadratic curves.
-/

noncomputable section
open Set
namespace Analog.QuadraticFrontier
open Analog.GeneralQuadratic

/-- Separation of the canonical unit-power curve, continuously extended by
zero at b=2. -/
def separation (M b : ℝ) : ℝ := b^2*(2-b)/((M^2-1)*b+2)

lemma denominator_pos {M b : ℝ} (hM : 0 < M) (hb : 1 ≤ b) (hb2 : b ≤ 2) :
    0 < (M^2-1)*b+2 := by
  have hm := mul_pos (sq_pos_of_pos hM) (show 0 < b by linarith)
  nlinarith

lemma separation_continuousOn {M : ℝ} (hM : 0 < M) :
    ContinuousOn (separation M) (Icc 1 2) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro b hb
  exact ne_of_gt (denominator_pos hM hb.1 hb.2)

lemma separation_pos {M b : ℝ} (hM : 0 < M) (hb : 1 ≤ b) (hb2 : b < 2) :
    0 < separation M b := by
  exact div_pos (mul_pos (sq_pos_of_pos (by linarith)) (sub_pos.mpr hb2))
    (denominator_pos hM hb hb2.le)

lemma separation_two (M : ℝ) : separation M 2 = 0 := by simp [separation]

lemma separation_deriv {M b : ℝ} (hM : 0 < M) (hb : 1 ≤ b) (hb2 : b ≤ 2) :
    HasDerivAt (separation M)
      (2*b*((2-b)^2-M^2*b*(b-1))/((M^2-1)*b+2)^2) b := by
  have hd := ne_of_gt (denominator_pos hM hb hb2)
  have hn := ((hasDerivAt_id b).pow 2).mul ((hasDerivAt_const b 2).sub (hasDerivAt_id b))
  have hden := ((hasDerivAt_id b).const_mul (M^2-1)).add_const 2
  convert hn.div hden hd using 1
  simp only [id_eq,Pi.pow_apply,Pi.mul_apply,Pi.sub_apply,Nat.cast_ofNat]
  ring

lemma root_sign_above {M b : ℝ} (hM : 0 < M)
    (hb : optimalParameter M < b) (hb2 : b ≤ 2) :
    (2-b)^2-M^2*b*(b-1) < 0 := by
  have hp := optimalParameter_bounds M hM
  have hr := optimalParameter_root M hM
  have hprod : optimalParameter M*(optimalParameter M-1) < b*(b-1) := by
    nlinarith [mul_pos (sub_pos.mpr hb) (show 0 < b+optimalParameter M-1 by linarith)]
  have hm := mul_lt_mul_of_pos_left hprod (sq_pos_of_pos hM)
  have hs : (2-b)^2 < (2-optimalParameter M)^2 := by
    nlinarith [mul_pos (sub_pos.mpr hb) (show 0 < 4-b-optimalParameter M by linarith)]
  nlinarith

/-- The robustness curve is strictly decreasing on its full upper branch,
including the zero-separation endpoint. -/
theorem separation_strictAntiOn {M : ℝ} (hM : 0 < M) :
    StrictAntiOn (separation M) (Icc (optimalParameter M) 2) := by
  have hp := optimalParameter_bounds M hM
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    ((separation_continuousOn hM).mono (by intro b hb; exact ⟨hp.1.le.trans hb.1,hb.2⟩))
  intro b hb
  rw [interior_Icc] at hb
  obtain ⟨hblo,hbhi⟩ := hb
  rw [(separation_deriv hM (by linarith) hbhi.le).deriv]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (by linarith) (root_sign_above hM hblo hbhi.le))
    (sq_pos_of_pos (denominator_pos hM (by linarith) hbhi.le))

/-- Existence and uniqueness of the upper root follow from continuity and
strict decrease, including the convention b₊(0)=2. -/
theorem upper_root_exists_unique {M r : ℝ} (hM : 0 < M) (hr : 0 ≤ r)
    (hrmax : r ≤ separation M (optimalParameter M)) :
    ∃! b : ℝ, b ∈ Icc (optimalParameter M) 2 ∧ separation M b = r := by
  have hp := optimalParameter_bounds M hM
  have hc := (separation_continuousOn hM).mono
    (show Icc (optimalParameter M) (2 : ℝ) ⊆ Icc 1 2 from
      fun b hb => ⟨hp.1.le.trans hb.1,hb.2⟩)
  obtain ⟨b,hb,he⟩ := intermediate_value_Icc' hp.2.le hc
    (show r ∈ Icc (separation M 2) (separation M (optimalParameter M)) by
      rw [separation_two]; exact ⟨hr,hrmax⟩)
  refine ⟨b,⟨hb,he⟩,?_⟩
  intro c hc
  exact (separation_strictAntiOn hM).injOn hc.1 hb (hc.2.trans he.symm)

/-- The upper robustness root, with the paper's zero-floor convention. -/
def upperRoot (M r : ℝ) (hM : 0 < M) (hr : 0 ≤ r)
    (hrmax : r ≤ separation M (optimalParameter M)) : ℝ :=
  (upper_root_exists_unique hM hr hrmax).choose

lemma upperRoot_spec {M r : ℝ} (hM : 0 < M) (hr : 0 ≤ r)
    (hrmax : r ≤ separation M (optimalParameter M)) :
    upperRoot M r hM hr hrmax ∈ Icc (optimalParameter M) 2 ∧
      separation M (upperRoot M r hM hr hrmax) = r :=
  (upper_root_exists_unique hM hr hrmax).choose_spec.1

lemma upperRoot_zero {M : ℝ} (hM : 0 < M)
    (hmax : 0 ≤ separation M (optimalParameter M)) :
    upperRoot M 0 hM le_rfl hmax = 2 := by
  have hp := optimalParameter_bounds M hM
  have hs := upperRoot_spec hM le_rfl hmax
  exact (separation_strictAntiOn hM).injOn hs.1 ⟨hp.2.le,le_rfl⟩
    (hs.2.trans (separation_two M).symm)

/-- The robustness constraint on the upper branch is exactly an interval
ending at the constructed upper root. -/
theorem upper_branch_feasible_iff {M r b : ℝ} (hM : 0 < M) (hr : 0 ≤ r)
    (hrmax : r ≤ separation M (optimalParameter M))
    (hb : b ∈ Icc (optimalParameter M) 2) :
    r ≤ separation M b ↔ b ≤ upperRoot M r hM hr hrmax := by
  have hs := upperRoot_spec hM hr hrmax
  constructor
  · intro he
    by_contra hn
    have hh := separation_strictAntiOn hM hs.1 hb (lt_of_not_ge hn)
    rw [hs.2] at hh
    linarith
  · intro he
    have hh := (separation_strictAntiOn hM).antitoneOn hb hs.1 he
    rwa [hs.2] at hh

/-- The strict ordering of endpoint sensitivities reverses the ordering of
their stationary curve coefficients. -/
lemma stationary_root_order {x y b c : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hb : 1 < b) (hc : c < 2) (hbc : b ≤ c)
    (hrb : x^2*b*(b-1) = (2-b)^2)
    (hrc : y^2*c*(c-1) = (2-c)^2) : y ≤ x := by
  by_contra hn
  have hxy : x < y := lt_of_not_ge hn
  have hsq : x^2 < y^2 := by nlinarith
  have hprod : b*(b-1) ≤ c*(c-1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbc) (show 0 ≤ c+b-1 by linarith)]
  have hp := mul_lt_mul_of_pos_right hsq (mul_pos (by linarith : 0 < b) (by linarith : 0 < b-1))
  have hm := mul_le_mul_of_nonneg_left hprod (sq_nonneg y)
  have hnum : (2-c)^2 ≤ (2-b)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbc) (show 0 ≤ 4-c-b by linarith)]
  nlinarith

theorem optimalParameter_antitone {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    optimalParameter y < optimalParameter x := by
  have hy := hx.trans hxy
  have hbx := optimalParameter_bounds x hx
  have hby := optimalParameter_bounds y hy
  by_contra hn
  have hle := stationary_root_order hx hy hbx.1 hby.2 (le_of_not_gt hn)
    (optimalParameter_root x hx) (optimalParameter_root y hy)
  linarith

/-- Prior inverse-Gram cost, before the common factor 1/(2K²P). -/
def curveRisk (e : Curve) (x : ℝ) : ℝ :=
  (e.A+x^2*e.B)/(e.A*e.B-e.C^2)

lemma determinant_optimal {b : ℝ} (hb : 1 ≤ b) (hb2 : b < 2) :
    0 < (GeneralQuadratic.optimalCurve b).A*(GeneralQuadratic.optimalCurve b).B-(GeneralQuadratic.optimalCurve b).C^2 := by
  rw [GeneralQuadratic.optimal_A b (by linarith) hb2.le,GeneralQuadratic.optimal_B,GeneralQuadratic.optimal_C]
  simp only [zero_pow (by decide : 2 ≠ 0),sub_zero]
  exact mul_pos (mul_pos (by linarith) (by linarith)) (sq_pos_of_pos (by linarith))

lemma separation_eq_gramScore {M b : ℝ} (hM : 0 < M) (hb : 1 ≤ b) (hb2 : b < 2) :
    separation M b = gramScore (GeneralQuadratic.optimalCurve b) M := by
  unfold separation gramScore
  rw [GeneralQuadratic.optimal_A b (by linarith) hb2.le,GeneralQuadratic.optimal_B,GeneralQuadratic.optimal_C]
  simp only [zero_pow (by decide : 2 ≠ 0),sub_zero,abs_zero,mul_zero,add_zero]
  have hb0 : b ≠ 0 := by linarith
  have hd := ne_of_gt (denominator_pos hM hb hb2.le)
  field_simp
  ring

lemma optimalRisk_eq_reciprocal {M b : ℝ} (hM : 0 < M) (hb : 1 ≤ b) (hb2 : b < 2) :
    curveRisk (GeneralQuadratic.optimalCurve b) M = 1/separation M b := by
  rw [separation_eq_gramScore hM hb hb2]
  unfold curveRisk gramScore
  rw [GeneralQuadratic.optimal_C]
  simp

lemma curveRisk_eq_scalar {x b : ℝ} (hb : 1 ≤ b) (hb2 : b < 2) :
    curveRisk (GeneralQuadratic.optimalCurve b) x = x^2/(b*(2-b))+1/b^2 := by
  unfold curveRisk
  rw [GeneralQuadratic.optimal_A b (by linarith) hb2.le,GeneralQuadratic.optimal_B,GeneralQuadratic.optimal_C]
  simp only [zero_pow (by decide : 2 ≠ 0),sub_zero]
  have hb0 : b ≠ 0 := by linarith
  have hb20 : 2-b ≠ 0 := by linarith
  field_simp
  ring

/-- A sharp inverse-risk lower bound against every feasible planar quadratic
curve, obtained from the existing peak supporting inequality. -/
theorem curveRisk_lower_bound {e : Curve} (he : e.PeakFeasible)
    (hd : 0 < e.A*e.B-e.C^2) {x b : ℝ} (hx : 0 < x)
    (hb : 1 < b) (hb2 : b < 2)
    (hr : x^2*b*(b-1) = (2-b)^2) :
    curveRisk (GeneralQuadratic.optimalCurve b) x ≤ curveRisk e x := by
  rw [optimalRisk_eq_reciprocal hx hb.le hb2,
    separation_eq_gramScore hx hb.le hb2,GeneralQuadratic.optimal_score x b hx hb hb2 hr]
  have hp := GeneralQuadratic.product_bound e he x b hb hr
  have hc : 0 < b^2*(b-1) := mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
  unfold curveRisk
  apply (div_le_div_iff₀ hc hd).mpr
  nlinarith [sq_nonneg e.C]

lemma risk_mix (e : Curve) (x y t : ℝ) :
    (1-t)*curveRisk e x+t*curveRisk e y =
      (e.A+((1-t)*x^2+t*y^2)*e.B)/(e.A*e.B-e.C^2) := by
  unfold curveRisk
  ring

/-- A feasible robustness floor bounds the uncorrelated directional risk;
the omitted correlation term is nonnegative. -/
lemma risk_le_of_score {e : Curve} {M r : ℝ} (hM : 0 < M) (hr : 0 < r)
    (hd : 0 < e.A*e.B-e.C^2) (hs : r ≤ gramScore e M) :
    curveRisk e M ≤ 1/r := by
  have hA : 0 ≤ e.A := by dsimp [Curve.A]; positivity
  have hB : 0 ≤ e.B := by dsimp [Curve.B]; positivity
  have hAB : 0 < e.A+M^2*e.B := by
    have hAp : 0 < e.A := by nlinarith [sq_nonneg e.C]
    positivity
  have hc : 0 ≤ 2*M*|e.C| := by positivity
  have hden : 0 < e.A+M^2*e.B+2*M*|e.C| := by linarith
  have hs' := (le_div_iff₀ hden).mp hs
  have hw := mul_nonneg hr.le hc
  unfold curveRisk
  apply (div_le_div_iff₀ hd hr).mpr
  nlinarith

/-- A scalar coefficient determines its unique positive stationary slope. -/
def stationarySlope (b : ℝ) : ℝ := Real.sqrt ((2-b)^2/(b*(b-1)))

lemma stationarySlope_spec {b : ℝ} (hb : 1 < b) (hb2 : b < 2) :
    0 < stationarySlope b ∧ (stationarySlope b)^2*b*(b-1) = (2-b)^2 := by
  have hd : 0 < b*(b-1) := mul_pos (by linarith) (by linarith)
  have hn : 0 < (2-b)^2 := sq_pos_of_pos (by linarith)
  refine ⟨Real.sqrt_pos.mpr (div_pos hn hd), ?_⟩
  unfold stationarySlope
  rw [Real.sq_sqrt (div_pos hn hd).le]
  have he := div_mul_cancel₀ ((2-b)^2) (ne_of_gt hd)
  nlinarith only [he]

/-- A weighted sharp supporting certificate proves global optimality of
an active upper-branch coefficient. -/
theorem active_coefficient_optimal {e : Curve} (he : e.PeakFeasible)
    (hd : 0 < e.A*e.B-e.C^2) {m M b : ℝ} (hm : 0 < m) (hmM : m < M)
    (hbM : optimalParameter M < b) (hbm : b ≤ optimalParameter m)
    (hs : separation M b ≤ gramScore e M) :
    curveRisk (GeneralQuadratic.optimalCurve b) m ≤ curveRisk e m := by
  have hM := hm.trans hmM
  have hbp := optimalParameter_bounds M hM
  have hmp := optimalParameter_bounds m hm
  have hb : 1 < b := hbp.1.trans hbM
  have hb2 : b < 2 := hbm.trans_lt hmp.2
  let x := stationarySlope b
  have hx := stationarySlope_spec hb hb2
  have hmx : m ≤ x := stationary_root_order hx.1 hm hb hmp.2 hbm hx.2
    (optimalParameter_root m hm)
  have hxM : x < M := by
    have hsign := root_sign_above hM hbM hb2.le
    have hden : 0 < b*(b-1) := mul_pos (by linarith) (by linarith)
    have hxroot := hx.2
    change x^2*b*(b-1) = (2-b)^2 at hxroot
    by_contra hn
    have hsquares : M^2 ≤ x^2 := by nlinarith [hx.1]
    have hh := mul_le_mul_of_nonneg_right hsquares hden.le
    nlinarith
  let t := (x^2-m^2)/(M^2-m^2)
  have hden : 0 < M^2-m^2 := by nlinarith
  have ht : 0 ≤ t := div_nonneg (by nlinarith [hx.1]) hden.le
  have ht1 : t < 1 := (div_lt_one hden).mpr (by nlinarith [hx.1])
  have htiden : t*(M^2-m^2) = x^2-m^2 := div_mul_cancel₀ _ (ne_of_gt hden)
  have hmix : (1-t)*m^2+t*M^2 = x^2 := by nlinarith
  have hlo := curveRisk_lower_bound he hd hx.1 hb hb2 hx.2
  have hrob := risk_le_of_score hM (separation_pos hM hb.le hb2) hd hs
  rw [← optimalRisk_eq_reciprocal hM hb.le hb2] at hrob
  have hwe := risk_mix e m M t
  have hwo := risk_mix (GeneralQuadratic.optimalCurve b) m M t
  rw [hmix] at hwe hwo
  change (1-t)*curveRisk e m+t*curveRisk e M = curveRisk e x at hwe
  change (1-t)*curveRisk (GeneralQuadratic.optimalCurve b) m+
    t*curveRisk (GeneralQuadratic.optimalCurve b) M =
      curveRisk (GeneralQuadratic.optimalCurve b) x at hwo
  have hw := mul_le_mul_of_nonneg_left hrob ht
  nlinarith

/-- At the maximum robustness floor, the supporting identity forces the
unique lower Gram coefficients, including zero correlation. -/
theorem maximal_score_unique_coefficients {e : Curve} (he : e.PeakFeasible)
    (hd : 0 < e.A*e.B-e.C^2) {M b : ℝ} (hM : 0 < M)
    (hb : 1 < b) (hb2 : b < 2) (hr : M^2*b*(b-1) = (2-b)^2)
    (hs : b^2*(b-1) ≤ gramScore e M) :
    e.A = b*(2-b) ∧ e.B = b^2 ∧ e.C = 0 := by
  have hA : 0 ≤ e.A := by dsimp [Curve.A]; positivity
  have hB : 0 ≤ e.B := by dsimp [Curve.B]; positivity
  have hAp : 0 < e.A := by nlinarith [sq_nonneg e.C]
  have hBp : 0 < e.B := by nlinarith [sq_nonneg e.C]
  have hsum : 0 < e.A+M^2*e.B := by positivity
  have hcorr : 0 ≤ 2*M*|e.C| := by positivity
  have hden : 0 < e.A+M^2*e.B+2*M*|e.C| := by linarith
  have hc : 0 < b^2*(b-1) := mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
  have hs' := (le_div_iff₀ hden).mp hs
  have hp := GeneralQuadratic.product_bound e he M b hb hr
  have hw := mul_nonneg hc.le hcorr
  have hC : e.C = 0 := by nlinarith [sq_nonneg e.C]
  have hab : e.A*e.B = b^2*(b-1)*(e.A+M^2*e.B) := by nlinarith
  have hsupport := GeneralQuadratic.supporting_bound e he b hb.le
  have hi := GeneralQuadratic.sos_identity M b e.A e.B hr
  have hweight : 0 < b*(b-1)*(e.A+M^2*e.B) :=
    mul_pos (mul_pos (by linarith) (by linarith)) hsum
  have hsupp := mul_le_mul_of_nonneg_left hsupport hweight.le
  have heq : b*e.A-(2-b)*e.B = 0 := by
    have hcalc : (b*(b-1)*(e.A+M^2*e.B))*b^2 = b*(e.A*e.B) := by
      rw [hab]
      ring
    rw [hcalc] at hsupp
    have hprod : (b-1)*(b*e.A-(2-b)*e.B)^2 ≤ 0 := by linarith only [hi,hsupp]
    have hsq := sq_nonneg (b*e.A-(2-b)*e.B)
    have hbsub : 0 < b-1 := by linarith
    have hz : (b*e.A-(2-b)*e.B)^2 = 0 := by nlinarith only [hsq,hprod,hbsub]
    exact sq_eq_zero_iff.mp hz
  have hsupporteq : b*e.A+(b-1)*e.B = b^2 := by
    rw [heq,zero_pow (by decide : 2 ≠ 0),mul_zero] at hi
    have hzero : (b*(b-1)*(e.A+M^2*e.B))*(b*e.A+(b-1)*e.B-b^2) = 0 := by
      calc
        _ = b*(b-1)*(e.A+M^2*e.B)*(b*e.A+(b-1)*e.B)-b*(e.A*e.B) := by
          rw [hab]
          ring
        _ = 0 := by simpa only [mul_assoc] using hi
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (ne_of_gt hweight))
  have heB : e.B = b^2 := by nlinarith [heq,hsupporteq]
  have heA : e.A = b*(2-b) := by
    rw [heB] at heq
    have hx : b*(e.A-b*(2-b)) = 0 := by nlinarith only [heq]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left (by linarith))
  exact ⟨heA,heB,hC⟩

/-- The upper-root equation is exactly the cubic printed in the paper. -/
lemma separation_eq_iff_cubic {M b r : ℝ} (hM : 0 < M)
    (hb : 1 ≤ b) (hb2 : b ≤ 2) :
    separation M b = r ↔ b^3-2*b^2+r*(M^2-1)*b+2*r = 0 := by
  unfold separation
  rw [div_eq_iff (ne_of_gt (denominator_pos hM hb hb2))]
  constructor <;> intro h <;> nlinarith only [h]

/-- The selected coefficient is precisely the prior-optimal coefficient
clipped at the uniquely constructed upper robustness root. -/
def clippedParameter (m M r : ℝ) (hM : 0 < M) (hr : 0 ≤ r)
    (hrmax : r ≤ separation M (optimalParameter M)) : ℝ :=
  min (optimalParameter m) (upperRoot M r hM hr hrmax)

lemma clippedParameter_bounds {m M r : ℝ} (hm : 0 < m) (hmM : m < M)
    (hr : 0 ≤ r) (hrmax : r ≤ separation M (optimalParameter M)) :
    optimalParameter M ≤ clippedParameter m M r (hm.trans hmM) hr hrmax ∧
      clippedParameter m M r (hm.trans hmM) hr hrmax ≤ optimalParameter m ∧
      clippedParameter m M r (hm.trans hmM) hr hrmax < 2 := by
  have hs := upperRoot_spec (hm.trans hmM) hr hrmax
  have hb := optimalParameter_antitone hm hmM
  have hmp := optimalParameter_bounds m hm
  unfold clippedParameter
  exact ⟨le_min hb.le hs.1.1,min_le_left _ _,(min_le_left _ _).trans_lt hmp.2⟩

/-- The clipping threshold is the actual robustness of the unconstrained
prior-optimal coefficient. -/
theorem clippedParameter_plateau_iff {m M r : ℝ} (hm : 0 < m) (hmM : m < M)
    (hr : 0 ≤ r) (hrmax : r ≤ separation M (optimalParameter M)) :
    clippedParameter m M r (hm.trans hmM) hr hrmax = optimalParameter m ↔
      r ≤ separation M (optimalParameter m) := by
  have hb := optimalParameter_antitone hm hmM
  have hmp := optimalParameter_bounds m hm
  rw [upper_branch_feasible_iff (hm.trans hmM) hr hrmax ⟨hb.le,hmp.2.le⟩]
  exact min_eq_left_iff

/-- Unit-power constrained quadratic optimization over every peak-feasible
positive-definite planar quadratic curve. The upper root, clipping choice,
feasibility and global risk comparison are derived; no argmin or feasible
interval is assumed. -/
theorem clipped_curve_optimal {m M r : ℝ} (hm : 0 < m) (hmM : m < M)
    (hr : 0 ≤ r) (hrmax : r ≤ separation M (optimalParameter M)) :
    let b := clippedParameter m M r (hm.trans hmM) hr hrmax
    1 < b ∧ b < 2 ∧
      (GeneralQuadratic.optimalCurve b).PeakFeasible ∧
      r ≤ gramScore (GeneralQuadratic.optimalCurve b) M ∧
      curveRisk (GeneralQuadratic.optimalCurve b) m = m^2/(b*(2-b))+1/b^2 ∧
      ∀ e : Curve, e.PeakFeasible → 0 < e.A*e.B-e.C^2 → r ≤ gramScore e M →
        curveRisk (GeneralQuadratic.optimalCurve b) m ≤ curveRisk e m := by
  let b := clippedParameter m M r (hm.trans hmM) hr hrmax
  have hM := hm.trans hmM
  have hp := optimalParameter_bounds M hM
  have hb := clippedParameter_bounds hm hmM hr hrmax
  change optimalParameter M ≤ b ∧ b ≤ optimalParameter m ∧ b < 2 at hb
  have hb1 : 1 < b := hp.1.trans_le hb.1
  have hu := upperRoot_spec hM hr hrmax
  have hble : b ≤ upperRoot M r hM hr hrmax := min_le_right _ _
  have hfeas := (upper_branch_feasible_iff hM hr hrmax ⟨hb.1,hb.2.2.le⟩).mpr hble
  refine ⟨hb1,hb.2.2,GeneralQuadratic.optimal_peak b (by linarith) hb.2.2.le,?_,
    curveRisk_eq_scalar hb1.le hb.2.2,?_⟩
  · rwa [separation_eq_gramScore hM hb1.le hb.2.2] at hfeas
  intro e he hd hs
  change curveRisk (GeneralQuadratic.optimalCurve b) m ≤ curveRisk e m
  by_cases hinactive : optimalParameter m ≤ upperRoot M r hM hr hrmax
  · have hbeq : b = optimalParameter m := min_eq_left hinactive
    rw [hbeq]
    have hmp := optimalParameter_bounds m hm
    exact curveRisk_lower_bound he hd hm hmp.1 hmp.2 (optimalParameter_root m hm)
  · have hbeq : b = upperRoot M r hM hr hrmax := min_eq_right (le_of_not_ge hinactive)
    have hactive : separation M b = r := hbeq ▸ hu.2
    by_cases hfull : b = optimalParameter M
    · have hopt := GeneralQuadratic.optimal_score M (optimalParameter M) hM hp.1 hp.2
        (optimalParameter_root M hM)
      have hscore : (optimalParameter M)^2*(optimalParameter M-1) ≤ gramScore e M := by
        rw [hfull,separation_eq_gramScore hM hp.1.le hp.2,hopt] at hactive
        simpa only [← hactive] using hs
      obtain ⟨hA,hB,hC⟩ := maximal_score_unique_coefficients he hd hM hp.1 hp.2
        (optimalParameter_root M hM) hscore
      rw [hfull]
      unfold curveRisk
      rw [hA,hB,hC,GeneralQuadratic.optimal_A (optimalParameter M) (by linarith) hp.2.le,
        GeneralQuadratic.optimal_B,GeneralQuadratic.optimal_C]
    · exact active_coefficient_optimal he hd hm hmM
        (lt_of_le_of_ne hb.1 (Ne.symm hfull)) hb.2.1 (hactive.trans_le hs)

lemma curveRisk_scale (e : Curve) (x a : ℝ) (ha : a ≠ 0) :
    curveRisk (e.scale a) x = curveRisk e x / a^2 := by
  unfold curveRisk
  rw [Curve.scale_A,Curve.scale_B,Curve.scale_C]
  have hn : a^2*e.A+x^2*(a^2*e.B) = a^2*(e.A+x^2*e.B) := by ring
  have hd : a^2*e.A*(a^2*e.B)-(a^2*e.C)^2 =
    a^2*(a^2*(e.A*e.B-e.C^2)) := by ring
  rw [hn,hd,mul_div_mul_left _ _ (pow_ne_zero 2 ha)]
  rw [div_mul_eq_div_div]
  ring

lemma determinant_scale (e : Curve) (a : ℝ) :
    (e.scale a).A*(e.scale a).B-(e.scale a).C^2 =
      a^4*(e.A*e.B-e.C^2) := by
  rw [Curve.scale_A,Curve.scale_B,Curve.scale_C]
  ring

/-- The clipped solution remains globally optimal at every positive power,
with exactly the scaling and risk expression in the manuscript. -/
theorem clipped_curve_optimal_all_power {m M P γ : ℝ}
    (hm : 0 < m) (hmM : m < M) (hP : 0 < P) (hγ : 0 ≤ γ)
    (hγmax : γ ≤ P*separation M (optimalParameter M)) :
    let r := γ/P
    let b := clippedParameter m M r (hm.trans hmM)
      (div_nonneg hγ hP.le) ((div_le_iff₀ hP).mpr (by nlinarith))
    let e := (GeneralQuadratic.optimalCurve b).scale (Real.sqrt P)
    e.PeakFeasibleAt P ∧ γ ≤ gramScore e M ∧
      curveRisk e m = (m^2/(b*(2-b))+1/b^2)/P ∧
      ∀ other : Curve, other.PeakFeasibleAt P →
        0 < other.A*other.B-other.C^2 → γ ≤ gramScore other M →
        curveRisk e m ≤ curveRisk other m := by
  dsimp only
  have hr : 0 ≤ γ/P := div_nonneg hγ hP.le
  have hrmax : γ/P ≤ separation M (optimalParameter M) :=
    (div_le_iff₀ hP).mpr (by nlinarith)
  let b := clippedParameter m M (γ/P) (hm.trans hmM) hr hrmax
  have hbase := clipped_curve_optimal hm hmM hr hrmax
  change 1 < b ∧ b < 2 ∧ _ at hbase
  have hs : Real.sqrt P ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hP)
  have hs2 := Real.sq_sqrt hP.le
  have hi2 : (1/Real.sqrt P)^2 = 1/P := by rw [div_pow,one_pow,hs2]
  have hpeak := (GeneralQuadratic.optimalCurve b).scale_peak (Real.sqrt P) 1 hbase.2.2.1
  simp only [hs2,mul_one] at hpeak
  refine ⟨hpeak, ?_, ?_, ?_⟩
  · rw [Curve.scale_gramScore,hs2]
    exact (div_le_iff₀ hP).mp hbase.2.2.2.1 |>.trans_eq (mul_comm _ _)
  · rw [curveRisk_scale _ _ _ hs,hs2]
    rw [hbase.2.2.2.2.1]
  · intro other hother hd hscore
    have hnorm := other.normalize_peak hP hother
    have hnD : 0 < (other.scale (1/Real.sqrt P)).A*(other.scale (1/Real.sqrt P)).B-
        (other.scale (1/Real.sqrt P)).C^2 := by
      rw [determinant_scale]
      exact mul_pos (pow_pos (one_div_pos.mpr (Real.sqrt_pos.mpr hP)) 4) hd
    have hnscore : γ/P ≤ gramScore (other.scale (1/Real.sqrt P)) M := by
      rw [Curve.scale_gramScore,hi2,one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right hscore hP.le
    have hopt := hbase.2.2.2.2.2 _ hnorm hnD hnscore
    rw [curveRisk_scale _ _ _ (one_div_ne_zero hs),hi2,div_div_eq_mul_div,div_one] at hopt
    have ho := div_le_div_of_nonneg_right hopt hP.le
    rw [mul_div_cancel_right₀ _ hP.ne'] at ho
    rw [curveRisk_scale _ _ _ hs,hs2]
    exact ho

end Analog.QuadraticFrontier
