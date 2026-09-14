import Analog.Certificate
import Mathlib.Data.Real.Sqrt

/-!
# Gram reduction and planar reconstruction

We use real coordinates for symmetric quadratic forms. Positive semidefiniteness
means nonnegativity at every real vector, rather than an assumed Schur-complement
condition. This module proves the algebraic synthesis bridge; it does not assert
compactness of the feasible design set or continuous-encoder rigidity.
-/

noncomputable section

namespace Analog.GramSynthesis

/-- The determinant of the lower-right two-dimensional Gram block. -/
def det (A B C : ℝ) : ℝ := A * B - C ^ 2

def form2 (A B C x y : ℝ) : ℝ := A * x ^ 2 + 2 * C * x * y + B * y ^ 2

def form3 (h l₁ l₂ A B C t x y : ℝ) : ℝ :=
  h * t ^ 2 + 2 * t * (l₁ * x + l₂ * y) + form2 A B C x y

def PSD3 (h l₁ l₂ A B C : ℝ) : Prop :=
  ∀ t x y : ℝ, 0 ≤ form3 h l₁ l₂ A B C t x y

def invX (A B C w₁ w₂ : ℝ) : ℝ := (B * w₁ - C * w₂) / det A B C

def invY (A B C w₁ w₂ : ℝ) : ℝ := (A * w₂ - C * w₁) / det A B C

/-- The quadratic form wᵀG⁻¹w. -/
def dual (A B C w₁ w₂ : ℝ) : ℝ :=
  w₁ * invX A B C w₁ w₂ + w₂ * invY A B C w₁ w₂

lemma inverse_equations (A B C w₁ w₂ : ℝ) (hD : det A B C ≠ 0) :
    A * invX A B C w₁ w₂ + C * invY A B C w₁ w₂ = w₁ ∧
    C * invX A B C w₁ w₂ + B * invY A B C w₁ w₂ = w₂ := by
  dsimp [invX, invY]
  constructor <;> field_simp <;> dsimp [det] <;> ring

lemma dual_formula (A B C w₁ w₂ : ℝ) :
    dual A B C w₁ w₂ =
      (B * w₁ ^ 2 - 2 * C * w₁ * w₂ + A * w₂ ^ 2) / det A B C := by
  dsimp [dual, invX, invY]
  ring

lemma form2_inverse (A B C w₁ w₂ : ℝ) (hD : det A B C ≠ 0) :
    form2 A B C (invX A B C w₁ w₂) (invY A B C w₁ w₂) =
      dual A B C w₁ w₂ := by
  have he := inverse_equations A B C w₁ w₂ hD
  calc
    _ = invX A B C w₁ w₂ *
          (A * invX A B C w₁ w₂ + C * invY A B C w₁ w₂) +
        invY A B C w₁ w₂ *
          (C * invX A B C w₁ w₂ + B * invY A B C w₁ w₂) := by
            dsimp [form2]; ring
    _ = dual A B C w₁ w₂ := by rw [he.1, he.2]; dsimp [dual]; ring

lemma form2_scaled (A B C x y : ℝ) :
    A * form2 A B C x y = (A * x + C * y) ^ 2 + det A B C * y ^ 2 := by
  dsimp [form2, det]; ring

lemma form2_nonneg (A B C : ℝ) (hA : 0 < A) (hD : 0 < det A B C)
    (x y : ℝ) : 0 ≤ form2 A B C x y := by
  have he := form2_scaled A B C x y
  have hn := mul_nonneg hD.le (sq_nonneg y)
  nlinarith [sq_nonneg (A * x + C * y)]

lemma form2_pos (A B C : ℝ) (hA : 0 < A) (hD : 0 < det A B C)
    (x y : ℝ) (hxy : x ≠ 0 ∨ y ≠ 0) : 0 < form2 A B C x y := by
  have he := form2_scaled A B C x y
  by_cases hy : y = 0
  · have hx : x ≠ 0 := hxy.resolve_right (not_not_intro hy)
    have hx2 := sq_pos_of_ne_zero hx
    subst y
    simpa [form2] using mul_pos hA hx2
  · have hy2 := sq_pos_of_ne_zero hy
    have hprod := mul_pos hD hy2
    nlinarith [sq_nonneg (A * x + C * y)]

lemma dual_pos (A B C w₁ w₂ : ℝ) (hA : 0 < A) (hD : 0 < det A B C)
    (hw : w₁ ≠ 0 ∨ w₂ ≠ 0) : 0 < dual A B C w₁ w₂ := by
  have he := inverse_equations A B C w₁ w₂ (ne_of_gt hD)
  have hi : invX A B C w₁ w₂ ≠ 0 ∨ invY A B C w₁ w₂ ≠ 0 := by
    by_contra hn
    push_neg at hn
    rw [hn.1, hn.2] at he
    simp only [mul_zero, zero_add] at he
    rcases hw with hw | hw
    · exact hw he.1.symm
    · exact hw he.2.symm
  rw [← form2_inverse A B C w₁ w₂ (ne_of_gt hD)]
  exact form2_pos A B C hA hD _ _ hi

/-- Completing the square is an identity, derived from the inverse equations. -/
lemma schur_identity (h l₁ l₂ A B C t x y : ℝ) (hD : det A B C ≠ 0) :
    form3 h l₁ l₂ A B C t x y =
      (h - dual A B C l₁ l₂) * t ^ 2 +
      form2 A B C (x + t * invX A B C l₁ l₂) (y + t * invY A B C l₁ l₂) := by
  have he := inverse_equations A B C l₁ l₂ hD
  have hf := form2_inverse A B C l₁ l₂ hD
  have hexpand :
      form2 A B C (x + t * invX A B C l₁ l₂) (y + t * invY A B C l₁ l₂) =
      form2 A B C x y +
        2 * t * ((A * invX A B C l₁ l₂ + C * invY A B C l₁ l₂) * x +
          (C * invX A B C l₁ l₂ + B * invY A B C l₁ l₂) * y) +
        t ^ 2 * form2 A B C (invX A B C l₁ l₂) (invY A B C l₁ l₂) := by
    dsimp [form2]; ring
  rw [hexpand, he.1, he.2, hf]
  dsimp [form3]; ring

/-- The Schur-complement criterion for an arbitrary symmetric three-dimensional
quadratic form with a positive-definite lower-right block. -/
theorem psd3_iff_schur (h l₁ l₂ A B C : ℝ)
    (hA : 0 < A) (hD : 0 < det A B C) :
    PSD3 h l₁ l₂ A B C ↔ dual A B C l₁ l₂ ≤ h := by
  constructor
  · intro hpsd
    have htest := hpsd 1 (-invX A B C l₁ l₂) (-invY A B C l₁ l₂)
    rw [schur_identity _ _ _ _ _ _ _ _ _ (ne_of_gt hD)] at htest
    simp only [one_mul, neg_add_cancel, one_pow, mul_one, form2,
      zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at htest
    linarith
  · intro h t x y
    rw [schur_identity _ _ _ _ _ _ _ _ _ (ne_of_gt hD)]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr h) (sq_nonneg t))
      (form2_nonneg A B C hA hD _ _)

/-- Lowering the leading Gram entry to the Schur value preserves genuine PSD
and decreases the full quadratic form at every vector. -/
theorem schur_reduction (h l₁ l₂ A B C : ℝ)
    (hA : 0 < A) (hD : 0 < det A B C) (hpsd : PSD3 h l₁ l₂ A B C) :
    PSD3 (dual A B C l₁ l₂) l₁ l₂ A B C ∧
      ∀ t x y : ℝ,
        form3 (dual A B C l₁ l₂) l₁ l₂ A B C t x y ≤ form3 h l₁ l₂ A B C t x y := by
  have hs := (psd3_iff_schur h l₁ l₂ A B C hA hD).1 hpsd
  constructor
  · exact (psd3_iff_schur _ l₁ l₂ A B C hA hD).2 le_rfl
  · intro t x y
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg t)
    dsimp [form3]
    linarith

/-- The reduced Gram matrix preserves every continuum peak constraint. -/
theorem peak_reduction (h l₁ l₂ A B C P : ℝ) (φ : ℝ → ℝ)
    (hA : 0 < A) (hD : 0 < det A B C) (hpsd : PSD3 h l₁ l₂ A B C)
    (hpeak : ∀ s : ℝ, -1 ≤ s → s ≤ 1 → form3 h l₁ l₂ A B C 1 s (φ s) ≤ P) :
    ∀ s : ℝ, -1 ≤ s → s ≤ 1 →
      form3 (dual A B C l₁ l₂) l₁ l₂ A B C 1 s (φ s) ≤ P := by
  intro s hlo hhi
  exact le_trans ((schur_reduction h l₁ l₂ A B C hA hD hpsd).2 1 s (φ s))
    (hpeak s hlo hhi)

/-- Three vectors c,u,v in the real plane. -/
structure Planar where
  cx : ℝ
  cy : ℝ
  ux : ℝ
  uy : ℝ
  vx : ℝ
  vy : ℝ

def Planar.h (e : Planar) : ℝ := e.cx ^ 2 + e.cy ^ 2
def Planar.l₁ (e : Planar) : ℝ := e.cx * e.ux + e.cy * e.uy
def Planar.l₂ (e : Planar) : ℝ := e.cx * e.vx + e.cy * e.vy
def Planar.A (e : Planar) : ℝ := e.ux ^ 2 + e.uy ^ 2
def Planar.B (e : Planar) : ℝ := e.vx ^ 2 + e.vy ^ 2
def Planar.C (e : Planar) : ℝ := e.ux * e.vx + e.uy * e.vy

def Planar.energy (e : Planar) (t x y : ℝ) : ℝ :=
  (t * e.cx + x * e.ux + y * e.vx) ^ 2 +
    (t * e.cy + x * e.uy + y * e.vy) ^ 2

lemma Planar.energy_eq_form3 (e : Planar) (t x y : ℝ) :
    e.energy t x y = form3 e.h e.l₁ e.l₂ e.A e.B e.C t x y := by
  dsimp [Planar.energy, Planar.h, Planar.l₁, Planar.l₂,
    Planar.A, Planar.B, Planar.C, form3, form2]
  ring

theorem Planar.gram_psd (e : Planar) : PSD3 e.h e.l₁ e.l₂ e.A e.B e.C := by
  intro t x y
  rw [← e.energy_eq_form3]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Explicit Cholesky reconstruction. Its columns are u=(√A,0),
v=(C/√A,√det/√A), and c=G⁻¹ℓ expressed in that basis. -/
def reconstruct (A B C l₁ l₂ : ℝ) : Planar where
  cx := invX A B C l₁ l₂ * Real.sqrt A + invY A B C l₁ l₂ * (C / Real.sqrt A)
  cy := invY A B C l₁ l₂ * (Real.sqrt (det A B C) / Real.sqrt A)
  ux := Real.sqrt A
  uy := 0
  vx := C / Real.sqrt A
  vy := Real.sqrt (det A B C) / Real.sqrt A

lemma reconstruct_lower_gram (A B C l₁ l₂ : ℝ)
    (hA : 0 < A) (hD : 0 < det A B C) :
    (reconstruct A B C l₁ l₂).A = A ∧
    (reconstruct A B C l₁ l₂).B = B ∧
    (reconstruct A B C l₁ l₂).C = C := by
  have hs : Real.sqrt A ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hA)
  refine ⟨?_, ?_, ?_⟩
  · simp [Planar.A, reconstruct, Real.sq_sqrt hA.le]
  · dsimp [Planar.B, reconstruct]
    rw [div_pow, div_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hD.le]
    field_simp
    dsimp [det]
    ring
  · dsimp [Planar.C, reconstruct]
    field_simp
    ring

/-- Every reduced block Gram form has the stated explicit realization in ℝ². -/
theorem reconstruct_gram (A B C l₁ l₂ : ℝ)
    (hA : 0 < A) (hD : 0 < det A B C) :
    (reconstruct A B C l₁ l₂).h = dual A B C l₁ l₂ ∧
    (reconstruct A B C l₁ l₂).l₁ = l₁ ∧
    (reconstruct A B C l₁ l₂).l₂ = l₂ ∧
    (reconstruct A B C l₁ l₂).A = A ∧
    (reconstruct A B C l₁ l₂).B = B ∧
    (reconstruct A B C l₁ l₂).C = C := by
  let e := reconstruct A B C l₁ l₂
  let p := invX A B C l₁ l₂
  let q := invY A B C l₁ l₂
  have hg := reconstruct_lower_gram A B C l₁ l₂ hA hD
  have he := inverse_equations A B C l₁ l₂ (ne_of_gt hD)
  have hcx : e.cx = p * e.ux + q * e.vx := by rfl
  have hcy : e.cy = p * e.uy + q * e.vy := by simp [e, p, q, reconstruct]
  have hnorm : e.h = form2 e.A e.B e.C p q := by
    dsimp [Planar.h]
    rw [hcx, hcy]
    dsimp [form2, Planar.A, Planar.B, Planar.C]
    ring
  have hfirst : e.l₁ = e.A * p + e.C * q := by
    dsimp [Planar.l₁]
    rw [hcx, hcy]
    dsimp [Planar.A, Planar.C]
    ring
  have hsecond : e.l₂ = e.C * p + e.B * q := by
    dsimp [Planar.l₂]
    rw [hcx, hcy]
    dsimp [Planar.B, Planar.C]
    ring
  change e.h = _ ∧ e.l₁ = _ ∧ e.l₂ = _ ∧ _
  refine ⟨?_, ?_, ?_, hg⟩
  · rw [hnorm, hg.1, hg.2.1, hg.2.2]
    exact form2_inverse A B C l₁ l₂ (ne_of_gt hD)
  · rw [hfirst, hg.1, hg.2.2]
    exact he.1
  · rw [hsecond, hg.2.2, hg.2.1]
    exact he.2

/-- A feasible symmetric Gram matrix with a positive-definite lower block yields
an explicit planar encoder satisfying every original pointwise peak bound. -/
theorem planar_synthesis (h l₁ l₂ A B C P : ℝ) (φ : ℝ → ℝ)
    (hA : 0 < A) (hD : 0 < det A B C) (hpsd : PSD3 h l₁ l₂ A B C)
    (hpeak : ∀ s : ℝ, -1 ≤ s → s ≤ 1 → form3 h l₁ l₂ A B C 1 s (φ s) ≤ P) :
    ∀ s : ℝ, -1 ≤ s → s ≤ 1 →
      (reconstruct A B C l₁ l₂).energy 1 s (φ s) ≤ P := by
  have hg := reconstruct_gram A B C l₁ l₂ hA hD
  intro s hlo hhi
  rw [Planar.energy_eq_form3, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1,
    hg.2.2.2.2.1, hg.2.2.2.2.2]
  exact peak_reduction h l₁ l₂ A B C P φ hA hD hpsd hpeak s hlo hhi

/-- Nonnegativity of the rank-one constrained quadratic form at every real vector. -/
def RankOnePSD (A B C lam w₁ w₂ : ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ form2 A B C x y - lam * (w₁ * x + w₂ * y) ^ 2

lemma gram_determinant_identity (A B C p q x y : ℝ) :
    form2 A B C p q * form2 A B C x y -
      ((A * p + C * q) * x + (C * p + B * q) * y) ^ 2 =
      det A B C * (p * y - q * x) ^ 2 := by
  dsimp [form2, det]
  ring

/-- The dual Cauchy--Schwarz inequality follows from a two-dimensional square. -/
lemma dual_cauchy (A B C w₁ w₂ x y : ℝ)
    (hD : 0 < det A B C) :
    (w₁ * x + w₂ * y) ^ 2 ≤ dual A B C w₁ w₂ * form2 A B C x y := by
  have he := inverse_equations A B C w₁ w₂ (ne_of_gt hD)
  have hi := gram_determinant_identity A B C
    (invX A B C w₁ w₂) (invY A B C w₁ w₂) x y
  rw [he.1, he.2, form2_inverse A B C w₁ w₂ (ne_of_gt hD)] at hi
  have hn := mul_nonneg hD.le
    (sq_nonneg (invX A B C w₁ w₂ * y - invY A B C w₁ w₂ * x))
  linarith

/-- The exact reciprocal-dual-norm characterization of the rank-one PSD score
constraint, with its matrix inequality interpreted on all real vectors. -/
theorem rank_one_psd_iff (A B C lam w₁ w₂ : ℝ)
    (hA : 0 < A) (hD : 0 < det A B C) (hlam : 0 ≤ lam)
    (hw : w₁ ≠ 0 ∨ w₂ ≠ 0) :
    RankOnePSD A B C lam w₁ w₂ ↔ lam ≤ 1 / dual A B C w₁ w₂ := by
  have hd := dual_pos A B C w₁ w₂ hA hD hw
  constructor
  · intro hpsd
    have ht := hpsd (invX A B C w₁ w₂) (invY A B C w₁ w₂)
    rw [form2_inverse A B C w₁ w₂ (ne_of_gt hD)] at ht
    change 0 ≤ dual A B C w₁ w₂ - lam * (dual A B C w₁ w₂) ^ 2 at ht
    apply (le_div_iff₀ hd).2
    nlinarith
  · intro hbound x y
    have hb := (le_div_iff₀ hd).1 hbound
    have hc := dual_cauchy A B C w₁ w₂ x y hD
    have hc' := mul_le_mul_of_nonneg_left hc hlam
    have hn := form2_nonneg A B C hA hD x y
    have hb' := mul_le_mul_of_nonneg_right hb hn
    nlinarith

/-- Two independent rank-one constraints at a positive score force the lower
Gram block to be positive definite; no separate definiteness assumption is used. -/
theorem two_rank_one_constraints_positive (A B C lam a b c d : ℝ)
    (hlam : 0 < lam) (hind : a * d - b * c ≠ 0)
    (hfirst : RankOnePSD A B C lam a b) (hsecond : RankOnePSD A B C lam c d) :
    0 < A ∧ 0 < det A B C := by
  have hpos : ∀ x y : ℝ, x ≠ 0 ∨ y ≠ 0 → 0 < form2 A B C x y := by
    intro x y hxy
    have hlin : a * x + b * y ≠ 0 ∨ c * x + d * y ≠ 0 := by
      by_contra hn
      push_neg at hn
      have hx : (a * d - b * c) * x = 0 := by
        calc
          _ = d * (a * x + b * y) - b * (c * x + d * y) := by ring
          _ = 0 := by rw [hn.1, hn.2]; ring
      have hy : (a * d - b * c) * y = 0 := by
        calc
          _ = a * (c * x + d * y) - c * (a * x + b * y) := by ring
          _ = 0 := by rw [hn.1, hn.2]; ring
      have hx0 := (mul_eq_zero.mp hx).resolve_left hind
      have hy0 := (mul_eq_zero.mp hy).resolve_left hind
      rcases hxy with hxy | hxy
      · exact hxy hx0
      · exact hxy hy0
    rcases hlin with hlin | hlin
    · have ht := hfirst x y
      have hs := mul_pos hlam (sq_pos_of_ne_zero hlin)
      linarith
    · have ht := hsecond x y
      have hs := mul_pos hlam (sq_pos_of_ne_zero hlin)
      linarith
  have hA : 0 < A := by simpa [form2] using hpos 1 0 (Or.inl one_ne_zero)
  refine ⟨hA, ?_⟩
  have ht := hpos (-C) A (Or.inr (ne_of_gt hA))
  have he : form2 A B C (-C) A = A * det A B C := by dsimp [form2, det]; ring
  rw [he] at ht
  nlinarith

/-- The algebraic reconstruction direction of the semi-infinite SDP, including
its implication of positive definiteness from two independent score vectors. -/
theorem positive_sdp_synthesis (h l₁ l₂ A B C P lam a b c d : ℝ) (φ : ℝ → ℝ)
    (hlam : 0 < lam) (hind : a * d - b * c ≠ 0)
    (hpsd : PSD3 h l₁ l₂ A B C)
    (hfirst : RankOnePSD A B C lam a b) (hsecond : RankOnePSD A B C lam c d)
    (hpeak : ∀ s : ℝ, -1 ≤ s → s ≤ 1 → form3 h l₁ l₂ A B C 1 s (φ s) ≤ P) :
    ∃ e : Planar,
      e.h = dual A B C l₁ l₂ ∧ e.l₁ = l₁ ∧ e.l₂ = l₂ ∧
      e.A = A ∧ e.B = B ∧ e.C = C ∧
      0 < e.A ∧ 0 < det e.A e.B e.C ∧
      RankOnePSD e.A e.B e.C lam a b ∧ RankOnePSD e.A e.B e.C lam c d ∧
      ∀ s : ℝ, -1 ≤ s → s ≤ 1 → e.energy 1 s (φ s) ≤ P := by
  have hpd := two_rank_one_constraints_positive A B C lam a b c d hlam hind hfirst hsecond
  have hg := reconstruct_gram A B C l₁ l₂ hpd.1 hpd.2
  refine ⟨reconstruct A B C l₁ l₂, hg.1, hg.2.1, hg.2.2.1,
    hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2, ?_⟩
  rw [hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2]
  exact ⟨hpd.1, hpd.2, hfirst, hsecond,
    planar_synthesis h l₁ l₂ A B C P φ hpd.1 hpd.2 hpsd hpeak⟩

end Analog.GramSynthesis
