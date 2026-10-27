import Analog.GramSynthesis

/-!
# Planar reconstruction including singular Gram blocks

Every positive semidefinite three-by-three form admits a planar realization
with the same lower block and cross terms, and a no-larger offset norm.
An explicit case split replaces the manuscript's Moore--Penrose formula.
The two encoder columns depend only on the common lower block, so the same
columns work simultaneously for heterogeneous node offsets.
-/

noncomputable section
namespace Analog.SingularGram
open GramSynthesis

private lemma linear_nonnegative_constant {a b : ℝ}
    (h : ∀ x : ℝ, 0 ≤ a + b * x) : b = 0 := by
  by_contra hb
  have ht := h (-(a + 1) / b)
  have he : a + b * (-(a + 1) / b) = -1 := by field_simp; ring
  rw [he] at ht
  norm_num at ht

private lemma psd_diagonal {h l₁ l₂ A B C : ℝ}
    (hp : PSD3 h l₁ l₂ A B C) : 0 ≤ h ∧ 0 ≤ A ∧ 0 ≤ B := by
  exact ⟨by simpa [form3, form2] using hp 1 0 0,
    by simpa [form3, form2] using hp 0 1 0,
    by simpa [form3, form2] using hp 0 0 1⟩

private lemma zero_first_diagonal {h l₁ l₂ B C : ℝ}
    (hp : PSD3 h l₁ l₂ 0 B C) : l₁ = 0 ∧ C = 0 := by
  have hl := linear_nonnegative_constant (a := h) (b := 2 * l₁) (by
    intro x
    simpa [form3, form2, mul_assoc] using hp 1 x 0)
  have hc := linear_nonnegative_constant (a := B) (b := 2 * C) (by
    intro x
    have ht := hp 0 x 1
    dsimp [form3, form2] at ht
    nlinarith)
  constructor <;> linarith

private lemma first_offset_bound {h l₁ l₂ A B C : ℝ}
    (hp : PSD3 h l₁ l₂ A B C) (hA : 0 < A) : l₁ ^ 2 / A ≤ h := by
  have ht := hp 1 (-l₁ / A) 0
  have he : form3 h l₁ l₂ A B C 1 (-l₁ / A) 0 = h - l₁ ^ 2 / A := by
    dsimp [form3, form2]
    field_simp
    ring
  rw [he] at ht
  linarith

private lemma det_nonnegative_of_pos {h l₁ l₂ A B C : ℝ}
    (hp : PSD3 h l₁ l₂ A B C) (hA : 0 < A) : 0 ≤ det A B C := by
  have ht := hp 0 (-C) A
  have he : form3 h l₁ l₂ A B C 0 (-C) A = A * det A B C := by
    dsimp [form3, form2, det]; ring
  rw [he] at ht
  exact (mul_nonneg_iff_of_pos_left hA).mp ht

private lemma singular_cross {h l₁ l₂ A B C : ℝ}
    (hp : PSD3 h l₁ l₂ A B C) (hA : 0 < A)
    (hD : det A B C = 0) : l₂ = l₁ * C / A := by
  have hAB : A * B = C ^ 2 := by dsimp [det] at hD; linarith
  have hB : B = C ^ 2 / A := (eq_div_iff (ne_of_gt hA)).mpr (by nlinarith)
  have ht : ∀ y : ℝ, 0 ≤ h + (2 * (l₂ - l₁ * C / A)) * y := by
    intro y
    have hh := hp 1 (-(C / A) * y) y
    have he : form3 h l₁ l₂ A B C 1 (-(C / A) * y) y =
        h + (2 * (l₂ - l₁ * C / A)) * y := by
      rw [hB]
      dsimp [form3, form2]
      field_simp
      ring
    rwa [he] at hh
  have hz := linear_nonnegative_constant ht
  linarith

/-- A rank-one realization when the first lower diagonal is positive. -/
def rankOne (A C l₁ : ℝ) : Planar where
  cx := l₁ / Real.sqrt A
  cy := 0
  ux := Real.sqrt A
  uy := 0
  vx := C / Real.sqrt A
  vy := 0

/-- A realization supported on the second feature coordinate. -/
def secondOnly (B l₂ : ℝ) : Planar where
  cx := 0
  cy := l₂ / Real.sqrt B
  ux := 0
  uy := 0
  vx := 0
  vy := Real.sqrt B

def zeroPlanar : Planar := ⟨0, 0, 0, 0, 0, 0⟩

/-- A common-column reconstruction, valid at every rank of the lower block. -/
def reconstructPSD (A B C l₁ l₂ : ℝ) : Planar :=
  if 0 < A then
    if 0 < det A B C then reconstruct A B C l₁ l₂ else rankOne A C l₁
  else if 0 < B then secondOnly B l₂ else zeroPlanar

private lemma rankOne_gram {h l₁ l₂ A B C : ℝ}
    (hp : PSD3 h l₁ l₂ A B C) (hA : 0 < A) (hD : det A B C = 0) :
    (rankOne A C l₁).h ≤ h ∧ (rankOne A C l₁).l₁ = l₁ ∧
    (rankOne A C l₁).l₂ = l₂ ∧ (rankOne A C l₁).A = A ∧
    (rankOne A C l₁).B = B ∧ (rankOne A C l₁).C = C := by
  have hs : Real.sqrt A ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hA)
  have hsq := Real.sq_sqrt hA.le
  have hcross := singular_cross hp hA hD
  have hAB : A * B = C ^ 2 := by dsimp [det] at hD; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Planar.h, rankOne, div_pow, hsq] using first_offset_bound hp hA
  · simp [Planar.l₁, rankOne, hs]
  · dsimp [Planar.l₂, rankOne]
    simp only [← mul_div_mul_comm, ← pow_two, hsq]
    simpa using hcross.symm
  · simp [Planar.A, rankOne, hsq]
  · simp only [Planar.B, rankOne, zero_pow (by decide : 2 ≠ 0), add_zero,
      div_pow, hsq]
    exact (div_eq_iff (ne_of_gt hA)).mpr (by nlinarith)
  · dsimp [Planar.C, rankOne]
    field_simp
    ring

/-- Generalized Schur reconstruction: no positive-definiteness assumption. -/
theorem reconstructPSD_gram {h l₁ l₂ A B C : ℝ}
    (hp : PSD3 h l₁ l₂ A B C) :
    (reconstructPSD A B C l₁ l₂).h ≤ h ∧
    (reconstructPSD A B C l₁ l₂).l₁ = l₁ ∧
    (reconstructPSD A B C l₁ l₂).l₂ = l₂ ∧
    (reconstructPSD A B C l₁ l₂).A = A ∧
    (reconstructPSD A B C l₁ l₂).B = B ∧
    (reconstructPSD A B C l₁ l₂).C = C := by
  have hd := psd_diagonal hp
  by_cases hA : 0 < A
  · by_cases hD : 0 < det A B C
    · rw [reconstructPSD, if_pos hA, if_pos hD]
      have hg := reconstruct_gram A B C l₁ l₂ hA hD
      exact ⟨hg.1.trans_le ((psd3_iff_schur h l₁ l₂ A B C hA hD).mp hp), hg.2⟩
    · have hz : det A B C = 0 := le_antisymm (le_of_not_gt hD)
        (det_nonnegative_of_pos hp hA)
      simpa [reconstructPSD, hA, hD] using rankOne_gram hp hA hz
  · have hAz : A = 0 := le_antisymm (le_of_not_gt hA) hd.2.1
    subst A
    have hz := zero_first_diagonal hp
    rcases hz with ⟨hl₁, hC⟩
    subst l₁
    subst C
    by_cases hB : 0 < B
    · have hs : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hB)
      have hsq := Real.sq_sqrt hB.le
      have hp' : PSD3 h l₂ 0 B 0 0 := by
        intro t x y
        simpa [form3, form2] using hp t y x
      have hb := first_offset_bound hp' hB
      simp [reconstructPSD, secondOnly, Planar.h, Planar.l₁, Planar.l₂,
        Planar.A, Planar.B, Planar.C, hB, hs, div_pow, hsq, hb]
    · have hBz : B = 0 := le_antisymm (le_of_not_gt hB) hd.2.2
      subst B
      have hl₂ : l₂ = 0 := by
        have ht : PSD3 h l₂ 0 0 0 0 := by
          intro t x y
          simpa [form3, form2] using hp t y x
        exact (zero_first_diagonal ht).1
      subst l₂
      simpa [reconstructPSD, zeroPlanar, Planar.h, Planar.l₁, Planar.l₂,
        Planar.A, Planar.B, Planar.C] using hd.1

/-- Reconstruction decreases power at every feature vector, not just samples. -/
theorem reconstructPSD_energy_le {h l₁ l₂ A B C : ℝ}
    (hp : PSD3 h l₁ l₂ A B C) (t x y : ℝ) :
    (reconstructPSD A B C l₁ l₂).energy t x y ≤ form3 h l₁ l₂ A B C t x y := by
  obtain ⟨hh, h₁, h₂, hA, hB, hC⟩ := reconstructPSD_gram hp
  rw [Planar.energy_eq_form3, h₁, h₂, hA, hB, hC]
  have hb := mul_le_mul_of_nonneg_right hh (sq_nonneg t)
  dsimp [form3]
  linarith

/-- All node reconstructions with a shared lower block use identical columns. -/
theorem reconstructPSD_common_columns (A B C l₁ l₂ q₁ q₂ : ℝ) :
    (reconstructPSD A B C l₁ l₂).ux = (reconstructPSD A B C q₁ q₂).ux ∧
    (reconstructPSD A B C l₁ l₂).uy = (reconstructPSD A B C q₁ q₂).uy ∧
    (reconstructPSD A B C l₁ l₂).vx = (reconstructPSD A B C q₁ q₂).vx ∧
    (reconstructPSD A B C l₁ l₂).vy = (reconstructPSD A B C q₁ q₂).vy := by
  unfold reconstructPSD
  split_ifs <;> simp [reconstruct, rankOne, secondOnly, zeroPlanar]

end Analog.SingularGram
