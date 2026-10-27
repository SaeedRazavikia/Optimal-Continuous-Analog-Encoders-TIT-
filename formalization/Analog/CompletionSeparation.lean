import Analog.LocalPexider
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Rank-one completion identities and continuous separation

This module supplies the analytic contradiction behind dense two-completion
separation. A determinant identity on a rectangle gives logarithmic Pexider
identities. Independent feature coordinates force both Pexider slopes to
vanish. Nonvanishing is explicit in the core logarithmic theorem; a separate
lemma derives it from the corresponding row/column nonvanishing conditions.
-/

noncomputable section
open Set
namespace Analog.CompletionSeparation

/-- A fully rank-one mixed array cannot have a zero entry if each row and
column required by the argument contains a nonzero witness. -/
theorem mixed_rank_one_nonzero {X Y T : Type*} (A : X → T → ℝ) (B : Y → T → ℝ)
    (hdet : ∀ x y t u, A x t * B y u = A x u * B y t)
    (hArow : ∀ x, ∃ t, A x t ≠ 0) (hBcol : ∀ t, ∃ y, B y t ≠ 0) :
    ∀ x t, A x t ≠ 0 := by
  intro x t hzero
  obtain ⟨u, hu⟩ := hArow x
  obtain ⟨y, hy⟩ := hBcol t
  have hh := hdet x y t u
  rw [hzero, zero_mul] at hh
  exact (mul_ne_zero hu hy) hh.symm

/-- The logarithm of a mixed rank-one identity separates the two arguments.
Real logarithms permit either sign, provided all factors are nonzero. -/
theorem log_rank_one (p q r s : ℝ)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0)
    (heq : p * q = r * s) : Real.log p + Real.log q = Real.log r + Real.log s := by
  rw [← Real.log_mul hp hq, ← Real.log_mul hr hs, heq]

/-- A fixed completion produces the logarithmic Pexider equation in the
first coordinate from the mixed determinant identity. -/
theorem log_pexider_identity {X Y T : Type*} (A : X → T → ℝ) (B : Y → T → ℝ)
    (hA : ∀ x t, A x t ≠ 0) (hB : ∀ y t, B y t ≠ 0)
    (hdet : ∀ x y t u, A x t * B y u = A x u * B y t)
    (x₀ : X) (y₀ : Y) (u : T) (x : X) (t : T) :
    Real.log (A x t) = Real.log (A x u) +
      (Real.log (A x₀ t) - Real.log (A x₀ u)) := by
  have h₁ := log_rank_one _ _ _ _ (hA x t) (hB y₀ u) (hA x u) (hB y₀ t)
    (hdet x y₀ t u)
  have h₂ := log_rank_one _ _ _ _ (hA x₀ t) (hB y₀ u) (hA x₀ u) (hB y₀ t)
    (hdet x₀ y₀ t u)
  linarith

/-- For independent completion-feature coordinates, a continuous mixed
rank-one identity makes both log-derivatives constant on translated open
rectangles. The interval-image hypotheses are the actual coordinate ranges,
not differentiability or invertibility assumptions on either coordinate. -/
theorem log_constants_of_independent_features
    {a b c d e f g h : ℝ} (hab : a < b) (hcd : c < d)
    (hef : e < f) (hgh : g < h)
    (T : Set ℝ) (x y A B : ℝ → ℝ) {u : ℝ} (hu : u ∈ T)
    (hx : MapsTo x T (Icc c d)) (hy : MapsTo y T (Icc g h))
    (hsx : ∀ q ∈ Icc c d, ∃ t ∈ T, x t = q)
    (hsy : ∀ q ∈ Icc g h, ∃ t ∈ T, y t = q)
    (hLA : ContinuousOn (fun z => Real.log (A z)) (Icc (a + c) (b + d)))
    (hLB : ContinuousOn (fun z => Real.log (B z)) (Icc (e + g) (f + h)))
    (hA : ∀ z ∈ Icc (a + c) (b + d), A z ≠ 0)
    (hB : ∀ z ∈ Icc (e + g) (f + h), B z ≠ 0)
    (hind : GeneralRigidity.NotInAffineLine T x y)
    (hdet : ∀ ξ ∈ Icc a b, ∀ η ∈ Icc e f, ∀ t ∈ T, ∀ v ∈ T,
      A (ξ + x t) * B (η + y v) = A (ξ + x v) * B (η + y t)) :
    ∃ C D : ℝ,
      (∀ ξ ∈ Icc a b, Real.log (A (ξ + x u)) = C) ∧
      (∀ η ∈ Icc e f, Real.log (B (η + y u)) = D) := by
  let AA : Icc a b → T → ℝ := fun ξ t => A (ξ + x t)
  let BB : Icc e f → T → ℝ := fun η t => B (η + y t)
  have hAA : ∀ ξ t, AA ξ t ≠ 0 := by
    intro ξ t
    apply hA
    exact ⟨add_le_add ξ.property.1 (hx t.property).1,
      add_le_add ξ.property.2 (hx t.property).2⟩
  have hBB : ∀ η t, BB η t ≠ 0 := by
    intro η t
    apply hB
    exact ⟨add_le_add η.property.1 (hy t.property).1,
      add_le_add η.property.2 (hy t.property).2⟩
  have hDD : ∀ ξ η t v, AA ξ t * BB η v = AA ξ v * BB η t := by
    intro ξ η t v
    exact hdet ξ ξ.property η η.property t t.property v v.property
  let HA : ℝ → ℝ := fun ξ => Real.log (A (ξ + x u))
  let QA : ℝ → ℝ := fun q => Real.log (A (a + q)) - Real.log (A (a + x u))
  let HB : ℝ → ℝ := fun η => Real.log (B (η + y u))
  let QB : ℝ → ℝ := fun q => Real.log (B (e + q)) - Real.log (B (e + y u))
  have hHA : ContinuousOn HA (Icc a b) := by
    apply hLA.comp (continuousOn_id.add continuousOn_const)
    intro ξ hξ
    exact ⟨add_le_add hξ.1 (hx hu).1, add_le_add hξ.2 (hx hu).2⟩
  have hQA : ContinuousOn QA (Icc c d) := by
    apply ContinuousOn.sub _ continuousOn_const
    apply hLA.comp (continuousOn_const.add continuousOn_id)
    intro q hq
    exact ⟨add_le_add_left hq.1 a, add_le_add hab.le hq.2⟩
  have hHB : ContinuousOn HB (Icc e f) := by
    apply hLB.comp (continuousOn_id.add continuousOn_const)
    intro η hη
    exact ⟨add_le_add hη.1 (hy hu).1, add_le_add hη.2 (hy hu).2⟩
  have hQB : ContinuousOn QB (Icc g h) := by
    apply ContinuousOn.sub _ continuousOn_const
    apply hLB.comp (continuousOn_const.add continuousOn_id)
    intro q hq
    exact ⟨add_le_add_left hq.1 e, add_le_add hef.le hq.2⟩
  have hEqA : ∀ ξ ∈ Icc a b, ∀ q ∈ Icc c d,
      Real.log (A (ξ + q)) = HA ξ + QA q := by
    intro ξ hξ q hq
    obtain ⟨t, ht, rfl⟩ := hsx q hq
    exact log_pexider_identity AA BB hAA hBB hDD
      ⟨a, le_rfl, hab.le⟩ ⟨e, le_rfl, hef.le⟩ ⟨u, hu⟩ ⟨ξ, hξ⟩ ⟨t, ht⟩
  have hEqB : ∀ η ∈ Icc e f, ∀ q ∈ Icc g h,
      Real.log (B (η + q)) = HB η + QB q := by
    intro η hη q hq
    obtain ⟨t, ht, rfl⟩ := hsy q hq
    apply log_pexider_identity BB AA hBB hAA
      (fun η ξ t v => ?_) ⟨e, le_rfl, hef.le⟩ ⟨a, le_rfl, hab.le⟩
      ⟨u, hu⟩ ⟨η, hη⟩ ⟨t, ht⟩
    simpa only [mul_comm] using (hDD ξ η t v).symm
  obtain ⟨lamA, h₀, q₀, hhA, hqA⟩ := LocalPexider.rectangle_affine_of_continuousOn
    hab hcd (fun z => Real.log (A z)) HA QA hLA hHA hQA hEqA
  obtain ⟨lamB, h₁, q₁, hhB, hqB⟩ := LocalPexider.rectangle_affine_of_continuousOn
    hef hgh (fun z => Real.log (B z)) HB QB hLB hHB hQB hEqB
  have hratio : ∀ t ∈ T, QA (x t) = QB (y t) := by
    intro t ht
    have hd := log_rank_one _ _ _ _
      (hAA ⟨a, le_rfl, hab.le⟩ ⟨t, ht⟩) (hBB ⟨e, le_rfl, hef.le⟩ ⟨u, hu⟩)
      (hAA ⟨a, le_rfl, hab.le⟩ ⟨u, hu⟩) (hBB ⟨e, le_rfl, hef.le⟩ ⟨t, ht⟩)
      (hDD ⟨a, le_rfl, hab.le⟩ ⟨e, le_rfl, hef.le⟩ ⟨t, ht⟩ ⟨u, hu⟩)
    dsimp [QA, QB, AA, BB] at hd ⊢
    linarith
  have hrel : ∀ t ∈ T, lamA * x t + (-lamB) * y t = q₁ - q₀ := by
    intro t ht
    have hr := hratio t ht
    rw [hqA (x t) (hx ht), hqB (y t) (hy ht)] at hr
    linarith
  have hzero : lamA = 0 ∧ lamB = 0 := by
    by_contra hz
    apply hind
    refine ⟨lamA, -lamB, q₁ - q₀, ?_, hrel⟩
    by_cases ha : lamA = 0
    · right
      intro hb
      have hbb : lamB = 0 := neg_eq_zero.mp hb
      exact hz ⟨ha, hbb⟩
    · exact Or.inl ha
  refine ⟨h₀, h₁, ?_, ?_⟩
  · intro ξ hξ
    simpa only [hzero.1, zero_mul, add_zero] using hhA ξ hξ
  · intro η hη
    simpa only [hzero.2, zero_mul, add_zero] using hhB η hη

/-- The derivative does not vanish identically on any nonempty open
subinterval of its prescribed domain. -/
def NoZeroInterval (D : Set ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ l r : ℝ, l < r → Ioo l r ⊆ D → ∃ z ∈ Ioo l r, F z ≠ 0

private theorem sum_interval_decomposition {a b c d z : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hz : z ∈ Icc (a + c) (b + d)) :
    ∃ ξ ∈ Icc a b, ∃ q ∈ Icc c d, ξ + q = z := by
  let ξ := max a (z - d)
  refine ⟨ξ, ⟨le_max_left _ _, max_le hab (by linarith [hz.2])⟩,
    z - ξ, ⟨?_, ?_⟩, by ring⟩
  · have hξ : ξ ≤ z - c := max_le (by linarith [hz.1]) (by linarith)
    linarith
  · have hξ : z - d ≤ ξ := le_max_right _ _
    linarith

/-- Rank-zero completion identities plus the no-flat-derivative condition
derive nonvanishing at every argument in the sum intervals. -/
theorem nonzero_of_noZeroInterval
    {a b c d e f g h : ℝ} (hab : a < b) (hcd : c < d)
    (hef : e < f) (hgh : g < h)
    (T : Set ℝ) (x y A B : ℝ → ℝ)
    (hx : MapsTo x T (Icc c d)) (hy : MapsTo y T (Icc g h))
    (hsx : ∀ q ∈ Icc c d, ∃ t ∈ T, x t = q)
    (hsy : ∀ q ∈ Icc g h, ∃ t ∈ T, y t = q)
    (hNA : NoZeroInterval (Icc (a + c) (b + d)) A)
    (hNB : NoZeroInterval (Icc (e + g) (f + h)) B)
    (hdet : ∀ ξ ∈ Icc a b, ∀ η ∈ Icc e f, ∀ t ∈ T, ∀ v ∈ T,
      A (ξ + x t) * B (η + y v) = A (ξ + x v) * B (η + y t)) :
    (∀ z ∈ Icc (a + c) (b + d), A z ≠ 0) ∧
    (∀ z ∈ Icc (e + g) (f + h), B z ≠ 0) := by
  let AA : Icc a b → T → ℝ := fun ξ t => A (ξ + x t)
  let BB : Icc e f → T → ℝ := fun η t => B (η + y t)
  have hDD : ∀ ξ η t v, AA ξ t * BB η v = AA ξ v * BB η t := by
    intro ξ η t v
    exact hdet ξ ξ.property η η.property t t.property v v.property
  have hAr : ∀ ξ, ∃ t, AA ξ t ≠ 0 := by
    intro ξ
    obtain ⟨z, hz, hnz⟩ := hNA (ξ + c) (ξ + d) (by linarith) (by
      intro z hz
      exact ⟨by linarith [ξ.property.1, hz.1], by linarith [ξ.property.2, hz.2]⟩)
    obtain ⟨t, ht, hxt⟩ := hsx (z - ξ) ⟨by linarith [hz.1], by linarith [hz.2]⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    dsimp [AA]
    rw [hxt]
    have he : (ξ : ℝ) + (z - ξ) = z := by ring
    rwa [he]
  have hBr : ∀ η, ∃ t, BB η t ≠ 0 := by
    intro η
    obtain ⟨z, hz, hnz⟩ := hNB (η + g) (η + h) (by linarith) (by
      intro z hz
      exact ⟨by linarith [η.property.1, hz.1], by linarith [η.property.2, hz.2]⟩)
    obtain ⟨t, ht, hyt⟩ := hsy (z - η) ⟨by linarith [hz.1], by linarith [hz.2]⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    dsimp [BB]
    rw [hyt]
    have he : (η : ℝ) + (z - η) = z := by ring
    rwa [he]
  have hAc : ∀ t, ∃ ξ, AA ξ t ≠ 0 := by
    intro t
    obtain ⟨z, hz, hnz⟩ := hNA (a + x t) (b + x t) (by linarith) (by
      intro z hz
      exact ⟨by linarith [(hx t.property).1, hz.1],
        by linarith [(hx t.property).2, hz.2]⟩)
    refine ⟨⟨z - x t, by constructor <;> linarith [hz.1, hz.2]⟩, ?_⟩
    simpa [AA] using hnz
  have hBc : ∀ t, ∃ η, BB η t ≠ 0 := by
    intro t
    obtain ⟨z, hz, hnz⟩ := hNB (e + y t) (f + y t) (by linarith) (by
      intro z hz
      exact ⟨by linarith [(hy t.property).1, hz.1],
        by linarith [(hy t.property).2, hz.2]⟩)
    refine ⟨⟨z - y t, by constructor <;> linarith [hz.1, hz.2]⟩, ?_⟩
    simpa [BB] using hnz
  have hAA := mixed_rank_one_nonzero AA BB hDD hAr hBc
  have hBB := mixed_rank_one_nonzero BB AA
    (fun η ξ t v => by simpa only [mul_comm] using (hDD ξ η t v).symm) hBr hAc
  constructor
  · intro z hz
    obtain ⟨ξ, hξ, q, hq, rfl⟩ := sum_interval_decomposition hab.le hcd.le hz
    obtain ⟨t, ht, rfl⟩ := hsx q hq
    exact hAA ⟨ξ, hξ⟩ ⟨t, ht⟩
  · intro z hz
    obtain ⟨η, hη, q, hq, rfl⟩ := sum_interval_decomposition hef.le hgh.le hz
    obtain ⟨t, ht, rfl⟩ := hsy q hq
    exact hBB ⟨η, hη⟩ ⟨t, ht⟩

/-- A continuous nonvanishing real function with constant real logarithm
is constant on an interval; continuity rules out a sign switch. -/
theorem constant_of_log_constant {a b C : ℝ} (hab : a ≤ b) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Icc a b)) (hn : ∀ z ∈ Icc a b, F z ≠ 0)
    (hlog : ∀ z ∈ Icc a b, Real.log (F z) = C) :
    ∀ z ∈ Icc a b, F z = F a := by
  intro z hz
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have habs : |F z| = |F a| := by
    rw [← Real.exp_log_eq_abs (hn z hz), ← Real.exp_log_eq_abs (hn a ha),
      hlog z hz, hlog a ha]
  rcases abs_eq_abs.mp habs with heq | hneg
  · exact heq
  · have hmid : (0 : ℝ) ∈ uIcc (F a) (F z) := by
      rw [mem_uIcc]
      rcases le_total (F a) 0 with hh | hh
      · exact Or.inl ⟨hh, by linarith⟩
      · exact Or.inr ⟨by linarith, hh⟩
    have hsmall : ContinuousOn F (uIcc a z) := by
      rw [uIcc_of_le hz.1]
      exact hF.mono (Icc_subset_Icc le_rfl hz.2)
    obtain ⟨w, hw, hw0⟩ := intermediate_value_uIcc hsmall hmid
    have hwin : w ∈ Icc a b := by
      rw [uIcc_of_le hz.1] at hw
      exact ⟨hw.1, hw.2.trans hz.2⟩
    exact False.elim ((hn w hwin) hw0)

/-- The full rectangular rank-zero contradiction: without affine feature
dependence, both completion derivatives must be constant on nonempty
translated intervals. No nonvanishing or differentiability is added as a
premise: nonvanishing is derived from the no-zero-interval condition. -/
theorem constants_of_rank_zero
    {a b c d e f g h : ℝ} (hab : a < b) (hcd : c < d)
    (hef : e < f) (hgh : g < h)
    (T : Set ℝ) (x y A B : ℝ → ℝ) {u : ℝ} (hu : u ∈ T)
    (hx : MapsTo x T (Icc c d)) (hy : MapsTo y T (Icc g h))
    (hsx : ∀ q ∈ Icc c d, ∃ t ∈ T, x t = q)
    (hsy : ∀ q ∈ Icc g h, ∃ t ∈ T, y t = q)
    (hA : ContinuousOn A (Icc (a + c) (b + d)))
    (hB : ContinuousOn B (Icc (e + g) (f + h)))
    (hNA : NoZeroInterval (Icc (a + c) (b + d)) A)
    (hNB : NoZeroInterval (Icc (e + g) (f + h)) B)
    (hind : GeneralRigidity.NotInAffineLine T x y)
    (hdet : ∀ ξ ∈ Icc a b, ∀ η ∈ Icc e f, ∀ t ∈ T, ∀ v ∈ T,
      A (ξ + x t) * B (η + y v) = A (ξ + x v) * B (η + y t)) :
    (∀ ξ ∈ Icc a b, A (ξ + x u) = A (a + x u)) ∧
    (∀ η ∈ Icc e f, B (η + y u) = B (e + y u)) := by
  obtain ⟨hnA, hnB⟩ := nonzero_of_noZeroInterval hab hcd hef hgh
    T x y A B hx hy hsx hsy hNA hNB hdet
  obtain ⟨C, D, hC, hD⟩ := log_constants_of_independent_features hab hcd hef hgh
    T x y A B hu hx hy hsx hsy (hA.log hnA) (hB.log hnB) hnA hnB hind hdet
  constructor
  · apply constant_of_log_constant hab.le (fun ξ => A (ξ + x u)) _ _ hC
    · apply hA.comp (continuousOn_id.add continuousOn_const)
      intro ξ hξ
      exact ⟨add_le_add hξ.1 (hx hu).1, add_le_add hξ.2 (hx hu).2⟩
    · intro ξ hξ
      exact hnA _ ⟨add_le_add hξ.1 (hx hu).1, add_le_add hξ.2 (hx hu).2⟩
  · apply constant_of_log_constant hef.le (fun η => B (η + y u)) _ _ hD
    · apply hB.comp (continuousOn_id.add continuousOn_const)
      intro η hη
      exact ⟨add_le_add hη.1 (hy hu).1, add_le_add hη.2 (hy hu).2⟩
    · intro η hη
      exact hnB _ ⟨add_le_add hη.1 (hy hu).1, add_le_add hη.2 (hy hu).2⟩

/-- No constant values on any nonempty open subinterval. -/
def NoConstantInterval (D : Set ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ l r : ℝ, l < r → Ioo l r ⊆ D → ¬ ∃ C : ℝ, ∀ z ∈ Ioo l r, F z = C

theorem NoZeroInterval.mono {D E : Set ℝ} {F : ℝ → ℝ}
    (hF : NoZeroInterval D F) (hED : E ⊆ D) : NoZeroInterval E F := by
  intro l r hlr hsub
  exact hF l r hlr (hsub.trans hED)

theorem NoConstantInterval.mono {D E : Set ℝ} {F : ℝ → ℝ}
    (hF : NoConstantInterval D F) (hED : E ⊆ D) : NoConstantInterval E F := by
  intro l r hlr hsub
  exact hF l r hlr (hsub.trans hED)

/-- Nonconstant-on-every-interval implies nonzero-on-some-point in every interval. -/
theorem NoConstantInterval.noZeroInterval {D : Set ℝ} {F : ℝ → ℝ}
    (hF : NoConstantInterval D F) : NoZeroInterval D F := by
  intro l r hlr hsub
  by_contra hz
  push_neg at hz
  exact hF l r hlr hsub ⟨0, hz⟩

/-- Every rectangle contains two completions with linearly independent
receiver gradients, provided one receiver derivative is nowhere locally
constant and neither is identically zero on an interval. -/
theorem exists_separating_completions
    {a b c d e f g h : ℝ} (hab : a < b) (hcd : c < d)
    (hef : e < f) (hgh : g < h)
    (T : Set ℝ) (x y A B : ℝ → ℝ) {u : ℝ} (hu : u ∈ T)
    (hx : MapsTo x T (Icc c d)) (hy : MapsTo y T (Icc g h))
    (hsx : ∀ q ∈ Icc c d, ∃ t ∈ T, x t = q)
    (hsy : ∀ q ∈ Icc g h, ∃ t ∈ T, y t = q)
    (hA : ContinuousOn A (Icc (a + c) (b + d)))
    (hB : ContinuousOn B (Icc (e + g) (f + h)))
    (hNA : NoZeroInterval (Icc (a + c) (b + d)) A)
    (hNB : NoZeroInterval (Icc (e + g) (f + h)) B)
    (hNC : NoConstantInterval (Icc (a + c) (b + d)) A ∨
      NoConstantInterval (Icc (e + g) (f + h)) B)
    (hind : GeneralRigidity.NotInAffineLine T x y) :
    ∃ ξ ∈ Icc a b, ∃ η ∈ Icc e f, ∃ t ∈ T, ∃ v ∈ T,
      A (ξ + x t) * B (η + y v) ≠ A (ξ + x v) * B (η + y t) := by
  by_contra hn
  push_neg at hn
  obtain ⟨hCA, hCB⟩ := constants_of_rank_zero hab hcd hef hgh
    T x y A B hu hx hy hsx hsy hA hB hNA hNB hind hn
  rcases hNC with hNC | hNC
  · apply hNC (a + x u) (b + x u) (by linarith)
      (fun z hz => ⟨by linarith [(hx hu).1, hz.1],
        by linarith [(hx hu).2, hz.2]⟩)
    refine ⟨A (a + x u), ?_⟩
    intro z hz
    have hh := hCA (z - x u) ⟨by linarith [hz.1], by linarith [hz.2]⟩
    simpa using hh
  · apply hNC (e + y u) (f + y u) (by linarith)
      (fun z hz => ⟨by linarith [(hy hu).1, hz.1],
        by linarith [(hy hu).2, hz.2]⟩)
    refine ⟨B (e + y u), ?_⟩
    intro z hz
    have hh := hCB (z - y u) ⟨by linarith [hz.1], by linarith [hz.2]⟩
    simpa using hh

/-- The points at which two alternative completions have independent
gradients. The harmless common normalization factor is omitted. -/
def separatingLocus (T : Set ℝ) (x y A B : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ t ∈ T, ∃ v ∈ T,
    A (p.1 + x t) * B (p.2 + y v) ≠ A (p.1 + x v) * B (p.2 + y t)}

/-- Dense two-completion separation on the actual open rectangle follows
from continuous receiver derivatives and independent completion features.
The conclusion supplies the density input used by the rigidity argument. -/
theorem separatingLocus_dense
    {a b c d e f g h : ℝ} (hcd : c < d) (hgh : g < h)
    (T : Set ℝ) (x y A B : ℝ → ℝ) {u : ℝ} (hu : u ∈ T)
    (hx : MapsTo x T (Icc c d)) (hy : MapsTo y T (Icc g h))
    (hsx : ∀ q ∈ Icc c d, ∃ t ∈ T, x t = q)
    (hsy : ∀ q ∈ Icc g h, ∃ t ∈ T, y t = q)
    (hA : ContinuousOn A (Ioo (a + c) (b + d)))
    (hB : ContinuousOn B (Ioo (e + g) (f + h)))
    (hNA : NoZeroInterval (Ioo (a + c) (b + d)) A)
    (hNB : NoZeroInterval (Ioo (e + g) (f + h)) B)
    (hNC : NoConstantInterval (Ioo (a + c) (b + d)) A ∨
      NoConstantInterval (Ioo (e + g) (f + h)) B)
    (hind : GeneralRigidity.NotInAffineLine T x y) :
    Ioo a b ×ˢ Ioo e f ⊆
      closure (separatingLocus T x y A B ∩ (Ioo a b ×ˢ Ioo e f)) := by
  intro p hp
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hmin : 0 < min ε (min (p.1 - a) (min (b - p.1)
      (min (p.2 - e) (f - p.2)))) := by
    exact lt_min hε (lt_min (sub_pos.mpr hp.1.1) (lt_min (sub_pos.mpr hp.1.2)
      (lt_min (sub_pos.mpr hp.2.1) (sub_pos.mpr hp.2.2))))
  obtain ⟨δ, hδ, hδmin⟩ := exists_between hmin
  rcases lt_min_iff.mp hδmin with ⟨hδε, hrest⟩
  rcases lt_min_iff.mp hrest with ⟨hδa, hrest⟩
  rcases lt_min_iff.mp hrest with ⟨hδb, hrest⟩
  rcases lt_min_iff.mp hrest with ⟨hδe, hδf⟩
  have hsubA : Icc (p.1 - δ + c) (p.1 + δ + d) ⊆ Ioo (a + c) (b + d) := by
    intro z hz
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hsubB : Icc (p.2 - δ + g) (p.2 + δ + h) ⊆ Ioo (e + g) (f + h) := by
    intro z hz
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hNC' : NoConstantInterval (Icc (p.1 - δ + c) (p.1 + δ + d)) A ∨
      NoConstantInterval (Icc (p.2 - δ + g) (p.2 + δ + h)) B :=
    hNC.elim (fun h => Or.inl (h.mono hsubA)) (fun h => Or.inr (h.mono hsubB))
  obtain ⟨ξ, hξ, η, hη, t, ht, v, hv, hsep⟩ := exists_separating_completions
    (by linarith : p.1 - δ < p.1 + δ) hcd
    (by linarith : p.2 - δ < p.2 + δ) hgh T x y A B hu
    hx hy hsx hsy (hA.mono hsubA) (hB.mono hsubB)
    (hNA.mono hsubA) (hNB.mono hsubB) hNC' hind
  refine ⟨(ξ, η), ⟨⟨t, ht, v, hv, hsep⟩, ?_⟩, ?_⟩
  · exact ⟨⟨by linarith [hξ.1], by linarith [hξ.2]⟩,
      ⟨by linarith [hη.1], by linarith [hη.2]⟩⟩
  · rw [Prod.dist_eq]
    apply max_lt
    · rw [Real.dist_eq]
      exact lt_of_le_of_lt (abs_le.mpr ⟨by linarith [hξ.2], by linarith [hξ.1]⟩) hδε
    · rw [Real.dist_eq]
      exact lt_of_le_of_lt (abs_le.mpr ⟨by linarith [hη.2], by linarith [hη.1]⟩) hδε

/-- The separating locus is open relative to the rectangle. -/
theorem separatingLocus_open
    {a b c d e f g h : ℝ} (T : Set ℝ) (x y A B : ℝ → ℝ)
    (hx : MapsTo x T (Icc c d)) (hy : MapsTo y T (Icc g h))
    (hA : ContinuousOn A (Ioo (a + c) (b + d)))
    (hB : ContinuousOn B (Ioo (e + g) (f + h))) :
    IsOpen (separatingLocus T x y A B ∩ (Ioo a b ×ˢ Ioo e f)) := by
  let R : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo e f
  have hR : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hAC : ∀ t ∈ T, ContinuousOn (fun p : ℝ × ℝ => A (p.1 + x t)) R := by
    intro t ht
    apply hA.comp (continuous_fst.add continuous_const).continuousOn
    intro p hp
    exact ⟨by linarith [hp.1.1, (hx ht).1], by linarith [hp.1.2, (hx ht).2]⟩
  have hBC : ∀ t ∈ T, ContinuousOn (fun p : ℝ × ℝ => B (p.2 + y t)) R := by
    intro t ht
    apply hB.comp (continuous_snd.add continuous_const).continuousOn
    intro p hp
    exact ⟨by linarith [hp.2.1, (hy ht).1], by linarith [hp.2.2, (hy ht).2]⟩
  apply isOpen_iff_mem_nhds.mpr
  rintro p ⟨⟨t, ht, v, hv, hsep⟩, hp⟩
  let D : ℝ × ℝ → ℝ := fun q =>
    A (q.1 + x t) * B (q.2 + y v) - A (q.1 + x v) * B (q.2 + y t)
  have hD : ContinuousOn D R := ((hAC t ht).mul (hBC v hv)).sub ((hAC v hv).mul (hBC t ht))
  have hop : IsOpen (R ∩ D ⁻¹' ({0}ᶜ : Set ℝ)) :=
    hD.isOpen_inter_preimage hR isOpen_compl_singleton
  have hpn : R ∩ D ⁻¹' ({0}ᶜ : Set ℝ) ∈ nhds p := by
    apply hop.mem_nhds
    exact ⟨hp, sub_ne_zero.mpr hsep⟩
  apply Filter.mem_of_superset hpn
  rintro q ⟨hq, hDq⟩
  exact ⟨⟨t, ht, v, hv, sub_ne_zero.mp hDq⟩, hq⟩

/-- The receiver is nonaffine on every nonempty open subinterval. -/
def NoAffineInterval (D : Set ℝ) (ψ : ℝ → ℝ) : Prop :=
  ∀ l r : ℝ, l < r → Ioo l r ⊆ D →
    ¬ ∃ α β : ℝ, ∀ z ∈ Ioo l r, ψ z = α + β * z

/-- The manuscript's nowhere-affine condition implies that its receiver
derivative is not constant on any interval. -/
theorem noConstant_derivative_of_noAffine {D : Set ℝ} (ψ A : ℝ → ℝ)
    (hd : ∀ z ∈ D, HasDerivAt ψ (A z) z) (hna : NoAffineInterval D ψ) :
    NoConstantInterval D A := by
  intro l r hlr hsub hconst
  obtain ⟨C, hC⟩ := hconst
  let F : ℝ → ℝ := fun z => ψ z - C * z
  have hdF : ∀ z ∈ Ioo l r, HasDerivAt F 0 z := by
    intro z hz
    convert (hd z (hsub hz)).sub ((hasDerivAt_id z).const_mul C) using 1
    rw [hC z hz]
    simp
  have hdiff : DifferentiableOn ℝ F (Ioo l r) :=
    fun z hz => (hdF z hz).differentiableAt.differentiableWithinAt
  obtain ⟨q, hq⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff
    (fun z hz => (hdF z hz).deriv)
  apply hna l r hlr hsub
  refine ⟨q, C, ?_⟩
  intro z hz
  have hh := hq z hz
  dsimp [F] at hh
  linarith

/-- A nonconstant affine receiver has a nonzero constant derivative on its
open domain, hence satisfies the other derivative nonvanishing alternative. -/
theorem noZero_derivative_of_affine {D : Set ℝ} (hD : IsOpen D)
    (ψ : ℝ → ℝ) {α β : ℝ} (hβ : β ≠ 0)
    (haff : ∀ z ∈ D, ψ z = α + β * z) : NoZeroInterval D (deriv ψ) := by
  intro l r hlr hsub
  obtain ⟨z, hz⟩ := nonempty_Ioo.mpr hlr
  have hderiv : HasDerivAt ψ β z := by
    have hd : HasDerivAt (fun w : ℝ => α + β * w) β z := by
      simpa using ((hasDerivAt_id z).const_mul β).const_add α
    apply hd.congr_of_eventuallyEq
    filter_upwards [hD.mem_nhds (hsub hz)] with w hw
    exact haff w hw
  exact ⟨z, hz, by simpa only [hderiv.deriv] using hβ⟩

/-- Scaling the two prescribed features by a common nonzero factor retains
functional independence, as required by normalization by the node count. -/
theorem independent_div {T : Set ℝ} (x y : ℝ → ℝ) {K : ℝ} (hK : K ≠ 0)
    (hind : GeneralRigidity.NotInAffineLine T x y) :
    GeneralRigidity.NotInAffineLine T (fun t => x t / K) (fun t => y t / K) := by
  rintro ⟨A, B, C, hAB, heq⟩
  apply hind
  refine ⟨A / K, B / K, C, ?_, ?_⟩
  · exact hAB.elim (fun h => Or.inl (div_ne_zero h hK))
      (fun h => Or.inr (div_ne_zero h hK))
  · intro t ht
    convert heq t ht using 1
    ring

/-- Continuous nonconstant scalar features have nondegenerate closed
interval images, with every intermediate value actually attained. -/
theorem continuous_nonconstant_range {l r : ℝ} (hlr : l ≤ r) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Icc l r))
    (hn : ∃ s ∈ Icc l r, ∃ t ∈ Icc l r, F s ≠ F t) :
    ∃ c d : ℝ, c < d ∧ MapsTo F (Icc l r) (Icc c d) ∧
      ∀ q ∈ Icc c d, ∃ s ∈ Icc l r, F s = q := by
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hlr) hF
  obtain ⟨s₁, hs₁, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hlr) hF
  have hlt : F s₀ < F s₁ := by
    have hle := hmin hs₁
    by_contra hnot
    have heq := le_antisymm hle (le_of_not_gt hnot)
    obtain ⟨s, hs, t, ht, hst⟩ := hn
    have hss : F s = F s₀ := le_antisymm (by simpa only [← heq] using hmax hs) (hmin hs)
    have htt : F t = F s₀ := le_antisymm (by simpa only [← heq] using hmax ht) (hmin ht)
    exact hst (hss.trans htt.symm)
  refine ⟨F s₀, F s₁, hlt, (fun s hs => ⟨hmin hs, hmax hs⟩), ?_⟩
  intro q hq
  exact isPreconnected_Icc.intermediate_value hs₀ hs₁ hF hq

/-- The current functional independence assumption derives both actual
nondegenerate coordinate ranges needed by the dense-separation theorem. -/
theorem independent_coordinate_ranges {l r : ℝ} (hlr : l ≤ r) (x y : ℝ → ℝ)
    (hx : ContinuousOn x (Icc l r)) (hy : ContinuousOn y (Icc l r))
    (hind : GeneralRigidity.NotInAffineLine (Icc l r) x y) :
    ∃ c d g h : ℝ, c < d ∧ g < h ∧
      MapsTo x (Icc l r) (Icc c d) ∧ MapsTo y (Icc l r) (Icc g h) ∧
      (∀ q ∈ Icc c d, ∃ t ∈ Icc l r, x t = q) ∧
      (∀ q ∈ Icc g h, ∃ t ∈ Icc l r, y t = q) := by
  have hnx : ∃ s ∈ Icc l r, ∃ t ∈ Icc l r, x s ≠ x t := by
    by_contra hn
    push_neg at hn
    apply hind
    exact ⟨1, 0, x l, Or.inl one_ne_zero,
      fun t ht => by simpa using hn t ht l ⟨le_rfl, hlr⟩⟩
  have hny : ∃ s ∈ Icc l r, ∃ t ∈ Icc l r, y s ≠ y t := by
    by_contra hn
    push_neg at hn
    apply hind
    exact ⟨0, 1, y l, Or.inr one_ne_zero,
      fun t ht => by simpa using hn t ht l ⟨le_rfl, hlr⟩⟩
  obtain ⟨c, d, hcd, hmx, hsx⟩ := continuous_nonconstant_range hlr x hx hnx
  obtain ⟨g, h, hgh, hmy, hsy⟩ := continuous_nonconstant_range hlr y hy hny
  exact ⟨c, d, g, h, hcd, hgh, hmx, hmy, hsx, hsy⟩

/-- The nonconstant-affine/nowhere-affine alternative in the manuscript,
expressed with its nonzero affine slope. -/
def ReceiverAlternative (D : Set ℝ) (ψ : ℝ → ℝ) : Prop :=
  (∃ α β : ℝ, β ≠ 0 ∧ ∀ z ∈ D, ψ z = α + β * z) ∨ NoAffineInterval D ψ

/-- The receiver alternative derives the no-zero-interval hypothesis for
its actual derivative, including the nonconstant affine branch. -/
theorem receiver_derivative_noZeroInterval {D : Set ℝ} (hD : IsOpen D)
    (ψ A : ℝ → ℝ) (hd : ∀ z ∈ D, HasDerivAt ψ (A z) z)
    (halt : ReceiverAlternative D ψ) : NoZeroInterval D A := by
  rcases halt with ⟨α, β, hβ, haff⟩ | hna
  · have hn := noZero_derivative_of_affine hD ψ hβ haff
    intro l r hlr hsub
    obtain ⟨z, hz, hnz⟩ := hn l r hlr hsub
    exact ⟨z, hz, by simpa only [(hd z (hsub hz)).deriv] using hnz⟩
  · exact (noConstant_derivative_of_noAffine ψ A hd hna).noZeroInterval

/-- A nonconstant affine representation necessarily has nonzero slope. -/
theorem receiverAlternative_of_nonconstant {D : Set ℝ} (ψ : ℝ → ℝ)
    (hn : ∃ s ∈ D, ∃ t ∈ D, ψ s ≠ ψ t)
    (halt : (∃ α β : ℝ, ∀ z ∈ D, ψ z = α + β * z) ∨ NoAffineInterval D ψ) :
    ReceiverAlternative D ψ := by
  rcases halt with ⟨α, β, haff⟩ | hna
  · left
    refine ⟨α, β, ?_, haff⟩
    intro hβ
    obtain ⟨s, hs, t, ht, hst⟩ := hn
    apply hst
    simp only [haff s hs, haff t ht, hβ, zero_mul, add_zero]
  · exact Or.inr hna

/-- Dense open two-completion gradient separation from the receiver
alternatives used in the current theorem. The derivative nonvanishing and
nonconstancy conditions are derived, not assumed in this assembly. -/
theorem dense_open_separation_of_receiver_alternatives
    {a b c d e f g h : ℝ} (hcd : c < d) (hgh : g < h)
    (T : Set ℝ) (x y ψ₁ ψ₂ A B : ℝ → ℝ) {u : ℝ} (hu : u ∈ T)
    (hx : MapsTo x T (Icc c d)) (hy : MapsTo y T (Icc g h))
    (hsx : ∀ q ∈ Icc c d, ∃ t ∈ T, x t = q)
    (hsy : ∀ q ∈ Icc g h, ∃ t ∈ T, y t = q)
    (hA : ContinuousOn A (Ioo (a + c) (b + d)))
    (hB : ContinuousOn B (Ioo (e + g) (f + h)))
    (hdA : ∀ z ∈ Ioo (a + c) (b + d), HasDerivAt ψ₁ (A z) z)
    (hdB : ∀ z ∈ Ioo (e + g) (f + h), HasDerivAt ψ₂ (B z) z)
    (haltA : ReceiverAlternative (Ioo (a + c) (b + d)) ψ₁)
    (haltB : ReceiverAlternative (Ioo (e + g) (f + h)) ψ₂)
    (hna : NoAffineInterval (Ioo (a + c) (b + d)) ψ₁ ∨
      NoAffineInterval (Ioo (e + g) (f + h)) ψ₂)
    (hind : GeneralRigidity.NotInAffineLine T x y) :
    IsOpen (separatingLocus T x y A B ∩ (Ioo a b ×ˢ Ioo e f)) ∧
      Ioo a b ×ˢ Ioo e f ⊆
        closure (separatingLocus T x y A B ∩ (Ioo a b ×ˢ Ioo e f)) := by
  have hNA := receiver_derivative_noZeroInterval isOpen_Ioo ψ₁ A hdA haltA
  have hNB := receiver_derivative_noZeroInterval isOpen_Ioo ψ₂ B hdB haltB
  have hNC : NoConstantInterval (Ioo (a + c) (b + d)) A ∨
      NoConstantInterval (Ioo (e + g) (f + h)) B :=
    hna.elim (fun ha => Or.inl (noConstant_derivative_of_noAffine ψ₁ A hdA ha))
      (fun hb => Or.inr (noConstant_derivative_of_noAffine ψ₂ B hdB hb))
  exact ⟨separatingLocus_open T x y A B hx hy hA hB,
    separatingLocus_dense hcd hgh T x y A B hu hx hy hsx hsy hA hB hNA hNB hNC hind⟩

end Analog.CompletionSeparation
