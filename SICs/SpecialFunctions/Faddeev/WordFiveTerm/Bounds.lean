/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.FiveTerm.ParameterDomain
import SICs.SpecialFunctions.Faddeev.WordFiveTerm.Kernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Bounds for the five-term kernel along a letter word

The five-term kernel of a letter word has exponential bounds on its upper and lower vertical
tails, uniformly for complex periods near a real period with positive word periods, and it is
integrable along regular vertical lines at that real period under the strict convergence
conditions.

This module supplies the tail bounds behind the convergence of [RW26, Radchenko, Wheeler (2026),
Theorem 3, `thm:5term.mod.fad`, equation (23), `eq:5term.int`], for the word product of
equation (20), `eq:modulartofaddeevCF`, through the asymptotics of Lemma 1, `lem:asymp`, in
`SICs.SpecialFunctions.Faddeev.WordAsymptotics`.

## The argument

On an upper vertical tail `z = x+it`, `t → ∞`, both word products tend to one uniformly near
`τ₀`, so their ratio is bounded, and the phase exponential has modulus
`exp(-2π Im((cw/ε+ℓ)z) + O(1))`, whose slope at `τ₀` is the upper rate `λ = cw/ε+ℓ`. On a lower
tail, divide each word product by its reflection asymptote
`(-1)^{m+n} e(Q_{γ,-m,-n}(-z,τ)) κ_γ`; the normalized products tend to one. The quadratic terms
of the two exponents `Q_{γ,-m-1,0}(-z,τ)` and `Q_{γ,-m-p,0}(-z-y,τ)` are equal, so the remaining
exponential is affine in `z`, and at `τ₀` its vertical slope is the lower rate
`μ = c(w+y)/ε+ℓ+p-1`. Continuity of the affine coefficients in `τ` keeps strict decay rates
in a neighborhood. Along a vertical line whose crossing and its translate by `y` avoid
`ℤ+ℤτ₀`, the kernel at `τ₀` is continuous, and the two tail majorants make it integrable.

As in `SICs.SpecialFunctions.Faddeev.FiveTerm.Bounds`, the lower rate retains the term `p` that
the printed convergence condition of Theorem 3 omits.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology MatrixGroups

namespace SIC

/-! ### Affine phases of the word kernel -/

/-- The exponential phase of the word kernel; used by the kernel and residue tail estimates. -/
def fiveTermWordPhase (bs : List ℤ) (ℓ : ℤ) (w : ℂ) (m : ℤ)
    (z τ : ℂ) : ℂ :=
  2 * Real.pi * I *
    ((((letterWord bs 1 0 : ℤ) : ℂ) * z +
        fltDenominator (letterWord bs : Mat(2, ℤ)) τ * m) * w /
      fltDenominator (letterWord bs : Mat(2, ℤ)) τ + ℓ * (z + m * τ))

/-- The coefficient of the argument in the word kernel phase, used by the residue bounds. -/
private def fiveTermWordPhaseCoeff (bs : List ℤ) (ℓ : ℤ) (w τ : ℂ) : ℂ :=
  2 * Real.pi * I *
    (((letterWord bs 1 0 : ℤ) : ℂ) * w /
      fltDenominator (letterWord bs : Mat(2, ℤ)) τ + ℓ)

/-- The reflected phase after normalizing both word products on the lower tail, also used by the
residue bounds. -/
def fiveTermWordReflectedPhase (bs : List ℤ) (ℓ p m : ℤ)
    (w y z τ : ℂ) : ℂ :=
  2 * Real.pi * I *
      (faddeevReflectionExponent (letterWord bs) (-(m + 1)) 0 (-z) τ -
        faddeevReflectionExponent (letterWord bs) (-(m + p)) 0 (-(z + y)) τ) +
    fiveTermWordPhase bs ℓ w m z τ

/-- The coefficient of the argument in the reflected word kernel phase, used by the residue
bounds. -/
private def fiveTermWordReflectedPhaseCoeff (bs : List ℤ) (ℓ p : ℤ)
    (w y τ : ℂ) : ℂ :=
  2 * Real.pi * I *
    (((letterWord bs 1 0 : ℤ) : ℂ) * (w + y) /
      fltDenominator (letterWord bs : Mat(2, ℤ)) τ + ℓ + p - 1)

/-- The word kernel phase is affine in its argument; used by the residue bounds. -/
lemma fiveTermWordPhase_eq_affine (bs : List ℤ) (ℓ m : ℤ)
    (w z τ : ℂ) :
    fiveTermWordPhase bs ℓ w m z τ =
      fiveTermWordPhaseCoeff bs ℓ w τ * z + fiveTermWordPhase bs ℓ w m 0 τ := by
  simp only [fiveTermWordPhase, fiveTermWordPhaseCoeff]
  ring

/-- The two reflection quadratics cancel, leaving the lower-rate coefficient; used by the residue
bounds. -/
lemma fiveTermWordReflectedPhase_eq_affine (bs : List ℤ) (ℓ p m : ℤ)
    (w y z τ : ℂ) :
    fiveTermWordReflectedPhase bs ℓ p m w y z τ =
      fiveTermWordReflectedPhaseCoeff bs ℓ p w y τ * z +
        fiveTermWordReflectedPhase bs ℓ p m w y 0 τ := by
  simp only [fiveTermWordReflectedPhase, fiveTermWordReflectedPhaseCoeff,
    fiveTermWordPhase, faddeevReflectionExponent]
  push_cast
  ring

/-- The word Jacobi denominator stays nonzero at the real period of the bound. -/
private lemma fiveTermWordDenominator_ne_zero (bs : List ℤ)
    {τ₀ : ℝ} (hτ₀ : FaddeevWordPeriodsPos bs τ₀) :
    fltDenominator (letterWord bs : Mat(2, ℤ)) (τ₀ : ℂ) ≠ 0 := by
  by_cases hbs : bs = []
  · subst bs
    simp [letterWord, fltDenominator]
  have h := hτ₀.fltDenominator_pos hbs
  have hc : (fltDenominator (letterWord bs : Mat(2, ℤ)) τ₀ : ℂ) ≠ 0 := by
    exact_mod_cast h.ne'
  simpa [fltDenominator] using hc

/-- The upper affine coefficient at the real period is `2πiλ`; used by the residue bounds. -/
lemma fiveTermWordPhaseCoeff_atReal (bs : List ℤ) (ℓ : ℤ)
    (w τ₀ : ℝ) :
    fiveTermWordPhaseCoeff bs ℓ w τ₀ =
      2 * Real.pi * I * (fiveTermUpperRate (letterWord bs) ℓ w τ₀ : ℂ) := by
  simp only [fiveTermWordPhaseCoeff, fiveTermUpperRate]
  congr 1
  norm_cast

/-- The reflected affine coefficient at the real period is `2πiμ`; used by the residue bounds. -/
lemma fiveTermWordReflectedPhaseCoeff_atReal (bs : List ℤ) (ℓ p : ℤ)
    (w y τ₀ : ℝ) :
    fiveTermWordReflectedPhaseCoeff bs ℓ p w y τ₀ =
      2 * Real.pi * I * (fiveTermLowerRate (letterWord bs) ℓ p w y τ₀ : ℂ) := by
  simp only [fiveTermWordReflectedPhaseCoeff, fiveTermLowerRate]
  congr 1
  norm_cast

/-- The upper affine coefficient is continuous at the real word period. -/
private lemma continuousAt_fiveTermWordPhaseCoeff (bs : List ℤ)
    {τ₀ : ℝ} (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ : ℤ) (w : ℂ) :
    ContinuousAt (fiveTermWordPhaseCoeff bs ℓ w) (τ₀ : ℂ) := by
  have hJ := fiveTermWordDenominator_ne_zero bs hτ₀
  unfold fiveTermWordPhaseCoeff fltDenominator at hJ ⊢
  fun_prop

/-- The reflected affine coefficient is continuous at the real word period. -/
private lemma continuousAt_fiveTermWordReflectedPhaseCoeff (bs : List ℤ)
    {τ₀ : ℝ} (hτ₀ : FaddeevWordPeriodsPos bs τ₀)
    (ℓ p : ℤ) (w y : ℂ) :
    ContinuousAt (fiveTermWordReflectedPhaseCoeff bs ℓ p w y) (τ₀ : ℂ) := by
  have hJ := fiveTermWordDenominator_ne_zero bs hτ₀
  unfold fiveTermWordReflectedPhaseCoeff fltDenominator at hJ ⊢
  fun_prop

/-- The upper affine intercept is continuous at the real word period. -/
private lemma continuousAt_fiveTermWordPhase_zero (bs : List ℤ)
    {τ₀ : ℝ} (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ m : ℤ) (w : ℂ) :
    ContinuousAt (fun τ : ℂ => fiveTermWordPhase bs ℓ w m 0 τ) (τ₀ : ℂ) := by
  have hJ := fiveTermWordDenominator_ne_zero bs hτ₀
  unfold fiveTermWordPhase fltDenominator at hJ ⊢
  fun_prop

/-- The reflected affine intercept is continuous at the real word period. -/
private lemma continuousAt_fiveTermWordReflectedPhase_zero (bs : List ℤ)
    {τ₀ : ℝ} (hτ₀ : FaddeevWordPeriodsPos bs τ₀)
    (ℓ p m : ℤ) (w y : ℂ) :
    ContinuousAt (fun τ : ℂ => fiveTermWordReflectedPhase bs ℓ p m w y 0 τ)
      (τ₀ : ℂ) := by
  have hJ := fiveTermWordDenominator_ne_zero bs hτ₀
  unfold fiveTermWordReflectedPhase faddeevReflectionExponent fiveTermWordPhase flt
  unfold fltDenominator at hJ ⊢
  fun_prop

/-- The upper kernel phase decays uniformly on nearby upper vertical rays. -/
private lemma exists_norm_exp_fiveTermWordPhase_le (bs : List ℤ) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ m : ℤ) (w x : ℝ)
    (hRate : 0 < fiveTermUpperRate (letterWord bs) ℓ w τ₀) :
    ∃ ε C κ : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧
      ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → ∀ t : ℝ, 0 ≤ t →
        ‖Complex.exp (fiveTermWordPhase bs ℓ w m ((x : ℂ) + t * I) τ)‖ ≤
          C * Real.exp (-κ * t) := by
  have hIm : 0 < (fiveTermWordPhaseCoeff bs ℓ w (τ₀ : ℂ)).im := by
    rw [fiveTermWordPhaseCoeff_atReal]
    simp [Complex.mul_im]
    nlinarith [Real.pi_pos]
  obtain ⟨ε, C, κ, hε, hC, hκ, hbound⟩ :=
    exists_norm_exp_affine_vertical_le
      (continuousAt_fiveTermWordPhaseCoeff bs hτ₀ ℓ w)
      (continuousAt_fiveTermWordPhase_zero bs hτ₀ ℓ m w) hIm x
  refine ⟨ε, C, κ, hε, hC, hκ, fun τ hτ t ht => ?_⟩
  rw [fiveTermWordPhase_eq_affine]
  exact hbound τ hτ t ht

/-- The reflected kernel phase decays uniformly on nearby lower vertical rays. -/
private lemma exists_norm_exp_fiveTermWordReflectedPhase_le (bs : List ℤ)
    {τ₀ : ℝ} (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p m : ℤ)
    (w y x : ℝ) (hRate : fiveTermLowerRate (letterWord bs) ℓ p w y τ₀ < 0) :
    ∃ ε C κ : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧
      ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → ∀ t : ℝ, t ≤ 0 →
        ‖Complex.exp (fiveTermWordReflectedPhase bs ℓ p m w y
          ((x : ℂ) + t * I) τ)‖ ≤ C * Real.exp (κ * t) := by
  have hIm : (fiveTermWordReflectedPhaseCoeff bs ℓ p w y (τ₀ : ℂ)).im < 0 := by
    rw [fiveTermWordReflectedPhaseCoeff_atReal]
    simp [Complex.mul_im]
    nlinarith [Real.pi_pos]
  obtain ⟨ε, C, κ, hε, hC, hκ, hbound⟩ :=
    exists_norm_exp_affine_vertical_le_of_im_neg
      (continuousAt_fiveTermWordReflectedPhaseCoeff bs hτ₀ ℓ p w y)
      (continuousAt_fiveTermWordReflectedPhase_zero bs hτ₀ ℓ p m w y) hIm x
  refine ⟨ε, C, κ, hε, hC, hκ, fun τ hτ t ht => ?_⟩
  rw [fiveTermWordReflectedPhase_eq_affine]
  exact hbound τ hτ t ht

/-! ### Uniform tail bounds near a real period -/

/-- The exact lower reflection asymptote for one word product in the kernel and residue bounds. -/
def fiveTermWordReflectionFactor (bs : List ℤ) (k : ℤ) (z τ : ℂ) : ℂ :=
  (-1 : ℂ) ^ k * Complex.exp (2 * Real.pi * I *
      faddeevReflectionExponent (letterWord bs) (-k) 0 (-z) τ) *
    Complex.exp (-(Real.pi : ℂ) * I *
      (((bs.sum : ℤ) : ℂ) - 3 * bs.length) / 6)

/-- The reflection asymptote never vanishes. -/
private lemma fiveTermWordReflectionFactor_ne_zero (bs : List ℤ) (k : ℤ)
    (z τ : ℂ) : fiveTermWordReflectionFactor bs k z τ ≠ 0 := by
  unfold fiveTermWordReflectionFactor
  exact mul_ne_zero (mul_ne_zero (zpow_ne_zero k (by norm_num))
    (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)

/-- A normalized word product approaches one on the selected sector. -/
private lemma exists_norm_fiveTermWord_normalized_sub_one_le
    (bs : List ℤ) (lower : Bool) (hbs : lower = true → bs ≠ []) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (k : ℤ) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ τ z : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε →
        |z.re| ≤ K * (if lower then -z.im else z.im) →
        R ≤ (if lower then -z.im else z.im) →
        ‖(if lower then faddeevWord bs k 0 z τ /
            fiveTermWordReflectionFactor bs k z τ
          else faddeevWord bs k 0 z τ) - 1‖ ≤
            C * Real.exp (-κ * (if lower then -z.im else z.im)) := by
  cases lower with
  | false =>
      simpa using exists_norm_faddeevWord_sub_one_le bs hτ₀ k 0 K
  | true =>
      simpa [fiveTermWordReflectionFactor] using
        exists_norm_faddeevWord_div_reflection_sub_one_le bs (hbs rfl) hτ₀ k 0 K

/-- Both normalized word products have a bounded quotient in a remote sector. -/
private lemma exists_norm_fiveTermWord_ratio_sector
    (bs : List ℤ) (lower : Bool) (hbs : lower = true → bs ≠ []) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (p m : ℤ) (y K : ℝ) :
    ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → ∀ z : ℂ,
        |z.re| ≤ K * (if lower then -z.im else z.im) →
        R ≤ (if lower then -z.im else z.im) →
        ‖(if lower then faddeevWord bs (m + 1) 0 z τ /
              fiveTermWordReflectionFactor bs (m + 1) z τ
            else faddeevWord bs (m + 1) 0 z τ) /
          (if lower then faddeevWord bs (m + p) 0 (z + y) τ /
              fiveTermWordReflectionFactor bs (m + p) (z + y) τ
            else faddeevWord bs (m + p) 0 (z + y) τ)‖ ≤ 3 := by
  let K' := max K 0 + |y|
  obtain ⟨ε₁, C₁, κ₁, R₁, hε₁, _, hκ₁, _, h₁⟩ :=
    exists_norm_fiveTermWord_normalized_sub_one_le bs lower hbs hτ₀ (m + 1) K'
  obtain ⟨ε₂, C₂, κ₂, R₂, hε₂, _, hκ₂, _, h₂⟩ :=
    exists_norm_fiveTermWord_normalized_sub_one_le bs lower hbs hτ₀ (m + p) K'
  let R := max 1 (max R₁ (max R₂ (max (2 * C₁ / κ₁) (2 * C₂ / κ₂))))
  let ε := min ε₁ ε₂
  refine ⟨ε, R, lt_min hε₁ hε₂,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun τ hτ z hz ht => ?_⟩
  let s := if lower then -z.im else z.im
  have hs : 1 ≤ s := (le_max_left _ _).trans ht
  have hle (a : ℝ) (ha : a ≤ R) : a ≤ s := ha.trans ht
  have hsShift : (if lower then -(z + y).im else (z + y).im) = s := by
    simp [s]
  have h₁' := h₁ τ z (hτ.trans (by simp [ε]))
    (abs_re_le_widened_sector z y K s (zero_le_one.trans hs) hz)
    (hle R₁ (by simp [R]))
  have h₂' := h₂ τ (z + y) (hτ.trans (by simp [ε]))
    (by rw [hsShift]; exact abs_re_add_ofReal_le_widened_sector z y K s hs hz)
    (by rw [hsShift]; exact hle R₂ (by simp [R]))
  have hC₁ : 2 * C₁ ≤ κ₁ * s := by
    have h := (div_le_iff₀ hκ₁).mp (hle (2 * C₁ / κ₁) (by simp [R]))
    nlinarith
  have hC₂ : 2 * C₂ ≤ κ₂ * s := by
    have h := (div_le_iff₀ hκ₂).mp (hle (2 * C₂ / κ₂) (by simp [R]))
    nlinarith
  apply norm_div_le_three_of_exponential_bounds _ _ hC₁ hC₂
  · exact h₁'
  · simpa only [hsShift] using h₂'

/-- The quotient of word products is uniformly bounded in a sufficiently high sector. -/
lemma exists_norm_fiveTermWord_ratio_upper_sector (bs : List ℤ) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (p m : ℤ) (y K : ℝ) :
    ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → ∀ z : ℂ, |z.re| ≤ K * z.im → R ≤ z.im →
      ‖faddeevWord bs (m + 1) 0 z τ /
        faddeevWord bs (m + p) 0 (z + y) τ‖ ≤ 3 := by
  simpa using exists_norm_fiveTermWord_ratio_sector bs false (by simp) hτ₀ p m y K

/-- The quotient of reflection-normalized products is bounded in a sufficiently low sector. -/
lemma exists_norm_fiveTermWord_ratio_lower_sector (bs : List ℤ) (hbs : bs ≠ []) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (p m : ℤ) (y K : ℝ) :
    ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → ∀ z : ℂ, |z.re| ≤ K * -z.im → R ≤ -z.im →
      ‖(faddeevWord bs (m + 1) 0 z τ /
          fiveTermWordReflectionFactor bs (m + 1) z τ) /
        (faddeevWord bs (m + p) 0 (z + y) τ /
          fiveTermWordReflectionFactor bs (m + p) (z + y) τ)‖ ≤ 3 := by
  simpa using exists_norm_fiveTermWord_ratio_sector bs true (by simpa) hτ₀ p m y K

/-- The sector ratio bound on a fixed vertical line, for either tail. -/
private lemma exists_norm_fiveTermWord_ratio_vertical
    (bs : List ℤ) (lower : Bool) (hbs : lower = true → bs ≠ []) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (p m : ℤ) (y x : ℝ) :
    ∃ ε T : ℝ, 0 < ε ∧ 0 < T ∧
      ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → ∀ t : ℝ,
        (if lower then t ≤ -T else T ≤ t) →
        ‖(if lower then faddeevWord bs (m + 1) 0 ((x : ℂ) + t * I) τ /
              fiveTermWordReflectionFactor bs (m + 1) ((x : ℂ) + t * I) τ
            else faddeevWord bs (m + 1) 0 ((x : ℂ) + t * I) τ) /
          (if lower then faddeevWord bs (m + p) 0 (((x : ℂ) + t * I) + y) τ /
              fiveTermWordReflectionFactor bs (m + p) (((x : ℂ) + t * I) + y) τ
            else faddeevWord bs (m + p) 0 (((x : ℂ) + t * I) + y) τ)‖ ≤ 3 := by
  obtain ⟨ε, R, hε, hR, hbound⟩ :=
    exists_norm_fiveTermWord_ratio_sector bs lower hbs hτ₀ p m y 1
  refine ⟨ε, max R |x|, hε, lt_of_lt_of_le hR (le_max_left _ _),
    fun τ hτ t ht => ?_⟩
  have hs : |x| ≤ (if lower then -t else t) := by
    cases lower <;> dsimp at ht ⊢
    all_goals linarith [le_max_right R |x|]
  have hR' : R ≤ (if lower then -t else t) := by
    cases lower <;> dsimp at ht ⊢
    all_goals linarith [le_max_left R |x|]
  apply hbound τ hτ _
  · simpa using hs
  · simpa using hR'

/-- The upper sector ratio bound on a vertical line. -/
private lemma exists_norm_fiveTermWord_ratio_upper (bs : List ℤ) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (p m : ℤ) (y x : ℝ) :
    ∃ ε T : ℝ, 0 < ε ∧ 0 < T ∧
      ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → ∀ t : ℝ, T ≤ t →
        ‖faddeevWord bs (m + 1) 0 ((x : ℂ) + t * I) τ /
          faddeevWord bs (m + p) 0 (((x : ℂ) + t * I) + y) τ‖ ≤ 3 := by
  simpa using exists_norm_fiveTermWord_ratio_vertical bs false (by simp) hτ₀ p m y x

/-- The lower sector ratio bound on a vertical line. -/
private lemma exists_norm_fiveTermWord_ratio_lower (bs : List ℤ) (hbs : bs ≠ [])
    {τ₀ : ℝ} (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (p m : ℤ) (y x : ℝ) :
    ∃ ε T : ℝ, 0 < ε ∧ 0 < T ∧
      ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → ∀ t : ℝ, t ≤ -T →
        ‖(faddeevWord bs (m + 1) 0 ((x : ℂ) + t * I) τ /
            fiveTermWordReflectionFactor bs (m + 1) ((x : ℂ) + t * I) τ) /
          (faddeevWord bs (m + p) 0 (((x : ℂ) + t * I) + y) τ /
            fiveTermWordReflectionFactor bs (m + p) (((x : ℂ) + t * I) + y) τ)‖ ≤ 3 := by
  simpa using exists_norm_fiveTermWord_ratio_vertical bs true (by simpa) hτ₀ p m y x

/-- The lower normalization separates the bounded word ratio from its exact phase, also for
the residue kernel bounds. -/
lemma fiveTermWordKernel_eq_lower_normalized (bs : List ℤ) (ℓ p m : ℤ)
    (w y τ z : ℂ) :
    fiveTermWordKernel bs ℓ p w y τ m z =
      (faddeevWord bs (m + 1) 0 z τ /
          fiveTermWordReflectionFactor bs (m + 1) z τ) /
        (faddeevWord bs (m + p) 0 (z + y) τ /
          fiveTermWordReflectionFactor bs (m + p) (z + y) τ) *
        (fiveTermWordReflectionFactor bs (m + 1) z τ /
          fiveTermWordReflectionFactor bs (m + p) (z + y) τ *
          Complex.exp (fiveTermWordPhase bs ℓ w m z τ)) := by
  let N := faddeevWord bs (m + 1) 0 z τ
  let D := faddeevWord bs (m + p) 0 (z + y) τ
  let A := fiveTermWordReflectionFactor bs (m + 1) z τ
  let B := fiveTermWordReflectionFactor bs (m + p) (z + y) τ
  let P := Complex.exp (fiveTermWordPhase bs ℓ w m z τ)
  change N / D * P = (N / A) / (D / B) * ((A / B) * P)
  rw [div_div_div_comm, ← mul_assoc,
    div_mul_cancel₀ _ (div_ne_zero
      (fiveTermWordReflectionFactor_ne_zero bs (m + 1) z τ)
      (fiveTermWordReflectionFactor_ne_zero bs (m + p) (z + y) τ))]

/-- The quotient of reflection asymptotes contributes the reflected phase in norm, also in the
residue bounds. -/
lemma norm_fiveTermWord_reflection_phase (bs : List ℤ) (ℓ p m : ℤ)
    (w y τ z : ℂ) :
    ‖fiveTermWordReflectionFactor bs (m + 1) z τ /
        fiveTermWordReflectionFactor bs (m + p) (z + y) τ *
        Complex.exp (fiveTermWordPhase bs ℓ w m z τ)‖ =
      ‖Complex.exp (fiveTermWordReflectedPhase bs ℓ p m w y z τ)‖ := by
  let E₁ := 2 * Real.pi * I *
    faddeevReflectionExponent (letterWord bs) (-(m + 1)) 0 (-z) τ
  let E₂ := 2 * Real.pi * I *
    faddeevReflectionExponent (letterWord bs) (-(m + p)) 0 (-(z + y)) τ
  let K := Complex.exp (-(Real.pi : ℂ) * I *
    (((bs.sum : ℤ) : ℂ) - 3 * bs.length) / 6)
  have hK : K ≠ 0 := Complex.exp_ne_zero _
  have hE₂ : Complex.exp E₂ ≠ 0 := Complex.exp_ne_zero _
  have hS₂ : (-1 : ℂ) ^ (m + p) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hfact :
      fiveTermWordReflectionFactor bs (m + 1) z τ /
          fiveTermWordReflectionFactor bs (m + p) (z + y) τ =
        (((-1 : ℂ) ^ (m + 1)) / ((-1 : ℂ) ^ (m + p))) *
          (Complex.exp E₁ / Complex.exp E₂) := by
    change (((-1 : ℂ) ^ (m + 1)) * Complex.exp E₁ * K) /
        (((-1 : ℂ) ^ (m + p)) * Complex.exp E₂ * K) = _
    field_simp [hK, hE₂, hS₂]
  rw [hfact, fiveTermWordReflectedPhase,
    show 2 * Real.pi * I *
      (faddeevReflectionExponent (letterWord bs) (-(m + 1)) 0 (-z) τ -
        faddeevReflectionExponent (letterWord bs) (-(m + p)) 0 (-(z + y)) τ) +
        fiveTermWordPhase bs ℓ w m z τ =
        E₁ - E₂ + fiveTermWordPhase bs ℓ w m z τ by dsimp [E₁, E₂]; ring,
    Complex.exp_add, Complex.exp_sub]
  simp [mul_assoc]


/-- Uniformly for complex periods near a real period with positive word periods, the five-term
kernel of a letter word decays exponentially on the upper tail of every vertical line when the
upper rate `λ = cw/ε+ℓ` at `τ₀` is positive. -/
theorem exists_norm_fiveTermWordKernel_upper (bs : List ℤ) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p m : ℤ) (w y x : ℝ)
    (hRate : 0 < fiveTermUpperRate (letterWord bs) ℓ w τ₀) :
    ∃ ε C κ T : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < T ∧
      ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → ∀ t : ℝ, T ≤ t →
        ‖fiveTermWordKernel bs ℓ p w y τ m ((x : ℂ) + t * I)‖ ≤ C * Real.exp (-κ * t) := by
  obtain ⟨ε₁, T, hε₁, hT, hratio⟩ :=
    exists_norm_fiveTermWord_ratio_upper bs hτ₀ p m y x
  obtain ⟨ε₂, C, κ, hε₂, hC, hκ, hphase⟩ :=
    exists_norm_exp_fiveTermWordPhase_le bs hτ₀ ℓ m w x hRate
  let ε := min ε₁ ε₂
  refine ⟨ε, 3 * C, κ, T, lt_min hε₁ hε₂, mul_pos (by norm_num) hC, hκ, hT,
    fun τ hτ t ht => ?_⟩
  have hratio' := hratio τ (hτ.trans (by simp [ε])) t ht
  have hphase' := hphase τ (hτ.trans (by simp [ε])) t (hT.le.trans ht)
  change ‖faddeevWord bs (m + 1) 0 ((x : ℂ) + t * I) τ /
      faddeevWord bs (m + p) 0 (((x : ℂ) + t * I) + y) τ *
        Complex.exp (fiveTermWordPhase bs ℓ w m ((x : ℂ) + t * I) τ)‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ 3 * (C * Real.exp (-κ * t)) :=
      mul_le_mul hratio' hphase' (norm_nonneg _) (by norm_num)
    _ = (3 * C) * Real.exp (-κ * t) := by ring

/-- Uniformly for complex periods near a real period with positive word periods, the five-term
kernel of a nonempty letter word decays exponentially on the lower tail of every vertical line
when the lower rate `μ = c(w+y)/ε+ℓ+p-1` at `τ₀` is negative. -/
theorem exists_norm_fiveTermWordKernel_lower (bs : List ℤ) (hbs : bs ≠ []) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p m : ℤ) (w y x : ℝ)
    (hRate : fiveTermLowerRate (letterWord bs) ℓ p w y τ₀ < 0) :
    ∃ ε C κ T : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < T ∧
      ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → ∀ t : ℝ, t ≤ -T →
        ‖fiveTermWordKernel bs ℓ p w y τ m ((x : ℂ) + t * I)‖ ≤ C * Real.exp (κ * t) := by
  obtain ⟨ε₁, T, hε₁, hT, hratio⟩ :=
    exists_norm_fiveTermWord_ratio_lower bs hbs hτ₀ p m y x
  obtain ⟨ε₂, C, κ, hε₂, hC, hκ, hphase⟩ :=
    exists_norm_exp_fiveTermWordReflectedPhase_le bs hτ₀ ℓ p m w y x hRate
  let ε := min ε₁ ε₂
  refine ⟨ε, 3 * C, κ, T, lt_min hε₁ hε₂, mul_pos (by norm_num) hC, hκ, hT,
    fun τ hτ t ht => ?_⟩
  have hratio' := hratio τ (hτ.trans (by simp [ε])) t ht
  have hphase' := hphase τ (hτ.trans (by simp [ε])) t
    (ht.trans (neg_nonpos.mpr hT.le))
  rw [fiveTermWordKernel_eq_lower_normalized, norm_mul,
    norm_fiveTermWord_reflection_phase]
  calc
    _ ≤ 3 * (C * Real.exp (κ * t)) :=
      mul_le_mul hratio' hphase' (norm_nonneg _) (by norm_num)
    _ = (3 * C) * Real.exp (κ * t) := by ring

/-! ### Integrability at the real period -/

/-- The word kernel is continuous on a vertical line with regular crossings. -/
private lemma continuous_fiveTermWordKernel_vertical (bs : List ℤ) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p m : ℤ) (w y x : ℝ)
    (hx : IsRegularPeriodLatticeCrossing τ₀ y x) :
    Continuous (fun t : ℝ => fiveTermWordKernel bs ℓ p w y τ₀ m ((x : ℂ) + t * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have h := continuousAt_fiveTermWordKernel_vertical bs hτ₀ ℓ p m w y x t hx
  have harg : ContinuousAt (fun s : ℝ => (s, (τ₀ : ℂ))) t := by fun_prop
  simpa only [Function.comp_def] using h.comp_of_eq harg rfl

/-- At a real period with positive word periods, the five-term kernel of a nonempty letter word
is integrable along a vertical line whose crossing `x` and its translate `x+y` avoid `ℤ+ℤτ₀`,
under the strict convergence conditions `0 < λ` and `μ < 0`. -/
theorem integrable_fiveTermWordKernel (bs : List ℤ) (hbs : bs ≠ []) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p m : ℤ) (w y x : ℝ)
    (hx : IsRegularPeriodLatticeCrossing τ₀ y x)
    (hupper : 0 < fiveTermUpperRate (letterWord bs) ℓ w τ₀)
    (hlower : fiveTermLowerRate (letterWord bs) ℓ p w y τ₀ < 0) :
    Integrable (fun t : ℝ => fiveTermWordKernel bs ℓ p w y τ₀ m ((x : ℂ) + t * I)) := by
  let f : ℝ → ℂ := fun t => fiveTermWordKernel bs ℓ p w y τ₀ m ((x : ℂ) + t * I)
  have hf : Continuous f := continuous_fiveTermWordKernel_vertical bs hτ₀ ℓ p m w y x hx
  obtain ⟨ε₁, C₁, κ₁, T₁, hε₁, _, hκ₁, _, hbound₁⟩ :=
    exists_norm_fiveTermWordKernel_upper bs hτ₀ ℓ p m w y x hupper
  obtain ⟨ε₂, C₂, κ₂, T₂, hε₂, _, hκ₂, _, hbound₂⟩ :=
    exists_norm_fiveTermWordKernel_lower bs hbs hτ₀ ℓ p m w y x hlower
  have hupperT : IntegrableOn f (Ioi T₁) := by
    apply Integrable.mono' ((integrableOn_exp_mul_Ioi
      (by linarith : -κ₁ < 0) T₁).const_mul C₁) hf.aestronglyMeasurable
    exact (ae_restrict_mem measurableSet_Ioi).mono (fun t ht =>
      hbound₁ τ₀ (by simp [hε₁.le]) t ht.le)
  have hlowerT : IntegrableOn f (Iio (-T₂)) := by
    have hi : IntegrableOn (fun t : ℝ => C₂ * Real.exp (κ₂ * t))
        (Iic (-T₂)) := (integrableOn_exp_mul_Iic hκ₂ (-T₂)).const_mul C₂
    apply Integrable.mono' (hi.mono_set Iio_subset_Iic_self) hf.aestronglyMeasurable
    exact (ae_restrict_mem measurableSet_Iio).mono (fun t ht =>
      hbound₂ τ₀ (by simp [hε₂.le]) t ht.le)
  let a := min (-T₂) T₁
  let b := max (-T₂) T₁
  have ha : IntegrableOn f (Iio a) :=
    hlowerT.mono_set (Iio_subset_Iio (min_le_left _ _))
  have hb : IntegrableOn f (Ioi b) :=
    hupperT.mono_set (Ioi_subset_Ioi (le_max_right _ _))
  have hm : IntegrableOn f (Icc a b) := hf.continuousOn.integrableOn_Icc
  have hab : a ≤ b := (min_le_left _ _).trans (le_max_left _ _)
  change Integrable f
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := b),
    ← Set.Iio_union_Icc_eq_Iic hab]
  exact (ha.union hm).union hb

end SIC

end
