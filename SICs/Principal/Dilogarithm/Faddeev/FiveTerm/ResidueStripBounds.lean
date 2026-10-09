/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.Telescoping
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ComplexBounds

/-!
# Growth of the principal residue kernel

Exponential bounds for the residue kernel on vertical tails and on horizontal segments, and
integrability of the residue sum on vertical lines.

This module follows the convergence remarks in [RW26, Radchenko, Wheeler (2026), Section 3.1,
the proof of Theorem 4, `thm:fn.equs`, "to compute the residue we need to assume not just that
`0 < w` but that `0 < w - ε`"], at `γ = A_d`, `τ = ρ_d`, `ε = ρ_d³ > 1`, and Theorem 3,
`thm:5term.mod.fad`.

## The argument

The residue kernel is the five-term kernel times `(1 - q^m e(z))/(e(z/ε) - q^m e(z))`. As
`Im z → +∞` the pole factor is dominated by `e(z/ε)`, whose modulus decays more slowly than
`e(z)`, so the factor grows like `e^{2π Im z/ε}`: the upper decay rate is `λ - 1/ε`, where `λ` is
the five-term upper rate. As `Im z → -∞` both terms grow like `e(z)` and the factor is bounded, so
the lower rate `μ` is unchanged. The five-term kernel's sector bounds
(`exists_norm_principalFaddeev_sub_one_le` and the lower normalized bound) are uniform in
the real part, and the phases depend on the real part only through a modulus-one factor, so the
bounds hold uniformly on horizontal segments of a strip. Integrability on a vertical line then
follows from the two tails and continuity on the compact middle, which needs the crossing and its
translate by `y` to avoid the period lattice and the kernel poles.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology MatrixGroups

namespace SIC

/-! ### The pole factor on vertical tails

The two exponentials in the pole factor have moduli `exp(-2π Im z/ε)` and `exp(-2π Im z)`. -/

/-- The slower pole-factor exponential has modulus `exp(-2π Im z/ρ_d³)`. -/
private lemma norm_principalFiveTermPoleFactor_slow_term (d : ℕ) (z : ℂ) :
    ‖Complex.exp (2 * Real.pi * I * (z / (principalRoot d : ℂ) ^ 3))‖ =
      Real.exp (-2 * Real.pi * z.im / principalRoot d ^ 3) := by
  rw [norm_exp_two_pi_I_mul, ← Complex.ofReal_pow, Complex.div_ofReal_im]
  congr 1
  ring

/-- The faster pole-factor exponential has modulus `exp(-2π Im z)`. -/
private lemma norm_principalFiveTermPoleFactor_fast_term (d : ℕ) (m : ℤ) (z : ℂ) :
    ‖Complex.exp (2 * Real.pi * I * (z + m * (principalRoot d : ℂ)))‖ =
      Real.exp (-2 * Real.pi * z.im) := by
  rw [norm_exp_two_pi_I_mul]
  simp [Complex.add_im, Complex.mul_im]

/-- For `Im z ≥ T`, the modulus of the pole factor is at least half of `exp(-2π Im z/ε)`, and the
factor `(1 - q^m e(z))/(e(z/ε) - q^m e(z))` is bounded by `4 exp(2π Im z/ε)`. -/
theorem exists_norm_div_principalFiveTermPoleFactor_upper (d : ℕ) (hd : 3 < d)
    (m : ℤ) :
    ∃ T : ℝ, ∀ z : ℂ, T ≤ z.im →
      ‖(1 - Complex.exp (2 * Real.pi * I * (z + m * (principalRoot d : ℂ)))) /
          principalFiveTermPoleFactor d m z‖ ≤
        4 * Real.exp (2 * Real.pi * z.im / principalRoot d ^ 3) := by
  let r := principalRoot d ^ 3
  let T := max 0 (Real.log 2 / (2 * Real.pi * (r - 1) / r))
  have hr : 1 < r := one_lt_principalRoot_pow_three d hd
  refine ⟨T, fun z hz => ?_⟩
  let a := Complex.exp (2 * Real.pi * I * (z / (principalRoot d : ℂ) ^ 3))
  let b := Complex.exp (2 * Real.pi * I * (z + m * (principalRoot d : ℂ)))
  have ha : ‖a‖ = Real.exp (-2 * Real.pi * z.im / r) := by
    simpa only [a, r] using norm_principalFiveTermPoleFactor_slow_term d z
  have hb : ‖b‖ = Real.exp (-2 * Real.pi * z.im) := by
    simpa only [b] using norm_principalFiveTermPoleFactor_fast_term d m z
  have hba : ‖b‖ ≤ ‖a‖ / 2 := by
    rw [ha, hb]
    exact exp_neg_two_pi_le_half_exp_div r z.im hr ((le_max_right _ _).trans hz)
  have hb1 : ‖b‖ ≤ 1 := by
    rw [hb, Real.exp_le_one_iff]
    have ht : 0 ≤ z.im := (le_max_left _ _).trans hz
    nlinarith [Real.pi_pos]
  have h := norm_one_sub_div_le_four_div_of_first_dominates a b (by rw [ha]; positivity) hb1 hba
  rw [ha] at h
  have hright : 4 / Real.exp (-2 * Real.pi * z.im / r) =
      4 * Real.exp (2 * Real.pi * z.im / r) := by
    rw [div_eq_mul_inv, ← Real.exp_neg]
    congr 1
    ring_nf
  rw [hright] at h
  simpa only [principalFiveTermPoleFactor, a, b, r, ← Complex.ofReal_pow] using h

/-- For `Im z ≤ -T`, the factor `(1 - q^m e(z))/(e(z/ε) - q^m e(z))` is bounded by `4`. -/
theorem exists_norm_div_principalFiveTermPoleFactor_lower (d : ℕ) (hd : 3 < d)
    (m : ℤ) :
    ∃ T : ℝ, ∀ z : ℂ, z.im ≤ -T →
      ‖(1 - Complex.exp (2 * Real.pi * I * (z + m * (principalRoot d : ℂ)))) /
          principalFiveTermPoleFactor d m z‖ ≤ 4 := by
  let r := principalRoot d ^ 3
  let T := max 0 (Real.log 2 / (2 * Real.pi * (r - 1) / r))
  have hr : 1 < r := one_lt_principalRoot_pow_three d hd
  refine ⟨T, fun z hz => ?_⟩
  let a := Complex.exp (2 * Real.pi * I * (z / (principalRoot d : ℂ) ^ 3))
  let b := Complex.exp (2 * Real.pi * I * (z + m * (principalRoot d : ℂ)))
  have ha : ‖a‖ = Real.exp (-2 * Real.pi * z.im / r) := by
    simpa only [a, r] using norm_principalFiveTermPoleFactor_slow_term d z
  have hb : ‖b‖ = Real.exp (-2 * Real.pi * z.im) := by
    simpa only [b] using norm_principalFiveTermPoleFactor_fast_term d m z
  have hab : ‖a‖ ≤ ‖b‖ / 2 := by
    rw [ha, hb]
    have hT : Real.log 2 / (2 * Real.pi * (r - 1) / r) ≤ T := le_max_right _ _
    exact exp_div_le_half_exp_neg_two_pi r z.im hr (by linarith)
  have hb1 : 1 ≤ ‖b‖ := by
    rw [hb, Real.one_le_exp_iff]
    have hT : 0 ≤ T := le_max_left _ _
    have ht : z.im ≤ 0 := by linarith
    nlinarith [Real.pi_pos]
  simpa only [principalFiveTermPoleFactor, a, b] using
    norm_one_sub_div_le_four_of_second_dominates a b hb1 hab

/-! ### Sector bounds for the residue kernel

Uniform bounds in the real part, for the horizontal sides of the rectangles. -/

/-- The quotient of principal products stays bounded in an upper sector. -/
private lemma exists_norm_principalFaddeev_div_upper
    (d : ℕ) (hd : 3 < d) (p m : ℤ) (y K : ℝ) :
    ∃ R : ℝ, ∀ z : ℂ, |z.re| ≤ K * z.im → R ≤ z.im →
      ‖principalFaddeev d (m + 1) 0 z /
        principalFaddeev d (m + p) 0 (z + y)‖ ≤ 3 := by
  let K' := max K 0 + |y|
  obtain ⟨C₁, κ₁, R₁, _, hκ₁, _, h₁⟩ :=
    exists_norm_principalFaddeev_sub_one_le d hd (m + 1) 0 K'
  obtain ⟨C₂, κ₂, R₂, _, hκ₂, _, h₂⟩ :=
    exists_norm_principalFaddeev_sub_one_le d hd (m + p) 0 K'
  let R := max 1 (max R₁ (max R₂ (max (2 * C₁ / κ₁) (2 * C₂ / κ₂))))
  refine ⟨R, fun z hz ht => ?_⟩
  have hs : 1 ≤ z.im := (le_max_left _ _).trans ht
  have hle (a : ℝ) (ha : a ≤ R) : a ≤ z.im := ha.trans ht
  have h₁' := h₁ z (abs_re_le_widened_sector z y K z.im (zero_le_one.trans hs) hz)
    (hle R₁ (by simp [R]))
  have h₂' := h₂ (z + y) (by
      simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using
        abs_re_add_ofReal_le_widened_sector z y K z.im hs hz)
    (by simpa using hle R₂ (by simp [R]))
  have hC₁ : 2 * C₁ ≤ κ₁ * z.im := by
    have h := (div_le_iff₀ hκ₁).mp (hle (2 * C₁ / κ₁) (by simp [R]))
    nlinarith
  have hC₂ : 2 * C₂ ≤ κ₂ * z.im := by
    have h := (div_le_iff₀ hκ₂).mp (hle (2 * C₂ / κ₂) (by simp [R]))
    nlinarith
  apply norm_div_le_three_of_exponential_bounds _ _ hC₁ hC₂
  · exact h₁'
  · simpa using h₂'

/-- The quotient of reflected-normalized principal products stays bounded in a lower sector. -/
private lemma exists_norm_principalFaddeev_div_lower
    (d : ℕ) (hd : 3 < d) (p m : ℤ) (y K : ℝ) :
    ∃ R : ℝ, ∀ z : ℂ, |z.re| ≤ K * -z.im → R ≤ -z.im →
      ‖(principalFaddeev d (m + 1) 0 z /
          Complex.exp (principalFaddeevLowerExponentComplex d (m + 1) 0 z
            (principalRoot d))) /
        (principalFaddeev d (m + p) 0 (z + y) /
          Complex.exp (principalFaddeevLowerExponentComplex d (m + p) 0 (z + y)
            (principalRoot d)))‖ ≤ 3 := by
  let K' := max K 0 + |y|
  obtain ⟨C₁, κ₁, R₁, _, hκ₁, _, h₁⟩ :=
    exists_norm_principalFaddeev_div_exp_sub_one_le d hd (m + 1) 0 K'
  obtain ⟨C₂, κ₂, R₂, _, hκ₂, _, h₂⟩ :=
    exists_norm_principalFaddeev_div_exp_sub_one_le d hd (m + p) 0 K'
  let R := max 1 (max R₁ (max R₂ (max (2 * C₁ / κ₁) (2 * C₂ / κ₂))))
  refine ⟨R, fun z hz ht => ?_⟩
  have hs : 1 ≤ -z.im := (le_max_left _ _).trans ht
  have hle (a : ℝ) (ha : a ≤ R) : a ≤ -z.im := ha.trans ht
  have h₁' := h₁ z (abs_re_le_widened_sector z y K (-z.im) (zero_le_one.trans hs) hz)
    (hle R₁ (by simp [R]))
  have h₂' := h₂ (z + y) (by
      simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using
        abs_re_add_ofReal_le_widened_sector z y K (-z.im) hs hz)
    (by simpa using hle R₂ (by simp [R]))
  have hC₁ : 2 * C₁ ≤ κ₁ * -z.im := by
    have h := (div_le_iff₀ hκ₁).mp (hle (2 * C₁ / κ₁) (by simp [R]))
    nlinarith
  have hC₂ : 2 * C₂ ≤ κ₂ * -z.im := by
    have h := (div_le_iff₀ hκ₂).mp (hle (2 * C₂ / κ₂) (by simp [R]))
    nlinarith
  apply norm_div_le_three_of_exponential_bounds _ _ hC₁ hC₂
  · exact h₁'
  · simpa using h₂'

/-- At the principal period, the reflected phase has a purely imaginary slope `2πiμ`. -/
private lemma norm_principalFiveTermReflectedPhase_exp_sector (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y : ℝ) (z : ℂ) :
    ‖Complex.exp (principalFiveTermReflectedPhaseComplex d ℓ p m w y z
      (principalRoot d))‖ =
      ‖Complex.exp (principalFiveTermReflectedPhaseComplex d ℓ p m w y 0
        (principalRoot d))‖ *
        Real.exp ((-2 * Real.pi * principalFiveTermLowerRate d ℓ p w y) * z.im) := by
  have hρ : (principalRoot d : ℂ) ≠ 0 := ofReal_principalRoot_ne_zero d hd
  have hfix : flt (principalU d : Mat(2, ℤ)) (principalRoot d : ℂ) =
      (principalRoot d : ℂ) := flt_principalU_principalRoot_complex d hd
  have hτ₁ : flt (principalU d : Mat(2, ℤ)) (principalRoot d : ℂ) ≠ 0 := by
    simpa only [hfix] using hρ
  have hτ₂ : flt (principalU d : Mat(2, ℤ))
      (flt (principalU d : Mat(2, ℤ)) (principalRoot d : ℂ)) ≠ 0 := by
    simpa only [hfix] using hρ
  rw [principalFiveTermReflectedPhaseComplex_eq_affine d ℓ p m w y z
    (principalRoot d) hρ hτ₁ hτ₂,
    principalFiveTermReflectedPhaseCoeffComplex_principalRoot d hd ℓ p w y,
    Complex.exp_add, norm_mul, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * I * (principalFiveTermLowerRate d ℓ p w y : ℂ) * z).re =
      (-2 * Real.pi * principalFiveTermLowerRate d ℓ p w y) * z.im := by
    simp [Complex.mul_re]
  rw [hre]
  ring

/-- In an upper sector, the residue kernel decays like `exp(-2π(λ - 1/ε) Im z)` when
`λ > 1/ε`. The five-term products tend to one uniformly
(`exists_norm_principalFaddeev_sub_one_le`), the phase has modulus
`exp(-2πλ Im z)`, and the pole factor contributes `exp(2π Im z/ε)`. -/
theorem exists_norm_principalFiveTermResidueKernel_upper (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y : ℝ) (K : ℝ)
    (hRate : (principalRoot d ^ 3)⁻¹ < principalFiveTermUpperRate d ℓ w) :
    ∃ C κ R : ℝ, 0 < κ ∧ ∀ z : ℂ, |z.re| ≤ K * z.im → R ≤ z.im →
      ‖principalFiveTermResidueKernel d ℓ p w y m z‖ ≤ C * Real.exp (-κ * z.im) := by
  obtain ⟨R₁, hratio⟩ :=
    exists_norm_principalFaddeev_div_upper d hd p m y K
  obtain ⟨R₂, hpole⟩ :=
    exists_norm_div_principalFiveTermPoleFactor_upper d hd m
  let κ := 2 * Real.pi *
    (principalFiveTermUpperRate d ℓ w - (principalRoot d ^ 3)⁻¹)
  have hκ : 0 < κ := mul_pos (by positivity) (sub_pos.mpr hRate)
  refine ⟨12, κ, max R₁ R₂, hκ, fun z hz ht => ?_⟩
  have hratio' := hratio z hz ((le_max_left _ _).trans ht)
  have hpole' := hpole z ((le_max_right _ _).trans ht)
  have hphase := norm_exp_principalFiveTermPhase d ℓ m w z
  have hk : ‖principalFiveTermKernel d ℓ p w y m z‖ ≤
      3 * Real.exp ((-2 * Real.pi * principalFiveTermUpperRate d ℓ w) * z.im) := by
    rw [principalFiveTermKernel, norm_mul, hphase]
    exact mul_le_mul_of_nonneg_right hratio' (Real.exp_pos _).le
  rw [principalFiveTermResidueKernel, mul_div_assoc, norm_mul]
  calc
    _ ≤ (3 * Real.exp ((-2 * Real.pi * principalFiveTermUpperRate d ℓ w) * z.im)) *
        (4 * Real.exp (2 * Real.pi * z.im / principalRoot d ^ 3)) :=
      mul_le_mul hk hpole' (norm_nonneg _) (by positivity)
    _ = 12 * Real.exp (-κ * z.im) := by
      rw [mul_mul_mul_comm, ← Real.exp_add]
      congr 1
      · norm_num
      · congr 1
        dsimp [κ]
        rw [inv_eq_one_div]
        ring

/-- In a lower sector, the residue kernel decays like `exp(-2πμ Im z)` when `μ < 0`. The
normalized products tend to one (`exists_norm_principalFaddeev_div_exp_sub_one_le`), the
quadratic parts of the two exact exponents cancel
(`principalFiveTermReflectedPhaseComplex_eq_affine`
at `τ = ρ_d`), the phase has modulus `exp(-2πμ Im z)`, and the pole factor is bounded. -/
theorem exists_norm_principalFiveTermResidueKernel_lower (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y : ℝ) (K : ℝ)
    (hRate : principalFiveTermLowerRate d ℓ p w y < 0) :
    ∃ C κ R : ℝ, 0 < κ ∧ ∀ z : ℂ, |z.re| ≤ K * -z.im → R ≤ -z.im →
      ‖principalFiveTermResidueKernel d ℓ p w y m z‖ ≤ C * Real.exp (-κ * -z.im) := by
  obtain ⟨R₁, hratio⟩ :=
    exists_norm_principalFaddeev_div_lower d hd p m y K
  obtain ⟨R₂, hpole⟩ :=
    exists_norm_div_principalFiveTermPoleFactor_lower d hd m
  let A := ‖Complex.exp (principalFiveTermReflectedPhaseComplex d ℓ p m w y 0
    (principalRoot d))‖
  let κ := -2 * Real.pi * principalFiveTermLowerRate d ℓ p w y
  have hκ : 0 < κ := by
    dsimp [κ]
    nlinarith [mul_pos Real.pi_pos (neg_pos.mpr hRate)]
  refine ⟨12 * A, κ, max R₁ R₂, hκ, fun z hz ht => ?_⟩
  have hratio' := hratio z hz ((le_max_left _ _).trans ht)
  have hpole' := hpole z (by linarith [le_max_right R₁ R₂])
  have hk : ‖principalFiveTermKernel d ℓ p w y m z‖ ≤
      3 * (A * Real.exp (κ * z.im)) := by
    rw [← principalFiveTermKernelComplex_principalRoot d hd ℓ p m w y z,
      principalFiveTermKernelComplex_eq_lower_normalized,
      principalFaddeevComplex_principalRoot d hd,
      principalFaddeevComplex_principalRoot d hd, norm_mul,
      norm_principalFiveTermReflectedPhase_exp_sector d hd ℓ p m w y z]
    exact mul_le_mul_of_nonneg_right hratio' (by positivity)
  rw [principalFiveTermResidueKernel, mul_div_assoc, norm_mul]
  calc
    _ ≤ (3 * (A * Real.exp (κ * z.im))) * 4 :=
      mul_le_mul hk hpole' (norm_nonneg _) (by positivity)
    _ = 12 * A * Real.exp (-κ * -z.im) := by ring_nf

/-! ### Vertical lines

On a line whose crossing avoids the period lattice, its translate by `y`, and the kernel poles,
the residue kernel is continuous; with the two tails it is integrable. -/

/-- A real crossing is regular for the residue kernel of index `m` when it and its translate by
`y` avoid the period lattice and it is not a kernel pole. -/
structure IsPrincipalFiveTermResidueCrossing (d : ℕ) (m : ℤ) (y x : ℝ) : Prop where
  /-- The crossing and its translate by `y` avoid the period lattice. -/
  lattice : IsRegularPeriodLatticeCrossing (principalRoot d) y x
  /-- The crossing is not a lattice argument of index `m`. -/
  pole : ∀ k : ℤ, x ≠ principalFiveTermLatticeArgument d m k

/-- A regular crossing excludes every zero of the pole factor along its line. -/
private lemma principalFiveTermPoleFactor_vertical_ne_zero (d : ℕ) (hd : 3 < d)
    (m : ℤ) (y x t : ℝ) (hx : IsPrincipalFiveTermResidueCrossing d m y x) :
    principalFiveTermPoleFactor d m ((x : ℂ) + t * I) ≠ 0 := by
  intro hzero
  obtain ⟨k, hk⟩ := (principalFiveTermPoleFactor_eq_zero_iff d hd m _).mp hzero
  have him : t = 0 := by
    have h := congrArg Complex.im hk
    simpa using h
  have hreal : x = principalFiveTermLatticeArgument d m k := by
    have h := congrArg Complex.re hk
    simpa [him] using h
  exact hx.pole k hreal

/-- Along a regular vertical line the residue kernel is continuous: the five-term kernel is
continuous there (`continuousAt_principalFiveTermKernelComplex_vertical` at the fixed
period) and the pole factor has no zero on the line. -/
theorem continuous_principalFiveTermResidueKernel_vertical (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y x : ℝ) (hx : IsPrincipalFiveTermResidueCrossing d m y x) :
    Continuous (fun t : ℝ => principalFiveTermResidueKernel d ℓ p w y m ((x : ℂ) + t * I)) := by
  have hk := continuous_principalFiveTermKernel_vertical
    d hd ℓ p m w y x hx.lattice.base hx.lattice.shifted
  have hnum : Continuous (fun t : ℝ =>
      (1 : ℂ) - Complex.exp (2 * Real.pi * I *
        (((x : ℂ) + t * I) + m * (principalRoot d : ℂ)))) := by fun_prop
  have hden : Continuous (fun t : ℝ =>
      principalFiveTermPoleFactor d m ((x : ℂ) + t * I)) := by
    unfold principalFiveTermPoleFactor
    fun_prop
  have hdiv := hnum.div hden (fun t =>
    principalFiveTermPoleFactor_vertical_ne_zero d hd m y x t hx)
  have hres : Continuous (fun t : ℝ =>
      principalFiveTermKernel d ℓ p w y m ((x : ℂ) + t * I) *
        ((1 - Complex.exp (2 * Real.pi * I *
          (((x : ℂ) + t * I) + m * (principalRoot d : ℂ)))) /
          principalFiveTermPoleFactor d m ((x : ℂ) + t * I))) := by
    convert hk.mul hdiv using 1
  simpa only [principalFiveTermResidueKernel, mul_div_assoc] using hres

/-- The upper sector estimate gives integrability on a high vertical ray. -/
private lemma integrableOn_principalFiveTermResidueKernel_upper
    (d : ℕ) (hd : 3 < d) (ℓ p m : ℤ) (w y x : ℝ)
    (hx : IsPrincipalFiveTermResidueCrossing d m y x)
    (hupper : (principalRoot d ^ 3)⁻¹ < principalFiveTermUpperRate d ℓ w) :
    ∃ T : ℝ, IntegrableOn
      (fun t : ℝ => principalFiveTermResidueKernel d ℓ p w y m ((x : ℂ) + t * I))
      (Ioi T) := by
  obtain ⟨C, κ, R, hκ, hbound⟩ :=
    exists_norm_principalFiveTermResidueKernel_upper d hd ℓ p m w y 1 hupper
  let T := max R |x|
  have hf := continuous_principalFiveTermResidueKernel_vertical d hd ℓ p m w y x hx
  refine ⟨T, ?_⟩
  apply Integrable.mono' ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hκ) T).const_mul C)
    hf.aestronglyMeasurable
  apply (ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  have hsector : |(((x : ℂ) + t * I).re)| ≤ (1 : ℝ) * (((x : ℂ) + t * I).im) := by
    simpa using (le_max_right R |x|).trans ht.le
  have hR : R ≤ (((x : ℂ) + t * I).im) := by
    simpa using (le_max_left R |x|).trans ht.le
  simpa using hbound _ hsector hR

/-- The lower sector estimate gives integrability on a low vertical ray. -/
private lemma integrableOn_principalFiveTermResidueKernel_lower
    (d : ℕ) (hd : 3 < d) (ℓ p m : ℤ) (w y x : ℝ)
    (hx : IsPrincipalFiveTermResidueCrossing d m y x)
    (hlower : principalFiveTermLowerRate d ℓ p w y < 0) :
    ∃ T : ℝ, IntegrableOn
      (fun t : ℝ => principalFiveTermResidueKernel d ℓ p w y m ((x : ℂ) + t * I))
      (Iio (-T)) := by
  obtain ⟨C, κ, R, hκ, hbound⟩ :=
    exists_norm_principalFiveTermResidueKernel_lower d hd ℓ p m w y 1 hlower
  let T := max R |x|
  have hf := continuous_principalFiveTermResidueKernel_vertical d hd ℓ p m w y x hx
  refine ⟨T, ?_⟩
  have hi : IntegrableOn (fun t : ℝ => C * Real.exp (κ * t)) (Iic (-T)) :=
    (integrableOn_exp_mul_Iic hκ (-T)).const_mul C
  apply Integrable.mono' (hi.mono_set Iio_subset_Iic_self) hf.aestronglyMeasurable
  apply (ae_restrict_mem measurableSet_Iio).mono
  intro t ht
  have hheight : T ≤ -t := by
    change t < -T at ht
    linarith
  have hsector : |(((x : ℂ) + t * I).re)| ≤
      (1 : ℝ) * -(((x : ℂ) + t * I).im) := by
    simpa using (le_max_right R |x|).trans hheight
  have hR : R ≤ -(((x : ℂ) + t * I).im) := by
    simpa using (le_max_left R |x|).trans hheight
  simpa using hbound _ hsector hR

/-- On a regular vertical line, the residue kernel is integrable when `λ > 1/ε` and `μ < 0`. -/
theorem integrable_principalFiveTermResidueKernel (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y x : ℝ) (hx : IsPrincipalFiveTermResidueCrossing d m y x)
    (hupper : (principalRoot d ^ 3)⁻¹ < principalFiveTermUpperRate d ℓ w)
    (hlower : principalFiveTermLowerRate d ℓ p w y < 0) :
    Integrable (fun t : ℝ => principalFiveTermResidueKernel d ℓ p w y m ((x : ℂ) + t * I)) := by
  let f : ℝ → ℂ := fun t =>
    principalFiveTermResidueKernel d ℓ p w y m ((x : ℂ) + t * I)
  obtain ⟨T₁, hupperT⟩ :=
    integrableOn_principalFiveTermResidueKernel_upper d hd ℓ p m w y x hx hupper
  obtain ⟨T₂, hlowerT⟩ :=
    integrableOn_principalFiveTermResidueKernel_lower d hd ℓ p m w y x hx hlower
  let a := min (-T₂) T₁
  let b := max (-T₂) T₁
  have ha : IntegrableOn f (Iio a) :=
    hlowerT.mono_set (Iio_subset_Iio (min_le_left _ _))
  have hb : IntegrableOn f (Ioi b) :=
    hupperT.mono_set (Ioi_subset_Ioi (le_max_right _ _))
  have hm : IntegrableOn f (Icc a b) :=
    (continuous_principalFiveTermResidueKernel_vertical d hd ℓ p m w y x hx).continuousOn
      |>.integrableOn_Icc
  have hab : a ≤ b := (min_le_left _ _).trans (le_max_left _ _)
  change Integrable f
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := b),
    ← Set.Iio_union_Icc_eq_Iic hab]
  exact (ha.union hm).union hb

/-- The residue sum `L` is integrable on a vertical line whose crossings `x - mε/c` are regular
for every index `m`, under `λ > 1/ε` and `μ < 0`. -/
theorem integrable_principalFiveTermResidueSum (d : ℕ) (hd : 3 < d)
    (ℓ p : ℤ) (w y x : ℝ)
    (hx : ∀ m : FiveTermIndex (principalA d),
      IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ) y
        (x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ)))
    (hupper : (principalRoot d ^ 3)⁻¹ < principalFiveTermUpperRate d ℓ w)
    (hlower : principalFiveTermLowerRate d ℓ p w y < 0) :
    Integrable (fun t : ℝ => principalFiveTermResidueSum d ℓ p w y ((x : ℂ) + t * I)) := by
  let f : FiveTermIndex (principalA d) → ℝ → ℂ := fun m t =>
    principalFiveTermResidueKernel d ℓ p w y ((m : ℕ) : ℤ)
      (((x : ℂ) + t * I) -
        ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ))
  have hterm : ∀ m : FiveTermIndex (principalA d), Integrable (f m) := by
    intro m
    have h := integrable_principalFiveTermResidueKernel d hd ℓ p ((m : ℕ) : ℤ)
      w y (x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ))
      (hx m) hupper hlower
    convert h using 1
    funext t
    dsimp [f]
    congr 1
    push_cast
    ring
  simpa only [principalFiveTermResidueSum, f] using
    (integrable_finsetSum Finset.univ (fun m _ => hterm m))

end SIC

end
