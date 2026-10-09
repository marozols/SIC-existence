/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Mellin.Integration
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Summing inverse Mellin transforms over positive dilations

Interchange of positive-dilation sums with inverse Mellin integrals.

This file supplies the summation step used in [95, Shintani (1977), proof of Lemma 1,
pp. 170–171]. If `F` is absolutely integrable on `Re(s)=sigma>1`, summing its inverse
Mellin transform at `nt`, for `n>=1` and `t>0`, inserts the Dirichlet series `zeta(s)`.
Indeed, `|(nt)^(-s)| = n^(-sigma) t^(-sigma)` on this line. The convergent `p`-series
therefore bounds the sum of the integrals of the norms, justifying the interchange.

The statements are general integral API: they require vertical integrability but no
holomorphy or forward Mellin representation. The trigamma application is in
`SICs.SpecialFunctions.Mellin.TrigammaRemainder`.
-/

noncomputable section

open Complex MeasureTheory

namespace SIC

/-! ### The Dirichlet series and its vertical majorant -/

/-- The positive-integer Dirichlet series for `zeta(s)`, in negative-power notation.
This rewrites Mathlib's Dirichlet-series formula for `hasSum_mellinInv_nat_mul`. -/
private lemma hasSum_nat_add_one_cpow_neg (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (((n + 1 : ℕ) : ℂ) ^ (-s))) (riemannZeta s) := by
  have hsum := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  simpa only [Complex.cpow_neg, one_div, Nat.cast_add, Nat.cast_one] using hsum.hasSum

/-- The positive-integer real majorant is summable when `sigma>1`.
This bounds both the zeta factor and the integrated kernels below. -/
private lemma summable_nat_add_one_rpow_neg (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-σ))) := by
  exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))

/-- The norm of `zeta(sigma+iy)` is bounded by `sum n^(-sigma)` for `sigma>1`.
This is the Dirichlet-series majorant used by `verticalIntegrable_riemannZeta_mul`. -/
private lemma norm_riemannZeta_vertical_le (σ : ℝ) (hσ : 1 < σ) (y : ℝ) :
    ‖riemannZeta ((σ : ℂ) + y * I)‖ ≤
      ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (-σ)) := by
  have hs : 1 < ((σ : ℂ) + y * I).re := by simpa using hσ
  rw [← (hasSum_nat_add_one_cpow_neg _ hs).tsum_eq]
  have hn (n : ℕ) : ‖(((n + 1 : ℕ) : ℂ) ^ (-((σ : ℂ) + y * I)))‖ =
      ((n + 1 : ℕ) : ℝ) ^ (-σ) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp
  simpa only [hn] using norm_tsum_le_tsum_norm
    ((summable_nat_add_one_rpow_neg σ hσ).congr (fun n => (hn n).symm))

/-- Multiplication by `zeta(s)` preserves absolute integrability on `Re(s)=sigma>1`.
This connects the bounded Dirichlet series to the vertical-integral API. -/
theorem verticalIntegrable_riemannZeta_mul {F : ℂ → ℂ} {σ : ℝ}
    (hσ : 1 < σ) (hF : VerticalIntegrable F σ) :
    VerticalIntegrable (fun s => riemannZeta s * F s) σ := by
  have hc : Continuous (fun y : ℝ => riemannZeta ((σ : ℂ) + y * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hs : (σ : ℂ) + y * I ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        zero_mul, sub_self, add_zero, one_re] at this
      linarith
    exact (differentiableAt_riemannZeta hs).continuousAt.comp
      (f := fun y : ℝ => (σ : ℂ) + y * I) (by fun_prop)
  simpa only [VerticalIntegrable, mul_comm] using
    hF.mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_riemannZeta_vertical_le σ hσ))

/-! ### Absolute convergence and interchange

Each dilated kernel is integrable because its complex-power factor has constant norm
on the line. Factoring this constant out of the norm integral gives a summable sequence,
so Mathlib's integral-series theorem applies before multiplying by `1/(2*pi)`.
-/

/-- A positive real Mellin weight has constant norm on a vertical line.
This supplies the integrable kernels in `hasSum_mellinInv_nat_mul`. -/
private lemma integrable_mellinInv_kernel {F : ℂ → ℂ} {σ : ℝ}
    (hF : VerticalIntegrable F σ) (t : ℝ) (ht : 0 < t) :
    Integrable (fun y : ℝ => (t : ℂ) ^ (-((σ : ℂ) + y * I)) * F (σ + y * I)) := by
  simpa only [VerticalIntegrable, mul_comm] using verticalIntegrable_mul_cpow hF t ht

/-- Integrating the norm of a positive Mellin weight times `F` factors out `t^(-sigma)`.
This computes the summable majorant in `summable_integral_norm_mellinInv_nat_mul`. -/
private lemma integral_norm_mellinInv_kernel (F : ℂ → ℂ) (σ t : ℝ) (ht : 0 < t) :
    (∫ y : ℝ, ‖(t : ℂ) ^ (-((σ : ℂ) + y * I)) * F (σ + y * I)‖) =
      t ^ (-σ) * ∫ y : ℝ, ‖F (σ + y * I)‖ := by
  simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, neg_re, add_re,
    ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, zero_mul, sub_self, add_zero]
  exact integral_const_mul _ _

/-- The norm integrals of the kernels at `(n+1)t` are summable for `sigma>1`.
This is the absolute-convergence hypothesis for the integral-series interchange. -/
private lemma summable_integral_norm_mellinInv_nat_mul (F : ℂ → ℂ) (σ : ℝ)
    (hσ : 1 < σ) (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ => ∫ y : ℝ,
      ‖((((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) ^ (-((σ : ℂ) + y * I)) * F (σ + y * I)‖) := by
  have h := (summable_nat_add_one_rpow_neg σ hσ).mul_right
    (t ^ (-σ) * ∫ y : ℝ, ‖F (σ + y * I)‖)
  apply h.congr
  intro n
  rw [integral_norm_mellinInv_kernel F σ _ (mul_pos (by positivity) ht),
    Real.mul_rpow (by positivity) ht.le, mul_assoc]

/-- The dilated kernels sum pointwise to the kernel with an additional `zeta(s)` factor.
This evaluates the integrand after the interchange in `hasSum_mellinInv_nat_mul`. -/
private lemma hasSum_mellinInv_nat_mul_kernel (F : ℂ → ℂ) (s : ℂ) (hs : 1 < s.re)
    (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ =>
      ((((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) ^ (-s) * F s)
      ((t : ℂ) ^ (-s) * (riemannZeta s * F s)) := by
  have hterm (n : ℕ) :
      ((((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) ^ (-s) * F s =
        (((n + 1 : ℕ) : ℂ) ^ (-s)) * ((t : ℂ) ^ (-s) * F s) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) ht.le]
    simp only [Complex.ofReal_natCast, mul_assoc]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    ((hasSum_nat_add_one_cpow_neg s hs).mul_right ((t : ℂ) ^ (-s) * F s)).congr_fun hterm

/-- For `sigma>1`, `t>0` and a vertically integrable `F`,
`sum_{n>=1} mellinInv(sigma,F)(nt) = mellinInv(sigma,zeta*F)(t)`, with convergence.
This integral API justifies the positive-dilation summation in
[95, Shintani (1977), proof of Lemma 1, pp. 170–171]. -/
theorem hasSum_mellinInv_nat_mul {F : ℂ → ℂ} {σ : ℝ}
    (hσ : 1 < σ) (hF : VerticalIntegrable F σ) (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ => mellinInv σ F (((n + 1 : ℕ) : ℝ) * t))
      (mellinInv σ (fun s => riemannZeta s * F s) t) := by
  have h := hasSum_integral_of_summable_integral_norm
    (fun n : ℕ => integrable_mellinInv_kernel hF (((n + 1 : ℕ) : ℝ) * t)
      (mul_pos (by positivity) ht))
    (summable_integral_norm_mellinInv_nat_mul F σ hσ t ht)
  have heq (y : ℝ) := (hasSum_mellinInv_nat_mul_kernel F (σ + y * I)
    (by simpa using hσ) t ht).tsum_eq
  simp_rw [heq] at h
  simpa only [mellinInv, smul_eq_mul, Complex.real_smul] using
    h.mul_left ((1 / (2 * Real.pi) : ℝ) : ℂ)

end SIC

end
