/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import SICs.Analysis.Sectors

/-!
# Elementary bounds for the complex hyperbolic functions

Modulus formulas, Taylor remainders, and uniform contour bounds for complex `sinh` and `cosh`.

This file collects the estimates on `sinh` and `cosh` of a complex argument that control the
double-sine kernels of [AFK25, equation (8.7), `eq:dsintrep`] uniformly in their complex
parameters: the modulus formulas `|sinh(x+iy)|² = sinh²x + sin²y` and
`|cosh(x+iy)|² = sinh²x + cos²y`, the resulting comparisons with `sinh` and `cosh` of the real
part, the nonvanishing of `sinh(τt)` for `Re τ > 0` and `t > 0`, Taylor remainders of `sinh`
and `cosh` on the unit disc derived from `Complex.exp_bound`, and real exponential
comparisons: `e^x/4 ≤ sinh x` for `x ≥ 1`, `e^x ≤ 2 sinh x/(1 - e^{-2x₀})` for `x ≥ x₀ > 0`,
`x² ≤ sinh² x`, `cosh x ≤ e^{|x|}`, the resulting exponential decay
`cosh(ct)/(sinh(at) sinh t) ≤ 16 e^{(|c| - a - 1)t}` of the double-sine kernels at infinity,
and the factorization `1 - e^{-2x} = 2 e^{-x} sinh x` of a geometric-series denominator. None of
this is specific to the double sine; it is placed here because Mathlib does not provide it.

## Mathematical argument

Writing `sinh(x+iy) = sinh x cos y + i cosh x sin y` and
`cosh(x+iy) = cosh x cos y + i sinh x sin y` and using `cosh² = 1 + sinh²` gives the two modulus
formulas, hence `|sinh(Re w)| ≤ |sinh w| ≤ cosh(Re w)` and `|cosh w| ≤ cosh(Re w)`. The Taylor
remainders follow
from `Complex.exp_bound` applied to `exp(±x)`: the even or odd partial sums cancel in
`sinh = (exp x - exp(-x))/2` and `cosh = (exp x + exp(-x))/2`, leaving the displayed bound with a
constant at most `1`.

For the common contour, a zero of `sinh(τz)` has both `Re(τz) = 0` and
`sin(Im(τz)) = 0`. The first equality gives
`Re τ · Im(τz) = ‖τ‖² Im z`, so the displayed strip forces `|Im(τz)| < π` and hence
`z = 0`. Continuity preserves this inequality for nearby periods. On a shifted horizontal
line, `|Re(τ(x+ir))| ≥ b|x| - r` for periods with `Re τ ≥ b` and `|Im τ| ≤ 1`;
the reciprocal-sinh bound controls the tails, while compactness controls the finite segment.
These estimates support the contour shift in S. N. M. Ruijsenaars, *First order analytic
difference equations and integrable quantum systems*, J. Math. Phys. 38 (1997), 1069–1146,
proof of Proposition III.4, equations (3.54)–(3.56),
[doi:10.1063/1.531809](https://doi.org/10.1063/1.531809).
-/

noncomputable section

open Complex

namespace SIC

/-! ### Modulus of `sinh` and `cosh` -/

/-- `|sinh(x+iy)|² = sinh²x + sin²y`. -/
lemma normSq_sinh (w : ℂ) :
    Complex.normSq (Complex.sinh w) = Real.sinh w.re ^ 2 + Real.sin w.im ^ 2 := by
  rw [← Complex.re_add_im w, Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I]
  simp [Complex.normSq_apply, Complex.sinh_ofReal_re, Complex.sin_ofReal_re,
    Complex.cos_ofReal_re]
  nlinarith [Real.cosh_sq w.re, Real.sin_sq_add_cos_sq w.im]

/-- `|cosh(x+iy)|² = sinh²x + cos²y`. -/
lemma normSq_cosh (w : ℂ) :
    Complex.normSq (Complex.cosh w) = Real.sinh w.re ^ 2 + Real.cos w.im ^ 2 := by
  rw [← Complex.re_add_im w, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp [Complex.normSq_apply, Complex.sinh_ofReal_re, Complex.sin_ofReal_re,
    Complex.cos_ofReal_re]
  nlinarith [Real.cosh_sq w.re, Real.sin_sq_add_cos_sq w.im]

/-- `|sinh(Re w)| ≤ |sinh w|`. -/
lemma abs_sinh_re_le_norm_sinh (w : ℂ) : |Real.sinh w.re| ≤ ‖Complex.sinh w‖ := by
  have hsq : |Real.sinh w.re| ^ 2 ≤ ‖Complex.sinh w‖ ^ 2 := by
    rw [sq_abs, Complex.sq_norm, normSq_sinh]
    exact le_add_of_nonneg_right (sq_nonneg _)
  nlinarith [abs_nonneg (Real.sinh w.re), norm_nonneg (Complex.sinh w)]

/-- `|sinh w| ≤ cosh(Re w)`. -/
lemma norm_sinh_le_cosh_re (w : ℂ) : ‖Complex.sinh w‖ ≤ Real.cosh w.re := by
  have hsq : ‖Complex.sinh w‖ ^ 2 ≤ Real.cosh w.re ^ 2 := by
    rw [Complex.sq_norm, normSq_sinh, Real.cosh_sq]
    gcongr
    exact Real.sin_sq_le_one w.im
  nlinarith [norm_nonneg (Complex.sinh w), Real.cosh_pos w.re]

/-- `|cosh w| ≤ cosh(Re w)`. -/
lemma norm_cosh_le_cosh_re (w : ℂ) : ‖Complex.cosh w‖ ≤ Real.cosh w.re := by
  have hsq : ‖Complex.cosh w‖ ^ 2 ≤ Real.cosh w.re ^ 2 := by
    rw [Complex.sq_norm, normSq_cosh, Real.cosh_sq]
    gcongr
    exact Real.cos_sq_le_one w.im
  nlinarith [norm_nonneg (Complex.cosh w), Real.cosh_pos w.re]

/-- `sinh(Re τ · t) ≤ ‖sinh(τt)‖` for real `t`. -/
lemma sinh_re_mul_le_norm_sinh_mul_ofReal (tau : ℂ) (t : ℝ) :
    Real.sinh (tau.re * t) ≤ ‖Complex.sinh (tau * t)‖ := by
  have h := abs_sinh_re_le_norm_sinh (tau * t)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h
  exact (le_abs_self _).trans h

/-- `sinh(at) ≤ ‖sinh(τt)‖` for `a ≤ Re τ` and real `t ≥ 0`. -/
lemma sinh_mul_le_norm_sinh_mul_ofReal (tau : ℂ) {a t : ℝ} (ha : a ≤ tau.re) (ht : 0 ≤ t) :
    Real.sinh (a * t) ≤ ‖Complex.sinh (tau * t)‖ :=
  (Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right ha ht)).trans
    (sinh_re_mul_le_norm_sinh_mul_ofReal tau t)

/-- `sinh(τt) ≠ 0` for real `t > 0` and `Re τ > 0`. -/
lemma sinh_mul_ofReal_ne_zero_of_re_pos (tau : ℂ) {t : ℝ} (htau : 0 < tau.re) (ht : 0 < t) :
    Complex.sinh (tau * t) ≠ 0 := by
  intro h
  have hle := sinh_re_mul_le_norm_sinh_mul_ofReal tau t
  rw [h, norm_zero] at hle
  exact absurd hle (not_le.mpr (Real.sinh_pos_iff.mpr (mul_pos htau ht)))

/-- `‖sinh t‖ = |sinh t|` for real `t`. -/
lemma norm_sinh_ofReal (t : ℝ) : ‖Complex.sinh (t : ℂ)‖ = |Real.sinh t| := by
  rw [← Complex.ofReal_sinh, Complex.norm_real, Real.norm_eq_abs]

/-- `sinh t ≠ 0` in `ℂ` for a nonzero real `t`. -/
lemma sinh_ofReal_ne_zero {t : ℝ} (ht : t ≠ 0) : Complex.sinh (t : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_sinh]
  exact_mod_cast Real.sinh_ne_zero.mpr ht

/-! ### Taylor remainders on the unit disc

Each bound has the form `‖f(x) - P(x)‖ ≤ ‖x‖ⁿ` for `‖x‖ ≤ 1`, where `P` is the Taylor polynomial
of `f` of degree `n - 1`; the constants coming from `Complex.exp_bound` are all below `1`. -/

/-- `‖sinh x - x‖ ≤ ‖x‖³` for `‖x‖ ≤ 1`. -/
lemma norm_sinh_sub_self_le {x : ℂ} (hx : ‖x‖ ≤ 1) : ‖Complex.sinh x - x‖ ≤ ‖x‖ ^ 3 := by
  calc
    ‖Complex.sinh x - x‖ =
        ‖(Complex.exp x - ∑ m ∈ Finset.range 3, x ^ m / m.factorial) / 2 -
          (Complex.exp (-x) - ∑ m ∈ Finset.range 3, (-x) ^ m / m.factorial) / 2‖ := by
      simp [Complex.sinh, field, Finset.sum_range_succ, Nat.factorial]
      ring_nf
    _ ≤ ‖Complex.exp x - ∑ m ∈ Finset.range 3, x ^ m / m.factorial‖ / 2 +
        ‖Complex.exp (-x) - ∑ m ∈ Finset.range 3, (-x) ^ m / m.factorial‖ / 2 := by
      grw [norm_sub_le]
      simp
    _ ≤ ‖x‖ ^ 3 *
          (Nat.succ 3 * (Nat.factorial 3 * (3 : ℕ) : ℝ)⁻¹) / 2 +
        ‖-x‖ ^ 3 *
          (Nat.succ 3 * (Nat.factorial 3 * (3 : ℕ) : ℝ)⁻¹) / 2 := by
      grw [Complex.exp_bound hx (by simp), Complex.exp_bound (by simpa) (by simp)]
    _ ≤ ‖x‖ ^ 3 := by
      norm_num
      nlinarith [pow_nonneg (norm_nonneg x) 3]

/-- `‖sinh x - (x + x³/6)‖ ≤ ‖x‖⁵` for `‖x‖ ≤ 1`. -/
lemma norm_sinh_sub_cubic_le {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖Complex.sinh x - (x + x ^ 3 / 6)‖ ≤ ‖x‖ ^ 5 := by
  calc
    ‖Complex.sinh x - (x + x ^ 3 / 6)‖ =
        ‖(Complex.exp x - ∑ m ∈ Finset.range 5, x ^ m / m.factorial) / 2 -
          (Complex.exp (-x) - ∑ m ∈ Finset.range 5, (-x) ^ m / m.factorial) / 2‖ := by
      simp [Complex.sinh, field, Finset.sum_range_succ, Nat.factorial]
      ring_nf
    _ ≤ ‖Complex.exp x - ∑ m ∈ Finset.range 5, x ^ m / m.factorial‖ / 2 +
        ‖Complex.exp (-x) - ∑ m ∈ Finset.range 5, (-x) ^ m / m.factorial‖ / 2 := by
      grw [norm_sub_le]
      simp
    _ ≤ ‖x‖ ^ 5 *
          (Nat.succ 5 * (Nat.factorial 5 * (5 : ℕ) : ℝ)⁻¹) / 2 +
        ‖-x‖ ^ 5 *
          (Nat.succ 5 * (Nat.factorial 5 * (5 : ℕ) : ℝ)⁻¹) / 2 := by
      grw [Complex.exp_bound hx (by simp), Complex.exp_bound (by simpa) (by simp)]
    _ ≤ ‖x‖ ^ 5 := by
      norm_num
      nlinarith [pow_nonneg (norm_nonneg x) 5]

/-- `‖cosh x - (1 + x²/2)‖ ≤ ‖x‖⁴` for `‖x‖ ≤ 1`. -/
lemma norm_cosh_sub_quadratic_le {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖Complex.cosh x - (1 + x ^ 2 / 2)‖ ≤ ‖x‖ ^ 4 := by
  calc
    ‖Complex.cosh x - (1 + x ^ 2 / 2)‖ =
        ‖(Complex.exp x - ∑ m ∈ Finset.range 4, x ^ m / m.factorial) / 2 +
          (Complex.exp (-x) - ∑ m ∈ Finset.range 4, (-x) ^ m / m.factorial) / 2‖ := by
      simp [Complex.cosh, field, Finset.sum_range_succ, Nat.factorial]
      ring_nf
    _ ≤ ‖Complex.exp x - ∑ m ∈ Finset.range 4, x ^ m / m.factorial‖ / 2 +
        ‖Complex.exp (-x) - ∑ m ∈ Finset.range 4, (-x) ^ m / m.factorial‖ / 2 := by
      grw [norm_add_le]
      simp
    _ ≤ ‖x‖ ^ 4 *
          (Nat.succ 4 * (Nat.factorial 4 * (4 : ℕ) : ℝ)⁻¹) / 2 +
        ‖-x‖ ^ 4 *
          (Nat.succ 4 * (Nat.factorial 4 * (4 : ℕ) : ℝ)⁻¹) / 2 := by
      grw [Complex.exp_bound hx (by simp), Complex.exp_bound (by simpa) (by simp)]
    _ ≤ ‖x‖ ^ 4 := by
      norm_num
      nlinarith [pow_nonneg (norm_nonneg x) 4]

/-! ### Real exponential comparisons -/

/-- `e^x ≤ (2/(1 - e^{-2x₀})) sinh x` for `x ≥ x₀ > 0`: away from the origin the hyperbolic
sine dominates a fixed multiple of its exponential, with a constant depending only on `x₀`. -/
lemma exp_le_mul_sinh {x₀ x : ℝ} (hx₀ : 0 < x₀) (hx : x₀ ≤ x) :
    Real.exp x ≤ 2 / (1 - Real.exp (-2 * x₀)) * Real.sinh x := by
  have hq : Real.exp (-(2 * x)) ≤ Real.exp (-(2 * x₀)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hd : 0 < 1 - Real.exp (-(2 * x₀)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hfactor : Real.exp x * (1 - Real.exp (-(2 * x))) = 2 * Real.sinh x := by
    have he : Real.exp x * Real.exp (-(2 * x)) = Real.exp (-x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [Real.sinh_eq]
    linarith
  have hcomp : Real.exp x * (1 - Real.exp (-(2 * x₀))) ≤ 2 * Real.sinh x := by
    rw [← hfactor]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hq 1) (Real.exp_pos x).le
  calc
    Real.exp x ≤ (2 * Real.sinh x) / (1 - Real.exp (-(2 * x₀))) :=
      (le_div_iff₀ hd).2 hcomp
    _ = 2 / (1 - Real.exp (-2 * x₀)) * Real.sinh x := by ring_nf

/-- `x² ≤ sinh² x` for every real `x`, from `|x| ≤ |sinh x|`. -/
lemma sq_le_sinh_sq (x : ℝ) : x ^ 2 ≤ Real.sinh x ^ 2 := by
  have h (u : ℝ) (hu : 0 ≤ u) : u ^ 2 ≤ Real.sinh u ^ 2 := by
    have hs : u ≤ Real.sinh u := Real.self_le_sinh_iff.mpr hu
    nlinarith
  by_cases hx : 0 ≤ x
  · exact h x hx
  · have hs := h (-x) (by linarith)
    rw [Real.sinh_neg] at hs
    nlinarith

/-- `exp(x)/4 ≤ sinh x` for `x ≥ 1`. -/
lemma exp_div_four_le_sinh {x : ℝ} (hx : 1 ≤ x) : Real.exp x / 4 ≤ Real.sinh x := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hneg : Real.exp (-(1 : ℝ)) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num) he)
  have hd : 0 < 1 - Real.exp (-(1 : ℝ)) := by linarith
  have hc : 2 / (1 - Real.exp (-(1 : ℝ))) ≤ 4 :=
    (div_le_iff₀ hd).2 (by linarith)
  have h := exp_le_mul_sinh (x₀ := (1 : ℝ) / 2) (by norm_num) (by linarith : (1 : ℝ) / 2 ≤ x)
  have hs : 0 ≤ Real.sinh x := (Real.sinh_pos_iff.mpr (by linarith : 0 < x)).le
  have hm := mul_le_mul_of_nonneg_right hc hs
  nlinarith [h, hm]

/-- `cosh x ≤ exp |x|`. -/
lemma cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have hpos : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have hneg : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

/-- **Exponential decay of the double-sine kernels.** For `t ≥ 1` and `at ≥ 1`,
`cosh(ct)/(sinh(at) sinh t) ≤ 16 e^{(|c| - a - 1)t}`, from `sinh x ≥ e^x/4` for `x ≥ 1` and
`cosh x ≤ e^{|x|}`. -/
lemma cosh_div_sinh_mul_sinh_le_exp {a c t : ℝ} (ht : 1 ≤ t) (hat : 1 ≤ a * t) :
    Real.cosh (c * t) / (Real.sinh (a * t) * Real.sinh t) ≤
      16 * Real.exp ((|c| - a - 1) * t) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hcosh : Real.cosh (c * t) ≤ Real.exp (|c| * t) := by
    calc
      Real.cosh (c * t) ≤ Real.exp |c * t| := cosh_le_exp_abs _
      _ = Real.exp (|c| * t) := by rw [abs_mul, abs_of_pos ht0]
  have hden : Real.exp (a * t) / 4 * (Real.exp t / 4) ≤ Real.sinh (a * t) * Real.sinh t := by
    gcongr
    · exact exp_div_four_le_sinh hat
    · exact exp_div_four_le_sinh ht
  calc
    Real.cosh (c * t) / (Real.sinh (a * t) * Real.sinh t) ≤
        Real.exp (|c| * t) / (Real.exp (a * t) / 4 * (Real.exp t / 4)) :=
      div_le_div₀ (Real.exp_pos _).le hcosh (by positivity) hden
    _ = 16 * Real.exp ((|c| - a - 1) * t) := by
      rw [show (|c| - a - 1) * t = |c| * t - (a * t + t) by ring, Real.exp_sub, Real.exp_add]
      field_simp
      norm_num

/-- `1 - e^{-2x} = 2 e^{-x} sinh x`: the geometric-series denominator of the Barnes kernel at
`-2x` as a hyperbolic sine. -/
lemma one_sub_exp_neg_two_mul (x : ℝ) :
    1 - Real.exp (-(2 * x)) = 2 * Real.exp (-x) * Real.sinh x := by
  have h : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  rw [Real.sinh_eq, show -(2 * x) = -x + -x by ring, Real.exp_add]
  linear_combination -h

/-! ### A common contour for nearby complex periods

The moving zeros of `sinh(τz)` leave a common strip around the real axis when `τ` is
near a positive real period. The reciprocal has an exponential bound on any fixed
horizontal line inside that strip. These are elementary estimates supporting the contour
shift in Ruijsenaars (1997), proof of Proposition III.4, equations (3.54)–(3.56).
-/

/-- The strip `|Im z| ‖τ‖² < π Re τ` contains no nonzero zero of `sinh(τz)`.
This controls the moving zeros in Ruijsenaars (1997), proof of Proposition III.4,
equations (3.54)–(3.56). -/
lemma sinh_mul_ne_zero_of_abs_im_mul_normSq_lt {τ z : ℂ} (hτ : 0 < τ.re)
    (hz : z ≠ 0) (hstrip : |z.im| * Complex.normSq τ < Real.pi * τ.re) :
    Complex.sinh (τ * z) ≠ 0 := by
  intro hzero
  have hs := normSq_sinh (τ * z)
  rw [hzero] at hs
  simp only [Complex.normSq_zero] at hs
  have hre : (τ * z).re = 0 := Real.sinh_eq_zero.mp (by
    nlinarith [sq_nonneg (Real.sin (τ * z).im)])
  have him : Real.sin (τ * z).im = 0 := by
    nlinarith [sq_nonneg (Real.sinh (τ * z).re)]
  have hlin : τ.re * (τ * z).im = Complex.normSq τ * z.im := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply] at hre ⊢
    linear_combination τ.im * hre
  have habs := congrArg abs hlin
  rw [abs_mul, abs_mul, abs_of_pos hτ, abs_of_nonneg (Complex.normSq_nonneg τ)] at habs
  have him_lt : |(τ * z).im| < Real.pi := by nlinarith
  have him0 : (τ * z).im = 0 :=
    (Real.sin_eq_zero_iff_of_lt_of_lt (abs_lt.mp him_lt).1
      (abs_lt.mp him_lt).2).mp him
  have hprod : τ * z = 0 := Complex.ext hre him0
  have hτne : τ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.zero_re] at this
    linarith
  exact hz ((mul_eq_zero.mp hprod).resolve_left hτne)

/-- Every closed strip of half-height less than `π/τ₀` remains free of nonzero
zeros of `sinh(τz)` for all complex `τ` sufficiently near `τ₀ > 0`.
This supplies a common contour for Ruijsenaars (1997), equation (3.56). -/
lemma eventually_sinh_mul_ne_zero_of_abs_im_le {τ₀ r : ℝ} (hτ₀ : 0 < τ₀)
    (hr : r < Real.pi / τ₀) :
    ∀ᶠ τ : ℂ in nhds (τ₀ : ℂ), ∀ z : ℂ, z ≠ 0 → |z.im| ≤ r →
      Complex.sinh (τ * z) ≠ 0 := by
  have hbase : r * Complex.normSq (τ₀ : ℂ) < Real.pi * (τ₀ : ℂ).re := by
    have hr' : r * τ₀ < Real.pi := (lt_div_iff₀ hτ₀).mp hr
    have h := mul_lt_mul_of_pos_right hr' hτ₀
    simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, add_zero] at *
    nlinarith
  have hpos : ∀ᶠ τ : ℂ in nhds (τ₀ : ℂ), 0 < τ.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt (by simpa using hτ₀)
  have hbound : ∀ᶠ τ : ℂ in nhds (τ₀ : ℂ),
      r * Complex.normSq τ < Real.pi * τ.re :=
    ((continuous_const.mul Complex.continuous_normSq).continuousAt).eventually_lt
      ((continuous_const.mul Complex.continuous_re).continuousAt) hbase
  filter_upwards [hpos, hbound] with τ hτ hb z hz him
  apply sinh_mul_ne_zero_of_abs_im_mul_normSq_lt hτ hz
  exact (mul_le_mul_of_nonneg_right him (Complex.normSq_nonneg τ)).trans_lt hb

/-- Away from the imaginary axis, the reciprocal hyperbolic sine satisfies
`|1/sinh w| ≤ 2 exp(-|Re w|)/(1-exp(-2d))` for `|Re w| ≥ d > 0`.
This bounds the denominator on the tails of Ruijsenaars (1997), equation (3.56). -/
lemma norm_inv_sinh_le_exp_of_abs_re {w : ℂ} {d : ℝ} (hd : 0 < d)
    (hw : d ≤ |w.re|) :
    ‖(Complex.sinh w)⁻¹‖ ≤
      (2 / (1 - Real.exp (-2 * d))) * Real.exp (-|w.re|) := by
  have hK : 0 < 2 / (1 - Real.exp (-2 * d)) :=
    div_pos (by norm_num) (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  have hsinh : Real.sinh |w.re| ≤ ‖Complex.sinh w‖ := by
    simpa only [Real.abs_sinh] using abs_sinh_re_le_norm_sinh w
  have hspos : 0 < Real.sinh |w.re| :=
    Real.sinh_pos_iff.mpr (lt_of_lt_of_le hd hw)
  have hnormpos : 0 < ‖Complex.sinh w‖ := hspos.trans_le hsinh
  have hexp : Real.exp |w.re| ≤
      (2 / (1 - Real.exp (-2 * d))) * ‖Complex.sinh w‖ :=
    (exp_le_mul_sinh hd hw).trans (mul_le_mul_of_nonneg_left hsinh hK.le)
  rw [norm_inv, Real.exp_neg]
  have hdiv : 1 / ‖Complex.sinh w‖ ≤
      (2 / (1 - Real.exp (-2 * d))) / Real.exp |w.re| :=
    (div_le_div_iff₀ hnormpos (Real.exp_pos _)).2 (by simpa using hexp)
  simpa only [div_eq_mul_inv, one_mul] using hdiv

/-- The shifted horizontal line does not pass through the origin; used in the compact
part of `exists_norm_inv_sinh_mul_horizontal_le_near_real`. -/
private lemma horizontal_point_ne_zero {r : ℝ} (hr : 0 < r) (x : ℝ) :
    (x : ℂ) + (r : ℂ) * Complex.I ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_add, Complex.zero_im] at him
  linarith

/-- A lower bound for the real part on a shifted horizontal line; used in the
tail estimate for `exists_norm_inv_sinh_mul_horizontal_le_near_real`. -/
private lemma horizontal_mul_abs_re_lower {τ : ℂ} {x r b : ℝ}
    (hb : 0 ≤ b) (hτ : b ≤ τ.re) (him : |τ.im| ≤ 1) (hr : 0 ≤ r) :
    b * |x| - r ≤ |(τ * ((x : ℂ) + (r : ℂ) * Complex.I)).re| := by
  have hrepr : (τ * ((x : ℂ) + (r : ℂ) * Complex.I)).re =
      τ.re * x - τ.im * r := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hrepr]
  have hτx : b * |x| ≤ τ.re * |x| :=
    mul_le_mul_of_nonneg_right hτ (abs_nonneg x)
  have hir : |τ.im| * r ≤ r := by
    simpa using mul_le_mul_of_nonneg_right him hr
  have htriangle : τ.re * |x| ≤ |τ.re * x - τ.im * r| + |τ.im| * r := by
    calc
      τ.re * |x| = |τ.re * x| := by rw [abs_mul, abs_of_nonneg (hb.trans hτ)]
      _ = |(τ.re * x - τ.im * r) + τ.im * r| := by simp
      _ ≤ |τ.re * x - τ.im * r| + |τ.im * r| := abs_add_le _ _
      _ = |τ.re * x - τ.im * r| + |τ.im| * r := by rw [abs_mul, abs_of_nonneg hr]
  linarith

/-- If `Re τ ≥ b`, `|Im τ| ≤ 1`, and the horizontal-contour point is sufficiently far from
the origin, then `1 / sinh(τ(x+ir))` decays like `exp(-a|x|)`. This is the reusable common-strip
tail estimate underlying `exists_norm_inv_sinh_mul_horizontal_le_near_real`. -/
lemma norm_inv_sinh_horizontal_tail_le {τ : ℂ} {x r a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hτ : b ≤ τ.re) (him : |τ.im| ≤ 1)
    (hr : 0 ≤ r) (hx : r + 1 ≤ (b - a) * |x|) :
    ‖(Complex.sinh (τ * ((x : ℂ) + (r : ℂ) * Complex.I)))⁻¹‖ ≤
      (2 / (1 - Real.exp (-2))) * Real.exp (-a * |x|) := by
  have hre := horizontal_mul_abs_re_lower (x := x) (le_of_lt (ha.trans hab)) hτ him hr
  have hax : a * |x| ≤ |(τ * ((x : ℂ) + (r : ℂ) * Complex.I)).re| := by
    nlinarith
  have h1 : 1 ≤ |(τ * ((x : ℂ) + (r : ℂ) * Complex.I)).re| := by
    nlinarith [mul_nonneg ha.le (abs_nonneg x)]
  have hK : 0 ≤ (2 / (1 - Real.exp (-2))) := by
    have hd : 0 < 1 - Real.exp (-2) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
    positivity
  calc
    _ ≤ (2 / (1 - Real.exp (-2))) *
        Real.exp (-|(τ * ((x : ℂ) + (r : ℂ) * Complex.I)).re|) := by
      simpa only [mul_one] using norm_inv_sinh_le_exp_of_abs_re (by norm_num) h1
    _ ≤ (2 / (1 - Real.exp (-2))) * Real.exp (-a * |x|) := by
      gcongr
      linarith

/-- Compactness bounds the reciprocal on the middle segment of a common
zero-free horizontal contour. Used in `exists_norm_inv_sinh_mul_horizontal_le_near_real`. -/
private lemma exists_norm_inv_sinh_horizontal_middle_bound {τ₀ ε r T : ℝ}
    (hr : 0 < r)
    (hzero : ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → ∀ z : ℂ, z ≠ 0 → |z.im| ≤ r →
      Complex.sinh (τ * z) ≠ 0) :
    ∃ M : ℝ, ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → ∀ x : ℝ, |x| ≤ T →
      ‖(Complex.sinh (τ * ((x : ℂ) + (r : ℂ) * Complex.I)))⁻¹‖ ≤ M := by
  let s : Set (ℂ × ℝ) := Metric.closedBall (τ₀ : ℂ) ε ×ˢ Set.Icc (-T) T
  have hs : IsCompact s := (ProperSpace.isCompact_closedBall _ _).prod isCompact_Icc
  have hn : ∀ p ∈ s, Complex.sinh
      (p.1 * ((p.2 : ℂ) + (r : ℂ) * Complex.I)) ≠ 0 := by
    intro ⟨τ, x⟩ hp
    apply hzero τ (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hp.1)
    · exact horizontal_point_ne_zero hr x
    · simp [abs_of_pos hr]
  have hc : Continuous (fun p : ℂ × ℝ =>
      Complex.sinh (p.1 * ((p.2 : ℂ) + (r : ℂ) * Complex.I))) := by fun_prop
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn (hc.continuousOn.inv₀ hn)
  refine ⟨M, ?_⟩
  intro τ hτ x hx
  apply hM (τ, x)
  exact ⟨by simpa only [Metric.mem_closedBall, dist_eq_norm] using hτ, abs_le.mp hx⟩

/-- A small closed ball around a positive real period has a common zero-free
strip, a lower real-part bound, and a bounded imaginary part. These are the
period conditions used in `exists_norm_inv_sinh_mul_horizontal_le_near_real`. -/
private lemma exists_closedBall_common_strip {τ₀ r b : ℝ}
    (hτ₀ : 0 < τ₀) (hb : b < τ₀) (hrπ : r < Real.pi / τ₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε →
      (∀ z : ℂ, z ≠ 0 → |z.im| ≤ r → Complex.sinh (τ * z) ≠ 0) ∧
      b ≤ τ.re ∧ |τ.im| ≤ 1 := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp
    (eventually_sinh_mul_ne_zero_of_abs_im_le hτ₀ hrπ)
  let ε := min (δ / 2) (min (τ₀ - b) 1)
  have hε : 0 < ε := lt_min (half_pos hδ) (lt_min (sub_pos.mpr hb) (by norm_num))
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hεb : ε ≤ τ₀ - b := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, hε, ?_⟩
  intro τ hτ
  refine ⟨hsub ?_, re_ge_and_abs_im_le_of_norm_sub_le hτ hεb hε1⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    exact hτ.trans_lt hεδ

/-- A uniform bound on a finite segment gives an exponentially weighted bound
there; this is the middle-segment step of the common-contour estimate. -/
private lemma middle_bound_le_exponential {u a T M C x : ℝ}
    (ha : 0 ≤ a) (hx : |x| ≤ T) (hu : u ≤ M)
    (hCM : max M 0 * Real.exp (a * T) ≤ C) :
    u ≤ C * Real.exp (-a * |x|) := by
  have hMnonneg : 0 ≤ max M 0 := le_max_right M 0
  have hweight : 1 ≤ Real.exp (a * T) * Real.exp (-a * |x|) := by
    rw [← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by
      nlinarith [mul_le_mul_of_nonneg_left hx ha])
  calc
    u ≤ M := hu
    _ ≤ max M 0 := le_max_left M 0
    _ = max M 0 * 1 := by ring
    _ ≤ max M 0 * (Real.exp (a * T) * Real.exp (-a * |x|)) :=
      mul_le_mul_of_nonneg_left hweight hMnonneg
    _ = (max M 0 * Real.exp (a * T)) * Real.exp (-a * |x|) := by ring
    _ ≤ C * Real.exp (-a * |x|) :=
      mul_le_mul_of_nonneg_right hCM (Real.exp_pos _).le

/-- The compact middle bound and the real-part tail bound combine into one
weighted estimate on the entire shifted contour. -/
private lemma norm_inv_sinh_horizontal_uniform_le {τ₀ ε r a b T M C : ℝ}
    (ha : 0 < a) (hab : a < b) (hr : 0 < r)
    (hT : T = (r + 1) / (b - a))
    (hnear : ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → b ≤ τ.re ∧ |τ.im| ≤ 1)
    (hM : ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → ∀ x : ℝ, |x| ≤ T →
      ‖(Complex.sinh (τ * ((x : ℂ) + (r : ℂ) * Complex.I)))⁻¹‖ ≤ M)
    (hCK : 2 / (1 - Real.exp (-2)) ≤ C)
    (hCM : max M 0 * Real.exp (a * T) ≤ C) :
    ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → ∀ x : ℝ,
      ‖(Complex.sinh (τ * ((x : ℂ) + (r : ℂ) * Complex.I)))⁻¹‖ ≤
        C * Real.exp (-a * |x|) := by
  intro τ hτ x
  obtain ⟨hτre, hτim⟩ := hnear τ hτ
  by_cases hx : |x| ≤ T
  · exact middle_bound_le_exponential ha.le hx (hM τ hτ x hx) hCM
  · have hxT : T ≤ |x| := le_of_lt (lt_of_not_ge hx)
    have hx' : r + 1 ≤ (b - a) * |x| := by
      exact (by simpa only [mul_comm] using
        (div_le_iff₀ (sub_pos.mpr hab)).mp (by simpa [hT] using hxT))
    exact (norm_inv_sinh_horizontal_tail_le ha hab hτre hτim hr.le hx').trans
      (mul_le_mul_of_nonneg_right hCK (Real.exp_pos _).le)

/-- On the line `z=x+ir`, with `0<r<π/τ₀`, the reciprocal `1/sinh(τz)` is at most
`C exp(-a|x|)` uniformly for complex `τ` in a closed neighborhood of `τ₀`, for every
`0<a<τ₀`. This is the common-contour denominator estimate needed to carry
Ruijsenaars (1997), equation (3.56), to nearby complex periods. -/
theorem exists_norm_inv_sinh_mul_horizontal_le_near_real {τ₀ r a : ℝ}
    (hτ₀ : 0 < τ₀) (ha : 0 < a) (haτ : a < τ₀) (hr : 0 < r)
    (hrπ : r < Real.pi / τ₀) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε →
      ∀ x : ℝ, ‖(Complex.sinh (τ * ((x : ℂ) + (r : ℂ) * Complex.I)))⁻¹‖ ≤
        C * Real.exp (-a * |x|) := by
  let b := (a + τ₀) / 2
  have hab : a < b := by dsimp [b]; linarith
  have hbτ : b < τ₀ := by dsimp [b]; linarith
  obtain ⟨ε, hε, hnear⟩ := exists_closedBall_common_strip hτ₀ hbτ hrπ
  let T := (r + 1) / (b - a)
  obtain ⟨M, hM⟩ := exists_norm_inv_sinh_horizontal_middle_bound hr
    (fun τ hτ z hz him => (hnear τ hτ).1 z hz him)
  let K : ℝ := 2 / (1 - Real.exp (-2))
  have hK : 0 < K := by
    dsimp [K]
    exact div_pos (by norm_num)
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))
  let C := K + max M 0 * Real.exp (a * T) + 1
  have hMnonneg : 0 ≤ max M 0 := le_max_right M 0
  have hC : 0 < C := by dsimp [C]; positivity
  have hCK : K ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hMnonneg (Real.exp_pos (a * T)).le]
  have hCM : max M 0 * Real.exp (a * T) ≤ C := by dsimp [C]; linarith
  exact ⟨ε, C, hε, hC, norm_inv_sinh_horizontal_uniform_le ha hab hr rfl
    (fun τ hτ => (hnear τ hτ).2) hM hCK hCM⟩

end SIC

end
