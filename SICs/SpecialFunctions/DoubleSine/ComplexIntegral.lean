/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.DoubleSine.RealIntegral
import SICs.Analysis.HyperbolicBounds
import SICs.Analysis.HolomorphicParametricIntegral

/-!
# The complex double-sine integral

The complex double-sine integral of equation (8.7): kernel bounds, holomorphy, midpoint value, joint
continuity on the chamber.

This file defines the complex integral in [AFK25, equation (8.7), `eq:dsintrep`], after
`t ↦ 2t` and replacing the displayed argument `z + 1` by `z`. Its restriction to real
parameters is exactly the real double sine in `SICs.SpecialFunctions.DoubleSine.RealIntegral`.
The kernel is continuous in both parameters away from its denominators. On the source chamber
`Re τ > 0`, `0 < Re z < Re τ + 1`, the kernel is integrable and the integral is holomorphic in
`z`: the exact hyperbolic bound decays exponentially away from `t = 0`, the fifth-order Taylor
expansions of `sinh` bound the kernel near `t = 0` uniformly on compact sets of `z`, and
`differentiableOn_integral_of_locally_bounded` differentiates under the integral sign. At the
midpoint `z = (1+τ)/2` the integral equals `1`.

The same bounds give joint continuity in `(z, τ)` on the chamber, by dominated convergence
along the neighbourhood filter of a chamber point: the domination constants depend on `τ` only
through a lower bound for `Re τ`, so they cover a product neighbourhood. Since the chamber is
open and meets the real axis, this expresses the value at a positive real modulus as a limit of
complex values, which is the passage to the real boundary that the conductor-lowering argument
needs.

The elementary exponential is always nonzero, including at Lean's totalized integral values.
The difference equations of the integral are in `SICs.SpecialFunctions.DoubleSine.ComplexShifts`,
and its agreement with Shintani's gamma ratio on the chamber is
`shintaniDoubleSineGamma_eq_integral` in
`SICs.SpecialFunctions.DoubleSine.IntegralRepresentation`.
-/

noncomputable section

open Complex Real MeasureTheory Set

namespace SIC

/-! ### The complex integral from [AFK25, equation (8.7), `eq:dsintrep`] -/

/-- The regularized complex kernel for the two-argument Barnes double sine `S₂(z,τ)`:

```text
(sinh((τ + 1 - 2z)t) / (sinh(τt) sinh(t)) - (τ + 1 - 2z)/(τt)) / t.
```

This is the integrand in [AFK25, equation (8.7), `eq:dsintrep`] after the change of variables
`t ↦ 2t` and after replacing that equation's argument `z + 1` by a general argument `z`.
The subtraction removes the quadratic singularity at `t = 0`. -/
noncomputable def doubleSineComplexKernel (z tau : ℂ) (t : ℝ) : ℂ :=
  (Complex.sinh ((tau + 1 - 2 * z) * t) /
      (Complex.sinh (tau * t) * Complex.sinh t) -
    (tau + 1 - 2 * z) / (tau * t)) / t

/-- Away from the displayed denominators' zeros, the complex double-sine kernel is continuous in
its two complex parameters.  This supplies the pointwise limit in the dominated-convergence
proof of `continuousAt_doubleSineComplexLogIntegral`. -/
lemma continuousAt_doubleSineComplexKernel (z tau : ℂ) (t : ℝ)
    (htau : tau ≠ 0) (ht : t ≠ 0) (hsinh : Complex.sinh (tau * t) ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => doubleSineComplexKernel p.1 p.2 t) (z, tau) := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hsinh_t : Complex.sinh (t : ℂ) ≠ 0 := sinh_ofReal_ne_zero ht
  have harg : Continuous (fun p : ℂ × ℂ => (p.2 + 1 - 2 * p.1) * (t : ℂ)) := by
    fun_prop
  have htauarg : Continuous (fun p : ℂ × ℂ => p.2 * (t : ℂ)) := by
    fun_prop
  have hnum : Continuous (fun p : ℂ × ℂ =>
      Complex.sinh ((p.2 + 1 - 2 * p.1) * (t : ℂ))) :=
    Complex.continuous_sinh.comp harg
  have hden : Continuous (fun p : ℂ × ℂ =>
      Complex.sinh (p.2 * (t : ℂ)) * Complex.sinh (t : ℂ)) :=
    (Complex.continuous_sinh.comp htauarg).mul continuous_const
  have hlin : Continuous (fun p : ℂ × ℂ => p.2 + 1 - 2 * p.1) := by
    fun_prop
  unfold doubleSineComplexKernel
  exact ((hnum.continuousAt.div hden.continuousAt (mul_ne_zero hsinh hsinh_t)).sub
    (hlin.continuousAt.div htauarg.continuousAt (mul_ne_zero htau htC))).div
      continuousAt_const htC

/-- The complex logarithmic double-sine integral

```text
∫₀∞ K(z,τ,t) dt.
```

On the chamber `0 < re(τ)` and `0 < re(z) < re(τ) + 1`, one half of its negative is the
logarithm in [AFK25, equation (8.7), `eq:dsintrep`].  As with the real
`doubleSineLogIntegral`, Lean's Bochner integral totalizes the expression outside its convergence
domain; no result below uses that totalized value as a Barnes double sine there. -/
noncomputable def doubleSineComplexLogIntegral (z tau : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), doubleSineComplexKernel z tau t

/-- The complex integral expression for the Barnes double sine in [AFK25, equation (8.7),
`eq:dsintrep`], after `t ↦ 2t`:

```text
S₂(z,τ) = exp(-½ ∫₀∞ K(z,τ,t) dt).
```

The source chamber is `0 < re(τ)` and `0 < re(z) < re(τ) + 1`.  The name records that this is
the integral representation, rather than claiming a global meromorphic construction outside that
chamber. -/
noncomputable def doubleSineComplexIntegral (z tau : ℂ) : ℂ :=
  Complex.exp (-doubleSineComplexLogIntegral z tau / 2)

/-- The complex integral expression never vanishes, since it is an exponential. -/
lemma doubleSineComplexIntegral_ne_zero (z tau : ℂ) :
    doubleSineComplexIntegral z tau ≠ 0 := by
  exact Complex.exp_ne_zero _

/-- Restricting the complex kernel to real parameters gives the real kernel defining
`doubleSine'` exactly.  This is the pointwise compatibility behind
`doubleSineComplexIntegral_ofReal`. -/
lemma doubleSineComplexKernel_ofReal (z tau t : ℝ) :
    doubleSineComplexKernel z tau t = (doubleSineKernel z tau 1 t : ℂ) := by
  simp only [doubleSineComplexKernel, doubleSineKernel, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_one, Complex.ofReal_sinh]
  ring_nf

/-- Restricting the complex logarithmic integral to real parameters gives the coercion of the
real logarithmic integral exactly. -/
lemma doubleSineComplexLogIntegral_ofReal (z tau : ℝ) :
    doubleSineComplexLogIntegral z tau = (doubleSineLogIntegral z tau 1 : ℂ) := by
  unfold doubleSineComplexLogIntegral doubleSineLogIntegral
  simp_rw [doubleSineComplexKernel_ofReal]
  exact integral_complex_ofReal

/-- **The complex integral restricts to the real Barnes double sine**, with the same
normalization and Kurokawa--Koyama convention. -/
lemma doubleSineComplexIntegral_ofReal (z tau : ℝ) :
    doubleSineComplexIntegral z tau = (doubleSine' z tau : ℂ) := by
  rw [doubleSineComplexIntegral, doubleSineComplexLogIntegral_ofReal]
  simp only [doubleSine', doubleSine, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_div, Complex.ofReal_ofNat]

/-! ### The midpoint value

At `z = (1+τ)/2` the parameter `τ + 1 - 2z` vanishes, so the kernel is identically zero and the
integral representation equals `1`. This normalizes the comparison with the double-gamma ratio,
which also equals `1` there. -/

/-- The kernel vanishes identically at the midpoint `z = (1+τ)/2`. -/
lemma doubleSineComplexKernel_midpoint (tau : ℂ) (t : ℝ) :
    doubleSineComplexKernel ((1 + tau) / 2) tau t = 0 := by
  have h : tau + 1 - 2 * ((1 + tau) / 2) = 0 := by ring
  simp [doubleSineComplexKernel, h]

/-- `S₂((1+τ)/2, τ) = 1` for the integral representation. -/
lemma doubleSineComplexIntegral_midpoint (tau : ℂ) :
    doubleSineComplexIntegral ((1 + tau) / 2) tau = 1 := by
  simp [doubleSineComplexIntegral, doubleSineComplexLogIntegral,
    doubleSineComplexKernel_midpoint]

/-! ### Bounds on the complex kernel

Write `w = τ + 1 - 2z`. The exact bound compares each hyperbolic factor with the real part of
its argument; it decays like `exp(-(Re τ + 1 - |Re w|) t)` and is integrable away from `0` when
`|Re w| < Re τ + 1`, that is, when `0 < Re z < Re τ + 1`. Near `t = 0` the kernel is
`(τt sinh(wt) - w sinh(τt) sinh t) / (τt² sinh(τt) sinh t)`; the Taylor expansions of `sinh`
to fifth order cancel the numerator to `O(t⁴)`, and the denominator is at least `a²t⁴` in
modulus for `Re τ ≥ a`. -/

/-- The exact bound, for `Re τ > 0` and `t > 0`:

```text
‖K(z, τ, t)‖ ≤ (cosh(Re w · t) / (sinh(Re τ · t) sinh t) + ‖w‖ / (Re τ · t)) / t,
```

with `w = τ + 1 - 2z`; from `‖sinh(wt)‖ ≤ cosh(Re w · t)`, `‖sinh(τt)‖ ≥ sinh(Re τ · t)`, and
`‖τ‖ ≥ Re τ`. -/
lemma norm_doubleSineComplexKernel_le (z tau : ℂ) (htau : 0 < tau.re) (t : ℝ) (ht : 0 < t) :
    ‖doubleSineComplexKernel z tau t‖ ≤
      (Real.cosh ((tau + 1 - 2 * z).re * t) / (Real.sinh (tau.re * t) * Real.sinh t) +
        ‖tau + 1 - 2 * z‖ / (tau.re * t)) / t := by
  let w := tau + 1 - 2 * z
  have htaut : 0 < tau.re * t := mul_pos htau ht
  have hsinh_t : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hsinh_tau : 0 < Real.sinh (tau.re * t) := Real.sinh_pos_iff.mpr htaut
  have hsinh_tau_le : Real.sinh (tau.re * t) ≤ ‖Complex.sinh (tau * t)‖ :=
    sinh_re_mul_le_norm_sinh_mul_ofReal tau t
  have hsinh_t_norm : ‖Complex.sinh (t : ℂ)‖ = Real.sinh t := by
    rw [norm_sinh_ofReal, abs_of_pos hsinh_t]
  have hfirst :
      ‖Complex.sinh (w * t) /
          (Complex.sinh (tau * t) * Complex.sinh t)‖ ≤
        Real.cosh (w.re * t) / (Real.sinh (tau.re * t) * Real.sinh t) := by
    rw [Complex.norm_div, Complex.norm_mul, hsinh_t_norm]
    apply div_le_div₀ (Real.cosh_pos _).le
      (by simpa [Complex.mul_re] using norm_sinh_le_cosh_re (w * t))
      (mul_pos hsinh_tau hsinh_t)
    exact mul_le_mul_of_nonneg_right hsinh_tau_le hsinh_t.le
  have htau_norm : tau.re * t ≤ ‖tau * t‖ := by
    rw [Complex.norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_right (Complex.re_le_norm tau) ht.le
  have hsecond : ‖w / (tau * t)‖ ≤ ‖w‖ / (tau.re * t) := by
    rw [Complex.norm_div]
    exact div_le_div₀ (norm_nonneg _) le_rfl htaut htau_norm
  change ‖((Complex.sinh (w * t) /
      (Complex.sinh (tau * t) * Complex.sinh t) - w / (tau * t)) / t : ℂ)‖ ≤ _
  rw [Complex.norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  apply div_le_div_of_nonneg_right _ ht.le
  exact (norm_sub_le _ _).trans (add_le_add hfirst hsecond)

/-- The numerator `τt sinh(wt) - w sinh(τt) sinh t` of the kernel is `O(t⁴)`: for
`‖τ‖, ‖w‖ ≤ T`, `T ≥ 1`, `t > 0`, and `Tt ≤ 1`, its modulus is at most `7T⁴t⁴`. The terms of
order `t²` cancel exactly, and the fifth-order Taylor remainders of `sinh` bound the rest. -/
private lemma norm_kernel_numerator_le (w tau : ℂ) {T : ℝ} (hT : 1 ≤ T) (htau : ‖tau‖ ≤ T)
    (hw : ‖w‖ ≤ T) (t : ℝ) (ht : 0 < t) (htT : T * t ≤ 1) :
    ‖tau * t * Complex.sinh (w * t) - w * Complex.sinh (tau * t) * Complex.sinh t‖ ≤
      7 * T ^ 4 * t ^ 4 := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have ht0 : 0 ≤ t := ht.le
  have ht1 : t ≤ 1 := by nlinarith
  have hwt : ‖w * t‖ ≤ T * t := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_right hw ht0
  have htaut : ‖tau * t‖ ≤ T * t := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_right htau ht0
  have hs : ‖(t : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] using ht1
  have hrw : ‖Complex.sinh (w * t) - w * t‖ ≤ (T * t) ^ 3 :=
    (norm_sinh_sub_self_le (hwt.trans htT)).trans (by gcongr)
  have hrtau : ‖Complex.sinh (tau * t) - tau * t‖ ≤ (T * t) ^ 3 :=
    (norm_sinh_sub_self_le (htaut.trans htT)).trans (by gcongr)
  have hrs : ‖Complex.sinh (t : ℂ) - t‖ ≤ t ^ 3 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] using
      norm_sinh_sub_self_le hs
  let rw' := Complex.sinh (w * t) - w * t
  let rtau := Complex.sinh (tau * t) - tau * t
  let rs := Complex.sinh (t : ℂ) - t
  have h1 : ‖tau * t * rw'‖ ≤ T ^ 4 * t ^ 4 := by
    simp only [rw', Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    calc
      ‖tau‖ * t * ‖Complex.sinh (w * t) - w * t‖ ≤ T * t * (T * t) ^ 3 := by
        gcongr
      _ = T ^ 4 * t ^ 4 := by ring
  have h2 : ‖w * rtau * t‖ ≤ T ^ 4 * t ^ 4 := by
    simp only [rtau, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    calc
      ‖w‖ * ‖Complex.sinh (tau * t) - tau * t‖ * t ≤ T * (T * t) ^ 3 * t := by
        gcongr
      _ = T ^ 4 * t ^ 4 := by ring
  have h3 : ‖w * (tau * t) * rs‖ ≤ T ^ 4 * t ^ 4 := by
    simp only [rs, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    calc
      ‖w‖ * (‖tau‖ * t) * ‖Complex.sinh (t : ℂ) - t‖ ≤ T * (T * t) * t ^ 3 := by
        gcongr
      _ ≤ T ^ 4 * t ^ 4 := by
        have hsq : 1 ≤ T ^ 2 := by nlinarith [sq_nonneg (T - 1)]
        have hpow : T ^ 2 ≤ T ^ 4 := by
          nlinarith [mul_nonneg (sq_nonneg T) (sub_nonneg.mpr hsq)]
        calc
          T * (T * t) * t ^ 3 = T ^ 2 * t ^ 4 := by ring
          _ ≤ T ^ 4 * t ^ 4 := by gcongr
  have h4 : ‖w * rtau * rs‖ ≤ T ^ 4 * t ^ 4 := by
    simp only [rtau, rs, Complex.norm_mul]
    calc
      ‖w‖ * ‖Complex.sinh (tau * t) - tau * t‖ *
          ‖Complex.sinh (t : ℂ) - t‖ ≤ T * (T * t) ^ 3 * t ^ 3 := by
        gcongr
      _ ≤ T ^ 4 * t ^ 4 := by
        have ht_sq : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg (t - 1)]
        calc
          T * (T * t) ^ 3 * t ^ 3 = (T ^ 4 * t ^ 4) * t ^ 2 := by ring
          _ ≤ (T ^ 4 * t ^ 4) * 1 := by gcongr
          _ = T ^ 4 * t ^ 4 := mul_one _
  have hid :
      tau * t * Complex.sinh (w * t) - w * Complex.sinh (tau * t) * Complex.sinh t =
        tau * t * rw' - w * rtau * t - w * (tau * t) * rs - w * rtau * rs := by
    simp only [rw', rtau, rs]
    ring
  rw [hid]
  calc
    ‖tau * t * rw' - w * rtau * t - w * (tau * t) * rs - w * rtau * rs‖ ≤
        ‖tau * t * rw'‖ + ‖w * rtau * t‖ + ‖w * (tau * t) * rs‖ +
          ‖w * rtau * rs‖ := by
      grw [norm_sub_le, norm_sub_le, norm_sub_le]
    _ ≤ 4 * (T ^ 4 * t ^ 4) := by linarith
    _ ≤ 7 * T ^ 4 * t ^ 4 := by
      have hnon : 0 ≤ T ^ 4 * t ^ 4 := by positivity
      nlinarith

/-- The Taylor bound near `t = 0`: `‖K(z, τ, t)‖ ≤ 8T⁴/a²` when `Re τ ≥ a > 0`, `T ≥ 1`,
`‖τ‖ ≤ T`, `‖τ + 1 - 2z‖ ≤ T`, `t > 0`, and `Tt ≤ 1`. The denominator
`τt² sinh(τt) sinh t` has modulus at least `a t² sinh(at) sinh t ≥ a²t⁴`. -/
lemma norm_doubleSineComplexKernel_le_of_mul_le_one (z tau : ℂ) {a T : ℝ} (ha : 0 < a)
    (htau : a ≤ tau.re) (hT : 1 ≤ T) (htauT : ‖tau‖ ≤ T) (hw : ‖tau + 1 - 2 * z‖ ≤ T)
    (t : ℝ) (ht : 0 < t) (htT : T * t ≤ 1) :
    ‖doubleSineComplexKernel z tau t‖ ≤ 8 * T ^ 4 / a ^ 2 := by
  let w := tau + 1 - 2 * z
  have htauRe : 0 < tau.re := ha.trans_le htau
  have htau0 : tau ≠ 0 := fun h => by simpa [h] using htauRe.ne'
  have hat : 0 < a * t := mul_pos ha ht
  have htaut : 0 < tau.re * t := mul_pos htauRe ht
  have hsinh_at : 0 < Real.sinh (a * t) := Real.sinh_pos_iff.mpr hat
  have hsinh_t : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hsinh_tau_lower : Real.sinh (a * t) ≤ ‖Complex.sinh (tau * t)‖ :=
    sinh_mul_le_norm_sinh_mul_ofReal tau htau ht.le
  have hsinh_tau0 : Complex.sinh (tau * t) ≠ 0 := sinh_mul_ofReal_ne_zero_of_re_pos tau htauRe ht
  have hsinh_t0 : Complex.sinh (t : ℂ) ≠ 0 := sinh_ofReal_ne_zero ht.ne'
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hid :
      doubleSineComplexKernel z tau t =
        (tau * t * Complex.sinh (w * t) -
          w * Complex.sinh (tau * t) * Complex.sinh t) /
          (tau * t ^ 2 * Complex.sinh (tau * t) * Complex.sinh t) := by
    simp only [doubleSineComplexKernel, w]
    field_simp [htau0, htC, hsinh_tau0, hsinh_t0]
  have hden : a ^ 2 * t ^ 4 ≤
      ‖tau * t ^ 2 * Complex.sinh (tau * t) * Complex.sinh t‖ := by
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_mul, Complex.norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, norm_sinh_ofReal, abs_of_pos hsinh_t]
    have ht_sinh : t ≤ Real.sinh t := Real.self_le_sinh_iff.mpr ht.le
    have hat_sinh : a * t ≤ Real.sinh (a * t) := Real.self_le_sinh_iff.mpr hat.le
    have htau_norm : a ≤ ‖tau‖ := htau.trans (Complex.re_le_norm tau)
    calc
      a ^ 2 * t ^ 4 = a * t ^ 2 * (a * t) * t := by ring
      _ ≤ ‖tau‖ * t ^ 2 * Real.sinh (a * t) * Real.sinh t := by gcongr
      _ ≤ ‖tau‖ * t ^ 2 * ‖Complex.sinh (tau * t)‖ * Real.sinh t := by gcongr
  have hden_pos : 0 < a ^ 2 * t ^ 4 := by positivity
  rw [hid, Complex.norm_div]
  calc
    ‖tau * t * Complex.sinh (w * t) -
        w * Complex.sinh (tau * t) * Complex.sinh t‖ /
        ‖tau * t ^ 2 * Complex.sinh (tau * t) * Complex.sinh t‖ ≤
      (7 * T ^ 4 * t ^ 4) / (a ^ 2 * t ^ 4) := by
        apply div_le_div₀ (by positivity)
          (norm_kernel_numerator_le w tau hT htauT hw t ht htT) hden_pos hden
    _ ≤ 8 * T ^ 4 / a ^ 2 := by
      field_simp
      nlinarith [mul_nonneg (by positivity : 0 ≤ T ^ 4) (by positivity : 0 ≤ a ^ 2)]

/-- The tail bound `(cosh(ct)/(sinh(at) sinh t) + W/(at))/t` is integrable on `(t₀, ∞)` for
`t₀ > 0`, `a > 0`, and `|c| < a + 1`: the first term is at most a constant multiple of
`exp(-(a + 1 - |c|)t)` and the second is `W/(at²)`. -/
lemma integrableOn_doubleSineKernelTailBound {a c W t₀ : ℝ} (ha : 0 < a) (hc : |c| < a + 1)
    (ht₀ : 0 < t₀) :
    IntegrableOn (fun t : ℝ =>
      (Real.cosh (c * t) / (Real.sinh (a * t) * Real.sinh t) + W / (a * t)) / t) (Ioi t₀) := by
  let t₁ := max t₀ (max 1 (1 / a))
  let d := a + 1 - |c|
  have hd : 0 < d := by simp only [d]; linarith
  have ht₀t₁ : t₀ ≤ t₁ := le_max_left _ _
  have ht₁ : 0 < t₁ := ht₀.trans_le ht₀t₁
  have hcont : ContinuousOn (fun t : ℝ =>
      (Real.cosh (c * t) / (Real.sinh (a * t) * Real.sinh t) + W / (a * t)) / t)
      (Ioi 0) := by
    apply ContinuousOn.div
    · apply ContinuousOn.add
      · apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro t ht
          exact mul_ne_zero
            (ne_of_gt (Real.sinh_pos_iff.mpr (mul_pos ha ht)))
            (ne_of_gt (Real.sinh_pos_iff.mpr ht))
      · apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro t ht
          exact mul_ne_zero ha.ne' ht.ne'
    · fun_prop
    · intro t ht
      exact ht.ne'
  have hbounded : IntegrableOn (fun t : ℝ =>
      (Real.cosh (c * t) / (Real.sinh (a * t) * Real.sinh t) + W / (a * t)) / t)
      (Ioc t₀ t₁) := by
    apply IntegrableOn.mono_set
      ((hcont.mono fun _ ht => ht₀.trans_le ht.1).integrableOn_Icc)
    exact Ioc_subset_Icc_self
  have hfirst : IntegrableOn (fun t : ℝ =>
      Real.cosh (c * t) / (Real.sinh (a * t) * Real.sinh t) / t) (Ioi t₁) := by
    have hdom : IntegrableOn (fun t : ℝ => 16 * Real.exp (-d * t)) (Ioi t₁) :=
      (exp_neg_integrableOn_Ioi t₁ hd).const_mul 16
    apply hdom.mono'
    · have hfirstCont : ContinuousOn (fun t : ℝ =>
          Real.cosh (c * t) / (Real.sinh (a * t) * Real.sinh t) / t) (Ioi t₁) := by
        apply ContinuousOn.div
        · apply ContinuousOn.div
          · fun_prop
          · fun_prop
          · intro t ht
            have ht0 := ht₁.trans ht
            exact mul_ne_zero
              (ne_of_gt (Real.sinh_pos_iff.mpr (mul_pos ha ht0)))
              (ne_of_gt (Real.sinh_pos_iff.mpr ht0))
        · fun_prop
        · intro t ht
          exact (ht₁.trans ht).ne'
      exact hfirstCont.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [mem_Ioi] at ht
      have ht_one : 1 ≤ t := (show 1 ≤ t₁ by simp [t₁]).trans ht.le
      have ht_inv : 1 / a ≤ t := (show 1 / a ≤ t₁ by simp [t₁]).trans ht.le
      have hat : 1 ≤ a * t := by
        calc
          1 = a * (1 / a) := by field_simp
          _ ≤ a * t := mul_le_mul_of_nonneg_left ht_inv ha.le
      have hpos : 0 ≤ Real.cosh (c * t) / (Real.sinh (a * t) * Real.sinh t) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc
        Real.cosh (c * t) / (Real.sinh (a * t) * Real.sinh t) / t ≤
            Real.cosh (c * t) / (Real.sinh (a * t) * Real.sinh t) / 1 :=
          div_le_div_of_nonneg_left hpos zero_lt_one ht_one
        _ ≤ 16 * Real.exp ((|c| - a - 1) * t) := by
          rw [div_one]
          exact cosh_div_sinh_mul_sinh_le_exp ht_one hat
        _ = 16 * Real.exp (-d * t) := by
          congr 2
          simp only [d]
          ring
  have hsecond : IntegrableOn (fun t : ℝ => W / (a * t) / t) (Ioi t₁) := by
    have hpow := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ht₁
    apply (hpow.const_mul (W / a)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [mem_Ioi] at ht
    rw [rpow_neg (le_of_lt (ht₁.trans ht)), rpow_two]
    field_simp [ha.ne', (ht₁.trans ht).ne']
  have htail : IntegrableOn (fun t : ℝ =>
      (Real.cosh (c * t) / (Real.sinh (a * t) * Real.sinh t) + W / (a * t)) / t)
      (Ioi t₁) := by
    apply (hfirst.add hsecond).congr
    filter_upwards with t
    simp only [Pi.add_apply]
    ring
  rw [← Ioc_union_Ioi_eq_Ioi ht₀t₁]
  exact hbounded.union htail

/-- **Locally uniform domination of the kernel in both parameters.** For constants `a > 0`,
`T ≥ 1` and `0 ≤ c < a + 1`, one integrable function of `t` dominates `‖K(z, τ, t)‖` on
`(0, ∞)` for every pair `(z, τ)` with `Re τ ≥ a`, `‖τ‖ ≤ T`, `‖τ + 1 - 2z‖ ≤ T` and
`|Re(τ + 1 - 2z)| ≤ c`: the constant `8T⁴/a²` on `(0, 1/T]` and the tail bound beyond.

The bound depends on `τ` only through the lower bound `a` for `Re τ`, so it dominates a whole
product neighbourhood; this is what lets both parameters move at once. -/
lemma doubleSineComplexKernel_dominated {a c T : ℝ} (ha : 0 < a) (hc0 : 0 ≤ c)
    (hc : c < a + 1) (hT : 1 ≤ T) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧ ∀ z tau : ℂ, a ≤ tau.re → ‖tau‖ ≤ T →
      ‖tau + 1 - 2 * z‖ ≤ T → |(tau + 1 - 2 * z).re| ≤ c → ∀ t ∈ Ioi (0 : ℝ),
        ‖doubleSineComplexKernel z tau t‖ ≤ g t := by
  let u := 1 / T
  let g := fun t : ℝ => if t ≤ u then 8 * T ^ 4 / a ^ 2 else
    (Real.cosh (c * t) / (Real.sinh (a * t) * Real.sinh t) + T / (a * t)) / t
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hu : 0 < u := one_div_pos.mpr hT0
  have hcabs : |c| < a + 1 := by simpa [abs_of_nonneg hc0] using hc
  have htail := integrableOn_doubleSineKernelTailBound ha hcabs hu (W := T)
  have hsmall : IntegrableOn (fun _ : ℝ => 8 * T ^ 4 / a ^ 2) (Ioc 0 u) :=
    integrableOn_const (ne_of_lt measure_Ioc_lt_top)
  have hgsmall : IntegrableOn g (Ioc 0 u) := by
    apply hsmall.congr_fun _ measurableSet_Ioc
    intro t ht
    simp [g, ht.2]
  have hgtail : IntegrableOn g (Ioi u) := by
    apply htail.congr_fun _ measurableSet_Ioi
    intro t ht
    simp only [mem_Ioi] at ht
    simp [g, not_le.mpr ht]
  refine ⟨g, ?_, ?_⟩
  · rw [← Ioc_union_Ioi_eq_Ioi hu.le]
    exact hgsmall.union hgtail
  · intro z tau hatau htauT hw hrew t ht
    simp only [mem_Ioi] at ht
    have htaure : 0 < tau.re := ha.trans_le hatau
    by_cases htu : t ≤ u
    · simp only [g, ite_eq_left htu]
      apply norm_doubleSineComplexKernel_le_of_mul_le_one z tau ha hatau hT htauT hw t ht
      change t ≤ 1 / T at htu
      simpa [mul_comm] using (le_div_iff₀ hT0).mp htu
    · simp only [g, ite_eq_right htu]
      have hexact := norm_doubleSineComplexKernel_le z tau htaure t ht
      have hsinh_at : 0 < Real.sinh (a * t) := Real.sinh_pos_iff.mpr (mul_pos ha ht)
      have hsinh_t : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
      have hatt : a * t ≤ tau.re * t := mul_le_mul_of_nonneg_right hatau ht.le
      apply hexact.trans
      apply div_le_div_of_nonneg_right _ ht.le
      apply add_le_add
      · refine div_le_div₀ (by positivity) ?_ (by positivity) ?_
        · apply Real.cosh_le_cosh.mpr
          rw [abs_mul, abs_mul, abs_of_nonneg hc0, abs_of_pos ht]
          exact mul_le_mul_of_nonneg_right hrew ht.le
        · exact mul_le_mul_of_nonneg_right (Real.sinh_le_sinh.mpr hatt) hsinh_t.le
      · exact div_le_div₀ (by linarith) hw (mul_pos ha ht) hatt

/-! ### Integrability and holomorphy on the source chamber -/

/-- For `Re τ > 0`, the kernel is continuous on `(0, ∞)`: `sinh(τt) ≠ 0` there because
`‖sinh(τt)‖ ≥ sinh(Re τ · t) > 0`. -/
lemma continuousOn_doubleSineComplexKernel (z tau : ℂ) (htau : 0 < tau.re) :
    ContinuousOn (doubleSineComplexKernel z tau) (Ioi 0) := by
  unfold doubleSineComplexKernel
  apply ContinuousOn.div
  · apply ContinuousOn.sub
    · apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro t ht
        exact mul_ne_zero (sinh_mul_ofReal_ne_zero_of_re_pos tau htau ht)
          (sinh_ofReal_ne_zero ht.ne')
    · apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro t ht
        exact mul_ne_zero (fun h => by simpa [h] using htau.ne') (by exact_mod_cast ht.ne')
  · fun_prop
  · intro t ht
    exact_mod_cast ht.ne'

/-- **Convergence of the complex integral on the source chamber** `Re τ > 0`,
`0 < Re z < Re τ + 1` of [AFK25, equation (8.7), `eq:dsintrep`]. -/
theorem doubleSineComplexKernel_integrableOn (z tau : ℂ) (htau : 0 < tau.re) (hz : 0 < z.re)
    (hzUpper : z.re < tau.re + 1) :
    IntegrableOn (doubleSineComplexKernel z tau) (Ioi 0) := by
  let w := tau + 1 - 2 * z
  let T := max ‖tau‖ (max ‖w‖ 1)
  let c := |w.re|
  have hc0 : 0 ≤ c := abs_nonneg _
  have hc : c < tau.re + 1 := by
    have hwre : w.re = tau.re + 1 - 2 * z.re := by
      simp [w, Complex.mul_re]
    simp only [c, hwre]
    rw [abs_lt]
    constructor <;> linarith
  have hT : 1 ≤ T := le_max_of_le_right (le_max_right _ _)
  have htauT : ‖tau‖ ≤ T := le_max_left _ _
  have hwT : ‖w‖ ≤ T := le_max_of_le_right (le_max_left _ _)
  obtain ⟨g, hg, hbound⟩ :=
    doubleSineComplexKernel_dominated htau hc0 hc hT
  apply hg.mono'
  · exact (continuousOn_doubleSineComplexKernel z tau htau).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hbound z tau le_rfl htauT (by simpa [w] using hwT) (by simp [c, w]) t ht

/-- The logarithmic integral is holomorphic in `z` on the source chamber, by
`differentiableOn_integral_of_locally_bounded` and `doubleSineComplexKernel_dominated`. -/
theorem differentiableOn_doubleSineComplexLogIntegral (tau : ℂ) (htau : 0 < tau.re) :
    DifferentiableOn ℂ (fun z => doubleSineComplexLogIntegral z tau)
      {z : ℂ | 0 < z.re ∧ z.re < tau.re + 1} := by
  let U := {z : ℂ | 0 < z.re ∧ z.re < tau.re + 1}
  unfold doubleSineComplexLogIntegral
  apply differentiableOn_integral_of_locally_bounded
  · intro z hz
    exact (doubleSineComplexKernel_integrableOn z tau htau hz.1 hz.2).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    unfold doubleSineComplexKernel
    fun_prop
  · intro z₀ hz₀
    let A := tau.re + 1
    let r := min z₀.re (A - z₀.re) / 4
    have hz₀A : z₀.re < A := hz₀.2
    have hr : 0 < r := div_pos (lt_min hz₀.1 (sub_pos.mpr hz₀A)) (by norm_num)
    have hrz : r ≤ z₀.re / 4 := by
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hrA : r ≤ (A - z₀.re) / 4 := by
      exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    have hball : Metric.closedBall z₀ r ⊆ U := by
      intro z hz
      have hre := abs_re_sub_le_of_mem_closedBall hz
      rw [abs_le] at hre
      change 0 < z.re ∧ z.re < A
      constructor <;> linarith
    let c := max (A - 2 * (z₀.re - r)) (2 * (z₀.re + r) - A)
    let T := max ‖tau‖ (max (‖tau + 1 - 2 * z₀‖ + 2 * r) 1)
    have hc0 : 0 ≤ c := by
      have hleft : A - 2 * (z₀.re - r) ≤ c := le_max_left _ _
      have hright : 2 * (z₀.re + r) - A ≤ c := le_max_right _ _
      linarith
    have hc : c < tau.re + 1 := by
      change c < A
      rw [max_lt_iff]
      constructor <;> linarith
    have hT : 1 ≤ T := le_max_of_le_right (le_max_right _ _)
    have htauT : ‖tau‖ ≤ T := le_max_left _ _
    obtain ⟨g, hg, hdom⟩ :=
      doubleSineComplexKernel_dominated htau hc0 hc hT
    refine ⟨r, hr, hball, g, hg, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have hre := abs_re_sub_le_of_mem_closedBall hz
    have hdist : ‖z - z₀‖ ≤ r := mem_closedBall_iff_norm.mp hz
    have hw : ‖tau + 1 - 2 * z‖ ≤ T := by
      have hid : tau + 1 - 2 * z = (tau + 1 - 2 * z₀) - 2 * (z - z₀) := by ring
      calc
        ‖tau + 1 - 2 * z‖ ≤ ‖tau + 1 - 2 * z₀‖ + ‖2 * (z - z₀)‖ := by
          rw [hid]
          exact norm_sub_le _ _
        _ ≤ ‖tau + 1 - 2 * z₀‖ + 2 * r := by
          rw [Complex.norm_mul, Complex.norm_ofNat]
          gcongr
        _ ≤ T := le_max_of_le_right (le_max_left _ _)
    have hrew : |(tau + 1 - 2 * z).re| ≤ c := by
      rw [abs_le]
      rw [abs_le] at hre
      have hleft : A - 2 * (z₀.re - r) ≤ c := le_max_left _ _
      have hright : 2 * (z₀.re + r) - A ≤ c := le_max_right _ _
      have hwre : (tau + 1 - 2 * z).re = A - 2 * z.re := by
        simp [A, Complex.mul_re]
      rw [hwre]
      constructor <;> linarith
    exact hdom z tau le_rfl htauT hw hrew t ht

/-- The integral representation is holomorphic in `z` on the source chamber. -/
theorem differentiableOn_doubleSineComplexIntegral (tau : ℂ) (htau : 0 < tau.re) :
    DifferentiableOn ℂ (fun z => doubleSineComplexIntegral z tau)
      {z : ℂ | 0 < z.re ∧ z.re < tau.re + 1} := by
  unfold doubleSineComplexIntegral
  exact ((differentiableOn_doubleSineComplexLogIntegral tau htau).neg.div_const 2).cexp

/-! ### Joint continuity on the source chamber

The chamber `Re τ > 0`, `0 < Re z < Re τ + 1` is open and contains points with `τ` real, so
joint continuity there expresses the value at a positive real modulus as a limit of nearby
complex values.  This is the passage to the real boundary used by the conductor-lowering
comparison, where the upper-half-plane parameters approach a real quadratic modulus.

The proof is dominated convergence along the neighbourhood filter of a chamber point
`(z₀, τ₀)`.  The pointwise limit is `continuousAt_doubleSineComplexKernel`, valid for every
`t > 0` because `sinh(τt) ≠ 0` there.  For the bound, choose `a < Re τ₀` still large enough
that `|Re(τ₀ + 1 - 2z₀)| < a + 1` with room to spare, and `T` larger than `‖τ₀‖` and
`‖τ₀ + 1 - 2z₀‖`; then `doubleSineComplexKernel_dominated`, whose constants depend on `τ` only
through `a`, dominates every pair in a neighbourhood of `(z₀, τ₀)` at once. -/

/-- **The complex logarithmic integral is jointly continuous on the source chamber**
`Re τ > 0`, `0 < Re z < Re τ + 1`. -/
theorem continuousAt_doubleSineComplexLogIntegral {z tau : ℂ} (htau : 0 < tau.re)
    (hz : 0 < z.re) (hzUpper : z.re < tau.re + 1) :
    ContinuousAt (fun p : ℂ × ℂ => doubleSineComplexLogIntegral p.1 p.2) (z, tau) := by
  have hwre : (tau + 1 - 2 * z).re = tau.re + 1 - 2 * z.re := by simp [Complex.mul_re]
  set m := |(tau + 1 - 2 * z).re| with hm
  have hm0 : 0 ≤ m := abs_nonneg _
  have hmlt : m < tau.re + 1 := by
    rw [hm, hwre, abs_lt]
    constructor <;> linarith
  set δ := min ((tau.re + 1 - m) / 4) (tau.re / 2) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ4 : δ ≤ (tau.re + 1 - m) / 4 := min_le_left _ _
  have hδhalf : δ ≤ tau.re / 2 := min_le_right _ _
  set a := tau.re - δ with ha'
  have ha : 0 < a := by simp only [ha']; linarith
  have halt : a < tau.re := by simp only [ha']; linarith
  set c := m + δ with hc'
  have hc0 : 0 ≤ c := by simp only [hc']; linarith
  have hca : c < a + 1 := by simp only [hc', ha']; linarith
  have hmc : m < c := by simp only [hc']; linarith
  set T := max 1 (max (‖tau‖ + 1) (‖tau + 1 - 2 * z‖ + 1)) with hT'
  have hT : 1 ≤ T := le_max_left _ _
  have hTtau : ‖tau‖ < T := by
    have : ‖tau‖ + 1 ≤ T := le_max_of_le_right (le_max_left _ _)
    linarith
  have hTw : ‖tau + 1 - 2 * z‖ < T := by
    have : ‖tau + 1 - 2 * z‖ + 1 ≤ T := le_max_of_le_right (le_max_right _ _)
    linarith
  obtain ⟨g, hg, hdom⟩ := doubleSineComplexKernel_dominated ha hc0 hca hT
  -- One neighbourhood of `(z, τ)` on which all four constraints of the domination hold.
  have hnbhd : ∀ᶠ p : ℂ × ℂ in nhds (z, tau),
      a ≤ p.2.re ∧ ‖p.2‖ ≤ T ∧ ‖p.2 + 1 - 2 * p.1‖ ≤ T ∧ |(p.2 + 1 - 2 * p.1).re| ≤ c := by
    have h1 : ContinuousAt (fun p : ℂ × ℂ => p.2.re) (z, tau) := by fun_prop
    have h2 : ContinuousAt (fun p : ℂ × ℂ => ‖p.2‖) (z, tau) := by fun_prop
    have h3 : ContinuousAt (fun p : ℂ × ℂ => ‖p.2 + 1 - 2 * p.1‖) (z, tau) := by fun_prop
    have h4 : ContinuousAt (fun p : ℂ × ℂ => |(p.2 + 1 - 2 * p.1).re|) (z, tau) := by fun_prop
    filter_upwards [h1.eventually_const_le halt, h2.eventually_le_const hTtau,
      h3.eventually_le_const hTw, h4.eventually_le_const hmc] with p hp1 hp2 hp3 hp4
    exact ⟨hp1, hp2, hp3, hp4⟩
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ))) (l := nhds (z, tau))
    (F := fun p : ℂ × ℂ => fun t : ℝ => doubleSineComplexKernel p.1 p.2 t)
    (f := fun t : ℝ => doubleSineComplexKernel z tau t) g ?_ ?_ hg ?_
  · simp only [doubleSineComplexLogIntegral]
    exact hlim
  · filter_upwards [hnbhd] with p hp
    exact (continuousOn_doubleSineComplexKernel p.1 p.2 (ha.trans_le hp.1)).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [hnbhd] with p hp
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hdom p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 t ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [mem_Ioi] at ht
    exact (continuousAt_doubleSineComplexKernel z tau t (fun h => by simpa [h] using htau.ne')
      ht.ne' (sinh_mul_ofReal_ne_zero_of_re_pos tau htau ht)).tendsto

/-- **The integral representation is jointly continuous on the source chamber.**  In particular
the value at a positive real modulus is the limit of the values at nearby complex parameters,
which identifies the exact real value with a limit from the upper half
plane. -/
theorem continuousAt_doubleSineComplexIntegral {z tau : ℂ} (htau : 0 < tau.re)
    (hz : 0 < z.re) (hzUpper : z.re < tau.re + 1) :
    ContinuousAt (fun p : ℂ × ℂ => doubleSineComplexIntegral p.1 p.2) (z, tau) := by
  unfold doubleSineComplexIntegral
  exact Complex.continuous_exp.continuousAt.comp
    (((continuousAt_doubleSineComplexLogIntegral htau hz hzUpper).neg).div_const 2)

end SIC
