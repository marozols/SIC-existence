/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.DoubleSine.ComplexIntegral
import SICs.SpecialFunctions.DoubleSine.ShiftIntegral

/-!
# The difference equations of the complex double-sine integral

Both difference equations of the complex double-sine integral.

This file proves the two difference equations of the integral representation
[AFK25, equation (8.7), `eq:dsintrep`] of the double sine `S₂(z, τ)` on its source chamber:

```text
S₂(z+1, τ) = S₂(z, τ) / (2 sin(πz/τ))     for 0 < Re z < Re τ,
S₂(z+τ, τ) = S₂(z, τ) / (2 sin(πz))       for 0 < Re z < 1,
```

where `S₂` is `doubleSineComplexIntegral` and `Re τ > 0`. These are the equations satisfied
by Shintani's double gamma ratio (`shintaniDoubleSineGamma_add_one_of_source_chamber` and
`shintaniDoubleSineGamma_add_tau_of_source_chamber`), and the two together characterize the
double sine up to a constant, which is how the integral representation is identified with the
double-gamma ratio in `SICs.SpecialFunctions.DoubleSine.IntegralRepresentation`.

## Mathematical argument

With `w = τ + 1 - 2z`, the addition formula
`sinh((w-2)t) - sinh(wt) = -2 cosh((w-1)t) sinh t` gives the pointwise identity
`K(z+1, τ, t) - K(z, τ, t) = 2 h(τ, τ - 2z, t)` between the double-sine kernel and the shift
kernel of `SICs.SpecialFunctions.DoubleSine.ShiftIntegral`; likewise
`K(z+τ, τ, t) - K(z, τ, t) = 2 h(1, 1 - 2z, t)`. Integrating, the logarithmic integrals differ by
`2H(τ, τ-2z)` and `2H(1, 1-2z)`, whose exponentials are `2 sin(πz/τ)` and `2 sin(πz)`
(`exp_doubleSineShiftLogIntegral_sub_two_mul`, `exp_doubleSineShiftLogIntegral_one_sub_two_mul`).
-/

noncomputable section

open Complex Real MeasureTheory Set

namespace SIC

/-! ### Kernel differences -/

/-- `K(z+1, τ, t) - K(z, τ, t) = 2 h(τ, τ - 2z, t)` wherever the denominators are nonzero. -/
lemma doubleSineComplexKernel_add_one_sub (z tau : ℂ) (t : ℝ) (htau : tau ≠ 0) (ht : t ≠ 0)
    (hs : Complex.sinh (tau * t) ≠ 0) :
    doubleSineComplexKernel (z + 1) tau t - doubleSineComplexKernel z tau t =
      2 * doubleSineShiftKernel tau (tau - 2 * z) t := by
  have htC : (t : ℂ) ≠ 0 := by
    exact_mod_cast ht
  have hsinh_t : Complex.sinh (t : ℂ) ≠ 0 := sinh_ofReal_ne_zero ht
  have hsub :
      Complex.sinh ((tau + 1 - 2 * (z + 1)) * t) =
        Complex.sinh ((tau - 2 * z) * t) * Complex.cosh t -
          Complex.cosh ((tau - 2 * z) * t) * Complex.sinh t := by
    rw [← Complex.sinh_sub]
    congr 1
    ring
  have hadd :
      Complex.sinh ((tau + 1 - 2 * z) * t) =
        Complex.sinh ((tau - 2 * z) * t) * Complex.cosh t +
          Complex.cosh ((tau - 2 * z) * t) * Complex.sinh t := by
    rw [← Complex.sinh_add]
    congr 1
    ring
  unfold doubleSineComplexKernel doubleSineShiftKernel
  rw [hsub, hadd]
  field_simp
  ring

/-- `K(z+τ, τ, t) - K(z, τ, t) = 2 h(1, 1 - 2z, t)` wherever the denominators are nonzero. -/
lemma doubleSineComplexKernel_add_tau_sub (z tau : ℂ) (t : ℝ) (htau : tau ≠ 0) (ht : t ≠ 0)
    (hs : Complex.sinh (tau * t) ≠ 0) :
    doubleSineComplexKernel (z + tau) tau t - doubleSineComplexKernel z tau t =
      2 * doubleSineShiftKernel 1 (1 - 2 * z) t := by
  have htC : (t : ℂ) ≠ 0 := by
    exact_mod_cast ht
  have hsinh_t : Complex.sinh (t : ℂ) ≠ 0 := sinh_ofReal_ne_zero ht
  have hs' : Complex.sinh ((t : ℂ) * tau) ≠ 0 := by
    simpa only [mul_comm] using hs
  have hsub :
      Complex.sinh ((tau + 1 - 2 * (z + tau)) * t) =
        Complex.sinh ((1 - 2 * z) * t) * Complex.cosh (tau * t) -
          Complex.cosh ((1 - 2 * z) * t) * Complex.sinh (tau * t) := by
    rw [← Complex.sinh_sub]
    congr 1
    ring
  have hadd :
      Complex.sinh ((tau + 1 - 2 * z) * t) =
        Complex.sinh ((1 - 2 * z) * t) * Complex.cosh (tau * t) +
          Complex.cosh ((1 - 2 * z) * t) * Complex.sinh (tau * t) := by
    rw [← Complex.sinh_add]
    congr 1
    ring
  unfold doubleSineComplexKernel doubleSineShiftKernel
  simp only [one_mul]
  rw [hsub, hadd]
  field_simp [hs']
  ring

/-! ### The logarithmic integrals -/

/-- `L(z+1, τ) = L(z, τ) + 2H(τ, τ - 2z)` for `0 < Re z < Re τ`, integrating
`doubleSineComplexKernel_add_one_sub` with both kernels integrable on the chamber. -/
theorem doubleSineComplexLogIntegral_add_one (z tau : ℂ) (hz : 0 < z.re)
    (hzUpper : z.re < tau.re) :
    doubleSineComplexLogIntegral (z + 1) tau =
      doubleSineComplexLogIntegral z tau + 2 * doubleSineShiftLogIntegral tau (tau - 2 * z) := by
  have htau : 0 < tau.re := hz.trans hzUpper
  have htau0 : tau ≠ 0 := Complex.ne_zero_of_re_pos htau
  have hzInt : IntegrableOn (doubleSineComplexKernel z tau) (Ioi 0) :=
    doubleSineComplexKernel_integrableOn z tau htau hz (by linarith)
  have hbeta : |(tau - 2 * z).re| < tau.re := by
    simp only [sub_re, mul_re, Complex.re_ofNat, Complex.im_ofNat]
    rw [abs_lt]
    constructor <;> linarith
  have hshiftInt : IntegrableOn (doubleSineShiftKernel tau (tau - 2 * z)) (Ioi 0) :=
    integrableOn_doubleSineShiftKernel tau (tau - 2 * z) hbeta
  unfold doubleSineComplexLogIntegral doubleSineShiftLogIntegral
  calc
    ∫ t in Ioi (0 : ℝ), doubleSineComplexKernel (z + 1) tau t =
        ∫ t in Ioi (0 : ℝ),
          (doubleSineComplexKernel z tau t +
            2 * doubleSineShiftKernel tau (tau - 2 * z) t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have hdiff := doubleSineComplexKernel_add_one_sub z tau t htau0 ht.ne'
        (sinh_mul_ofReal_ne_zero_of_re_pos tau htau ht)
      linear_combination hdiff
    _ = (∫ t in Ioi (0 : ℝ), doubleSineComplexKernel z tau t) +
        ∫ t in Ioi (0 : ℝ), 2 * doubleSineShiftKernel tau (tau - 2 * z) t := by
      exact MeasureTheory.integral_add hzInt (hshiftInt.const_mul 2)
    _ = (∫ t in Ioi (0 : ℝ), doubleSineComplexKernel z tau t) +
        2 * ∫ t in Ioi (0 : ℝ), doubleSineShiftKernel tau (tau - 2 * z) t := by
      rw [MeasureTheory.integral_const_mul]

/-- `L(z+τ, τ) = L(z, τ) + 2H(1, 1 - 2z)` for `Re τ > 0` and `0 < Re z < 1`. -/
theorem doubleSineComplexLogIntegral_add_tau (z tau : ℂ) (htau : 0 < tau.re) (hz : 0 < z.re)
    (hzUpper : z.re < 1) :
    doubleSineComplexLogIntegral (z + tau) tau =
      doubleSineComplexLogIntegral z tau + 2 * doubleSineShiftLogIntegral 1 (1 - 2 * z) := by
  have htau0 : tau ≠ 0 := Complex.ne_zero_of_re_pos htau
  have hzInt : IntegrableOn (doubleSineComplexKernel z tau) (Ioi 0) :=
    doubleSineComplexKernel_integrableOn z tau htau hz (by linarith)
  have hbeta : |(1 - 2 * z).re| < (1 : ℂ).re := by
    simp only [sub_re, one_re, mul_re, Complex.re_ofNat, Complex.im_ofNat]
    rw [abs_lt]
    constructor <;> linarith
  have hshiftInt : IntegrableOn (doubleSineShiftKernel 1 (1 - 2 * z)) (Ioi 0) :=
    integrableOn_doubleSineShiftKernel 1 (1 - 2 * z) hbeta
  unfold doubleSineComplexLogIntegral doubleSineShiftLogIntegral
  calc
    ∫ t in Ioi (0 : ℝ), doubleSineComplexKernel (z + tau) tau t =
        ∫ t in Ioi (0 : ℝ),
          (doubleSineComplexKernel z tau t +
            2 * doubleSineShiftKernel 1 (1 - 2 * z) t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have hdiff := doubleSineComplexKernel_add_tau_sub z tau t htau0 ht.ne'
        (sinh_mul_ofReal_ne_zero_of_re_pos tau htau ht)
      linear_combination hdiff
    _ = (∫ t in Ioi (0 : ℝ), doubleSineComplexKernel z tau t) +
        ∫ t in Ioi (0 : ℝ), 2 * doubleSineShiftKernel 1 (1 - 2 * z) t := by
      exact MeasureTheory.integral_add hzInt (hshiftInt.const_mul 2)
    _ = (∫ t in Ioi (0 : ℝ), doubleSineComplexKernel z tau t) +
        2 * ∫ t in Ioi (0 : ℝ), doubleSineShiftKernel 1 (1 - 2 * z) t := by
      rw [MeasureTheory.integral_const_mul]

/-! ### The difference equations -/

/-- **First difference equation of the integral representation.** For `0 < Re z < Re τ`,

```text
S₂(z+1, τ) = S₂(z, τ) / (2 sin(πz/τ)).
```

This is the period-one law of [95, Shintani (1977), proof of Proposition 5, p. 181] for the
integral of [AFK25, equation (8.7), `eq:dsintrep`]. -/
theorem doubleSineComplexIntegral_add_one (z tau : ℂ) (hz : 0 < z.re)
    (hzUpper : z.re < tau.re) :
    doubleSineComplexIntegral (z + 1) tau =
      doubleSineComplexIntegral z tau / (2 * Complex.sin (π * z / tau)) := by
  unfold doubleSineComplexIntegral
  rw [doubleSineComplexLogIntegral_add_one z tau hz hzUpper,
    show -(doubleSineComplexLogIntegral z tau +
      2 * doubleSineShiftLogIntegral tau (tau - 2 * z)) / 2 =
        -doubleSineComplexLogIntegral z tau / 2 -
          doubleSineShiftLogIntegral tau (tau - 2 * z) by ring,
    Complex.exp_sub, exp_doubleSineShiftLogIntegral_sub_two_mul z tau hz hzUpper]

/-- **Second difference equation of the integral representation.** For `Re τ > 0` and
`0 < Re z < 1`,

```text
S₂(z+τ, τ) = S₂(z, τ) / (2 sin(πz)).
```

This is the period-`τ` law of [95, Shintani (1977), proof of Proposition 5, p. 181] for the
integral of [AFK25, equation (8.7), `eq:dsintrep`]. -/
theorem doubleSineComplexIntegral_add_tau (z tau : ℂ) (htau : 0 < tau.re) (hz : 0 < z.re)
    (hzUpper : z.re < 1) :
    doubleSineComplexIntegral (z + tau) tau =
      doubleSineComplexIntegral z tau / (2 * Complex.sin (π * z)) := by
  unfold doubleSineComplexIntegral
  rw [doubleSineComplexLogIntegral_add_tau z tau htau hz hzUpper,
    show -(doubleSineComplexLogIntegral z tau +
      2 * doubleSineShiftLogIntegral 1 (1 - 2 * z)) / 2 =
        -doubleSineComplexLogIntegral z tau / 2 -
          doubleSineShiftLogIntegral 1 (1 - 2 * z) by ring,
    Complex.exp_sub, exp_doubleSineShiftLogIntegral_one_sub_two_mul z hz hzUpper]

end SIC

end
