/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.DoubleSine.IntegralRepresentation

/-!
# Ruijsenaars' hyperbolic gamma function

The logarithm `g(a₊,a₋;z)` of Ruijsenaars' hyperbolic gamma function: scaling, holomorphy on
its strip, and its identification with the double sine.

This module follows S. N. M. Ruijsenaars, *First order analytic difference equations and
integrable quantum systems*, J. Math. Phys. 38 (1997), 1069–1146, Section III.A,
[doi:10.1063/1.531809](https://doi.org/10.1063/1.531809). For periods `a₊, a₋ > 0` it defines

```text
g(a₊,a₋;z) = ∫₀^∞ (sin 2yz / (2 sinh(a₊y) sinh(a₋y)) - z/(a₊a₋y)) dy/y,
```

equation (3.1), absolutely convergent on the strip `|Im z| < (a₊+a₋)/2` of equation (3.2),
and the hyperbolic gamma function `G(z) = exp(i g(z))` of equation (3.3). Lean has no `a₊`
identifiers; the periods are written `a₁ = a₊` and `a₂ = a₋`. The module supplies the object
whose asymptotics, Ruijsenaars' Proposition III.4, are proved in
`SICs.SpecialFunctions.HyperbolicGamma.Asymptotics`.

## The argument

With `a₋ = 1` and `a₊ = τ`, the substitution `z = (τ+1)/2 + i w` turns the numerator
`sinh((τ+1-2z)t)` of the double-sine kernel `doubleSineComplexKernel` into `-i sin(2wt)`, so
the two integrands agree up to the factor `i/2` at every point: `g(τ,1;w)` is `i/2` times
`doubleSineComplexLogIntegral ((τ+1)/2 + i w) τ`, with no convergence hypothesis. The
substitution `y ↦ λy` gives the scaling law (3.24), which reduces any pair of periods to
`(a₊/a₋, 1)`. Integrability and holomorphy on the strip (3.2) then follow from those of the
complex double-sine integral on its chamber, and the integral representation
`shintaniDoubleSineGamma_eq_integral_ofReal` identifies
`S₂(z;1,τ)` with `G(τ,1;-i(z-(τ+1)/2))` on the chamber `0 < Re z < τ + 1`.
-/

noncomputable section

open Complex MeasureTheory Set

namespace SIC

/-! ### The integral of equation (3.1)

The integrand is totalized at `y = 0`, a null set. -/

/-- The integrand `(sin 2yz / (2 sinh(a₊y) sinh(a₋y)) - z/(a₊a₋y))/y` of Ruijsenaars (1997),
equation (3.1), with `a₁ = a₊` and `a₂ = a₋`. -/
noncomputable def hyperbolicGammaLogIntegrand (a₁ a₂ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  (Complex.sin (2 * y * z) / (2 * Complex.sinh (a₁ * y) * Complex.sinh (a₂ * y)) -
    z / (a₁ * a₂ * y)) / y

/-- Ruijsenaars' logarithm `g(a₊,a₋;z)` of the hyperbolic gamma function
`G(a₊,a₋;z) = exp(i g(a₊,a₋;z))`, Ruijsenaars (1997), equations (3.1) and (3.3), with
`a₁ = a₊` and `a₂ = a₋`. The integral converges absolutely on the strip
`|Im z| < (a₊+a₋)/2` of equation (3.2); outside it Lean's integral is totalized, and no
result uses that value. -/
noncomputable def hyperbolicGammaLog (a₁ a₂ : ℝ) (z : ℂ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), hyperbolicGammaLogIntegrand a₁ a₂ z y

/-- The pointwise scaling identity used in `hyperbolicGammaLog_mul` and in the strip
integrability proof. -/
private lemma hyperbolicGammaLogIntegrand_mul (a₁ a₂ : ℝ) (z : ℂ) {c : ℝ}
    (hc : 0 < c) (y : ℝ) :
    hyperbolicGammaLogIntegrand (c * a₁) (c * a₂) (c * z) y =
      c * hyperbolicGammaLogIntegrand a₁ a₂ z (c * y) := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold hyperbolicGammaLogIntegrand
  push_cast
  rw [show 2 * (y : ℂ) * ((c : ℂ) * z) = 2 * ((c : ℂ) * y) * z by ring,
    show (c : ℂ) * a₁ * y = (a₁ : ℂ) * ((c : ℂ) * y) by ring,
    show (c : ℂ) * a₂ * y = (a₂ : ℂ) * ((c : ℂ) * y) by ring]
  by_cases hy : y = 0
  · subst y; simp
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  field_simp [hcC, hyC]

/-- The scaling law `g(λa₊,λa₋;λz) = g(a₊,a₋;z)` for `λ > 0`, Ruijsenaars (1997),
equation (3.24). It holds for the totalized integral as well, by the substitution
`y ↦ λy`. -/
theorem hyperbolicGammaLog_mul (a₁ a₂ : ℝ) (z : ℂ) {c : ℝ} (hc : 0 < c) :
    hyperbolicGammaLog (c * a₁) (c * a₂) (c * z) = hyperbolicGammaLog a₁ a₂ z := by
  unfold hyperbolicGammaLog
  calc
    _ = ∫ y in Ioi (0 : ℝ), (c : ℂ) * hyperbolicGammaLogIntegrand a₁ a₂ z (c * y) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _
      exact hyperbolicGammaLogIntegrand_mul a₁ a₂ z hc y
    _ = (c : ℂ) * ∫ y in Ioi (0 : ℝ), hyperbolicGammaLogIntegrand a₁ a₂ z (c * y) :=
      integral_const_mul _ _
    _ = _ := by
      rw [integral_comp_mul_left_Ioi (hyperbolicGammaLogIntegrand a₁ a₂ z) 0 hc]
      simp [hc.ne']

/-! ### Comparison with the double-sine integral

At `a₋ = 1` the integrand is `i/2` times the double-sine kernel at `(τ+1)/2 + i w`. -/

/-- For a complex period `τ`, `i/2` times the double-sine kernel at `(τ+1)/2 + iw` is the
complex-period extension of Ruijsenaars' logarithmic integrand. This pointwise algebraic identity
is also used by the complex-period comparison argument. -/
theorem mul_I_div_two_doubleSineComplexKernel_eq (τ w : ℂ) (t : ℝ) :
    I / 2 * doubleSineComplexKernel ((τ + 1) / 2 + I * w) τ t =
      (Complex.sin (2 * t * w) /
          (2 * Complex.sinh (τ * t) * Complex.sinh t) - w / (τ * t)) / t := by
  unfold doubleSineComplexKernel
  have harg :
      ((τ + 1 - 2 * ((τ + 1) / 2 + I * w)) * (t : ℂ)) =
        -((2 * (t : ℂ) * w) * I) := by ring
  rw [harg, Complex.sinh_neg, Complex.sinh_mul_I]
  field_simp
  ring_nf
  simp [I_sq]

/-- The pointwise kernel comparison used by
`hyperbolicGammaLog_eq_doubleSineComplexLogIntegral` and strip integrability. -/
private lemma logIntegrand_eq_doubleSineComplexKernel
    (τ : ℝ) (w : ℂ) (t : ℝ) :
    hyperbolicGammaLogIntegrand τ 1 w t =
      I / 2 * doubleSineComplexKernel ((τ + 1) / 2 + I * w) τ t := by
  simpa [hyperbolicGammaLogIntegrand] using
    (mul_I_div_two_doubleSineComplexKernel_eq (τ : ℂ) w t).symm

/-- With `a₊ = τ` and `a₋ = 1`, `g(τ,1;w) = (i/2) L((τ+1)/2 + i w, τ)`, where `L` is
`doubleSineComplexLogIntegral`, the logarithmic integral of [AFK25, equation (8.7),
`eq:dsintrep`]. The integrands agree pointwise, so no convergence hypothesis is needed. -/
theorem hyperbolicGammaLog_eq_doubleSineComplexLogIntegral (τ : ℝ) (w : ℂ) :
    hyperbolicGammaLog τ 1 w =
      I / 2 * doubleSineComplexLogIntegral ((τ + 1) / 2 + I * w) τ := by
  unfold hyperbolicGammaLog doubleSineComplexLogIntegral
  simp_rw [logIntegrand_eq_doubleSineComplexKernel]
  exact integral_const_mul _ _

/-- The strip for `hyperbolicGammaLog` maps into the chamber of the double-sine integral.
This supplies the chamber conditions in the integrability and holomorphy proofs. -/
private lemma hyperbolicGammaLog_mem_doubleSineChamber {a₁ a₂ : ℝ} (h₂ : 0 < a₂)
    {z : ℂ} (hz : |z.im| < (a₁ + a₂) / 2) :
    0 < ((((a₁ / a₂ : ℝ) : ℂ) + 1) / 2 + I * (z / a₂)).re ∧
      ((((a₁ / a₂ : ℝ) : ℂ) + 1) / 2 + I * (z / a₂)).re < a₁ / a₂ + 1 := by
  have hmid : (a₁ / a₂ + 1) / 2 = ((a₁ + a₂) / 2) / a₂ := by
    field_simp [h₂.ne']
  have hsum : a₁ / a₂ + 1 = (a₁ + a₂) / a₂ := by
    field_simp [h₂.ne']
  have hRe :
      ((((a₁ / a₂ : ℝ) : ℂ) + 1) / 2 + I * (z / a₂)).re =
        ((a₁ + a₂) / 2 - z.im) / a₂ := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re,
      Complex.I_mul_re, Complex.div_ofReal_im, Complex.one_re]
    rw [hmid, sub_div]
    ring
  rw [hRe, hsum]
  obtain ⟨hzLower, hzUpper⟩ := abs_lt.mp hz
  constructor
  · exact div_pos (sub_pos.mpr hzUpper) h₂
  · apply div_lt_div_of_pos_right _ h₂
    linarith

/-- Integrability at the normalized periods `(a₁/a₂, 1)`, used by
`integrableOn_hyperbolicGammaLogIntegrand`. -/
private lemma integrableOn_logIntegrand_normalized {a₁ a₂ : ℝ}
    (h₁ : 0 < a₁) (h₂ : 0 < a₂) {z : ℂ} (hz : |z.im| < (a₁ + a₂) / 2) :
    IntegrableOn (hyperbolicGammaLogIntegrand (a₁ / a₂) 1 (z / a₂)) (Ioi 0) := by
  have hτ : 0 < a₁ / a₂ := div_pos h₁ h₂
  have hchamber := hyperbolicGammaLog_mem_doubleSineChamber h₂ hz
  have hkernel : IntegrableOn
      (doubleSineComplexKernel
        ((((a₁ / a₂ : ℝ) : ℂ) + 1) / 2 + I * (z / a₂)) ((a₁ / a₂ : ℝ) : ℂ))
      (Ioi 0) := by
    apply doubleSineComplexKernel_integrableOn
    · simpa using hτ
    · exact hchamber.1
    · simpa using hchamber.2
  change Integrable (hyperbolicGammaLogIntegrand (a₁ / a₂) 1 (z / a₂))
    (volume.restrict (Ioi 0))
  convert hkernel.const_mul (I / 2) using 1
  funext y
  exact logIntegrand_eq_doubleSineComplexKernel _ _ _

/-- The integrand of equation (3.1) is integrable on `(0, ∞)` for `z` in the strip
`|Im z| < (a₊+a₋)/2` of Ruijsenaars (1997), equation (3.2). -/
theorem integrableOn_hyperbolicGammaLogIntegrand {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂)
    {z : ℂ} (hz : |z.im| < (a₁ + a₂) / 2) :
    IntegrableOn (hyperbolicGammaLogIntegrand a₁ a₂ z) (Ioi 0) := by
  have hcomp : IntegrableOn
      (fun y => hyperbolicGammaLogIntegrand (a₁ / a₂) 1 (z / a₂) (a₂ * y))
      (Ioi 0) := by
    exact (integrableOn_Ioi_comp_mul_left_iff _ 0 h₂).2
      (by simpa using integrableOn_logIntegrand_normalized h₁ h₂ hz)
  have hscaled : IntegrableOn
      (fun y => (a₂ : ℂ) *
        hyperbolicGammaLogIntegrand (a₁ / a₂) 1 (z / a₂) (a₂ * y)) (Ioi 0) :=
    hcomp.const_mul (a₂ : ℂ)
  have hpoint (y : ℝ) :
      hyperbolicGammaLogIntegrand a₁ a₂ z y =
        (a₂ : ℂ) * hyperbolicGammaLogIntegrand (a₁ / a₂) 1 (z / a₂) (a₂ * y) := by
    convert hyperbolicGammaLogIntegrand_mul (a₁ / a₂) 1 (z / a₂) h₂ y using 1
    field_simp [h₂.ne']
  convert hscaled using 1
  funext y
  exact hpoint y

/-- The logarithm `g(a₊,a₋;·)` is holomorphic on the strip `|Im z| < (a₊+a₋)/2`,
Ruijsenaars (1997), the sentence after equation (3.2). -/
theorem differentiableOn_hyperbolicGammaLog {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    DifferentiableOn ℂ (hyperbolicGammaLog a₁ a₂) {z : ℂ | |z.im| < (a₁ + a₂) / 2} := by
  have hτ : 0 < a₁ / a₂ := div_pos h₁ h₂
  have hformula (z : ℂ) :
      hyperbolicGammaLog a₁ a₂ z = I / 2 *
        doubleSineComplexLogIntegral
          ((((a₁ / a₂ : ℝ) : ℂ) + 1) / 2 + I * (z / a₂))
          ((a₁ / a₂ : ℝ) : ℂ) := by
    have hscale := hyperbolicGammaLog_mul (a₁ / a₂) 1 (z / a₂) h₂
    have hscale' : hyperbolicGammaLog a₁ a₂ z =
        hyperbolicGammaLog (a₁ / a₂) 1 (z / a₂) := by
      have hp1 : a₂ * (a₁ / a₂) = a₁ := by field_simp [h₂.ne']
      have hpz : (a₂ : ℂ) * (z / a₂) = z := by field_simp [h₂.ne']
      simpa [hp1, hpz] using hscale
    rw [hscale', hyperbolicGammaLog_eq_doubleSineComplexLogIntegral]
  have hcomp := (differentiableOn_doubleSineComplexLogIntegral
    ((a₁ / a₂ : ℝ) : ℂ) (by simpa using hτ)).comp
    (s := {z : ℂ | |z.im| < (a₁ + a₂) / 2})
    (f := fun z : ℂ => (((a₁ / a₂ : ℝ) : ℂ) + 1) / 2 + I * (z / a₂))
    (by fun_prop)
    (by
      intro z hz
      exact hyperbolicGammaLog_mem_doubleSineChamber h₂ hz)
  convert hcomp.const_mul (I / 2) using 1
  funext z
  exact hformula z

/-- On the chamber `0 < Re z < τ + 1`, the double sine is Ruijsenaars' hyperbolic gamma
function: `S₂(z;1,τ) = G(τ,1;-i(z-(τ+1)/2)) = exp(i g(τ,1;-i(z-(τ+1)/2)))`. This combines
`shintaniDoubleSineGamma_eq_integral_ofReal` with
`hyperbolicGammaLog_eq_doubleSineComplexLogIntegral`. -/
theorem shintaniDoubleSineGamma_eq_exp_hyperbolicGammaLog (z : ℂ) (τ : ℝ) (hτ : 0 < τ)
    (hz : 0 < z.re) (hzUpper : z.re < τ + 1) :
    shintaniDoubleSineGamma z τ =
      Complex.exp (I * hyperbolicGammaLog τ 1 (-I * (z - (τ + 1) / 2))) := by
  rw [shintaniDoubleSineGamma_eq_integral_ofReal z τ hτ hz hzUpper,
    hyperbolicGammaLog_eq_doubleSineComplexLogIntegral]
  unfold doubleSineComplexIntegral
  have harg : (τ + 1) / 2 + I * (-I * (z - (τ + 1) / 2)) = z := by
    ring_nf
    simp [I_sq]
  rw [harg]
  ring_nf
  simp [I_sq]
  ring_nf

/-! ### Normalized logarithmic remainders -/

/-- The normalized hyperbolic-gamma logarithmic remainder
`g(a₊,a₋;z) + πz²/(2a₊a₋) + (π/24)(a₊/a₋ + a₋/a₊)` from Ruijsenaars (1997),
Proposition III.4. -/
noncomputable def hyperbolicGammaLogRemainder (a₁ a₂ : ℝ) (z : ℂ) : ℂ :=
  hyperbolicGammaLog a₁ a₂ z + Real.pi * z ^ 2 / (2 * a₁ * a₂) +
    Real.pi / 24 * (a₁ / a₂ + a₂ / a₁)

/-- The normalized complex double-sine logarithmic remainder corresponding to the correction
in Ruijsenaars (1997), Proposition III.4, after setting the periods to `(τ,1)`. -/
noncomputable def doubleSineComplexLogRemainder (z τ : ℂ) : ℂ :=
  I / 2 * doubleSineComplexLogIntegral ((τ + 1) / 2 + I * z) τ +
    Real.pi * z ^ 2 / (2 * τ) + Real.pi / 24 * (τ + τ⁻¹)

/-- At equal nonzero periods, the constant term in the normalized hyperbolic-gamma logarithmic
remainder is `π/12`. -/
theorem hyperbolicGammaLogRemainder_self (a : ℝ) (z : ℂ) (ha : a ≠ 0) :
    hyperbolicGammaLogRemainder a a z =
      hyperbolicGammaLog a a z + Real.pi * z ^ 2 / (2 * (a : ℂ) ^ 2) +
        Real.pi / 12 := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  unfold hyperbolicGammaLogRemainder
  field_simp [ha0]
  ring

end SIC

end
