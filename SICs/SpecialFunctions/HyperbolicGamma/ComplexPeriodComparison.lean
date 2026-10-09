/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.HyperbolicGamma.Basic

/-!
# Complex-period comparison kernels for the hyperbolic gamma function

The removable-origin kernel in Ruijsenaars' comparison proof, with complex mixed periods and
two fixed positive real equal-period references.

This module follows S. N. M. Ruijsenaars, *First order analytic difference equations and
integrable quantum systems*, J. Math. Phys. 38 (1997), 1069–1146, proof of Proposition III.4,
equations (3.51)–(3.56),
[doi:10.1063/1.531809](https://doi.org/10.1063/1.531809). For complex periods `a₁,a₂`, fixed
real reference periods `a,b`, and complex coefficients `α,β`, it uses

```text
J(y) = (1/(2y)) (a₁a₂/(sinh(a₁y)sinh(a₂y))
                    - αa²/sinh²(ay) - βb²/sinh²(by)).
```

The conditions `α+β=1` and
`αa²+βb²=(a₁²+a₂²)/2` cancel the terms of orders `y⁻²` and `y⁰` in the bracket, respectively.
Thus `J(y)=O(y)` at the origin, exactly as in equation (3.55). Taking two fixed real reference
periods avoids choosing a complex square root for Ruijsenaars' quadratic-mean period; the
equal-period evaluations used later therefore remain the real ones already proved in
`SICs.SpecialFunctions.HyperbolicGamma.EqualPeriods`.

The kernel is analytic at its totalized value `J(0)=0`. Away from the origin it is holomorphic
where its four hyperbolic-sine denominators do not vanish. The final theorem combines this with
the common zero-free strip for periods near a positive real one from
`SICs.Analysis.HyperbolicBounds`.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace SIC

/-! ### The kernel and its parity -/

/-- The two-reference comparison kernel used to extend Ruijsenaars' comparison argument to
complex periods near positive real periods. Its value at the removable origin is totalized to
zero. -/
noncomputable def complexComparisonKernel (a₁ a₂ : ℂ) (a b : ℝ) (α β : ℂ)
    (y : ℂ) : ℂ :=
  1 / (2 * y) *
    (a₁ * a₂ / (Complex.sinh (a₁ * y) * Complex.sinh (a₂ * y)) -
      α * (a : ℂ) ^ 2 / Complex.sinh (a * y) ^ 2 -
      β * (b : ℂ) ^ 2 / Complex.sinh (b * y) ^ 2)

/-- The complex comparison kernel is odd. -/
theorem complexComparisonKernel_neg (a₁ a₂ : ℂ) (a b : ℝ) (α β y : ℂ) :
    complexComparisonKernel a₁ a₂ a b α β (-y) =
      -complexComparisonKernel a₁ a₂ a b α β y := by
  simp [complexComparisonKernel, mul_neg, sinh_neg, neg_mul]

/-! ### The removable origin

We factor `sinh(cy) = cy S_c(y)`, where
`S_c(y) = 1 + c²y²/6 + O(y⁴)`. Products of four such factors have the form
`1 + By² + y⁴P(y)`. The two coefficient equations cancel the constant and quadratic terms in
the numerator after the three fractions are put over a common denominator.
-/

/-- The analytic fifth-order Taylor remainder of `sinh`. -/
private lemma exists_analytic_complex_sinh_remainder :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ w : ℂ,
      Complex.sinh w = w + w ^ 3 / 6 + w ^ 5 * R w := by
  obtain ⟨R, hRa, hR⟩ :=
    (Complex.analyticAt_sinh (x := 0)).exists_eq_sum_add_pow_mul 5
  refine ⟨R, hRa, ?_⟩
  intro w
  simpa [Finset.sum_range_succ, Nat.factorial,
    Complex.iteratedDeriv_even_sinh, Complex.iteratedDeriv_odd_sinh] using hR w

/-- The quadratic coefficient in `sinh(cy)/(cy)`. -/
private def sinhQuadraticCoeff (c : ℂ) : ℂ := c ^ 2 / 6

/-- The analytic fourth-degree coefficient in `sinh(cy)/(cy)`. -/
private def complexComparisonQ (R : ℂ → ℂ) (c y : ℂ) : ℂ :=
  c ^ 4 * R (c * y)

/-- The regular factor `S_c(y) = sinh(cy)/(cy)`. -/
private def complexComparisonS (R : ℂ → ℂ) (c y : ℂ) : ℂ :=
  1 + sinhQuadraticCoeff c * y ^ 2 + complexComparisonQ R c y * y ^ 4

/-- The coefficient of `y²` in `S_p(y)S_q(y)`. -/
private def complexComparisonPairQuadraticCoeff (p q : ℂ) : ℂ :=
  sinhQuadraticCoeff p + sinhQuadraticCoeff q

/-- The analytic remainder after the constant and quadratic terms of `S_p S_q`. -/
private def complexComparisonPairRemainder (R : ℂ → ℂ) (p q y : ℂ) : ℂ :=
  complexComparisonQ R p y + complexComparisonQ R q y +
    sinhQuadraticCoeff p * sinhQuadraticCoeff q +
    y ^ 2 * (sinhQuadraticCoeff p * complexComparisonQ R q y +
      sinhQuadraticCoeff q * complexComparisonQ R p y) +
    y ^ 4 * (complexComparisonQ R p y * complexComparisonQ R q y)

/-- The analytic remainder after the constant and quadratic terms of a product of four regular
hyperbolic-sine factors, grouped into two pairs. -/
private def complexComparisonFourRemainder (R : ℂ → ℂ)
    (p q r s y : ℂ) : ℂ :=
  let B₁ := complexComparisonPairQuadraticCoeff p q
  let B₂ := complexComparisonPairQuadraticCoeff r s
  let P₁ := complexComparisonPairRemainder R p q y
  let P₂ := complexComparisonPairRemainder R r s y
  P₁ + P₂ + B₁ * B₂ + y ^ 2 * (B₁ * P₂ + B₂ * P₁) + y ^ 4 * (P₁ * P₂)

/-- The analytic numerator remaining after the two coefficient cancellations. -/
private def complexComparisonRemainder (R : ℂ → ℂ) (a₁ a₂ : ℂ) (a b : ℝ)
    (α β y : ℂ) : ℂ :=
  complexComparisonFourRemainder R a a b b y -
    α * complexComparisonFourRemainder R a₁ a₂ b b y -
    β * complexComparisonFourRemainder R a₁ a₂ a a y

/-- Taylor factorization of the complex hyperbolic sine. -/
private lemma sinh_eq_mul_complexComparisonS (R : ℂ → ℂ)
    (hR : ∀ w : ℂ, Complex.sinh w = w + w ^ 3 / 6 + w ^ 5 * R w)
    (c y : ℂ) : Complex.sinh (c * y) = (c * y) * complexComparisonS R c y := by
  dsimp [complexComparisonS, complexComparisonQ, sinhQuadraticCoeff]
  rw [hR (c * y)]
  ring

/-- Expansion of a product of two regular hyperbolic-sine factors. -/
private lemma complexComparisonS_mul (R : ℂ → ℂ) (p q y : ℂ) :
    complexComparisonS R p y * complexComparisonS R q y =
      1 + complexComparisonPairQuadraticCoeff p q * y ^ 2 +
        complexComparisonPairRemainder R p q y * y ^ 4 := by
  simp only [complexComparisonS, complexComparisonPairQuadraticCoeff,
    complexComparisonPairRemainder]
  ring

/-- Expansion of a product of four regular hyperbolic-sine factors. -/
private lemma complexComparisonS_mul_four (R : ℂ → ℂ) (p q r s y : ℂ) :
    complexComparisonS R p y * complexComparisonS R q y *
        (complexComparisonS R r y * complexComparisonS R s y) =
      1 + (complexComparisonPairQuadraticCoeff p q +
        complexComparisonPairQuadraticCoeff r s) * y ^ 2 +
        complexComparisonFourRemainder R p q r s y * y ^ 4 := by
  rw [complexComparisonS_mul, complexComparisonS_mul]
  simp only [complexComparisonFourRemainder]
  ring

/-- The coefficient equations cancel the quadratic coefficient of the common numerator. -/
private lemma complexComparisonPairQuadraticCoeff_cancel {a₁ a₂ α β : ℂ} {a b : ℝ}
    (hsum : α + β = 1)
    (hquad : α * (a : ℂ) ^ 2 + β * (b : ℂ) ^ 2 = (a₁ ^ 2 + a₂ ^ 2) / 2) :
    complexComparisonPairQuadraticCoeff a a + complexComparisonPairQuadraticCoeff b b -
        α * (complexComparisonPairQuadraticCoeff a₁ a₂ +
          complexComparisonPairQuadraticCoeff b b) -
        β * (complexComparisonPairQuadraticCoeff a₁ a₂ +
          complexComparisonPairQuadraticCoeff a a) = 0 := by
  simp only [complexComparisonPairQuadraticCoeff, sinhQuadraticCoeff]
  linear_combination (1 / 3 : ℂ) * hquad -
    ((2 * (a : ℂ) ^ 2 + 2 * (b : ℂ) ^ 2 + a₁ ^ 2 + a₂ ^ 2) / 6) * hsum

/-- After putting the three fractions over a common denominator, their numerator is `y⁴`
times an analytic function. -/
private lemma complex_comparison_common_numerator {a₁ a₂ α β y : ℂ} {a b : ℝ}
    (R : ℂ → ℂ) (hsum : α + β = 1)
    (hquad : α * (a : ℂ) ^ 2 + β * (b : ℂ) ^ 2 = (a₁ ^ 2 + a₂ ^ 2) / 2) :
    (complexComparisonS R a y ^ 2 * complexComparisonS R b y ^ 2 -
      α * (complexComparisonS R a₁ y * complexComparisonS R a₂ y *
        complexComparisonS R b y ^ 2) -
      β * (complexComparisonS R a₁ y * complexComparisonS R a₂ y *
        complexComparisonS R a y ^ 2)) =
      y ^ 4 * complexComparisonRemainder R a₁ a₂ a b α β y := by
  have hA := complexComparisonS_mul_four R a a b b y
  have hB := complexComparisonS_mul_four R a₁ a₂ b b y
  have hC := complexComparisonS_mul_four R a₁ a₂ a a y
  have hcancel := complexComparisonPairQuadraticCoeff_cancel hsum hquad
  rw [show complexComparisonS R a y ^ 2 * complexComparisonS R b y ^ 2 =
      complexComparisonS R a y * complexComparisonS R a y *
        (complexComparisonS R b y * complexComparisonS R b y) by ring,
    hA]
  rw [show complexComparisonS R a₁ y * complexComparisonS R a₂ y *
      complexComparisonS R b y ^ 2 =
        complexComparisonS R a₁ y * complexComparisonS R a₂ y *
          (complexComparisonS R b y * complexComparisonS R b y) by ring,
    hB]
  rw [show complexComparisonS R a₁ y * complexComparisonS R a₂ y *
      complexComparisonS R a y ^ 2 =
        complexComparisonS R a₁ y * complexComparisonS R a₂ y *
          (complexComparisonS R a y * complexComparisonS R a y) by ring,
    hC]
  dsimp [complexComparisonRemainder]
  have hconst : 1 - α - β = 0 := by linear_combination -hsum
  linear_combination hconst + y ^ 2 * hcancel

/-- The fourth-degree Taylor coefficient is analytic at the origin. -/
private lemma analyticAt_complexComparisonQ (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0) (c : ℂ) :
    AnalyticAt ℂ (complexComparisonQ R c) 0 := by
  have hlin : AnalyticAt ℂ (fun y : ℂ => c * y) 0 := by fun_prop
  have hcomp : AnalyticAt ℂ (fun y : ℂ => R (c * y)) 0 := by
    have hRc : AnalyticAt ℂ R (c * (0 : ℂ)) := by simpa using hR
    simpa [Function.comp_def] using hRc.comp (f := fun y : ℂ => c * y) hlin
  exact analyticAt_const.mul hcomp

/-- The regular factor `S_c` is analytic at the origin. -/
private lemma analyticAt_complexComparisonS (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0) (c : ℂ) :
    AnalyticAt ℂ (complexComparisonS R c) 0 := by
  unfold complexComparisonS
  exact (analyticAt_const.add (analyticAt_const.mul (by fun_prop))).add
    ((analyticAt_complexComparisonQ R hR c).mul (by fun_prop))

/-- The two-factor remainder is analytic at the origin. -/
private lemma analyticAt_complexComparisonPairRemainder (R : ℂ → ℂ)
    (hR : AnalyticAt ℂ R 0) (p q : ℂ) :
    AnalyticAt ℂ (complexComparisonPairRemainder R p q) 0 := by
  have hp := analyticAt_complexComparisonQ R hR p
  have hq := analyticAt_complexComparisonQ R hR q
  unfold complexComparisonPairRemainder
  fun_prop

/-- The four-factor remainder is analytic at the origin. -/
private lemma analyticAt_complexComparisonFourRemainder (R : ℂ → ℂ)
    (hR : AnalyticAt ℂ R 0) (p q r s : ℂ) :
    AnalyticAt ℂ (complexComparisonFourRemainder R p q r s) 0 := by
  have h₁ := analyticAt_complexComparisonPairRemainder R hR p q
  have h₂ := analyticAt_complexComparisonPairRemainder R hR r s
  unfold complexComparisonFourRemainder
  exact (((h₁.add h₂).add (analyticAt_const.mul analyticAt_const)).add
    ((by fun_prop : AnalyticAt ℂ (fun y : ℂ => y ^ 2) 0).mul
      ((analyticAt_const.mul h₂).add (analyticAt_const.mul h₁)))).add
        ((by fun_prop : AnalyticAt ℂ (fun y : ℂ => y ^ 4) 0).mul (h₁.mul h₂))

/-- The cancelled common-numerator remainder is analytic at the origin. -/
private lemma analyticAt_complexComparisonRemainder (R : ℂ → ℂ)
    (hR : AnalyticAt ℂ R 0) (a₁ a₂ : ℂ) (a b : ℝ) (α β : ℂ) :
    AnalyticAt ℂ (complexComparisonRemainder R a₁ a₂ a b α β) 0 := by
  have h₀ := analyticAt_complexComparisonFourRemainder R hR (a : ℂ) a b b
  have h₁ := analyticAt_complexComparisonFourRemainder R hR a₁ a₂ b b
  have h₂ := analyticAt_complexComparisonFourRemainder R hR a₁ a₂ a a
  unfold complexComparisonRemainder
  fun_prop

/-- Near the origin, the totalized comparison kernel equals its analytic removable model. -/
private lemma kernel_eventuallyEq_model
    {a₁ a₂ α β : ℂ} {a b : ℝ} (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0)
    (hTaylor : ∀ w : ℂ, Complex.sinh w = w + w ^ 3 / 6 + w ^ 5 * R w)
    (hsum : α + β = 1)
    (hquad : α * (a : ℂ) ^ 2 + β * (b : ℂ) ^ 2 = (a₁ ^ 2 + a₂ ^ 2) / 2) :
    complexComparisonKernel a₁ a₂ a b α β =ᶠ[𝓝 (0 : ℂ)]
      fun y => y * complexComparisonRemainder R a₁ a₂ a b α β y /
        (2 * complexComparisonS R a₁ y * complexComparisonS R a₂ y *
          complexComparisonS R a y ^ 2 * complexComparisonS R b y ^ 2) := by
  have hS (c : ℂ) := analyticAt_complexComparisonS R hR c
  have hS0 (c : ℂ) : complexComparisonS R c 0 = 1 := by simp [complexComparisonS]
  filter_upwards [(hS a₁).continuousAt.eventually_ne
      (show complexComparisonS R a₁ 0 ≠ 0 by simp [hS0]),
    (hS a₂).continuousAt.eventually_ne
      (show complexComparisonS R a₂ 0 ≠ 0 by simp [hS0]),
    (hS a).continuousAt.eventually_ne
      (show complexComparisonS R a 0 ≠ 0 by simp [hS0]),
    (hS b).continuousAt.eventually_ne
      (show complexComparisonS R b 0 ≠ 0 by simp [hS0])]
      with y hs₁ hs₂ hsa hsb
  by_cases hy : y = 0
  · subst y
    simp [complexComparisonKernel]
  · have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb
    rw [complexComparisonKernel,
      sinh_eq_mul_complexComparisonS R hTaylor a₁ y,
      sinh_eq_mul_complexComparisonS R hTaylor a₂ y,
      sinh_eq_mul_complexComparisonS R hTaylor a y,
      sinh_eq_mul_complexComparisonS R hTaylor b y]
    field_simp
    have hcommon := complex_comparison_common_numerator (y := y) R hsum hquad
    linear_combination hcommon

/-- The origin of the complex comparison kernel is removable and analytic. This is the
two-reference form of Ruijsenaars (1997), equation (3.55). -/
theorem analyticAt_complexComparisonKernel_zero
    {a₁ a₂ α β : ℂ} {a b : ℝ} (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hsum : α + β = 1)
    (hquad : α * (a : ℂ) ^ 2 + β * (b : ℂ) ^ 2 = (a₁ ^ 2 + a₂ ^ 2) / 2) :
    AnalyticAt ℂ (complexComparisonKernel a₁ a₂ a b α β) 0 := by
  obtain ⟨R, hR, hTaylor⟩ := exists_analytic_complex_sinh_remainder
  have hnum : AnalyticAt ℂ
      (fun y => y * complexComparisonRemainder R a₁ a₂ a b α β y) 0 :=
    analyticAt_id.mul (analyticAt_complexComparisonRemainder R hR a₁ a₂ a b α β)
  have hden : AnalyticAt ℂ (fun y =>
      (2 : ℂ) * complexComparisonS R a₁ y * complexComparisonS R a₂ y *
        complexComparisonS R a y ^ 2 * complexComparisonS R b y ^ 2) 0 := by
    have hS (c : ℂ) := analyticAt_complexComparisonS R hR c
    fun_prop
  have hden0 : (2 : ℂ) * complexComparisonS R a₁ 0 * complexComparisonS R a₂ 0 *
      complexComparisonS R a 0 ^ 2 * complexComparisonS R b 0 ^ 2 ≠ 0 := by
    simp [complexComparisonS]
  have hmodel := hnum.div hden hden0
  exact hmodel.congr (kernel_eventuallyEq_model
    h₁ h₂ ha hb R hR hTaylor hsum hquad).symm

/-- The complex comparison kernel is continuous at its removable origin. Used by the origin
continuity of the hyperbolic comparison kernel in
`SICs.SpecialFunctions.HyperbolicGamma.Comparison`. -/
theorem continuousAt_complexComparisonKernel_zero
    {a₁ a₂ α β : ℂ} {a b : ℝ} (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hsum : α + β = 1)
    (hquad : α * (a : ℂ) ^ 2 + β * (b : ℂ) ^ 2 = (a₁ ^ 2 + a₂ ^ 2) / 2) :
    ContinuousAt (complexComparisonKernel a₁ a₂ a b α β) 0 :=
  (analyticAt_complexComparisonKernel_zero
    h₁ h₂ ha hb hsum hquad).continuousAt

/-! ### Algebraic comparison of the logarithmic integrands -/

/-- Pointwise form of the two-reference comparison identity. For a positive integration
variable, `τ` times the complex-period logarithmic integrand is the weighted sum of two
real equal-period integrands plus `J(t) sin(2tz)`. This is equations (3.51), (3.53), and (3.54)
of Ruijsenaars (1997), with two equal-period references; only `α+β=1` is needed for this
algebraic identity. -/
theorem doubleSineComplexKernel_comparison
    {τ z α β : ℂ} {a b t : ℝ} (hτ : 0 < τ.re) (ha : 0 < a) (hb : 0 < b)
    (ht : 0 < t) (hsum : α + β = 1) :
    τ * (I / 2 * doubleSineComplexKernel ((τ + 1) / 2 + I * z) τ t) =
      α * (a : ℂ) ^ 2 * hyperbolicGammaLogIntegrand a a z t +
        β * (b : ℂ) ^ 2 * hyperbolicGammaLogIntegrand b b z t +
          complexComparisonKernel τ 1 a b α β t *
            Complex.sin (2 * t * z) := by
  rw [mul_I_div_two_doubleSineComplexKernel_eq]
  have hτs : Complex.sinh (τ * t) ≠ 0 :=
    sinh_mul_ofReal_ne_zero_of_re_pos τ hτ ht
  have has : Complex.sinh ((a : ℂ) * t) ≠ 0 :=
    sinh_mul_ofReal_ne_zero_of_re_pos a (by simpa using ha) ht
  have hbs : Complex.sinh ((b : ℂ) * t) ≠ 0 :=
    sinh_mul_ofReal_ne_zero_of_re_pos b (by simpa using hb) ht
  have hts : Complex.sinh (t : ℂ) ≠ 0 := sinh_ofReal_ne_zero ht.ne'
  have hτ0 : τ ≠ 0 := fun h => by simpa [h] using hτ.ne'
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  unfold hyperbolicGammaLogIntegrand complexComparisonKernel
  field_simp
  have hβ : β = 1 - α := by linear_combination hsum
  rw [hβ]
  ring

/-- The pointwise comparison solved for the sine integrand. -/
private lemma complex_comparison_sine_integrand_eq
    {τ z α β : ℂ} {a b t : ℝ} (hτ : 0 < τ.re) (ha : 0 < a) (hb : 0 < b)
    (ht : 0 < t) (hsum : α + β = 1) :
    complexComparisonKernel τ 1 a b α β t * Complex.sin (2 * t * z) =
      τ * (I / 2 * doubleSineComplexKernel ((τ + 1) / 2 + I * z) τ t) -
        α * (a : ℂ) ^ 2 * hyperbolicGammaLogIntegrand a a z t -
          β * (b : ℂ) ^ 2 * hyperbolicGammaLogIntegrand b b z t := by
  have hpoint := doubleSineComplexKernel_comparison
    (τ := τ) (z := z) (α := α) (β := β) hτ ha hb ht hsum
  linear_combination -hpoint

/-! ### The integral comparison

Integrating the pointwise identity gives the two-reference version of Ruijsenaars' comparison
(3.51). The mixed-period integral is the complex double-sine integral, while both reference
integrals are the real equal-period hyperbolic-gamma logarithms already available in `Basic`.
-/

/-- The sine transform of the complex comparison kernel, extending the correction term `d(z)`
of Ruijsenaars (1997), equation (3.53), to two fixed real reference periods. -/
noncomputable def complexComparisonIntegral
    (τ : ℂ) (a b : ℝ) (α β z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ),
    complexComparisonKernel τ 1 a b α β t * Complex.sin (2 * t * z)

/-- The strip condition on `z` puts the shifted argument `(τ+1)/2+iz` in the chamber of the
complex double-sine integral. -/
private lemma complex_comparison_mem_double_sine_chamber {τ z : ℂ}
    (hz : |z.im| < (τ.re + 1) / 2) :
    0 < (((τ + 1) / 2 + I * z).re) ∧
      (((τ + 1) / 2 + I * z).re) < τ.re + 1 := by
  obtain ⟨hzLower, hzUpper⟩ := abs_lt.mp hz
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.I_mul_re]
  constructor <;> linarith

/-- Linearity for the three terms in the comparison integral. -/
private lemma integral_sub_sub_on_Ioi {f g h : ℝ → ℂ}
    (hf : IntegrableOn f (Ioi 0)) (hg : IntegrableOn g (Ioi 0))
    (hh : IntegrableOn h (Ioi 0)) :
    (∫ t in Ioi (0 : ℝ), f t - g t - h t) =
      (∫ t in Ioi (0 : ℝ), f t) - (∫ t in Ioi (0 : ℝ), g t) -
        ∫ t in Ioi (0 : ℝ), h t := by
  change (∫ t in Ioi (0 : ℝ), (f - g - h) t) = _
  calc
    _ = (∫ t in Ioi (0 : ℝ), (f - g) t) - ∫ t in Ioi (0 : ℝ), h t :=
      integral_sub (hf.sub hg) hh
    _ = _ := by
      congr 1
      exact integral_sub hf hg

/-- The integral correction equals the difference of the three logarithmic integrals. -/
private lemma complexComparisonIntegral_eq_sub
    {τ z α β : ℂ} {a b : ℝ} (hτ : 0 < τ.re)
    (hzτ : |z.im| < (τ.re + 1) / 2) (hza : |z.im| < a) (hzb : |z.im| < b)
    (hsum : α + β = 1) :
    complexComparisonIntegral τ a b α β z =
      τ * (I / 2 * doubleSineComplexLogIntegral ((τ + 1) / 2 + I * z) τ) -
        α * (a : ℂ) ^ 2 * hyperbolicGammaLog a a z -
          β * (b : ℂ) ^ 2 * hyperbolicGammaLog b b z := by
  have ha : 0 < a := (abs_nonneg z.im).trans_lt hza
  have hb : 0 < b := (abs_nonneg z.im).trans_lt hzb
  have hchamber := complex_comparison_mem_double_sine_chamber hzτ
  have hK := doubleSineComplexKernel_integrableOn
    ((τ + 1) / 2 + I * z) τ hτ hchamber.1 hchamber.2
  have hGa := integrableOn_hyperbolicGammaLogIntegrand ha ha (by simpa using hza)
  have hGb := integrableOn_hyperbolicGammaLogIntegrand hb hb (by simpa using hzb)
  unfold complexComparisonIntegral doubleSineComplexLogIntegral hyperbolicGammaLog
  calc
    _ = ∫ t in Ioi (0 : ℝ),
        (τ * (I / 2 * doubleSineComplexKernel ((τ + 1) / 2 + I * z) τ t) -
          α * (a : ℂ) ^ 2 * hyperbolicGammaLogIntegrand a a z t -
            β * (b : ℂ) ^ 2 * hyperbolicGammaLogIntegrand b b z t) :=
      setIntegral_congr_fun measurableSet_Ioi (fun _ ht =>
        complex_comparison_sine_integrand_eq hτ ha hb ht hsum)
    _ = (∫ t in Ioi (0 : ℝ),
          τ * (I / 2 * doubleSineComplexKernel ((τ + 1) / 2 + I * z) τ t)) -
        (∫ t in Ioi (0 : ℝ),
          α * (a : ℂ) ^ 2 * hyperbolicGammaLogIntegrand a a z t) -
        ∫ t in Ioi (0 : ℝ),
          β * (b : ℂ) ^ 2 * hyperbolicGammaLogIntegrand b b z t :=
      integral_sub_sub_on_Ioi ((hK.const_mul (I / 2)).const_mul τ)
        (hGa.const_mul (α * (a : ℂ) ^ 2)) (hGb.const_mul (β * (b : ℂ) ^ 2))
    _ = _ := by
      rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]

/-- The two-reference complex-period comparison obtained by integrating the pointwise identity:
`τ(i/2)L = αa²g(a,a;z) + βb²g(b,b;z) + d(z)`. This is the source comparison (3.51),
with its single quadratic-mean reference split into two fixed real references so that `τ` may be
complex. -/
theorem doubleSineComplexLogIntegral_comparison
    {τ z α β : ℂ} {a b : ℝ} (hτ : 0 < τ.re)
    (hzτ : |z.im| < (τ.re + 1) / 2) (hza : |z.im| < a) (hzb : |z.im| < b)
    (hsum : α + β = 1) :
    τ * (I / 2 * doubleSineComplexLogIntegral ((τ + 1) / 2 + I * z) τ) =
      α * (a : ℂ) ^ 2 * hyperbolicGammaLog a a z +
        β * (b : ℂ) ^ 2 * hyperbolicGammaLog b b z +
          complexComparisonIntegral τ a b α β z := by
  have hD := complexComparisonIntegral_eq_sub
    hτ hzτ hza hzb hsum
  linear_combination -hD

/-- Cancels a nonzero scalar against the matching denominator under an outer weight; used for
the quadratic normalization in `doubleSineComplexLogRemainder_comparison`. -/
private lemma weighted_mul_div_two_mul_self {v u c : ℂ} (hc : c ≠ 0) :
    v * c * (u / (2 * c)) = v * (u / 2) := by
  field_simp

/-- After the second coefficient equation is imposed, the comparison preserves the full
quadratic and constant normalization from Ruijsenaars (1997), Proposition III.4. This is the
form to which the shifted-contour bounds apply. -/
theorem doubleSineComplexLogRemainder_comparison
    {τ z α β : ℂ} {a b : ℝ} (hτ : 0 < τ.re)
    (hzτ : |z.im| < (τ.re + 1) / 2) (hza : |z.im| < a) (hzb : |z.im| < b)
    (hsum : α + β = 1)
    (hquad : α * (a : ℂ) ^ 2 + β * (b : ℂ) ^ 2 = (τ ^ 2 + 1) / 2) :
    τ * doubleSineComplexLogRemainder z τ =
      α * (a : ℂ) ^ 2 * hyperbolicGammaLogRemainder a a z +
        β * (b : ℂ) ^ 2 * hyperbolicGammaLogRemainder b b z +
        complexComparisonIntegral τ a b α β z := by
  have ha : 0 < a := (abs_nonneg z.im).trans_lt hza
  have hb : 0 < b := (abs_nonneg z.im).trans_lt hzb
  have hcomparison := doubleSineComplexLogIntegral_comparison
    hτ hzτ hza hzb hsum
  have hτ0 : τ ≠ 0 := fun h => by simpa [h] using hτ.ne'
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hτquad :
      τ * (Real.pi * z ^ 2 / (2 * τ)) = Real.pi * z ^ 2 / 2 := by
    simpa using weighted_mul_div_two_mul_self (v := 1) (u := Real.pi * z ^ 2) hτ0
  have hτconst :
      τ * (Real.pi / 24 * (τ + τ⁻¹)) = Real.pi / 24 * (τ ^ 2 + 1) := by
    field_simp [hτ0]
  rw [hyperbolicGammaLogRemainder_self a z ha.ne',
    hyperbolicGammaLogRemainder_self b z hb.ne']
  unfold doubleSineComplexLogRemainder
  rw [mul_add, mul_add, hτquad, hτconst]
  simp only [mul_add]
  rw [weighted_mul_div_two_mul_self (v := α) (pow_ne_zero 2 ha0),
    weighted_mul_div_two_mul_self (v := β) (pow_ne_zero 2 hb0)]
  rw [hcomparison]
  linear_combination
    -(Real.pi * z ^ 2 / 2) * hsum - (Real.pi / 12) * hquad

/-! ### Holomorphy domains -/

/-- The complex comparison kernel is holomorphic on any set where its four hyperbolic-sine
denominators have no nonzero zeros. At the origin holomorphy is supplied by the two coefficient
cancellations. -/
theorem differentiableOn_complexComparisonKernel
    {a₁ a₂ α β : ℂ} {a b : ℝ} (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hsum : α + β = 1)
    (hquad : α * (a : ℂ) ^ 2 + β * (b : ℂ) ^ 2 = (a₁ ^ 2 + a₂ ^ 2) / 2)
    {s : Set ℂ}
    (hz₁ : ∀ y ∈ s, y ≠ 0 → Complex.sinh (a₁ * y) ≠ 0)
    (hz₂ : ∀ y ∈ s, y ≠ 0 → Complex.sinh (a₂ * y) ≠ 0)
    (hza : ∀ y ∈ s, y ≠ 0 → Complex.sinh (a * y) ≠ 0)
    (hzb : ∀ y ∈ s, y ≠ 0 → Complex.sinh (b * y) ≠ 0) :
    DifferentiableOn ℂ (complexComparisonKernel a₁ a₂ a b α β) s := by
  intro y hy
  by_cases hy0 : y = 0
  · subst y
    exact (analyticAt_complexComparisonKernel_zero
      h₁ h₂ ha hb hsum hquad).differentiableAt.differentiableWithinAt
  · have htwo : (2 : ℂ) * y ≠ 0 := mul_ne_zero (by norm_num) hy0
    have hprod : Complex.sinh (a₁ * y) * Complex.sinh (a₂ * y) ≠ 0 :=
      mul_ne_zero (hz₁ y hy hy0) (hz₂ y hy hy0)
    have hpa : Complex.sinh (a * y) ^ 2 ≠ 0 := pow_ne_zero _ (hza y hy hy0)
    have hpb : Complex.sinh (b * y) ^ 2 ≠ 0 := pow_ne_zero _ (hzb y hy hy0)
    apply DifferentiableAt.differentiableWithinAt
    unfold complexComparisonKernel
    fun_prop (disch := assumption)

/-- A positive real period has no nonzero hyperbolic-sine zero in a strip of half-height less
than its first zero. -/
private lemma sinh_real_mul_ne_zero_of_abs_im_lt {c r : ℝ} (hc : 0 < c)
    (hrc : r < Real.pi / c) {y : ℂ} (hy : |y.im| < r) (hy0 : y ≠ 0) :
    Complex.sinh ((c : ℂ) * y) ≠ 0 := by
  apply sinh_mul_ne_zero_of_abs_im_mul_normSq_lt (by simpa using hc) hy0
  have hrc' : r * c < Real.pi := (lt_div_iff₀ hc).mp hrc
  have him : |y.im| * c < Real.pi :=
    (mul_lt_mul_of_pos_right hy hc).trans hrc'
  have himc := mul_lt_mul_of_pos_right him hc
  simpa [Complex.normSq_apply, mul_assoc] using himc

/-- Every sufficiently small complex neighborhood of a positive real mixed period has one
common strip on which the two-reference comparison kernel is holomorphic. This is the
complex-period zero control needed for the contour in Ruijsenaars (1997), equation (3.56). -/
theorem eventually_differentiableOn_complexComparisonKernel
    {τ₀ r a b : ℝ} (hτ₀ : 0 < τ₀) (ha : 0 < a) (hb : 0 < b)
    (hrτ : r < Real.pi / τ₀) (hrOne : r < Real.pi)
    (hra : r < Real.pi / a) (hrb : r < Real.pi / b) :
    ∀ᶠ τ : ℂ in 𝓝 (τ₀ : ℂ),
      ∀ α β : ℂ, α + β = 1 →
        α * (a : ℂ) ^ 2 + β * (b : ℂ) ^ 2 = (τ ^ 2 + 1) / 2 →
          DifferentiableOn ℂ
            (complexComparisonKernel τ 1 a b α β)
            {y : ℂ | |y.im| < r} := by
  have hτzero := eventually_sinh_mul_ne_zero_of_abs_im_le hτ₀ hrτ
  have hτpos : ∀ᶠ τ : ℂ in 𝓝 (τ₀ : ℂ), 0 < τ.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt (by simpa using hτ₀)
  filter_upwards [hτzero, hτpos] with τ hzero hpos
  intro α β hsum hquad
  apply differentiableOn_complexComparisonKernel
    (fun h => by simpa [h] using hpos.ne') (by norm_num) ha.ne' hb.ne'
    hsum (by simpa using hquad)
  · intro y hy hy0
    exact hzero y hy0 hy.le
  · intro y hy hy0
    exact sinh_real_mul_ne_zero_of_abs_im_lt (c := 1) (by norm_num)
      (by simpa using hrOne) hy hy0
  · intro y hy hy0
    exact sinh_real_mul_ne_zero_of_abs_im_lt ha hra hy hy0
  · intro y hy hy0
    exact sinh_real_mul_ne_zero_of_abs_im_lt hb hrb hy hy0

end SIC

end
