/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.NumberTheory.ModularForms.Discriminant
import SICs.SpecialFunctions.DoubleSine.QProducts
import SICs.SpecialFunctions.DoubleSine.SigmaSExponent

/-!
# Shintani's double-sine product

Eta normalization of Shintani's q-product quotient and its period-one law.

Following [95, Shintani (1977), Proposition 5 and its proof on p. 181], this file normalizes
the quotient of the two entire q-products constructed in
`SICs.SpecialFunctions.DoubleSine.QProducts` for periods `(1,τ)` with `Im τ > 0`.
The Dedekind eta inversion theorem determines the normalization:
the origin is a simple zero and the normalized quotient divided by `z` tends to
`2π / sqrt(τ)`. Elementary exponential algebra then gives the period-one law and the
normalization used in [72, Kopp (2024), Theorem 4.23, `thm:shin5`].
The eta product identity also normalizes the unshifted q-product ratio in
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`].

The product here is a pointwise quotient. At common zeros of `f₁` and `f₂`, it returns `0`,
whereas Shintani's meromorphic quotient cancels the common zero. For example both products
vanish at `z = 1`. Nonvanishing outside `ℤ + ℤτ` permits use of the raw quotient there.

This foundation does not identify the product with the double-gamma ratio or complex integral.
The identity with the double-gamma ratio, Shintani's Proposition 5, is proved in
`SICs.SpecialFunctions.DoubleSine.Comparison`; the gamma ratio is identified with the complex
integral in `SICs.SpecialFunctions.DoubleSine.IntegralRepresentation`.
-/

noncomputable section

open Complex Real Set

namespace SIC

/-! ### Dedekind eta normalization

Eta inversion determines the origin slope of the normalized q-product quotient. -/

/-- The Dedekind eta function is its leading exponential times Shintani's first product at
`z = tau`:

```text
eta(tau) = exp(πi tau/12) f₁(tau,tau).
```

This identifies Mathlib's `ModularForm.eta` with the first product used in
[95, Shintani (1977), proof of Proposition 5 on p. 181]. -/
lemma eta_eq_exp_mul_shintaniF1 (tau : ℂ) :
    ModularForm.eta tau =
      Complex.exp (π * I * tau / 12) * shintaniF1 tau tau := by
  unfold ModularForm.eta shintaniF1 qPochhammer
  congr 1
  · simp [Function.Periodic.qParam]
    congr 1
    ring
  · apply tprod_congr
    intro n
    rw [ModularForm.eta_q_eq_cexp]
    congr 2
    ring

/-- The ratio of the unshifted q-product tails is
`ϖ(τ,τ)/ϖ(σ,σ) = exp(πi(σ-τ)/12) η(τ)/η(σ)`.
This follows from `eta_eq_exp_mul_shintaniF1` and gives the exact prefactor
in the last display of [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`]. At `σ=γτ`, the exponential must be retained when converting
that display to eta multipliers; the printed Theorem 3 omits it, whereas
equations (14) and (15), `eq:PhiS.fourier` and `eq:PhiS.5term`, retain it
for `γ=S`. At a fixed point it is one. -/
theorem qPochhammer_self_div_eq_eta (τ σ : ℂ) :
    qPochhammer τ τ / qPochhammer σ σ =
      Complex.exp (π * I * (σ - τ) / 12) * (ModularForm.eta τ / ModularForm.eta σ) := by
  rw [eta_eq_exp_mul_shintaniF1 τ, eta_eq_exp_mul_shintaniF1 σ]
  rw [show π * I * (σ - τ) / 12 = π * I * σ / 12 - π * I * τ / 12 by ring,
    Complex.exp_sub]
  change qPochhammer τ τ / qPochhammer σ σ =
    (Complex.exp (π * I * σ / 12) / Complex.exp (π * I * τ / 12)) *
      ((Complex.exp (π * I * τ / 12) * qPochhammer τ τ) /
        (Complex.exp (π * I * σ / 12) * qPochhammer σ σ))
  have hτ : Complex.exp (π * I * τ / 12) ≠ 0 := Complex.exp_ne_zero _
  have hσ : Complex.exp (π * I * σ / 12) ≠ 0 := Complex.exp_ne_zero _
  symm
  calc
    _ = (Complex.exp (π * I * τ / 12) * Complex.exp (π * I * σ / 12) *
          qPochhammer τ τ) /
        (Complex.exp (π * I * τ / 12) * Complex.exp (π * I * σ / 12) *
          qPochhammer σ σ) := by
          rw [div_mul_div_comm]
          congr 1 <;> ring
    _ = _ := mul_div_mul_left _ _ (mul_ne_zero hτ hσ)

/-- The Dedekind eta function at `-1/tau` is its leading exponential times Shintani's second
product at `z = 0`:

```text
eta(-1/tau) = exp(-πi/(12 tau)) f₂(0,tau).
```

This identifies Mathlib's `ModularForm.eta` with the second product used in
[95, Shintani (1977), proof of Proposition 5 on p. 181]. -/
lemma eta_neg_inv_eq_exp_mul_shintaniF2 (tau : ℂ) :
    ModularForm.eta (-1 / tau) =
      Complex.exp (-π * I / (12 * tau)) * shintaniF2 0 tau := by
  unfold ModularForm.eta shintaniF2 qPochhammer
  congr 1
  · simp [Function.Periodic.qParam]
    congr 1
    ring
  · apply tprod_congr
    intro n
    rw [ModularForm.eta_q_eq_cexp]
    congr 2
    ring

/-- **The Dedekind-eta transformation step in Shintani's Proposition 5 proof.**  For
`im(tau) > 0`, the two specialized products satisfy

```text
exp(-πi/(12 tau)) f₂(0,tau)
  = sqrt(i)⁻¹ sqrt(tau) exp(πi tau/12) f₁(tau,tau).
```

This is [95, Shintani (1977), proof of Proposition 5 on p. 181], obtained from Mathlib's exact
Dedekind-eta inversion theorem `ModularForm.eta_comp_eq_csqrt_I_inv`.  It closes the eta
transformation ingredient of the source's product-side constant calculation; the gamma-side
normalization identities remain separate. -/
lemma shintaniEtaProductTransform (tau : ℂ) (htau : 0 < tau.im) :
    Complex.exp (-π * I / (12 * tau)) * shintaniF2 0 tau =
      (Complex.sqrt I)⁻¹ * Complex.sqrt tau *
        (Complex.exp (π * I * tau / 12) * shintaniF1 tau tau) := by
  rw [← eta_neg_inv_eq_exp_mul_shintaniF2]
  rw [show ModularForm.eta (-1 / tau) =
      (Complex.sqrt I)⁻¹ * Complex.sqrt tau * ModularForm.eta tau by
    simpa [Function.comp_apply, mul_assoc] using ModularForm.eta_comp_eq_csqrt_I_inv htau]
  rw [eta_eq_exp_mul_shintaniF1]

/-- The quadratic exponential phase in Shintani's specialized product formula:

```text
P(z,tau) = πi/2 (z²/tau - (1 + tau⁻¹)z).
```

This is [95, Shintani (1977), Proposition 5] with `(omega₁,omega₂) = (1,tau)`. -/
noncomputable def shintaniDoubleSineProductPhase (z tau : ℂ) : ℂ :=
  π * I / 2 * (z ^ 2 / tau - (1 + tau⁻¹) * z)

/-- The product quotient before Shintani determines its constant:

```text
F̃(z,tau) = f₁(z,tau) / f₂(z,tau) * exp(P(z,tau)).
```

This is the displayed quotient defining `F̃` in [95, Shintani (1977), proof of Proposition 5
on p. 181], on the domain `f₂(z,tau) ≠ 0`. At a common zero of the products it returns `0`;
identifying it with the source's meromorphic continuation requires removal of that singularity. -/
noncomputable def shintaniFTilde (z tau : ℂ) : ℂ :=
  (shintaniF1 z tau / shintaniF2 z tau) *
    Complex.exp (shintaniDoubleSineProductPhase z tau)

/-- The first product has the normalization limit

```text
lim_{z→0} f₁(z,tau) / z = -2πi f₁(tau,tau).
```

This is the first-factor calculation in [95, Shintani (1977), proof of Proposition 5 on p. 181]. -/
lemma tendsto_shintaniF1_div (tau : ℂ) (htau : 0 < tau.im) :
    Filter.Tendsto (fun z : ℂ => shintaniF1 z tau / z)
      (nhdsWithin 0 ({0} : Set ℂ)ᶜ)
      (nhds (-2 * π * I * shintaniF1 tau tau)) := by
  have h := (shintaniF1_hasDerivAt_zero tau htau).tendsto_slope_zero
  simpa only [zero_add, shintaniF1_zero tau, sub_zero, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using h

/-- **The product-side normalization limit in Shintani's proof.**

```text
lim_{z→0} F̃(z,tau) / z = -2πi f₁(tau,tau) / f₂(0,tau).
```

This formalizes the second displayed limit in [95, Shintani (1977), proof of Proposition 5 on
p. 181].  It uses the proved simple zero of `f₁`, holomorphy of both products, and nonvanishing
of `f₂(0,tau)`. -/
lemma tendsto_shintaniFTilde_div (tau : ℂ) (htau : 0 < tau.im) :
    Filter.Tendsto (fun z : ℂ => shintaniFTilde z tau / z)
      (nhdsWithin 0 ({0} : Set ℂ)ᶜ)
      (nhds
        (-2 * π * I * shintaniF1 tau tau /
          shintaniF2 0 tau)) := by
  have hF1 := tendsto_shintaniF1_div tau htau
  have hF2 : Filter.Tendsto (fun z : ℂ => shintaniF2 z tau)
      (nhds 0) (nhds (shintaniF2 0 tau)) :=
    (shintaniF2_differentiable tau htau).continuous.tendsto 0
  have hF2inv : Filter.Tendsto (fun z : ℂ => (shintaniF2 z tau)⁻¹)
      (nhdsWithin 0 ({0} : Set ℂ)ᶜ) (nhds (shintaniF2 0 tau)⁻¹) :=
    (hF2.inv₀ (shintaniF2_zero_ne_zero tau htau)).mono_left inf_le_left
  have hphaseNhds : Filter.Tendsto
      (fun z : ℂ => Complex.exp (shintaniDoubleSineProductPhase z tau))
      (nhds 0) (nhds (Complex.exp (shintaniDoubleSineProductPhase 0 tau))) :=
    (by
      unfold shintaniDoubleSineProductPhase
      fun_prop : ContinuousAt
        (fun z : ℂ => Complex.exp (shintaniDoubleSineProductPhase z tau)) 0)
  have hphase : Filter.Tendsto
      (fun z : ℂ => Complex.exp (shintaniDoubleSineProductPhase z tau))
      (nhdsWithin 0 ({0} : Set ℂ)ᶜ) (nhds 1) := by
    change Filter.Tendsto
      (fun z : ℂ => Complex.exp (shintaniDoubleSineProductPhase z tau))
      (nhds 0 ⊓ Filter.principal ({0} : Set ℂ)ᶜ) (nhds 1)
    simpa [shintaniDoubleSineProductPhase] using hphaseNhds.mono_left inf_le_left
  have hproduct := (hF1.mul hF2inv).mul hphase
  convert hproduct using 1
  · funext z
    unfold shintaniFTilde
    simp only [div_eq_mul_inv]
    ring
  · simp only [mul_one, div_eq_mul_inv]

/-- Shintani's specialized product expression for the Kurokawa--Koyama double sine:

```text
sqrt(i) exp(πi(tau + tau⁻¹)/12) f₁(z,tau) / f₂(z,tau) exp(P(z,tau)).
```

The specialization `(omega₁,omega₂) = (1,tau)` in [95, Shintani (1977), Proposition 5]
represents the same `S₂(z;tau,1)` used by [72, Kopp (2024), Theorem 4.23, `thm:shin5`], since
the double sine is symmetric in its periods.

This declaration names the exact right side of Shintani's formula. Its equality with the
double-gamma ratio wherever `f₂(z,tau) ≠ 0` and `Γ₂(1+tau-z;1,tau)⁻¹ ≠ 0` is
`shintaniDoubleSineGamma_eq_product` in
`SICs.SpecialFunctions.DoubleSine.Comparison`, and
`SICs.SpecialFunctions.DoubleSine.IntegralRepresentation` identifies the gamma ratio with
`doubleSineComplexIntegral` on the source chamber. At a common zero of `f₁` and `f₂`, the pointwise
quotient returns `0`, not the removable value of Shintani's meromorphic expression. -/
noncomputable def shintaniDoubleSineProduct (z tau : ℂ) : ℂ :=
  Complex.sqrt I * Complex.exp (π * I / 12 * (tau + tau⁻¹)) *
    (shintaniF1 z tau / shintaniF2 z tau) *
  Complex.exp (shintaniDoubleSineProductPhase z tau)

/-- The principal square root of `i` is nonzero. -/
lemma sqrt_I_ne_zero : Complex.sqrt I ≠ 0 := by
  rw [Complex.sqrt, Complex.cpow_ne_zero_iff]
  exact Or.inl I_ne_zero

/-- The square of the principal complex square root is its argument.  This is the
`n = 2` case of `Complex.cpow_nat_inv_pow`, isolated for Shintani's constant calculation. -/
private lemma complex_sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  unfold Complex.sqrt
  change (z ^ ((2 : ℂ)⁻¹)) ^ (2 : ℕ) = z
  exact Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)

/-- **Shintani's eta calculation determines the product normalization.**  The constant in
`shintaniDoubleSineProduct` converts the limit of `F̃(z,tau)/z` to

```text
2π / sqrt(tau).
```

This is the final Dedekind-eta calculation in [95, Shintani (1977), proof of Proposition 5 on
p. 181].  It combines `shintaniEtaProductTransform` with the two product nonvanishing
results and the principal-square-root identities. -/
lemma shintaniDoubleSineProduct_limitConstant (tau : ℂ) (htau : 0 < tau.im) :
    Complex.sqrt I * Complex.exp (π * I / 12 * (tau + tau⁻¹)) *
        (-2 * π * I * shintaniF1 tau tau / shintaniF2 0 tau) =
      2 * π / Complex.sqrt tau := by
  have htau0 : tau ≠ 0 := fun hzero => by simp [hzero] at htau
  have hI0 : Complex.sqrt I ≠ 0 := sqrt_I_ne_zero
  have htauSqrt0 : Complex.sqrt tau ≠ 0 := by
    rw [Complex.sqrt, Complex.cpow_ne_zero_iff]
    exact Or.inl htau0
  have hF2 := shintaniF2_zero_ne_zero tau htau
  have hEta := shintaniEtaProductTransform tau htau
  have hExp :
      Complex.exp (π * I / 12 * (tau + tau⁻¹)) *
          Complex.exp (-π * I / (12 * tau)) =
        Complex.exp (π * I * tau / 12) := by
    rw [← Complex.exp_add]
    congr 1
    field_simp
    ring
  have hperiods :
      Complex.sqrt tau * Complex.exp (π * I / 12 * (tau + tau⁻¹)) *
          shintaniF1 tau tau =
        Complex.sqrt I * shintaniF2 0 tau := by
    rw [← hExp] at hEta
    have hmul := congrArg (fun w : ℂ => Complex.sqrt I * w) hEta
    have hcancel :
        Complex.exp (-π * I / (12 * tau)) *
            (Complex.sqrt I * shintaniF2 0 tau) =
          Complex.exp (-π * I / (12 * tau)) *
            (Complex.sqrt tau * Complex.exp (π * I / 12 * (tau + tau⁻¹)) *
              shintaniF1 tau tau) := by
      calc
        _ = Complex.sqrt I *
            (Complex.exp (-π * I / (12 * tau)) * shintaniF2 0 tau) := by ring
        _ = Complex.sqrt I *
            ((Complex.sqrt I)⁻¹ * Complex.sqrt tau *
              ((Complex.exp (π * I / 12 * (tau + tau⁻¹)) *
                  Complex.exp (-π * I / (12 * tau))) *
                shintaniF1 tau tau)) := hmul
        _ = _ := by field_simp
    exact (mul_left_cancel₀ (Complex.exp_ne_zero _) hcancel).symm
  apply (eq_div_iff htauSqrt0).2
  calc
    Complex.sqrt I * Complex.exp (π * I / 12 * (tau + tau⁻¹)) *
          (-2 * π * I * shintaniF1 tau tau / shintaniF2 0 tau) *
        Complex.sqrt tau =
      (-2 * π * I) * Complex.sqrt I *
        (Complex.sqrt tau * Complex.exp (π * I / 12 * (tau + tau⁻¹)) *
          shintaniF1 tau tau) / shintaniF2 0 tau := by ring
    _ = (-2 * π * I) * Complex.sqrt I *
        (Complex.sqrt I * shintaniF2 0 tau) / shintaniF2 0 tau := by
      rw [hperiods]
    _ = (-2 * π * I) * (Complex.sqrt I * Complex.sqrt I) := by
      field_simp
    _ = (-2 * π * I) * I := by
      rw [show Complex.sqrt I * Complex.sqrt I = I by
        simpa only [pow_two] using complex_sqrt_sq I]
    _ = 2 * π := by
      rw [show (-2 * π * I) * I = (-2 * π) * (I * I) by ring,
        Complex.I_mul_I]
      ring

/-- **The fully normalized product has Shintani's double-gamma limit at the origin:**

```text
lim_{z→0} S₂^prod(z,tau) / z = 2π / sqrt(tau).
```

This completes the product side of the constant comparison in [95, Shintani (1977), proof of
Proposition 5 on p. 181].  Together with the gamma-side limit
`tendsto_shintaniDoubleSineGamma_div` it fixes the constant in Shintani's comparison. -/
lemma tendsto_shintaniDoubleSineProduct_div (tau : ℂ) (htau : 0 < tau.im) :
    Filter.Tendsto (fun z : ℂ => shintaniDoubleSineProduct z tau / z)
      (nhdsWithin 0 ({0} : Set ℂ)ᶜ) (nhds (2 * π / Complex.sqrt tau)) := by
  have h : Filter.Tendsto
      (fun z : ℂ =>
        (Complex.sqrt I * Complex.exp (π * I / 12 * (tau + tau⁻¹))) *
          (shintaniFTilde z tau / z))
      (nhdsWithin 0 ({0} : Set ℂ)ᶜ)
      (nhds
        ((Complex.sqrt I * Complex.exp (π * I / 12 * (tau + tau⁻¹))) *
          (-2 * π * I * shintaniF1 tau tau / shintaniF2 0 tau))) :=
    tendsto_const_nhds.mul (tendsto_shintaniFTilde_div tau htau)
  convert h using 1
  · funext z
    unfold shintaniDoubleSineProduct shintaniFTilde
    simp only [div_eq_mul_inv]
    ring
  · rw [shintaniDoubleSineProduct_limitConstant tau htau]

/-! ### Conversion from Shintani--Kopp's normalization -/

/-- The exponent in Shintani--Kopp's form of the `S`-generator identity:

```text
2πi ((tau - 3 + tau⁻¹) / 24 + (tau - z)(1 - z) / (4 tau)).
```

This is `X(z - 1, tau)`, where `X` is `faddeevSExpArg`. See
[72, Kopp (2024), Theorem 4.23, `thm:shin5`], which rephrases
[95, Shintani (1977), Proposition 5]. -/
noncomputable def sigmaSKoppExpArg (z tau : ℂ) : ℂ :=
  faddeevSExpArg (z - 1) tau

/-- Kopp's displayed exponent follows from the shifted form of `faddeevSExpArg`. -/
lemma sigmaSKoppExpArg_eq (z tau : ℂ) (htau : tau ≠ 0) :
    sigmaSKoppExpArg z tau =
      2 * π * I * ((tau - 3 + tau⁻¹) / 24 + ((tau - z) * (1 - z)) / (4 * tau)) :=
  faddeevSExpArg_sub_one z tau htau

/-- Adding the phase contributed by
`(1 - exp(2πiz/tau)) / (2 sin(πz/tau))` converts Shintani--Kopp's exponent exactly to
the exponent of [AFK25, equation (8.6), `eq:SFJacobiCocycleTermsDoubleSine`]. -/
lemma sigmaSKoppExpArg_add_shift (z tau : ℂ) (htau : tau ≠ 0) :
    sigmaSKoppExpArg z tau + π * I * (z / tau) + (-π / 2 * I) =
      faddeevSExpArg z tau := by
  have h := faddeevSExpArg_add_one (z - 1) tau htau
  rw [show z - 1 + 1 = z by ring] at h
  unfold sigmaSKoppExpArg
  linear_combination -h

/-- The principal square root of `i` is `exp(πi/4)`.  This converts the constant in
Shintani's Proposition 5 to Kopp's single exponential. -/
private lemma sqrt_I_eq_exp_pi_div_four_mul_I :
    Complex.sqrt I = Complex.exp (π / 4 * I) := by
  rw [Complex.sqrt_I, Complex.exp_mul_I]
  rw [show (π : ℂ) / 4 = ((π / 4 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  push_cast
  rw [Real.sqrt_inv]
  have hsqrtR : Real.sqrt 2 ≠ 0 := by positivity
  push_cast
  field_simp [hsqrtR]
  have hsqrtC : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)
  rw [hsqrtC]
  ring

/-- The three exponential terms in Shintani's specialized product formula add to Kopp's
exponent.  This is the elementary normalization used by
`shintaniDoubleSineProduct_eq_exp_sigmaSKoppExpArg`. -/
private lemma sigmaSKoppExpArg_eq_shintaniDoubleSineProductPhase (z tau : ℂ)
    (htau : tau ≠ 0) :
    sigmaSKoppExpArg z tau =
      π / 4 * I + π * I / 12 * (tau + tau⁻¹) +
        shintaniDoubleSineProductPhase z tau := by
  rw [sigmaSKoppExpArg_eq z tau htau]
  unfold shintaniDoubleSineProductPhase
  field_simp
  ring

/-- Shintani's specialized product expression is Kopp's exponential times `f₁/f₂`:

```text
S₂^prod(z,tau) = exp(E_K(z,tau)) f₁(z,tau) / f₂(z,tau).
```

This is the exact elementary rearrangement between [95, Shintani (1977), Proposition 5] and
[72, Kopp (2024), Theorem 4.23, `thm:shin5`]. -/
lemma shintaniDoubleSineProduct_eq_exp_sigmaSKoppExpArg
    (z tau : ℂ) (htau : tau ≠ 0) :
    shintaniDoubleSineProduct z tau =
      Complex.exp (sigmaSKoppExpArg z tau) *
        (shintaniF1 z tau / shintaniF2 z tau) := by
  unfold shintaniDoubleSineProduct
  rw [sqrt_I_eq_exp_pi_div_four_mul_I]
  rw [show
      Complex.exp (π / 4 * I) * Complex.exp (π * I / 12 * (tau + tau⁻¹)) *
          (shintaniF1 z tau / shintaniF2 z tau) *
          Complex.exp (shintaniDoubleSineProductPhase z tau) =
        (Complex.exp (π / 4 * I) * Complex.exp (π * I / 12 * (tau + tau⁻¹)) *
          Complex.exp (shintaniDoubleSineProductPhase z tau)) *
          (shintaniF1 z tau / shintaniF2 z tau) by ring]
  rw [← Complex.exp_add, ← Complex.exp_add,
    ← sigmaSKoppExpArg_eq_shintaniDoubleSineProductPhase z tau htau]

/-- Kopp's product exponent changes by `πi(z/tau - 1/2)` under `z ↦ z + 1`.
This is the exponential part of `shintaniDoubleSineProduct_add_one`. -/
private lemma sigmaSKoppExpArg_add_one (z tau : ℂ) (htau : tau ≠ 0) :
    sigmaSKoppExpArg (z + 1) tau =
      sigmaSKoppExpArg z tau + π * I * (z / tau - 1 / 2) := by
  have h := faddeevSExpArg_add_one (z - 1) tau htau
  unfold sigmaSKoppExpArg
  rw [show z + 1 - 1 = z - 1 + 1 by ring]
  linear_combination h

/-- **The complex period-one law for Shintani's product expression.**

```text
S₂^prod(z+1,tau) = S₂^prod(z,tau) / (2 sin(πz/tau)).
```

This is the first double-sine difference equation in [95, Shintani (1977), proof of
Proposition 5 on p. 181].  The proof combines the already formalized difference equations for
`f₁` and `f₂` with the quadratic exponential phase. This identity is about the raw pointwise
quotient, including its default values at common zeros; it reads as the source's
meromorphic identity only where those quotients and the displayed sine division are defined. -/
lemma shintaniDoubleSineProduct_add_one (z tau : ℂ) (htau : 0 < tau.im) :
    shintaniDoubleSineProduct (z + 1) tau =
      shintaniDoubleSineProduct z tau /
        (2 * Complex.sin (π * z / tau)) := by
  have htau0 : tau ≠ 0 := fun hzero => by simp [hzero] at htau
  rw [shintaniDoubleSineProduct_eq_exp_sigmaSKoppExpArg (z + 1) tau htau0,
    shintaniDoubleSineProduct_eq_exp_sigmaSKoppExpArg z tau htau0,
    shintaniF1_add_one z tau,
    shintaniF2_add_one z tau htau,
    sigmaSKoppExpArg_add_one z tau htau0, Complex.exp_add]
  rw [show π * I * (z / tau - 1 / 2) =
      π * I * (z / tau) - π / 2 * I by ring,
    one_sub_exp_two_pi_I_eq_two_exp_shift (z / tau),
    show π * (z / tau) = π * z / tau by ring]
  by_cases hs : Complex.sin (π * z / tau) = 0
  · simp [hs]
  by_cases hf : shintaniF2 z tau = 0
  · simp [hf]
  field_simp [Complex.exp_ne_zero, hs, hf]

end SIC
