/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The quadratic exponent of the sigma-S generator

The exponent `X(z,τ)` of the exponential prefactor in the double-sine form of `σ_S`, with its
reflection symmetry, shift laws, Kopp's form, continuity, and analyticity.

This module follows [AFK25, equation (8.6), `eq:SFJacobiCocycleTermsDoubleSine`], which writes
the `S`-letter of the Shintani–Faddeev Jacobi cocycle as
`σ_S(z,τ) = exp(X(z,τ)) / S₂(z+1,τ)` with
`X(z,τ) = (πi/(12τ))(6z² + 6(1-τ)z + τ² - 3τ + 1)`. One definition of `X` serves every form
of the generator in the project: the Faddeev generator
`Φ_{S,0,0}(z;τ) = S₂(z+1;1,τ) exp(-X(z,τ))` of [RW26, Radchenko, Wheeler (2026), Section 2.1]
(`SICs.SpecialFunctions.Faddeev.Generator`), the real cocycle generator `sigmaSBase`
(`SICs.Cocycle.SigmaS.Basic`, through its real restriction `sfExpArg`), and Kopp's exponent in
Shintani's product formula (`SICs.SpecialFunctions.DoubleSine.ShintaniProduct`), which is `X`
at `z - 1`.

## The argument

Everything here is polynomial algebra in `z` and `τ⁻¹`. The bracket
`6z² - 6(τ-1)z + τ² - 3τ + 1` is symmetric about `z = (τ-1)/2`, which is the reflection law.
A unit shift of `z` adds `πi(z+1)/τ - πi/2` and a shift by the period `τ` adds
`πi(z+1) - πi/2`; these are the exponential parts of the two difference equations of the
generator. Expanding at `z - 1` gives Kopp's form
`2πi((τ - 3 + τ⁻¹)/24 + (τ - z)(1 - z)/(4τ))`. For `τ ≠ 0` the exponent is jointly continuous
in `(z,τ)`, and for every `τ` it is a polynomial in `z`, so `exp(-X(·,τ))` is entire and the
exponential factor contributes neither zeros nor poles to the generator.
-/

noncomputable section

open Complex Real

namespace SIC

/-! ### The exponent and its symmetries

The definition and the identities that follow from it by `ring` and `field_simp`. -/

/-- The quadratic exponent `X(z,τ) = (πi/(12τ))(6z² + 6(1-τ)z + τ² - 3τ + 1)` of
[AFK25, equation (8.6), `eq:SFJacobiCocycleTermsDoubleSine`], in
`σ_S(z,τ) = exp(X(z,τ)) / S₂(z+1,τ)`. It also normalizes the Faddeev generator
`Φ_{S,0,0}(z;τ) = S₂(z+1;1,τ) exp(-X(z,τ))` of
[RW26, Radchenko, Wheeler (2026), Section 2.1]. -/
def faddeevSExpArg (z τ : ℂ) : ℂ :=
  π * I / (12 * τ) * (6 * z ^ 2 + 6 * (1 - τ) * z + τ ^ 2 - 3 * τ + 1)

/-- The exponent is invariant under the double sine's reflection `z ↦ τ - 1 - z`: the bracket
`6z² - 6(τ-1)z + τ² - 3τ + 1` is symmetric about `z = (τ-1)/2`. The real case is
`sfExpArg_reflect`. -/
theorem faddeevSExpArg_reflect (z τ : ℂ) :
    faddeevSExpArg (τ - 1 - z) τ = faddeevSExpArg z τ := by
  unfold faddeevSExpArg
  ring

/-- A unit shift adds `πi(z+1)/τ - πi/2` to the exponent. This is the exponential part of the
shift laws `faddeevS_add_one` and `sigmaSBase_add_one`. -/
theorem faddeevSExpArg_add_one (z τ : ℂ) (hτ : τ ≠ 0) :
    faddeevSExpArg (z + 1) τ - faddeevSExpArg z τ =
      π * I * ((z + 1) / τ) - π * I / 2 := by
  unfold faddeevSExpArg
  field_simp
  ring

/-- A shift by the period `τ` adds `πi(z+1) - πi/2` to the exponent. This is the exponential
part of the shift laws `faddeevS_add_tau` and `sfExpArg_add_period`. -/
theorem faddeevSExpArg_add_tau (z τ : ℂ) (hτ : τ ≠ 0) :
    faddeevSExpArg (z + τ) τ - faddeevSExpArg z τ =
      π * I * (z + 1) - π * I / 2 := by
  unfold faddeevSExpArg
  field_simp
  ring

/-- At `z - 1` the exponent is Kopp's `2πi((τ - 3 + τ⁻¹)/24 + (τ - z)(1 - z)/(4τ))` of
[72, Kopp (2024), Theorem 4.23, `thm:shin5`] and [72, Kopp (2024), Lemma 7.19,
`lem:deltafrac2`], which `sigmaSKoppExpArg` names. -/
theorem faddeevSExpArg_sub_one (z τ : ℂ) (hτ : τ ≠ 0) :
    faddeevSExpArg (z - 1) τ =
      2 * π * I * ((τ - 3 + τ⁻¹) / 24 + (τ - z) * (1 - z) / (4 * τ)) := by
  unfold faddeevSExpArg
  field_simp
  ring

/-! ### Continuity and analyticity

The exponent is a rational function of `(z,τ)` with the single pole `τ = 0`, and a polynomial in
`z` for every fixed `τ`. -/

/-- The exponent `X(z,τ)` is jointly continuous for `τ ≠ 0`, by its formula in
[AFK25, equation (8.6), `eq:SFJacobiCocycleTermsDoubleSine`]. -/
theorem continuousAt_faddeevSExpArg {z τ : ℂ} (hτ : τ ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => faddeevSExpArg p.1 p.2) (z, τ) := by
  have hfirst : ContinuousAt (fun p : ℂ × ℂ => π * I / (12 * p.2)) (z, τ) :=
    continuousAt_const.div (continuousAt_const.mul continuousAt_snd)
      (mul_ne_zero (by norm_num) hτ)
  have hpoly : ContinuousAt (fun p : ℂ × ℂ =>
      6 * p.1 ^ 2 + 6 * (1 - p.2) * p.1 + p.2 ^ 2 - 3 * p.2 + 1) (z, τ) := by
    fun_prop
  unfold faddeevSExpArg
  exact hfirst.mul hpoly

/-- For every period, `exp(-X(·,τ))` is analytic at every point: the exponential factor of
the generator contributes neither zeros nor poles. -/
theorem analyticAt_exp_neg_faddeevSExpArg (z τ : ℂ) :
    AnalyticAt ℂ (fun w => Complex.exp (-faddeevSExpArg w τ)) z := by
  unfold faddeevSExpArg
  fun_prop

end SIC

end
