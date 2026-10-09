/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.SigmaS.Reduction
import SICs.SpecialFunctions.Faddeev.Divisor
import SICs.SpecialFunctions.DoubleSine.IntegralRepresentation

/-!
# The Faddeev generator and the real sigma-S value

Comparison of the Faddeev generator with `sigmaSBase` and `sigmaSHonest` on the real line.

This module follows [RW26, Radchenko, Wheeler (2026), Section 2.1] and the double-sine
comparison in the proof of Proposition 5, `prop:starkfaddeev`.

## The argument

On the chamber `-1 < z < τ`, the gamma quotient equals the real double-sine integral,
which gives the reciprocal of `sigmaSBase`. Outside the real period lattice, the Barnes
zero set keeps the generator's denominator nonzero. Iterating the period-one equation
transports the chamber identity to all such real points, where it becomes the reciprocal
of `sigmaSHonest`.
-/

noncomputable section

open Complex Real

namespace SIC

/-- On `-1 < z < τ`, `Φ_{S,0,0}(z;τ) = σ_S(z,τ)⁻¹`. This compares the gamma-quotient
generator with [AFK25, equation (8.6), `eq:SFJacobiCocycleTermsDoubleSine`] through
`shintaniDoubleSineGamma_eq_doubleSine'`. -/
theorem faddeevS_eq_inv_sigmaSBase (z τ : ℝ) (hτ : 0 < τ)
    (hz : -1 < z) (hzu : z < τ) :
    faddeevS z τ = (sigmaSBase z τ)⁻¹ := by
  have hS := shintaniDoubleSineGamma_eq_doubleSine' (z + 1) τ hτ
    (by linarith) (by linarith)
  have harg : ((z + 1 : ℝ) : ℂ) = (z : ℂ) + 1 := by push_cast; ring
  rw [harg] at hS
  have hX : faddeevSExpArg z τ = sfExpArg z τ := rfl
  rw [faddeevS, hS, hX, sigmaSBase_eq_exp_div, inv_div, Complex.exp_neg]
  ring

/-- The gamma quotient's denominator is nonzero off `ℤτ + ℤ`. This specializes
`faddeevS_denominator_ne_zero_of_not_mem_lattice` to real arguments. -/
lemma SigmaSLatticeFree.faddeevS_den_ne_zero {z τ : ℝ}
    (hz : SigmaSLatticeFree τ z) (hτ : 0 < τ) :
    barnesDoubleGammaInv ((τ : ℂ) - z) 1 τ ≠ 0 := by
  exact faddeevS_denominator_ne_zero_of_not_mem_lattice (z : ℂ) (τ : ℂ)
    (Complex.ofReal_mem_slitPlane.mpr hτ)
    ((sigmaSLatticeFree_iff_not_isPeriodLatticePoint τ z).mp hz)

/-- The product of the Faddeev generator and the real evaluator is invariant under a unit shift.
Used by `faddeevS_mul_sigmaSHonest_add_int`. -/
private lemma faddeevS_mul_sigmaSHonest_add_one (w τ : ℝ) (hτ : 0 < τ)
    (hw : SigmaSLatticeFree τ w) :
    faddeevS ((w + 1 : ℝ) : ℂ) τ * sigmaSHonest (w + 1) τ =
      faddeevS w τ * sigmaSHonest w τ := by
  have hslit : (τ : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.mpr hτ
  have hw1 : SigmaSLatticeFree τ (w + 1) := by
    simpa using hw.add 0 1
  have hden1 := hw1.faddeevS_den_ne_zero hτ
  have hden1' : barnesDoubleGammaInv ((τ : ℂ) - w - 1) 1 τ ≠ 0 := by
    have harg : (τ : ℂ) - w - 1 = (τ : ℂ) - ((w + 1 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg]
    exact hden1
  have hF : faddeevS ((w + 1 : ℝ) : ℂ) τ *
      (1 - Complex.exp (2 * π * I * (((w + 1 : ℝ) : ℂ) / τ))) = faddeevS w τ := by
    have h := faddeevS_add_one w τ hslit hden1'
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using h
  have hσ : sigmaSHonest (w + 1) τ = sigmaSHonest w τ *
      (1 - Complex.exp (2 * π * I * (((w + 1 : ℝ) : ℂ) / τ))) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using
      (sigmaSHonest_add_one w τ hτ hw)
  rw [hσ]
  calc
    faddeevS ((w + 1 : ℝ) : ℂ) τ *
        (sigmaSHonest w τ * (1 - Complex.exp (2 * π * I * (((w + 1 : ℝ) : ℂ) / τ)))) =
        (faddeevS ((w + 1 : ℝ) : ℂ) τ *
          (1 - Complex.exp (2 * π * I * (((w + 1 : ℝ) : ℂ) / τ)))) *
          sigmaSHonest w τ := by ring
    _ = _ := by rw [hF]

/-- The unit-shift invariant is unchanged under every integral translation.
Used by `faddeevS_eq_inv_sigmaSHonest` to transport the chamber comparison. -/
private lemma faddeevS_mul_sigmaSHonest_add_int (w τ : ℝ) (hτ : 0 < τ)
    (hw : SigmaSLatticeFree τ w) (n : ℤ) :
    faddeevS ((w + (n : ℝ) : ℝ) : ℂ) τ * sigmaSHonest (w + (n : ℝ)) τ =
      faddeevS w τ * sigmaSHonest w τ := by
  exact SigmaSLatticeFree.add_intCast_of_add_one_iff
    (P := fun u => faddeevS (u : ℂ) τ * sigmaSHonest u τ =
      faddeevS w τ * sigmaSHonest w τ)
    (by
      intro u hu
      rw [faddeevS_mul_sigmaSHonest_add_one u τ hτ hu]) hw (by rfl) n

/-- On the base chamber, the two reciprocal values multiply to one.
Used by `faddeevS_eq_inv_sigmaSHonest` after reducing its argument. -/
private lemma faddeevS_mul_sigmaSHonest_base (w τ : ℝ) (hτ : 0 < τ)
    (hw : -1 < w) (hwu : w < τ) :
    faddeevS w τ * sigmaSHonest w τ = 1 := by
  have hσ : sigmaSHonest w τ = sigmaSBase w τ := by
    simpa only [sub_zero, Int.cast_zero, sigmaS_zero_zero] using
      sigmaSHonest_eq_sigmaS_of_mem w τ hτ 0 (by simpa using hw) (by simpa using hwu)
  have hbase : sigmaSBase w τ ≠ 0 := by
    rw [sigmaSBase_eq_exp_div]
    exact div_ne_zero (Complex.exp_ne_zero _)
      (by exact_mod_cast doubleSine_ne_zero (w + 1) τ 1)
  rw [faddeevS_eq_inv_sigmaSBase w τ hτ hw hwu, hσ]
  exact inv_mul_cancel₀ hbase

/-- At every positive real period and every real point off `ℤτ + ℤ`, the complex generator
agrees with the reciprocal real generator. This extends
`faddeevS_eq_inv_sigmaSBase` by the period-one shift of
[RW26, Radchenko, Wheeler (2026), Section 2.1]. -/
theorem faddeevS_eq_inv_sigmaSHonest (z τ : ℝ) (hτ : 0 < τ)
    (hz : SigmaSLatticeFree τ z) :
    faddeevS z τ = (sigmaSHonest z τ)⁻¹ := by
  let w : ℝ := z - sfShift z
  have hw : SigmaSLatticeFree τ w := by
    simpa [w, sub_eq_add_neg] using hz.add 0 (-sfShift z)
  have hwu : -1 < w := neg_one_lt_sub_sfShift z
  have hwτ : w < τ := sub_sfShift_lt z τ hτ
  have hshift := faddeevS_mul_sigmaSHonest_add_int w τ hτ hw (sfShift z)
  have harg : w + (sfShift z : ℝ) = z := by dsimp [w]; ring
  rw [harg] at hshift
  have hprod : faddeevS z τ * sigmaSHonest z τ = 1 :=
    hshift.trans (faddeevS_mul_sigmaSHonest_base w τ hτ hwu hwτ)
  exact (mul_eq_one_iff_eq_inv₀ (right_ne_zero_of_mul_eq_one hprod)).mp hprod

end SIC

end
