/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.DoubleSine.ComplexShifts
import SICs.SpecialFunctions.DoubleSine.Gamma

/-!
# The integral representation of the double sine

Equation (8.7) on the full right-half-plane chamber, including the real double sine.

This file proves the integral representation [AFK25, equation (8.7), `eq:dsintrep`] for
`Re τ > 0` and `0 < Re z < Re τ + 1`: the Barnes
double-gamma ratio `S₂(z;1,τ)` of `SICs.SpecialFunctions.DoubleSine.Gamma` equals the complex
integral `doubleSineComplexIntegral z τ` of `SICs.SpecialFunctions.DoubleSine.ComplexIntegral`
(`shintaniDoubleSineGamma_eq_integral_of_re_pos`). Its upper-half-plane
and positive real restrictions identify the complex integral and the real double sine
with the same gamma quotient
(`shintaniDoubleSineGamma_eq_doubleSine'`). Together with Shintani's Proposition 5 in
`SICs.SpecialFunctions.DoubleSine.Comparison`, the gamma ratio, the q-product, and the
integral agree on the upper-half-plane chamber off the period lattice.

## Mathematical argument

For nonreal `τ`, both sides are holomorphic and nonvanishing on the chamber and satisfy the
same two difference equations there, in `z ↦ z + 1`
(`shintaniDoubleSineGamma_add_one_of_source_chamber`, `doubleSineComplexIntegral_add_one`)
and in `z ↦ z + τ` (their `τ`-shift analogues). Their
quotient `Q` is therefore holomorphic on the strip `0 < Re z < Re τ + 1`, with `Q(z+1) = Q(z)`
for `0 < Re z < Re τ` and `Q(z+τ) = Q(z)` for `0 < Re z < 1`. Since the strip is wider than one
period, `Q` extends to a `1`-periodic entire function
(`exists_differentiable_periodic_one_extension`), which is `τ`-periodic by the identity theorem
(`periodic_of_differentiable_of_eqOn`, from the open strip `0 < Re z < 1`), hence constant by
Liouville's theorem (`apply_eq_apply_of_differentiable_of_periodic`). At the
midpoint `z = (1+τ)/2` both sides equal `1`, so the constant is `1`.

For positive real `τ`, approach the period vertically by `τ+iy`, with `y→0+`.
The gamma quotient is continuous because its denominator is evaluated in the right half plane,
and the integral is jointly continuous on the chamber. The equality therefore passes
to the limit, as in the period continuation of [95, Shintani (1977), paragraph 1.6,
p. 181]. Restricting the argument to the reals then gives `doubleSine'`.

## References

- [AFK25, equation (8.7), `eq:dsintrep`]
- [95, Shintani (1977), Proposition 5]
- [95, Shintani (1977), paragraph 1.6, p. 181]
- [72, Kopp (2024), equation (4.8), `eq:dsinegamma`]
-/

noncomputable section

open Complex Real Filter Topology

namespace SIC

/-! ### The two sides on the chamber -/

/-- The double-gamma ratio is holomorphic in `z` on the source chamber: numerator and
denominator are entire and the denominator `Γ₂(1+τ-z)⁻¹` is nonzero there. -/
private lemma differentiableOn_shintaniDoubleSineGamma (tau : ℂ) (htauRe : 0 < tau.re) :
    DifferentiableOn ℂ (fun z => shintaniDoubleSineGamma z tau)
      {z : ℂ | 0 < z.re ∧ z.re < tau.re + 1} := by
  unfold shintaniDoubleSineGamma barnesDoubleSineGamma
  apply DifferentiableOn.div
  · exact (differentiable_barnesDoubleGammaInv tau
      (Complex.mem_slitPlane_iff.mpr (Or.inl htauRe))).differentiableOn
  · exact (differentiable_barnesDoubleGammaInv tau
      (Complex.mem_slitPlane_iff.mpr (Or.inl htauRe))).comp (by fun_prop) |>.differentiableOn
  · intro z hz
    apply barnesDoubleGammaInv_ne_zero_of_re_pos
      (1 + tau - z) tau (Complex.mem_slitPlane_iff.mpr (Or.inl htauRe)) htauRe.le
    simp only [sub_re, add_re, one_re]
    linarith [hz.2]

/-- `S₂((1+τ)/2;1,τ) = 1`: the ratio's numerator and denominator coincide at the midpoint and
are nonzero. -/
private lemma shintaniDoubleSineGamma_midpoint (tau : ℂ) (htauRe : 0 < tau.re) :
    shintaniDoubleSineGamma ((1 + tau) / 2) tau = 1 := by
  unfold shintaniDoubleSineGamma barnesDoubleSineGamma
  rw [show 1 + tau - (1 + tau) / 2 = (1 + tau) / 2 by ring, div_self]
  apply barnesDoubleGammaInv_ne_zero_of_re_pos
    ((1 + tau) / 2) tau (Complex.mem_slitPlane_iff.mpr (Or.inl htauRe)) htauRe.le
  norm_num [div_re]
  linarith

/-! ### The quotient and its periodicity -/

/-- The quotient `Q(z) = S₂^int(z, τ) / S₂(z;1,τ)` of the integral representation by the
double-gamma ratio. -/
private def integralGammaQuotient (tau z : ℂ) : ℂ :=
  doubleSineComplexIntegral z tau / shintaniDoubleSineGamma z tau

/-- `Q` is holomorphic on the strip `0 < Re z < Re τ + 1`. -/
private lemma differentiableOn_integralGammaQuotient (tau : ℂ) (htauRe : 0 < tau.re) :
    DifferentiableOn ℂ (integralGammaQuotient tau) {z : ℂ | 0 < z.re ∧ z.re < tau.re + 1} := by
  apply (differentiableOn_doubleSineComplexIntegral tau htauRe).div
    (differentiableOn_shintaniDoubleSineGamma tau htauRe)
  intro z hz
  exact shintaniDoubleSineGamma_ne_zero_of_re_pos z tau htauRe hz.1 hz.2

/-- `Q(z+1) = Q(z)` for `0 < Re z < Re τ`: both factors are divided by the same nonzero
`2 sin(πz/τ)`. -/
private lemma integralGammaQuotient_add_one (tau z : ℂ) (hz : 0 < z.re)
    (hzUpper : z.re < tau.re) :
    integralGammaQuotient tau (z + 1) = integralGammaQuotient tau z := by
  have hsine : 2 * Complex.sin (π * z / tau) ≠ 0 := by
    intro hsine
    apply doubleSineComplexIntegral_ne_zero (z + 1) tau
    rw [doubleSineComplexIntegral_add_one z tau hz hzUpper, hsine, div_zero]
  unfold integralGammaQuotient
  rw [doubleSineComplexIntegral_add_one z tau hz hzUpper,
    shintaniDoubleSineGamma_add_one_of_source_chamber z tau hz hzUpper]
  exact div_div_div_cancel_right₀ hsine _ _

/-- `Q(z+τ) = Q(z)` for `0 < Re z < 1`: both factors are divided by the same nonzero
`2 sin(πz)`. -/
private lemma integralGammaQuotient_add_tau (tau z : ℂ) (htauRe : 0 < tau.re)
    (hz : 0 < z.re) (hzUpper : z.re < 1) :
    integralGammaQuotient tau (z + tau) = integralGammaQuotient tau z := by
  have hsine : 2 * Complex.sin (π * z) ≠ 0 := by
    intro hsine
    apply doubleSineComplexIntegral_ne_zero (z + tau) tau
    rw [doubleSineComplexIntegral_add_tau z tau htauRe hz hzUpper, hsine, div_zero]
  unfold integralGammaQuotient
  rw [doubleSineComplexIntegral_add_tau z tau htauRe hz hzUpper,
    shintaniDoubleSineGamma_add_tau_of_source_chamber z tau htauRe hz hzUpper]
  exact div_div_div_cancel_right₀ hsine _ _

/-- Extends `Q` from the strip to an entire function with periods `1` and `τ`; used by
`integralGammaQuotient_eq_one`. -/
private lemma integralGammaQuotient_doubly_periodic_extension (tau : ℂ) (htauRe : 0 < tau.re) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ Function.Periodic g 1 ∧ Function.Periodic g tau ∧
      ∀ z : ℂ, 0 < z.re → z.re < tau.re + 1 → g z = integralGammaQuotient tau z := by
  obtain ⟨g, hg, hgOne, hgEq⟩ := exists_differentiable_periodic_one_extension
    (L := tau.re + 1) (by linarith)
    (differentiableOn_integralGammaQuotient tau htauRe) (by
      intro w hw hwUpper
      exact integralGammaQuotient_add_one tau w hw (by linarith))
  have hgTau : Function.Periodic g tau := by
    refine periodic_of_differentiable_of_eqOn hg tau (U := {w : ℂ | 0 < w.re ∧ w.re < 1})
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const))
      ⟨1 / 2, by constructor <;> norm_num [div_re]⟩ ?_
    intro w hw
    rw [hgEq (w + tau) (by simpa only [add_re] using add_pos hw.1 htauRe)
      (by simp only [add_re]; linarith [hw.2]),
      integralGammaQuotient_add_tau tau w htauRe hw.1 hw.2,
      ← hgEq w hw.1 (by linarith [hw.2])]
  exact ⟨g, hg, hgOne, hgTau, hgEq⟩

/-- `Q = 1` on the strip: its doubly periodic entire extension is constant for `Im τ ≠ 0`
and equals `1` at the midpoint. -/
private lemma integralGammaQuotient_eq_one (tau : ℂ) (htau : tau.im ≠ 0)
    (htauRe : 0 < tau.re) (z : ℂ) (hz : 0 < z.re) (hzUpper : z.re < tau.re + 1) :
    integralGammaQuotient tau z = 1 := by
  obtain ⟨g, hg, hgOne, hgTau, hgEq⟩ :=
    integralGammaQuotient_doubly_periodic_extension tau htauRe
  have hmidLower : 0 < ((1 + tau) / 2).re := by
    norm_num [div_re]
    linarith
  have hmidUpper : ((1 + tau) / 2).re < tau.re + 1 := by
    norm_num [div_re]
    linarith
  calc
    integralGammaQuotient tau z = g z := (hgEq z hz hzUpper).symm
    _ = g ((1 + tau) / 2) :=
      apply_eq_apply_of_differentiable_of_periodic tau htau
        hg hgOne hgTau z ((1 + tau) / 2)
    _ = integralGammaQuotient tau ((1 + tau) / 2) :=
      hgEq ((1 + tau) / 2) hmidLower hmidUpper
    _ = 1 := by
      unfold integralGammaQuotient
      rw [doubleSineComplexIntegral_midpoint tau,
        shintaniDoubleSineGamma_midpoint tau htauRe, div_one]

/-! ### Nonreal periods

The quotient comparison applies whenever `Im τ ≠ 0`. Its shift identities and holomorphy
use only `Re τ > 0`; the imaginary-part hypothesis enters at the Liouville step.
-/

/-- The integral and gamma quotient agree for nonreal periods in the right half plane;
used by `shintaniDoubleSineGamma_eq_integral_of_re_pos`. -/
private lemma doubleSineGamma_eq_integral_of_im_ne_zero
    (z tau : ℂ) (htau : tau.im ≠ 0) (htauRe : 0 < tau.re)
    (hz : 0 < z.re) (hzUpper : z.re < tau.re + 1) :
    shintaniDoubleSineGamma z tau = doubleSineComplexIntegral z tau := by
  have hquotient := integralGammaQuotient_eq_one tau htau htauRe z hz hzUpper
  have hgamma :=
    shintaniDoubleSineGamma_ne_zero_of_re_pos z tau htauRe hz hzUpper
  unfold integralGammaQuotient at hquotient
  exact ((div_eq_one_iff_eq hgamma).mp hquotient).symm

/-! ### Positive real periods

Approach a positive real period from the upper half plane. The denominator stays
nonzero at the boundary because `Re(1+τ-z)>0`. Joint continuity of both sides
passes the equality to the real-period chamber without an irrationality assumption.
-/

/-- The positive real-period restriction of the double-sine integral representation on
`0 < Re z < τ + 1`. It follows by continuity from nonreal periods and supplies the real
boundary case of `shintaniDoubleSineGamma_eq_integral_of_re_pos`. -/
theorem shintaniDoubleSineGamma_eq_integral_ofReal (z : ℂ) (tau : ℝ)
    (htau : 0 < tau) (hz : 0 < z.re) (hzUpper : z.re < tau + 1) :
    shintaniDoubleSineGamma z tau = doubleSineComplexIntegral z tau := by
  have htauSlit : (tau : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr htau
  have hden : barnesDoubleGammaInv (1 + (tau : ℂ) - z) 1 tau ≠ 0 := by
    apply barnesDoubleGammaInv_ne_zero_of_re_pos _ _ htauSlit htau.le
    simp only [sub_re, add_re, one_re, ofReal_re]
    linarith
  have hpath : Tendsto (fun y : ℝ => (z, (tau : ℂ) + (y : ℂ) * I))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (z, (tau : ℂ))) := by
    have hcont : Continuous (fun y : ℝ => (z, (tau : ℂ) + (y : ℂ) * I)) := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  apply tendsto_nhds_unique_of_eventuallyEq
    ((continuousAt_shintaniDoubleSineGamma htauSlit hden).tendsto.comp hpath)
    ((continuousAt_doubleSineComplexIntegral htau hz hzUpper).tendsto.comp hpath)
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact doubleSineGamma_eq_integral_of_im_ne_zero z
    ((tau : ℂ) + (y : ℂ) * I) (by simpa using hy.ne')
    (by simpa using htau) hz (by simpa using hzUpper)

/-! ### The integral representation and its public restrictions -/

/-- The double-sine integral representation for `Re τ > 0` and `0 < Re z < Re τ + 1`:

```text
S₂(z;1,τ) = exp(-½ ∫₀^∞ (sinh((τ+1-2z)t)/(sinh(τt) sinh t) - (τ+1-2z)/(τt)) dt/t).
```

This is [AFK25, equation (8.7), `eq:dsintrep`], with its argument `z+1` renamed `z`,
including both signs of `Im τ` and the positive real boundary value. The left side is the
gamma quotient of [72, Kopp (2024), equation (4.8), `eq:dsinegamma`]. -/
@[source "AFK25, equation (8.7), p. 122, eq:dsintrep"]
theorem shintaniDoubleSineGamma_eq_integral_of_re_pos (z τ : ℂ)
    (hτ : 0 < τ.re) (hz : 0 < z.re) (hzτ : z.re < τ.re + 1) :
    shintaniDoubleSineGamma z τ = doubleSineComplexIntegral z τ := by
  by_cases hIm : τ.im = 0
  · have hτeq : (τ.re : ℂ) = τ := by
      apply Complex.ext <;> simp [hIm]
    rw [← hτeq]
    exact shintaniDoubleSineGamma_eq_integral_ofReal z τ.re
      hτ hz hzτ
  · exact doubleSineGamma_eq_integral_of_im_ne_zero z τ hIm
      hτ hz hzτ

/-- The upper-half-plane restriction of
`shintaniDoubleSineGamma_eq_integral_of_re_pos` on the chamber
`Im τ > 0`, `Re τ > 0`, and `0 < Re z < Re τ + 1`. -/
theorem shintaniDoubleSineGamma_eq_integral (z tau : ℂ) (_htau : 0 < tau.im)
    (htauRe : 0 < tau.re) (hz : 0 < z.re) (hzUpper : z.re < tau.re + 1) :
    shintaniDoubleSineGamma z tau = doubleSineComplexIntegral z tau := by
  exact shintaniDoubleSineGamma_eq_integral_of_re_pos z tau htauRe hz hzUpper

/-- On the real chamber `0 < z < τ + 1` with `τ > 0`, Shintani's gamma quotient is the
real double sine `doubleSine'`. This follows from
`shintaniDoubleSineGamma_eq_integral_ofReal` and
`doubleSineComplexIntegral_ofReal`, preserving the Kurokawa--Koyama convention. -/
theorem shintaniDoubleSineGamma_eq_doubleSine' (z tau : ℝ)
    (htau : 0 < tau) (hz : 0 < z) (hzUpper : z < tau + 1) :
    shintaniDoubleSineGamma z tau = (doubleSine' z tau : ℂ) := by
  rw [shintaniDoubleSineGamma_eq_integral_ofReal z tau htau hz hzUpper,
    doubleSineComplexIntegral_ofReal]

end SIC

end
