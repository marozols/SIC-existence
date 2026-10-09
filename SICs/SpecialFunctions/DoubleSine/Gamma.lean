/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.BarnesDoubleGamma.Continuity
import SICs.SpecialFunctions.BarnesDoubleGamma.Difference

/-!
# The Barnes double sine as a double-gamma quotient

The double-gamma ratio, its meromorphy and continuity, both shift laws, and the limit `2π/√τ`.

This file defines the double sine of [95, Shintani (1977), Proposition 5] and
[72, Kopp (2024), equation (4.8), `eq:dsinegamma`] as

```text
S₂(z; omega₁,omega₂)
  = Gamma₂(omega₁+omega₂-z) / Gamma₂(z)
  = Gamma₂(z)⁻¹ / Gamma₂(omega₁+omega₂-z)⁻¹.
```

The pointwise quotient is total: division by zero returns Lean's default value. Results
reading it as the source's meromorphic double sine therefore carry the nonvanishing
hypotheses their domains need. For periods `(1,tau)`, the double-gamma divisor shows that
both numerator and denominator are nonzero when `Re(tau)>0` and `0<Re(z)<1+Re(tau)`,
including positive real periods and the source chamber of
[AFK25, equation (8.7), `eq:dsintrep`]. Joint continuity of the inverse double gamma gives
continuity of this quotient away from its poles on the slit-plane period domain of
[95, Shintani (1977), paragraph 1.6, p. 181]. Entire dependence of the inverse double
gamma on its argument gives meromorphy of the quotient and analyticity wherever its
denominator is nonzero, throughout the same period domain.

For the period-one equation, we follow the proof of Shintani's Proposition 5 on p. 181.
Apply the inverse-double-gamma difference equation at `z` and `tau-z`, then use Euler's
gamma reflection formula. Clearing the double-sine denominators first gives an identity
of entire functions; division gives the quotient identity wherever those denominators
are nonzero. In particular, the source's period law holds on the overlap chamber
`0<Re(z)<Re(tau)`. The second-period equation follows by the same reflection
calculation. Both cleared equations hold on the slit plane.

At the origin the inverse double gamma has derivative one. Its evaluated denominator
at `1+tau` therefore gives Shintani's normalization `lim S₂(z;1,tau)/z = 2pi/sqrt(tau)`.

These results supply the gamma-quotient side of the comparison with the complex integral
and Shintani product. The constructions retain their distinct domains and totalizations.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace SIC

/-! ### The quotient and its continued period domain

The cone divisor excludes zeros of both gamma factors on the right-half-plane chamber,
including positive real periods. Joint continuity follows by composing the denominator
with `(z,τ) ↦ (1+τ-z,τ)` and dividing where this factor is nonzero.
-/

/-- The Barnes double sine as the ratio

```text
S₂(z; omega₁,omega₂)
  = Gamma₂(z)⁻¹ / Gamma₂(omega₁+omega₂-z)⁻¹.
```

This is [72, Kopp (2024), equation (4.8), `eq:dsinegamma`] and the convention used by
[95, Shintani (1977), Proposition 5].

Where the displayed denominator vanishes -- that is, at a pole of the source's meromorphic `S₂`
-- Lean's division returns its default value, so a result reading this declaration as the
meromorphic double sine carries a nonvanishing hypothesis for its own domain. -/
noncomputable def barnesDoubleSineGamma (z omega₁ omega₂ : ℂ) : ℂ :=
  barnesDoubleGammaInv z omega₁ omega₂ /
    barnesDoubleGammaInv (omega₁ + omega₂ - z) omega₁ omega₂

/-- The specialization `S₂(z;1,tau)` used in Shintani's Proposition 5.  The period symmetry of
the inverse double gamma (`barnesDoubleGammaInv_symm`) identifies it with Kopp's notation
`S₂(z;tau,1)`. -/
noncomputable def shintaniDoubleSineGamma (z tau : ℂ) : ℂ :=
  barnesDoubleSineGamma z 1 tau

/-- On `Re τ > 0` and `0 < Re z < Re τ + 1`, both gamma factors are nonzero, so
`S₂(z;1,τ) ≠ 0`. This is the chamber consequence of
`barnesDoubleGammaInv_eq_zero_iff`, including positive real periods. -/
lemma shintaniDoubleSineGamma_ne_zero_of_re_pos (z tau : ℂ)
    (htau : 0 < tau.re) (hz : 0 < z.re) (hzUpper : z.re < tau.re + 1) :
    shintaniDoubleSineGamma z tau ≠ 0 := by
  have htauSlit : tau ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl htau)
  have hdenRe : 0 < (1 + tau - z).re := by
    simp only [sub_re, add_re, one_re]
    linarith
  unfold shintaniDoubleSineGamma barnesDoubleSineGamma
  exact div_ne_zero
    (barnesDoubleGammaInv_ne_zero_of_re_pos z tau htauSlit htau.le hz)
    (barnesDoubleGammaInv_ne_zero_of_re_pos
      (1 + tau - z) tau htauSlit htau.le hdenRe)

/-- The gamma quotient `S₂(z;1,τ)` is jointly continuous for `τ` in the slit plane away
from its poles. This is the quotient consequence of `continuousAt_barnesDoubleGammaInv`;
the denominator condition prevents totalized division at a pole. -/
theorem continuousAt_shintaniDoubleSineGamma {z tau : ℂ}
    (htau : tau ∈ Complex.slitPlane)
    (hden : barnesDoubleGammaInv (1 + tau - z) 1 tau ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => shintaniDoubleSineGamma p.1 p.2) (z, tau) := by
  unfold shintaniDoubleSineGamma barnesDoubleSineGamma
  have hmap : ContinuousAt (fun p : ℂ × ℂ => (1 + p.2 - p.1, p.2)) (z, tau) :=
    ((continuousAt_const.add continuousAt_snd).sub continuousAt_fst).prodMk continuousAt_snd
  have hdenCont : ContinuousAt
      (fun p : ℂ × ℂ => barnesDoubleGammaInv (1 + p.2 - p.1) 1 p.2) (z, tau) :=
    ContinuousAt.comp
      (f := fun p : ℂ × ℂ => (1 + p.2 - p.1, p.2))
      (g := fun p : ℂ × ℂ => barnesDoubleGammaInv p.1 1 p.2)
      (continuousAt_barnesDoubleGammaInv (z := 1 + tau - z) htau) hmap
  exact (continuousAt_barnesDoubleGammaInv (z := z) htau).div hdenCont hden

/-- The reflected inverse Barnes double gamma is analytic at every point for a slit-plane
period. This packages composition with `w ↦ 1 + τ - w`. -/
theorem analyticAt_barnesDoubleGammaInv_reflect (z τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun w => barnesDoubleGammaInv (1 + τ - w) 1 τ) z := by
  have hreflect : AnalyticAt ℂ (fun w : ℂ => 1 + τ - w) z := by fun_prop
  simpa only [Function.comp_def] using
    ((differentiable_barnesDoubleGammaInv τ hτ).analyticAt
      (1 + τ - z)).comp hreflect

/-- The gamma quotient `S₂(z;1,τ)` is meromorphic in `z` for every slit-plane period `τ`.
This follows from `differentiable_barnesDoubleGammaInv` for its two
gamma factors. Meromorphy allows the totalized values at poles. -/
theorem meromorphicAt_shintaniDoubleSineGamma (z τ : ℂ) (hτ : τ ∈ Complex.slitPlane) :
    MeromorphicAt (fun w => shintaniDoubleSineGamma w τ) z := by
  have hnum := (differentiable_barnesDoubleGammaInv τ hτ).analyticAt z
  have hden := analyticAt_barnesDoubleGammaInv_reflect z τ hτ
  change MeromorphicAt
    ((fun w : ℂ => barnesDoubleGammaInv w 1 τ) /
      (fun w : ℂ => barnesDoubleGammaInv (1 + τ - w) 1 τ)) z
  exact hnum.meromorphicAt.div hden.meromorphicAt

/-- The gamma quotient `S₂(z;1,τ)` is analytic where its displayed denominator is nonzero.
This is the pointwise analytic form of `meromorphicAt_shintaniDoubleSineGamma`. -/
theorem analyticAt_shintaniDoubleSineGamma (z τ : ℂ) (hτ : τ ∈ Complex.slitPlane)
    (hz : barnesDoubleGammaInv (1 + τ - z) 1 τ ≠ 0) :
    AnalyticAt ℂ (fun w => shintaniDoubleSineGamma w τ) z := by
  have hnum := (differentiable_barnesDoubleGammaInv τ hτ).analyticAt z
  have hden := analyticAt_barnesDoubleGammaInv_reflect z τ hτ
  change AnalyticAt ℂ
    ((fun w : ℂ => barnesDoubleGammaInv w 1 τ) /
      (fun w : ℂ => barnesDoubleGammaInv (1 + τ - w) 1 τ)) z
  exact hnum.div hden hz

/-! ### The double-sine period-one equation

In Shintani's proof of Proposition 5, the two reciprocal-gamma multipliers combine by
Euler's reflection formula to `sin(pi z/tau)/pi`. Their exponential multipliers combine
to `1/(2pi)`. Clearing these constants gives the double-sine shift without cancelling a
gamma value at a pole. The quotient statement is then restricted to its actual domain.
-/

/-- Euler's reflection formula in entire reciprocal-gamma form:
`Gamma(w)⁻¹ Gamma(1-w)⁻¹ = sin(pi w)/pi`. This is the reciprocal of Mathlib's
`Complex.Gamma_mul_Gamma_one_sub`, used in `barnesDoubleGammaInv_reflect_add_one`. -/
private lemma inv_Gamma_mul_inv_Gamma_one_sub (w : ℂ) :
    (Complex.Gamma w)⁻¹ * (Complex.Gamma (1 - w))⁻¹ =
      Complex.sin (Real.pi * w) / Real.pi := by
  rw [← mul_inv, Complex.Gamma_mul_Gamma_one_sub, inv_div]

/-- The period-one exponential multipliers at `z` and `tau-z` multiply to `1/(2pi)`.
This is the elementary cancellation in `barnesDoubleGammaInv_reflect_add_one`. -/
private lemma barnesDoubleGamma_reflected_multiplier_mul (z tau : ℂ) (htau : tau ≠ 0) :
    Complex.exp ((z / tau - 1 / 2) * Complex.log tau -
        (Real.log (2 * Real.pi) : ℂ) / 2) *
      Complex.exp (((tau - z) / tau - 1 / 2) * Complex.log tau -
        (Real.log (2 * Real.pi) : ℂ) / 2) = (2 * (Real.pi : ℂ))⁻¹ := by
  rw [← Complex.exp_add]
  have hexp : (z / tau - 1 / 2) * Complex.log tau -
        (Real.log (2 * Real.pi) : ℂ) / 2 +
      (((tau - z) / tau - 1 / 2) * Complex.log tau -
        (Real.log (2 * Real.pi) : ℂ) / 2) = -(Real.log (2 * Real.pi) : ℂ) := by
    field_simp
    ring
  rw [hexp, Complex.exp_neg, Complex.ofReal_log (by positivity),
    Complex.exp_log (by exact_mod_cast (ne_of_gt (by positivity : 0 < 2 * Real.pi)))]
  norm_cast

/-- The double-sine period-one equation with all double-gamma denominators cleared:

```text
Gamma₂(z+1)⁻¹ Gamma₂(1+tau-z)⁻¹ (2 sin(pi z/tau)) =
  Gamma₂(z)⁻¹ Gamma₂(tau-z)⁻¹.
```

This is the entire-function form of the first double-sine difference equation in
[95, Shintani (1977), proof of Proposition 5 on p. 181], with periods `(1,tau)`.
It includes every `z`, even when the meromorphic double sine has a zero or pole. -/
theorem barnesDoubleGammaInv_reflect_add_one (z tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    barnesDoubleGammaInv (z + 1) 1 tau * barnesDoubleGammaInv (1 + tau - z) 1 tau *
        (2 * Complex.sin (Real.pi * z / tau)) =
      barnesDoubleGammaInv z 1 tau * barnesDoubleGammaInv (tau - z) 1 tau := by
  have htau0 : tau ≠ 0 := Complex.slitPlane_ne_zero htau
  have h := congrArg₂ (· * ·)
    (barnesDoubleGammaInv_add_one_mul_inv_Gamma z tau htau)
    (barnesDoubleGammaInv_add_one_mul_inv_Gamma (tau - z) tau htau)
  rw [show tau - z + 1 = 1 + tau - z by ring] at h
  have harg : (tau - z) / tau = 1 - z / tau := by field_simp
  have hleft :
      barnesDoubleGammaInv (z + 1) 1 tau * (Complex.Gamma (z / tau))⁻¹ *
          (barnesDoubleGammaInv (1 + tau - z) 1 tau *
            (Complex.Gamma ((tau - z) / tau))⁻¹) =
        barnesDoubleGammaInv (z + 1) 1 tau * barnesDoubleGammaInv (1 + tau - z) 1 tau *
          (Complex.sin (Real.pi * z / tau) / Real.pi) := by
    rw [harg]
    rw [mul_mul_mul_comm, inv_Gamma_mul_inv_Gamma_one_sub, mul_div_assoc]
  rw [hleft, mul_mul_mul_comm, barnesDoubleGamma_reflected_multiplier_mul z tau htau0] at h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp at h
  rw [mul_comm z (Real.pi : ℂ)] at h
  linear_combination h

/-- Where the double-sine denominators at `z` and `z+1` are nonzero,
`S₂(z;1,tau) = 2 sin(pi z/tau) S₂(z+1;1,tau)`.
This is the quotient form of `barnesDoubleGammaInv_reflect_add_one`; it allows a vanishing
sine factor and hence includes the zero at `z = 0`. -/
theorem shintaniDoubleSineGamma_eq_two_sin_mul_add_one (z tau : ℂ)
    (htau : tau ∈ Complex.slitPlane)
    (hz1 : barnesDoubleGammaInv (tau - z) 1 tau ≠ 0) :
    shintaniDoubleSineGamma z tau =
      2 * Complex.sin (Real.pi * z / tau) * shintaniDoubleSineGamma (z + 1) tau := by
  have hz : barnesDoubleGammaInv (1 + tau - z) 1 tau ≠ 0 := by
    intro hzero
    apply hz1
    have h := barnesDoubleGammaInv_eq_zero_of_eq_zero_sub_one
      (1 + tau - z) tau htau hzero
    simpa only [show 1 + tau - z - 1 = tau - z by ring] using h
  have h := barnesDoubleGammaInv_reflect_add_one z tau htau
  unfold shintaniDoubleSineGamma barnesDoubleSineGamma
  rw [show 1 + tau - (z + 1) = tau - z by ring]
  field_simp
  rw [mul_comm z (Real.pi : ℂ)]
  linear_combination -h

/-- On the overlap chamber `0 < Re(z) < Re(tau)`, the concrete Barnes double sine satisfies
`S₂(z+1;1,tau) = S₂(z;1,tau)/(2 sin(pi z/tau))`.
This specializes `shintaniDoubleSineGamma_eq_two_sin_mul_add_one`: both arguments lie in
the source chamber, so the double-gamma denominators and the sine factor are nonzero. -/
theorem shintaniDoubleSineGamma_add_one_of_source_chamber (z tau : ℂ)
    (hz : 0 < z.re) (hzUpper : z.re < tau.re) :
    shintaniDoubleSineGamma (z + 1) tau =
      shintaniDoubleSineGamma z tau / (2 * Complex.sin (Real.pi * z / tau)) := by
  have htauRe : 0 < tau.re := hz.trans hzUpper
  have hslit : tau ∈ Complex.slitPlane := Or.inl htauRe
  have hden1 := barnesDoubleGammaInv_ne_zero_of_re_pos
    (tau - z) tau hslit htauRe.le (by simp only [sub_re]; linarith)
  have hshift := shintaniDoubleSineGamma_eq_two_sin_mul_add_one z tau hslit hden1
  have hnonzero := shintaniDoubleSineGamma_ne_zero_of_re_pos z tau htauRe
    hz (by linarith)
  rw [hshift, mul_ne_zero_iff] at hnonzero
  exact (eq_div_iff hnonzero.1).2 (by rw [hshift]; ring)

/-! ### The second-period equation

Use the two gamma multipliers at `z` and `1-z`. Euler reflection gives
`sin(pi z)/pi`, and their constant exponentials give `1/(2pi)`.
-/

/-- The entire-function second-period identity
`Γ₂(z+τ)⁻¹ Γ₂(1+τ-z)⁻¹ 2 sin(πz) = Γ₂(z)⁻¹ Γ₂(1-z)⁻¹`.
This is the second double-sine shift in
[95, Shintani (1977), proof of Proposition 5, p. 181], with denominators cleared. -/
theorem barnesDoubleGammaInv_reflect_add_tau (z tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) :
    barnesDoubleGammaInv (z + tau) 1 tau * barnesDoubleGammaInv (1 + tau - z) 1 tau *
        (2 * Complex.sin (Real.pi * z)) =
      barnesDoubleGammaInv z 1 tau * barnesDoubleGammaInv (1 - z) 1 tau := by
  have h := congrArg₂ (· * ·)
    (barnesDoubleGammaInv_add_tau_mul_inv_Gamma z tau htau)
    (barnesDoubleGammaInv_add_tau_mul_inv_Gamma (1 - z) tau htau)
  rw [show 1 - z + tau = 1 + tau - z by ring, mul_mul_mul_comm,
    inv_Gamma_mul_inv_Gamma_one_sub, mul_mul_mul_comm, ← Complex.exp_add,
    show -(Real.log (2 * Real.pi) : ℂ) / 2 + -(Real.log (2 * Real.pi) : ℂ) / 2 =
      -(Real.log (2 * Real.pi) : ℂ) by ring,
    Complex.exp_neg, Complex.ofReal_log (by positivity),
    Complex.exp_log (by exact_mod_cast (ne_of_gt (by positivity : 0 < 2 * Real.pi)))] at h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast at h
  field_simp at h
  rw [mul_comm z (Real.pi : ℂ)] at h
  linear_combination h

/-- Where both displayed denominators are nonzero,
`S₂(z;1,τ)=2 sin(πz) S₂(z+τ;1,τ)`. This is the quotient reading of
`barnesDoubleGammaInv_reflect_add_tau`, including possible zeros of the sine. -/
theorem shintaniDoubleSineGamma_eq_two_sin_mul_add_tau (z tau : ℂ)
    (htau : tau ∈ Complex.slitPlane)
    (hzτ : barnesDoubleGammaInv (1 - z) 1 tau ≠ 0) :
    shintaniDoubleSineGamma z tau =
      2 * Complex.sin (Real.pi * z) * shintaniDoubleSineGamma (z + tau) tau := by
  have hz : barnesDoubleGammaInv (1 + tau - z) 1 tau ≠ 0 := by
    intro hzero
    apply hzτ
    have h := barnesDoubleGammaInv_eq_zero_of_eq_zero_sub_period
      (1 + tau - z) tau htau hzero
    simpa only [show 1 + tau - z - tau = 1 - z by ring] using h
  have h := barnesDoubleGammaInv_reflect_add_tau z tau htau
  unfold shintaniDoubleSineGamma barnesDoubleSineGamma
  rw [show 1 + tau - (z + tau) = 1 - z by ring]
  field_simp
  rw [mul_comm z (Real.pi : ℂ)]
  linear_combination -h

/-- On `0<Re(z)<1` with `Re(τ)>0`, the second-period law is
`S₂(z+τ;1,τ)=S₂(z;1,τ)/(2 sin(πz))`. This specializes
`shintaniDoubleSineGamma_eq_two_sin_mul_add_tau` to the overlap source chamber. -/
theorem shintaniDoubleSineGamma_add_tau_of_source_chamber (z tau : ℂ)
    (htauRe : 0 < tau.re) (hz : 0 < z.re) (hzUpper : z.re < 1) :
    shintaniDoubleSineGamma (z + tau) tau =
      shintaniDoubleSineGamma z tau / (2 * Complex.sin (Real.pi * z)) := by
  have hslit : tau ∈ Complex.slitPlane := Or.inl htauRe
  have hdenτ := barnesDoubleGammaInv_ne_zero_of_re_pos
    (1 - z) tau hslit htauRe.le (by simp only [sub_re, one_re]; linarith)
  have hshift := shintaniDoubleSineGamma_eq_two_sin_mul_add_tau z tau hslit hdenτ
  have hnonzero := shintaniDoubleSineGamma_ne_zero_of_re_pos z tau htauRe
    hz (by linarith)
  rw [hshift, mul_ne_zero_iff] at hnonzero
  exact (eq_div_iff hnonzero.1).2 (by rw [hshift]; ring)

/-! ### Normalization at the origin

Shintani determines the comparison constant from the slope at zero. The numerator
has derivative one and vanishes there; the denominator is continuous and its value
is `sqrt(tau)/(2pi)` by the double-gamma shift evaluation.
-/

/-- `Γ₂(1+τ;1,τ)⁻¹ = sqrt(τ)/(2π)`, the square-root reading of
`barnesDoubleGammaInv_one_add_tau`. -/
lemma barnesDoubleGammaInv_one_add_tau_eq_sqrt (tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) :
    barnesDoubleGammaInv (1 + tau) 1 tau = Complex.sqrt tau / (2 * Real.pi) := by
  rw [barnesDoubleGammaInv_one_add_tau tau htau, Complex.exp_sub,
    ← sqrt_eq_exp (Complex.slitPlane_ne_zero htau),
    Complex.ofReal_log (by positivity),
    Complex.exp_log (by exact_mod_cast (ne_of_gt (by positivity : 0 < 2 * Real.pi)))]
  norm_cast

/-- `lim_{z→0} S₂(z;1,τ)/z = 2π/sqrt(τ)`, the gamma-ratio normalization in
[95, Shintani (1977), proof of Proposition 5, p. 181]. The limit is punctured
and uses the nonzero denominator at the origin. -/
lemma tendsto_shintaniDoubleSineGamma_div (tau : ℂ) (htau : 0 < tau.im) :
    Tendsto (fun z : ℂ => shintaniDoubleSineGamma z tau / z)
      (nhdsWithin 0 ({0} : Set ℂ)ᶜ) (nhds (2 * Real.pi / Complex.sqrt tau)) := by
  have hder :=
    (differentiable_barnesDoubleGammaInv tau (Or.inr htau.ne') 0).hasDerivAt
  rw [deriv_barnesDoubleGammaInv_zero tau (Or.inr htau.ne')] at hder
  have hnum : Tendsto (fun z : ℂ => barnesDoubleGammaInv z 1 tau / z)
      (nhdsWithin 0 ({0} : Set ℂ)ᶜ) (nhds 1) := by
    simpa only [zero_add, barnesDoubleGammaInv_zero, sub_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using hder.tendsto_slope_zero
  have hden : ContinuousAt (fun z : ℂ => barnesDoubleGammaInv (1 + tau - z) 1 tau) 0 :=
    (differentiable_barnesDoubleGammaInv tau
      (Or.inr htau.ne')).continuous.continuousAt.comp
      (continuousAt_const.sub continuousAt_id)
  have hnz : barnesDoubleGammaInv (1 + tau) 1 tau ≠ 0 := by
    rw [barnesDoubleGammaInv_one_add_tau tau (Or.inr htau.ne')]
    exact Complex.exp_ne_zero _
  have h := hnum.div (by simpa using hden.tendsto.mono_left nhdsWithin_le_nhds) hnz
  convert h using 1
  · funext z
    simp only [shintaniDoubleSineGamma, barnesDoubleSineGamma, Pi.div_apply, div_right_comm]
  · rw [barnesDoubleGammaInv_one_add_tau_eq_sqrt tau (Or.inr htau.ne'), one_div_div]

end SIC

end
