/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Quotients of entire functions with simple common zeros

A quotient of entire functions with common zeros and simple denominator zeros extends to an
entire function.

This file removes the singularities of a quotient `N / D` of two entire functions whose zeros
are common and whose denominator zeros are simple: if `D` vanishes only on `Z`, and at every
point of `Z` both `N` and `D` vanish with `D' ≠ 0`, then `N / D` extends to an entire function
taking the value `N'(p) / D'(p)` at each `p ∈ Z`. This is the divisor-cancellation step of
[95, Shintani (1977), proof of Proposition 5 on p. 181], where the quotient of the double-gamma
ratio by the q-product ratio "is an entire function of `z`" because their zeros and poles cancel;
the statement here is the general fact, with the double-sine data supplied by its consumer.

## Mathematical argument

Near a point `p ∈ Z`, write `N(z) = (z - p) N₁(z)` and `D(z) = (z - p) D₁(z)` with `N₁, D₁`
analytic at `p` (Mathlib's `dslope`) and `D₁(p) = D'(p) ≠ 0`. Then `N / D = N₁ / D₁` on a
punctured neighborhood of `p`, and `N₁ / D₁` is analytic at `p`. Off `Z` the quotient is analytic
because `D ≠ 0` there. The nonzero derivative at a zero makes that zero isolated, while
continuity keeps `D` nonzero near every point off `Z`. Thus `Z` is closed and discrete as a
consequence, and the piecewise definition is analytic everywhere.
-/

noncomputable section

open Complex Filter Topology Set

namespace SIC

/-- The quotient `N / D` with its singularities on `Z` removed: at `p ∈ Z` it takes the value
`N'(p) / D'(p)`, elsewhere `N(p) / D(p)`. -/
def removableQuotient (N D : ℂ → ℂ) (Z : Set ℂ) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ Z then deriv N z / deriv D z else N z / D z

/-- Off `Z`, the removed quotient is the pointwise quotient. -/
lemma removableQuotient_of_not_mem (N D : ℂ → ℂ) {Z : Set ℂ} {z : ℂ} (hz : z ∉ Z) :
    removableQuotient N D Z z = N z / D z := by
  simp [removableQuotient, hz]

/-- On `Z`, the removed quotient is the quotient of derivatives. -/
lemma removableQuotient_of_mem (N D : ℂ → ℂ) {Z : Set ℂ} {z : ℂ} (hz : z ∈ Z) :
    removableQuotient N D Z z = deriv N z / deriv D z := by
  simp [removableQuotient, hz]

/-- **Removal of simple common zeros.** If `N` and `D` are entire, `D` is nonzero off `Z`,
and at every point of `Z` both vanish with `D' ≠ 0`, then the removed quotient is entire.
The zero set is automatically closed and discrete, by continuity and the nonzero derivatives. -/
theorem differentiable_removableQuotient {N D : ℂ → ℂ} {Z : Set ℂ}
    (hN : Differentiable ℂ N) (hD : Differentiable ℂ D)
    (hD₀ : ∀ z, z ∉ Z → D z ≠ 0)
    (hNZ : ∀ p ∈ Z, N p = 0) (hDZ : ∀ p ∈ Z, D p = 0) (hD' : ∀ p ∈ Z, deriv D p ≠ 0) :
    Differentiable ℂ (removableQuotient N D Z) := by
  intro z
  apply AnalyticAt.differentiableAt
  by_cases hz : z ∈ Z
  · have hZ := ((hD z).hasDerivAt.eventually_ne (hD' z hz) (c := 0)).mono
      fun w hw hwZ => hw (hDZ w hwZ)
    have haN : AnalyticAt ℂ (dslope N z) z :=
      ((Complex.differentiableOn_dslope (s := Set.univ) Filter.univ_mem).mpr
        hN.differentiableOn).analyticAt Filter.univ_mem
    have haD : AnalyticAt ℂ (dslope D z) z :=
      ((Complex.differentiableOn_dslope (s := Set.univ) Filter.univ_mem).mpr
        hD.differentiableOn).analyticAt Filter.univ_mem
    have hg : AnalyticAt ℂ (fun w => dslope N z w / dslope D z w) z :=
      haN.div haD (by simpa only [dslope_same] using hD' z hz)
    apply hg.congr
    filter_upwards [eventually_nhdsWithin_iff.1 hZ] with w hw
    by_cases hwz : w = z
    · subst w
      simp only [removableQuotient_of_mem N D hz, dslope_same]
    · have hwZ : w ∉ Z := hw hwz
      rw [removableQuotient_of_not_mem N D hwZ]
      simp only [dslope_of_ne _ hwz, slope_def_field, hNZ z hz, hDZ z hz, sub_zero]
      exact div_div_div_cancel_right₀ (sub_ne_zero.mpr hwz) (N w) (D w)
  · have hZn := ((hD z).continuousAt.eventually_ne (hD₀ z hz)).mono
      fun w hw hwZ => hw (hDZ w hwZ)
    have heq : removableQuotient N D Z =ᶠ[nhds z] fun w => N w / D w :=
      hZn.mono fun w hw => removableQuotient_of_not_mem N D hw
    apply ((hN.analyticAt z).div (hD.analyticAt z) (hD₀ z hz)).congr heq.symm

/-- The removed quotient satisfies `D · (N / D) = N` everywhere, including on `Z`, where both
sides vanish. -/
lemma mul_removableQuotient {N D : ℂ → ℂ} {Z : Set ℂ}
    (hD₀ : ∀ z, z ∉ Z → D z ≠ 0) (hNZ : ∀ p ∈ Z, N p = 0) (hDZ : ∀ p ∈ Z, D p = 0) (z : ℂ) :
    D z * removableQuotient N D Z z = N z := by
  by_cases hz : z ∈ Z
  · rw [hDZ z hz, hNZ z hz]
    simp
  · rw [removableQuotient_of_not_mem N D hz]
    exact mul_div_cancel₀ (N z) (hD₀ z hz)

end SIC

end
