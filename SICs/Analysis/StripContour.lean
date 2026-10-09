/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Cauchy's theorem on horizontal strips

Contour shifts between the two boundary lines of a horizontal strip on which a function is
holomorphic.

A function holomorphic on a closed horizontal strip has equal integrals along its two boundary
lines when the vertical integrals across the strip vanish at both ends. This is the pole-free
contour shift used by Ruijsenaars' comparison argument in
`SICs.SpecialFunctions.HyperbolicGamma.Comparison`, through the odd-kernel Fourier contour shift
of `SICs.Analysis.FourierContourShift`.

## The argument

Mathlib's Cauchy–Goursat theorem on rectangles
(`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) gives, for every truncation,
that the two long horizontal sides differ by the two short vertical sides. The short sides tend
to zero by hypothesis and the long sides converge, as symmetric truncations, to the two line
integrals, so the limits agree. When the boundary integrands are absolutely integrable, the
symmetric truncations converge to the full integrals by `intervalIntegral_tendsto_integral`.
A bound `‖g(x+iy)‖ ≤ h(x)` across the strip with `h → 0` makes the short sides vanish.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace SIC

/-! ### Horizontal strips

The long sides are the lines `Im z = a` and `Im z = b`; the short sides are vertical
segments, whose integrals must vanish as `|Re z| → ∞`. -/

/-- For a function holomorphic on the closed horizontal strip `a ≤ Im z ≤ b`, vertical
integrals tending to zero at both ends make the symmetric limits of the two horizontal line
integrals equal. -/
theorem integral_horizontal_eq_of_vertical_tendsto_zero (g : ℂ → ℂ)
    (a b : ℝ) (A B : ℂ) (hab : a ≤ b)
    (hg : DifferentiableOn ℂ g {z : ℂ | a ≤ z.im ∧ z.im ≤ b})
    (hv : Tendsto (fun x : ℝ => ∫ y : ℝ in a..b, g (x + y * I))
      (cocompact ℝ) (𝓝 0))
    (ha : Tendsto (fun X : ℝ => ∫ x : ℝ in -X..X, g (x + a * I)) atTop (𝓝 A))
    (hb : Tendsto (fun X : ℝ => ∫ x : ℝ in -X..X, g (x + b * I)) atTop (𝓝 B)) :
    A = B := by
  have hrect (X : ℝ) :
      (∫ x : ℝ in -X..X, g (x + a * I)) - (∫ x : ℝ in -X..X, g (x + b * I)) +
        I * (∫ y : ℝ in a..b, g (X + y * I)) -
        I * (∫ y : ℝ in a..b, g (-X + y * I)) = 0 := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g
      (⟨-X, a⟩ : ℂ) (⟨X, b⟩ : ℂ) (hg.mono (by
        intro z hz
        simpa only [uIcc_of_le hab, mem_preimage, mem_ofPred_eq, mem_Icc] using hz.2))
    simpa only [smul_eq_mul, ofReal_neg] using h
  have ht := ((ha.sub hb).add ((hv.mono_left atTop_le_cocompact).const_mul I)).sub
    ((hv.comp (tendsto_neg_atTop_atBot.mono_right atBot_le_cocompact)).const_mul I)
  have he : A - B + I * 0 - I * 0 = 0 := by
    apply tendsto_nhds_unique ht
    convert (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0)) using 1
    ext X
    simpa only [Function.comp_apply, ofReal_neg] using hrect X
  simpa only [mul_zero, sub_zero, add_zero, sub_eq_zero] using he

/-- The horizontal contour shift for absolutely integrable boundary integrands:
`∫ g(x+ia) dx = ∫ g(x+ib) dx` when `g` is holomorphic on `a ≤ Im z ≤ b` and its vertical
integrals tend to zero at both ends. -/
theorem integral_horizontal_eq_of_integrable (g : ℂ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hg : DifferentiableOn ℂ g {z : ℂ | a ≤ z.im ∧ z.im ≤ b})
    (hv : Tendsto (fun x : ℝ => ∫ y : ℝ in a..b, g (x + y * I))
      (cocompact ℝ) (𝓝 0))
    (ha : Integrable (fun x : ℝ => g (x + a * I)))
    (hb : Integrable (fun x : ℝ => g (x + b * I))) :
    ∫ x : ℝ, g (x + a * I) = ∫ x : ℝ, g (x + b * I) := by
  exact integral_horizontal_eq_of_vertical_tendsto_zero g a b _ _ hab hg hv
    (intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id)
    (intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id)

/-- A bound `‖g(x+iy)‖ ≤ h(x)` for `y` between `a` and `b`, with `h → 0` at both ends, makes
the vertical integrals across the strip tend to zero, as the horizontal contour shifts
require. -/
theorem tendsto_integral_vertical_of_norm_le (g : ℂ → ℂ) (a b : ℝ) (h : ℝ → ℝ)
    (hh : Tendsto h (cocompact ℝ) (𝓝 0))
    (hbound : ∀ᶠ x : ℝ in cocompact ℝ, ∀ y ∈ uIcc a b, ‖g ((x : ℂ) + (y : ℂ) * I)‖ ≤ h x) :
    Tendsto (fun x : ℝ => ∫ y : ℝ in a..b, g (x + y * I)) (cocompact ℝ) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (hbound.mono (fun x hx => intervalIntegral.norm_integral_le_of_norm_le_const
      (fun y hy => hx y (uIoc_subset_uIcc hy))))
  simpa using hh.mul_const |b - a|

end SIC

end
