/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.VerticalContourShift
import SICs.SpecialFunctions.Mellin.Integration

/-!
# Contour shifts for inverse Mellin transforms

Complex-power weighting and normalization of vertical contour shifts for inverse Mellin transforms.

This module specializes the general contour shifts in `SICs.Analysis.VerticalContourShift`
to the inverse Mellin kernels of [95, Shintani (1977), proof of Lemma 1, pp. 170–171].
For `t > 0`, multiplication by `t⁻ˢ` preserves uniform quadratic decay on a vertical strip:
its norm is `t^{-Re s}`, bounded on the compact interval of real parts. The horizontal
closing integrals therefore vanish.

For a weighted kernel with principal part `q/(s-c)²+r/(s-c)`, the general shift between vertical
lines gives a correction `2πr` between its integrals with respect to the height variable.
The normalization `1/(2π)` in `mellinInv` makes the correction `r`. The double-pole term
has zero integral and does not contribute to the shift. The resulting theorem includes
a simple pole by taking `q = 0`.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace SIC

/-! ### Horizontal limits of weighted kernels

The norm of the complex-power factor depends only on the real part of the integration variable.
-/

/-- For `t>0`, a uniform bound `|F(s)| ≤ C/(1+Im(s)²)` also makes the horizontal
integrals of `F(s)t^(-s)` tend to zero. This specializes
`tendsto_integral_horizontal_of_quadratic_decay` to the inverse Mellin kernels. -/
theorem tendsto_integral_horizontal_mul_cpow
    (F : ℂ → ℂ) (a b C : ℝ)
    (hC : ∀ s : ℂ, s.re ∈ uIcc a b → 1 ≤ |s.im| →
      ‖F s‖ ≤ C / (1 + s.im ^ 2)) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun y : ℝ => ∫ x : ℝ in a..b,
      F (x + y * I) * (t : ℂ) ^ (-(x + y * I))) (cocompact ℝ) (𝓝 0) := by
  have hc : Continuous (fun x : ℝ => t ^ (-x)) :=
    (Real.continuous_const_rpow ht.ne').comp continuous_neg
  obtain ⟨B, hB⟩ := (isCompact_uIcc (a := a) (b := b)).bddAbove_image hc.continuousOn
  apply tendsto_integral_horizontal_of_quadratic_decay (fun s => F s * (t : ℂ) ^ (-s))
    a b (C * max B 0)
  intro s hs hsi
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, neg_re]
  calc
    _ ≤ (C / (1 + s.im ^ 2)) * max B 0 :=
      mul_le_mul (hC s hs hsi)
        ((hB (mem_image_of_mem _ hs)).trans (le_max_left _ _))
        (by positivity) ((norm_nonneg _).trans (hC s hs hsi))
    _ = _ := by ring

/-! ### Normalized inverse Mellin contours -/

/-- For `a<c<b` and `t>0`, if the weighted kernel `F(s)t⁻ˢ` has principal part
`q/(s-c)²+r/(s-c)`, shifting the inverse Mellin contour gives
`mellinInv(b,F)(t)=mellinInv(a,F)(t)+r`. This applies
`integral_vertical_eq_sub_of_double_pole` with the Mellin normalization;
`q=0` includes simple poles. -/
theorem mellinInv_eq_add_of_double_pole (F : ℂ → ℂ) (a b c : ℝ) (q r : ℂ)
    (hac : a < c) (hcb : c < b) (t : ℝ) (ht : 0 < t)
    (hd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → s ≠ c → DifferentiableAt ℂ F s)
    (hr : Tendsto (fun s : ℂ => (s - c) * (F s * (t : ℂ) ^ (-s) - q / (s - c) ^ 2))
      (𝓝[≠] (c : ℂ)) (𝓝 r))
    (ha : VerticalIntegrable F a) (hb : VerticalIntegrable F b)
    (hh : Tendsto (fun y : ℝ => ∫ x : ℝ in a..b,
      F (x + y * I) * (t : ℂ) ^ (-(x + y * I))) (cocompact ℝ) (𝓝 0)) :
    mellinInv b F t = mellinInv a F t + r := by
  have h := integral_vertical_eq_sub_of_double_pole (fun s => F s * (t : ℂ) ^ (-s))
    a b c q r hac hcb (fun s hsa hsb hsc => (hd s hsa hsb hsc).mul
      (differentiableAt_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr ht.ne')))) hr
    (verticalIntegrable_mul_cpow ha t ht) (verticalIntegrable_mul_cpow hb t ht) hh
  simp only [mellinInv, smul_eq_mul, Complex.real_smul]
  push_cast
  have hm (s : ℂ) : (t : ℂ) ^ (-s) * F s = F s * (t : ℂ) ^ (-s) := mul_comm _ _
  simp_rw [hm]
  rw [h]
  field_simp
  ring_nf
  simp only [mul_comm I]

end SIC

end
