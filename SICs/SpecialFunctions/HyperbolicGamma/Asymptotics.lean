/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.HyperbolicGamma.Comparison
import SICs.SpecialFunctions.HyperbolicGamma.EqualPeriods

/-!
# Asymptotics of the hyperbolic gamma function

Ruijsenaars' Proposition III.4 on closed substrips: `g(a₊,a₋;z)` is the quadratic
`-πz²/(2a₊a₋) - (π/24)(a₊/a₋ + a₋/a₊)` up to an exponentially small error as `Re z → +∞`.

This module proves the strip part of S. N. M. Ruijsenaars, *First order analytic difference
equations and integrable quantum systems*, J. Math. Phys. 38 (1997), 1069–1146,
Proposition III.4, equation (3.49), p. 1096,
[doi:10.1063/1.531809](https://doi.org/10.1063/1.531809):

```text
±g(a₊,a₋;z) = -πz²/(2a₊a₋) - (π/24)(a₊/a₋ + a₋/a₊) + O(exp(±(ε - 2π/a_m) z)),
```

as `Re z → ±∞`, with `a_m = max(a₊,a₋)`, uniformly for `z` in a closed substrip of the strip
(3.2), with the upper signs, the case `Re z → +∞` that the consumer
`SICs.SpecialFunctions.Faddeev.Asymptotics` needs. The derivative asymptotics (3.50) are not
formalized, and neither is Ruijsenaars' extension to every horizontal strip by the difference
equations (3.57), which that consumer replaces by the multiplicative shift laws of the Faddeev
generator.

## The argument

By the comparison (3.51), `a₊a₋ g(a₊,a₋;z) = a² g(a,a;z) + d(z)`. The equal-period
asymptotics give `a² g(a,a;z) = -πz²/2 - πa²/12 + O(e^{(ε-2π/a) Re z})`, and
`πa²/12 = (π/24)(a₊² + a₋²)` by the choice (3.52) of `a`; dividing by `a₊a₋` produces the
constant `(π/24)(a₊/a₋ + a₋/a₊)`. The substrip `|Im z| ≤ c < (a₊+a₋)/2` lies inside the
equal-period strip `|Im z| < a`, and `a ≤ a_m`, so the first error is
`O(e^{(ε-2π/a_m) Re z})`; the second is `O(e^{-2r Re z})` for `r = π/a_m - ε/2`, by the
contour shift (3.56).
-/

noncomputable section

open Complex

namespace SIC

/-! ### Proposition III.4 on closed substrips -/

/-- The comparison identity gives the error term used by
`norm_hyperbolicGammaLog_add_le`. -/
private theorem hyperbolicGammaLog_comparison_error_eq {a₁ a₂ : ℝ}
    (h₁ : 0 < a₁) (h₂ : 0 < a₂) {z : ℂ} (hz : |z.im| < (a₁ + a₂) / 2) :
    hyperbolicGammaLog a₁ a₂ z + Real.pi * z ^ 2 / (2 * a₁ * a₂) +
        Real.pi / 24 * (a₁ / a₂ + a₂ / a₁) =
      ((hyperbolicComparisonPeriod a₁ a₂ : ℂ) ^ 2 *
          (hyperbolicGammaLog (hyperbolicComparisonPeriod a₁ a₂)
                (hyperbolicComparisonPeriod a₁ a₂) z +
            Real.pi * z ^ 2 / (2 * (hyperbolicComparisonPeriod a₁ a₂ : ℂ) ^ 2) +
            Real.pi / 12) + hyperbolicComparisonIntegral a₁ a₂ z) / (a₁ * a₂) := by
  let a := hyperbolicComparisonPeriod a₁ a₂
  have ha : 0 < a := hyperbolicComparisonPeriod_pos h₁ h₂
  have hs : (a : ℂ) ^ 2 = ((a₁ ^ 2 + a₂ ^ 2) / 2 : ℝ) := by
    exact_mod_cast sq_hyperbolicComparisonPeriod a₁ a₂
  have hcmp := hyperbolicGammaLog_comparison h₁ h₂ hz
  have h₁c : (a₁ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt h₁)
  have h₂c : (a₂ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt h₂)
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  change (a₁ : ℂ) * a₂ * hyperbolicGammaLog a₁ a₂ z =
    (a : ℂ) ^ 2 * hyperbolicGammaLog a a z +
      hyperbolicComparisonIntegral a₁ a₂ z at hcmp
  rw [hs] at hcmp
  change hyperbolicGammaLog a₁ a₂ z + Real.pi * z ^ 2 / (2 * a₁ * a₂) +
      Real.pi / 24 * (a₁ / a₂ + a₂ / a₁) =
    ((a : ℂ) ^ 2 * (hyperbolicGammaLog a a z +
        Real.pi * z ^ 2 / (2 * (a : ℂ) ^ 2) + Real.pi / 12) +
      hyperbolicComparisonIntegral a₁ a₂ z) / (a₁ * a₂)
  field_simp
  rw [hs]
  push_cast at hcmp ⊢
  linear_combination 576 * hcmp

/-- Combines the two error bounds for `norm_hyperbolicGammaLog_add_le`. -/
private theorem norm_hyperbolicGammaLog_add_le_of_errors {a₁ a₂ : ℝ}
    (h₁ : 0 < a₁) (h₂ : 0 < a₂) {z : ℂ} (hz : |z.im| < (a₁ + a₂) / 2)
    {K C₁ C₂ : ℝ}
    (hself : ‖hyperbolicGammaLog (hyperbolicComparisonPeriod a₁ a₂)
        (hyperbolicComparisonPeriod a₁ a₂) z +
        Real.pi * z ^ 2 / (2 * (hyperbolicComparisonPeriod a₁ a₂ : ℂ) ^ 2) +
        Real.pi / 12‖ ≤ C₁ * K)
    (hcomparison : ‖hyperbolicComparisonIntegral a₁ a₂ z‖ ≤ C₂ * K) :
    ‖hyperbolicGammaLog a₁ a₂ z + Real.pi * z ^ 2 / (2 * a₁ * a₂) +
        Real.pi / 24 * (a₁ / a₂ + a₂ / a₁)‖ ≤
      ((hyperbolicComparisonPeriod a₁ a₂ ^ 2 * C₁ + C₂) / (a₁ * a₂)) * K := by
  let a := hyperbolicComparisonPeriod a₁ a₂
  let E : ℂ := hyperbolicGammaLog a a z + Real.pi * z ^ 2 / (2 * (a : ℂ) ^ 2) +
    Real.pi / 12
  let D : ℂ := hyperbolicComparisonIntegral a₁ a₂ z
  have ha : 0 < a := hyperbolicComparisonPeriod_pos h₁ h₂
  have hden : 0 < a₁ * a₂ := mul_pos h₁ h₂
  have hnorma : ‖(a : ℂ) ^ 2‖ = a ^ 2 := by
    simp [norm_pow, abs_of_pos ha]
  have hnum : ‖(a : ℂ) ^ 2 * E + D‖ ≤ (a ^ 2 * C₁ + C₂) * K := by
    calc
      _ ≤ ‖(a : ℂ) ^ 2 * E‖ + ‖D‖ := norm_add_le _ _
      _ = a ^ 2 * ‖E‖ + ‖D‖ := by rw [norm_mul, hnorma]
      _ ≤ a ^ 2 * (C₁ * K) + C₂ * K := by
        have hmul := mul_le_mul_of_nonneg_left hself (sq_nonneg a)
        dsimp [E, D] at hmul ⊢
        linarith [hcomparison]
      _ = (a ^ 2 * C₁ + C₂) * K := by ring
  calc
    ‖hyperbolicGammaLog a₁ a₂ z + Real.pi * z ^ 2 / (2 * a₁ * a₂) +
        Real.pi / 24 * (a₁ / a₂ + a₂ / a₁)‖ =
      ‖(a : ℂ) ^ 2 * E + D‖ / (a₁ * a₂) := by
        rw [hyperbolicGammaLog_comparison_error_eq h₁ h₂ hz]
        simp [E, D, a, abs_of_pos h₁, abs_of_pos h₂]
    _ ≤ ((a ^ 2 * C₁ + C₂) / (a₁ * a₂)) * K := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hnum (le_of_lt hden)

/-- The equal-period error meets the rate in `norm_hyperbolicGammaLog_add_le` because the
comparison period is at most the larger original period. -/
private theorem exp_hyperbolicComparisonPeriod_le {a₁ a₂ : ℝ} (h₁ : 0 < a₁)
    (h₂ : 0 < a₂) {ε t : ℝ} (ht : 0 ≤ t) :
    Real.exp ((ε - 2 * Real.pi / hyperbolicComparisonPeriod a₁ a₂) * t) ≤
      Real.exp ((ε - 2 * Real.pi / max a₁ a₂) * t) := by
  have ha := hyperbolicComparisonPeriod_pos h₁ h₂
  have hle := hyperbolicComparisonPeriod_le_max h₁ h₂
  have hdiv : Real.pi / max a₁ a₂ ≤
      Real.pi / hyperbolicComparisonPeriod a₁ a₂ :=
    div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) ha hle
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ ht
  calc
    ε - 2 * Real.pi / hyperbolicComparisonPeriod a₁ a₂ =
        ε - 2 * (Real.pi / hyperbolicComparisonPeriod a₁ a₂) := by ring
    _ ≤ ε - 2 * (Real.pi / max a₁ a₂) := by linarith
    _ = ε - 2 * Real.pi / max a₁ a₂ := by ring

/-- A contour-shift height below `π/max(a₊,a₋)` whose decay rate meets the bound in
`norm_hyperbolicGammaLog_add_le`. -/
private theorem hyperbolicComparison_shift_rate {a₁ a₂ : ℝ} (h₁ : 0 < a₁)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < Real.pi / max a₁ a₂ ∧
      ∀ t : ℝ, 0 ≤ t →
        Real.exp (-2 * r * t) ≤ Real.exp ((ε - 2 * Real.pi / max a₁ a₂) * t) := by
  have hm : 0 < max a₁ a₂ := lt_of_lt_of_le h₁ (le_max_left a₁ a₂)
  let δ := min ε (Real.pi / max a₁ a₂)
  let r := Real.pi / max a₁ a₂ - δ / 2
  have hπ : 0 < Real.pi / max a₁ a₂ := div_pos Real.pi_pos hm
  have hδ : 0 < δ := lt_min hε hπ
  have hr : 0 < r := by
    have := min_le_right ε (Real.pi / max a₁ a₂)
    dsimp [r, δ]
    linarith
  have hrπ : r < Real.pi / max a₁ a₂ := by dsimp [r]; linarith
  refine ⟨r, hr, hrπ, ?_⟩
  intro t ht
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ ht
  dsimp [r, δ]
  have := min_le_left ε (Real.pi / max a₁ a₂)
  calc
    -2 * (Real.pi / max a₁ a₂ - min ε (Real.pi / max a₁ a₂) / 2) =
        min ε (Real.pi / max a₁ a₂) - 2 * (Real.pi / max a₁ a₂) := by ring
    _ ≤ ε - 2 * (Real.pi / max a₁ a₂) := by linarith
    _ = ε - 2 * Real.pi / max a₁ a₂ := by ring

/-- Replaces a constant by its nonnegative part when an exponential rate is weakened in the
proof of `norm_hyperbolicGammaLog_add_le`. -/
private theorem le_max_mul_exp_of_le {x C s t : ℝ}
    (hbound : x ≤ C * Real.exp s) (hrate : Real.exp s ≤ Real.exp t) :
    x ≤ max C 0 * Real.exp t := by
  calc
    x ≤ C * Real.exp s := hbound
    _ ≤ max C 0 * Real.exp s :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) (le_of_lt (Real.exp_pos _))
    _ ≤ max C 0 * Real.exp t :=
      mul_le_mul_of_nonneg_left hrate (le_max_right C 0)

/-- For periods `a₊, a₋ > 0`, `ε > 0`, and `c < (a₊+a₋)/2`, there is `C` with
`‖g(a₊,a₋;z) + πz²/(2a₊a₋) + (π/24)(a₊/a₋ + a₋/a₊)‖ ≤ C e^{(ε - 2π/max(a₊,a₋)) Re z}`
whenever `Re z ≥ 0` and `|Im z| ≤ c`: Ruijsenaars (1997), Proposition III.4, equation (3.49)
with the upper signs, on closed substrips of the strip (3.2). -/
theorem norm_hyperbolicGammaLog_add_le {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) {ε c : ℝ}
    (hε : 0 < ε) (hc : c < (a₁ + a₂) / 2) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → |z.im| ≤ c →
      ‖hyperbolicGammaLog a₁ a₂ z + Real.pi * z ^ 2 / (2 * a₁ * a₂) +
          Real.pi / 24 * (a₁ / a₂ + a₂ / a₁)‖ ≤
        C * Real.exp ((ε - 2 * Real.pi / max a₁ a₂) * z.re) := by
  let a := hyperbolicComparisonPeriod a₁ a₂
  have ha : 0 < a := hyperbolicComparisonPeriod_pos h₁ h₂
  have hc' : c < a := lt_of_lt_of_le hc (add_div_two_le_hyperbolicComparisonPeriod a₁ a₂)
  obtain ⟨C₁, hC₁⟩ := norm_hyperbolicGammaLog_self_add_le ha hε hc'
  obtain ⟨r, hr, hrπ, hrate₂⟩ := hyperbolicComparison_shift_rate h₁ hε
  obtain ⟨C₂, hC₂⟩ := norm_hyperbolicComparisonIntegral_le h₁ h₂ hc hr hrπ
  refine ⟨(a ^ 2 * max C₁ 0 + max C₂ 0) / (a₁ * a₂), ?_⟩
  intro z hzre hzim
  have hzstrip : |z.im| < (a₁ + a₂) / 2 := lt_of_le_of_lt hzim hc
  have hself : ‖hyperbolicGammaLog a a z + Real.pi * z ^ 2 / (2 * (a : ℂ) ^ 2) +
      Real.pi / 12‖ ≤ max C₁ 0 * Real.exp ((ε - 2 * Real.pi / max a₁ a₂) * z.re) :=
    le_max_mul_exp_of_le (hC₁ z hzre hzim)
      (exp_hyperbolicComparisonPeriod_le h₁ h₂ hzre)
  have hcomparison : ‖hyperbolicComparisonIntegral a₁ a₂ z‖ ≤
      max C₂ 0 * Real.exp ((ε - 2 * Real.pi / max a₁ a₂) * z.re) :=
    le_max_mul_exp_of_le (hC₂ z hzim) (hrate₂ z.re hzre)
  exact norm_hyperbolicGammaLog_add_le_of_errors h₁ h₂ hzstrip hself hcomparison

end SIC

end
