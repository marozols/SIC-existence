/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Uniform bounds for real powers

`a^p ≤ a^{p₁} + a^{p₂}` for `a > 0` and `p₁ ≤ p ≤ p₂`: a uniform majorant for real powers.

The function `p ↦ a^p` is increasing for `a ≥ 1` and decreasing for `0 < a ≤ 1`.
On an interval `p₁ ≤ p ≤ p₂` it is bounded by the larger endpoint value, hence by their sum:

$$a^{p} \le a^{p_1} + a^{p_2}.$$

This is the estimate that makes a family of Mellin integrands `t^{s-1} f(t)` with `Re s` in a
compact interval dominated by a single integrable function, so that holomorphy in `s` follows
from differentiation under the integral sign. It is used for the Mellin integrals of
`SICs.SpecialFunctions.GammaZetaBounds` and for Euler's gamma kernels in
`SICs.SpecialFunctions.Digamma.EulerLimit`.
-/

namespace SIC

/-! ### Uniform bounds for exponents in an interval -/

/-- For `a > 0` and `p₁ ≤ p ≤ p₂`, `a^p ≤ a^{p₁} + a^{p₂}`: the function `p ↦ a^p` is
increasing for `a ≥ 1` and decreasing for `0 < a ≤ 1`, so its value is at most the larger
of the two endpoint values. -/
lemma rpow_le_add_of_le {a p p₁ p₂ : ℝ} (ha : 0 < a) (h₁ : p₁ ≤ p) (h₂ : p ≤ p₂) :
    a ^ p ≤ a ^ p₁ + a ^ p₂ := by
  rcases le_total 1 a with ha1 | ha1
  · exact (Real.rpow_le_rpow_of_exponent_le ha1 h₂).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg ha.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge ha ha1 h₁).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg ha.le _))

end SIC
