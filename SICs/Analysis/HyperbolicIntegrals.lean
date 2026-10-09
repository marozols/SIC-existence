/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import SICs.Analysis.HyperbolicBounds

/-!
# Integrals of inverse squared hyperbolic sines

Three classical integrals over `(0, ∞)` with the kernel `1/sinh²`, used for the equal-period
hyperbolic gamma function.

This module supplies the evaluations of S. N. M. Ruijsenaars, *First order analytic difference
equations and integrable quantum systems*, J. Math. Phys. 38 (1997), 1069–1146,
[doi:10.1063/1.531809](https://doi.org/10.1063/1.531809), equations (2.66), (2.69), and (3.45):
for `a > 0` and real `z`,

```text
π z coth(πz/a) = a + a² ∫₀^∞ (1 - cos 2yz)/sinh²(ay) dy,        (2.66)
∫₀^∞ (a²/sinh²(ay) - 1/y²) dy = -a,                             (2.69)
∫₀^∞ t e^{-t}/sinh t dt = π²/12.                                (3.45)
```

They are consumed by `SICs.SpecialFunctions.HyperbolicGamma.EqualPeriods`, which
evaluates the hyperbolic gamma function with equal periods.

## The argument

For (2.69), `-a coth(ay) + 1/y` is an antiderivative of the integrand; it tends to `0` at
`y = 0⁺` and to `-a` at infinity. For (2.66), the cosine kernel is dominated by
`2z²y²/sinh²(ay)`; this majorant is bounded near zero and decays exponentially at infinity.
For (2.66) and (3.45), expand
`1/sinh²(y) = 4 ∑_{m≥1} m e^{-2my}` and `e^{-t}/sinh t = 2 ∑_{m≥1} e^{-2mt}` for `y, t > 0`.
All terms are nonnegative, so the integral of the sum is the sum of the integrals. After the
substitution `y ↦ y/a` with `v = z/a`, the terms `4m e^{-2my}(1 - cos 2vy)` integrate to
`2v²/(m²+v²)`, and the terms `2t e^{-2mt}` to `1/(2m²)`. The sums are
`πv coth(πv) - 1 = ∑_{m≥1} 2v²/(m²+v²)`, by Mathlib's
Mittag-Leffler expansion of the cotangent (`cot_series_rep`) at `iv`, and `ζ(2)/2 = π²/12`
(`hasSum_zeta_two`). Ruijsenaars derives (2.66) from his general theory of minimal solutions
of analytic difference equations (Theorem II.2); the series evaluation here is the classical
direct computation of the same integral.
-/

noncomputable section

open Real MeasureTheory Set
open scoped Filter Topology Pointwise

namespace SIC

/-! ### The subtracted inverse square: equation (2.69) -/

/-- The antiderivative used for equation (2.69). -/
private def hyperbolicSubAntiderivative (a y : ℝ) : ℝ :=
  -a * (Real.cosh (a * y) / Real.sinh (a * y)) + 1 / y

/-- The derivative of the antiderivative for equation (2.69). -/
private lemma hyperbolicSubAntiderivative_hasDerivAt {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    HasDerivAt (hyperbolicSubAntiderivative a)
      (a ^ 2 / Real.sinh (a * y) ^ 2 - 1 / y ^ 2) y := by
  have hs : Real.sinh (a * y) ≠ 0 := (Real.sinh_ne_zero).mpr (mul_pos ha hy).ne'
  have hmul : HasDerivAt (fun x : ℝ => a * x) a y := by
    simpa using (hasDerivAt_id y).const_mul a
  have hcosh : HasDerivAt (fun x : ℝ => Real.cosh (a * x))
      (Real.sinh (a * y) * a) y := (Real.hasDerivAt_cosh (a * y)).comp y hmul
  have hsinh : HasDerivAt (fun x : ℝ => Real.sinh (a * x))
      (Real.cosh (a * y) * a) y := (Real.hasDerivAt_sinh (a * y)).comp y hmul
  have hinv : HasDerivAt (fun x : ℝ => 1 / x) (-1 / y ^ 2) y := by
    convert (hasDerivAt_inv hy.ne') using 1
    · funext x
      simp [one_div]
    · ring
  have h := ((hcosh.div hsinh hs).const_mul (-a)).add hinv
  convert h using 1
  · ext x
    simp [hyperbolicSubAntiderivative]
  · apply Eq.symm
    calc
      -a * ((Real.sinh (a * y) * a * Real.sinh (a * y) -
          Real.cosh (a * y) * (Real.cosh (a * y) * a)) /
          Real.sinh (a * y) ^ 2) + -1 / y ^ 2 =
          a ^ 2 * ((Real.cosh (a * y) ^ 2 - Real.sinh (a * y) ^ 2) /
            Real.sinh (a * y) ^ 2) - 1 / y ^ 2 := by ring
      _ = a ^ 2 / Real.sinh (a * y) ^ 2 - 1 / y ^ 2 := by
        rw [Real.cosh_sq_sub_sinh_sq]
        ring

/-- The derivative in equation (2.69) is nonpositive on the positive half line. -/
private lemma subtractedSinhKernel_nonpos {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    a ^ 2 / Real.sinh (a * y) ^ 2 - 1 / y ^ 2 ≤ 0 := by
  have hshpos : 0 < Real.sinh (a * y) := Real.sinh_pos_iff.mpr (mul_pos ha hy)
  have hsq := sq_le_sinh_sq (a * y)
  have hdiv : a ^ 2 / Real.sinh (a * y) ^ 2 ≤ 1 / y ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hshpos) (sq_pos_of_pos hy)).2
    nlinarith [hsq]
  linarith

/-- A real form of the exponential quotient for `coth`, used in (2.69). -/
private lemma cosh_div_sinh_eq_exp_quotient {x : ℝ} (hx : 0 < x) :
    Real.cosh x / Real.sinh x =
      (1 + Real.exp (-(2 * x))) / (1 - Real.exp (-(2 * x))) := by
  have hs : Real.sinh x ≠ 0 := (Real.sinh_ne_zero).mpr hx.ne'
  have hq : Real.exp (-(2 * x)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hd : 1 - Real.exp (-(2 * x)) ≠ 0 := sub_ne_zero.mpr hq.ne'
  have hplus : 1 + Real.exp (-(2 * x)) = 2 * Real.exp (-x) * Real.cosh x := by
    have he : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    rw [Real.cosh_eq, show -(2 * x) = -x + -x by ring, Real.exp_add]
    nlinarith [he]
  apply (div_eq_div_iff hs hd).2
  rw [hplus, SIC.one_sub_exp_neg_two_mul]
  ring

/-- The hyperbolic cotangent ratio in (2.69) approaches one at infinity. -/
private lemma cosh_div_sinh_tendsto_atTop {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun y : ℝ => Real.cosh (a * y) / Real.sinh (a * y))
      Filter.atTop (nhds 1) := by
  have hlin : Filter.Tendsto (fun y : ℝ => -(2 * a) * y) Filter.atTop Filter.atBot :=
    (Filter.tendsto_const_mul_atBot_of_neg (by linarith : -(2 * a) < 0)).2 Filter.tendsto_id
  have hq : Filter.Tendsto (fun y : ℝ => Real.exp (-(2 * (a * y)))) Filter.atTop (nhds 0) := by
    have heq : (fun y : ℝ => Real.exp (-(2 * (a * y)))) =
        (fun y : ℝ => Real.exp (-(2 * a) * y)) := by
      funext y
      congr 1
      ring
    rw [heq]
    simpa only [Function.comp_def] using Real.tendsto_exp_atBot.comp hlin
  have hconst : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hnum : Filter.Tendsto
      (fun y : ℝ => 1 + Real.exp (-(2 * (a * y)))) Filter.atTop (nhds 1) := by
    simpa only [add_zero] using hconst.add hq
  have hden : Filter.Tendsto
      (fun y : ℝ => 1 - Real.exp (-(2 * (a * y)))) Filter.atTop (nhds 1) := by
    simpa only [sub_zero] using hconst.sub hq
  have htop : Filter.Tendsto
      (fun y : ℝ => (1 + Real.exp (-(2 * (a * y)))) /
        (1 - Real.exp (-(2 * (a * y))))) Filter.atTop (nhds 1) := by
    have h := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
    convert h using 1 with y
    simp
  apply htop.congr'
  filter_upwards [Filter.Ioi_mem_atTop (0 : ℝ)] with y hy
  exact (cosh_div_sinh_eq_exp_quotient (mul_pos ha hy)).symm

/-- The antiderivative in (2.69) approaches `-a` at infinity. -/
private lemma hyperbolicSubAntiderivative_tendsto_atTop {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (hyperbolicSubAntiderivative a) Filter.atTop (nhds (-a)) := by
  have hinv : Filter.Tendsto (fun y : ℝ => 1 / y) Filter.atTop (nhds 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero :
      Filter.Tendsto (fun y : ℝ => y⁻¹) Filter.atTop (nhds 0))
  have h := ((cosh_div_sinh_tendsto_atTop ha).const_mul (-a)).add hinv
  convert h using 1
  · ext y
    simp [hyperbolicSubAntiderivative]
  · ring_nf

/-- The derivative quotient in the right limit of the antiderivative in (2.69). -/
private lemma subtractedSinh_deriv_ratio_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto
      (fun y : ℝ => -(a ^ 2 * y * Real.sinh (a * y)) /
        (Real.sinh (a * y) + a * y * Real.cosh (a * y)))
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
  have hleft : Filter.Tendsto (fun y : ℝ => -(a ^ 2) * y)
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
    have hright : Filter.Tendsto (fun y : ℝ => y) (𝓝[>] (0 : ℝ)) (nhds 0) :=
      Filter.tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hright.const_mul (-(a ^ 2))
  apply Filter.Tendsto.squeeze' hleft tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have hp : 0 < a * y := mul_pos ha hy
    have hs : 0 < Real.sinh (a * y) := Real.sinh_pos_iff.mpr hp
    have hc : 0 < Real.cosh (a * y) := Real.cosh_pos _
    have hden : 0 < Real.sinh (a * y) + a * y * Real.cosh (a * y) :=
      add_pos_of_pos_of_nonneg hs (mul_nonneg hp.le hc.le)
    have hle : Real.sinh (a * y) ≤
        Real.sinh (a * y) + a * y * Real.cosh (a * y) :=
      le_add_of_nonneg_right (mul_nonneg hp.le hc.le)
    have hcoeff : 0 ≤ a ^ 2 * y := mul_nonneg (sq_nonneg a) hy.le
    have hm := mul_le_mul_of_nonneg_left hle hcoeff
    apply (le_div_iff₀ hden).2
    nlinarith [hm]
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have hp : 0 < a * y := mul_pos ha hy
    have hs : 0 < Real.sinh (a * y) := Real.sinh_pos_iff.mpr hp
    have hc : 0 < Real.cosh (a * y) := Real.cosh_pos _
    have hden : 0 < Real.sinh (a * y) + a * y * Real.cosh (a * y) :=
      add_pos_of_pos_of_nonneg hs (mul_nonneg hp.le hc.le)
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (mul_nonneg (mul_nonneg (sq_nonneg a) hy.le) hs.le)) hden.le

/-- Derivative of the numerator used to remove the pole in the antiderivative of (2.69). -/
private lemma subtractedSinh_num_hasDerivAt (a y : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sinh (a * x) - a * x * Real.cosh (a * x))
      (-(a ^ 2 * y * Real.sinh (a * y))) y := by
  have hmul : HasDerivAt (fun x : ℝ => a * x) a y := by
    simpa using (hasDerivAt_id y).const_mul a
  have hs := (Real.hasDerivAt_sinh (a * y)).comp y hmul
  have hc := (Real.hasDerivAt_cosh (a * y)).comp y hmul
  convert hs.sub (hmul.mul hc) using 1
  · funext x
    dsimp
  · dsimp
    ring

/-- Derivative of the denominator used to remove the pole in the antiderivative of (2.69). -/
private lemma subtractedSinh_den_hasDerivAt (a y : ℝ) :
    HasDerivAt (fun x : ℝ => x * Real.sinh (a * x))
      (Real.sinh (a * y) + a * y * Real.cosh (a * y)) y := by
  have hmul : HasDerivAt (fun x : ℝ => a * x) a y := by
    simpa using (hasDerivAt_id y).const_mul a
  have hs := (Real.hasDerivAt_sinh (a * y)).comp y hmul
  convert (hasDerivAt_id y).mul hs using 1
  · funext x
    dsimp
  · dsimp
    ring

/-- The regularized quotient in the right limit of the antiderivative in (2.69). -/
private lemma subtractedSinhQuotient_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun y : ℝ =>
      (Real.sinh (a * y) - a * y * Real.cosh (a * y)) / (y * Real.sinh (a * y)))
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
  let f : ℝ → ℝ := fun y => Real.sinh (a * y) - a * y * Real.cosh (a * y)
  let g : ℝ → ℝ := fun y => y * Real.sinh (a * y)
  have hf0 : Filter.Tendsto f (𝓝[>] (0 : ℝ)) (nhds 0) := by
    have hc : ContinuousAt f 0 := by fun_prop
    simpa [f] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hg0 : Filter.Tendsto g (𝓝[>] (0 : ℝ)) (nhds 0) := by
    have hc : ContinuousAt g 0 := by fun_prop
    simpa [g] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hf' : ∀ᶠ y in 𝓝[>] (0 : ℝ),
      HasDerivAt f (-(a ^ 2 * y * Real.sinh (a * y))) y :=
    Filter.Eventually.of_forall (fun y => subtractedSinh_num_hasDerivAt a y)
  have hg' : ∀ᶠ y in 𝓝[>] (0 : ℝ),
      HasDerivAt g (Real.sinh (a * y) + a * y * Real.cosh (a * y)) y :=
    Filter.Eventually.of_forall (fun y => subtractedSinh_den_hasDerivAt a y)
  have hg'ne : ∀ᶠ y in 𝓝[>] (0 : ℝ),
      Real.sinh (a * y) + a * y * Real.cosh (a * y) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hp : 0 < a * y := mul_pos ha hy
    have hs : 0 < Real.sinh (a * y) := Real.sinh_pos_iff.mpr hp
    have hc : 0 < Real.cosh (a * y) := Real.cosh_pos _
    exact (add_pos_of_pos_of_nonneg hs (mul_nonneg hp.le hc.le)).ne'
  have hquot : Filter.Tendsto (fun y => f y / g y) (𝓝[>] (0 : ℝ)) (nhds 0) :=
    HasDerivAt.lhopital_zero_nhdsGT hf' hg' hg'ne hf0 hg0
      (subtractedSinh_deriv_ratio_tendsto_zero ha)
  simpa only [f, g] using hquot

/-- The pole-subtracted antiderivative for (2.69) extends continuously to zero. -/
private lemma hyperbolicSubAntiderivative_continuousWithinAt {a : ℝ} (ha : 0 < a) :
    ContinuousWithinAt (hyperbolicSubAntiderivative a) (Ici 0) 0 := by
  have hF : Filter.Tendsto (hyperbolicSubAntiderivative a) (𝓝[>] (0 : ℝ)) (nhds 0) := by
    apply (subtractedSinhQuotient_tendsto_zero ha).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hys : y ≠ 0 := hy.ne'
    have hs : Real.sinh (a * y) ≠ 0 := (Real.sinh_ne_zero).mpr (mul_pos ha hy).ne'
    dsimp [hyperbolicSubAntiderivative]
    field_simp
    ring
  apply continuousWithinAt_Ioi_iff_Ici.mp
  change Filter.Tendsto (hyperbolicSubAntiderivative a) (𝓝[>] (0 : ℝ))
    (nhds (hyperbolicSubAntiderivative a 0))
  simpa [hyperbolicSubAntiderivative] using hF

/-- The integrand `a²/sinh²(ay) - 1/y²` of Ruijsenaars (1997), equation (2.69), is integrable
on `(0, ∞)`: it is bounded near `0` and `O(1/y²)` at infinity. -/
theorem integrableOn_sq_div_sinh_sq_sub_inv_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => a ^ 2 / Real.sinh (a * y) ^ 2 - 1 / y ^ 2) (Ioi 0) := by
  exact integrableOn_Ioi_deriv_of_nonpos
    (hyperbolicSubAntiderivative_continuousWithinAt ha)
    (fun y hy => hyperbolicSubAntiderivative_hasDerivAt ha hy)
    (fun y hy => subtractedSinhKernel_nonpos ha hy)
    (hyperbolicSubAntiderivative_tendsto_atTop ha)

/-- `∫₀^∞ (a²/sinh²(ay) - 1/y²) dy = -a` for `a > 0`, Ruijsenaars (1997), equation (2.69). -/
theorem integral_sq_div_sinh_sq_sub_inv_sq {a : ℝ} (ha : 0 < a) :
    ∫ y in Ioi (0 : ℝ), (a ^ 2 / Real.sinh (a * y) ^ 2 - 1 / y ^ 2) = -a := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (hyperbolicSubAntiderivative_continuousWithinAt ha)
    (fun y hy => hyperbolicSubAntiderivative_hasDerivAt ha hy)
    (integrableOn_sq_div_sinh_sq_sub_inv_sq ha)
    (hyperbolicSubAntiderivative_tendsto_atTop ha)
  simpa [hyperbolicSubAntiderivative] using h

/-! ### The majorant `y²/sinh²(ay)`

Bounded near the origin and exponentially small at infinity, it dominates the cosine kernel
of (2.66) and the derivative kernel of the equal-period logarithm. -/

/-- On `ay ≥ 1`, the majorant `y²/sinh²(ay)` is bounded by `16y²e^{-2ay}`. -/
private lemma sq_div_sinh_sq_le_exp {a y : ℝ} (hay : 1 ≤ a * y) :
    y ^ 2 / Real.sinh (a * y) ^ 2 ≤ 16 * y ^ 2 * Real.exp (-2 * a * y) := by
  have hs : Real.exp (a * y) / 4 ≤ Real.sinh (a * y) := exp_div_four_le_sinh hay
  have hden : (Real.exp (a * y) / 4) ^ 2 ≤ Real.sinh (a * y) ^ 2 := by gcongr
  have hdenpos : 0 < (Real.exp (a * y) / 4) ^ 2 := by positivity
  calc
    y ^ 2 / Real.sinh (a * y) ^ 2 ≤ y ^ 2 / (Real.exp (a * y) / 4) ^ 2 :=
      div_le_div₀ (by positivity) le_rfl hdenpos hden
    _ = 16 * y ^ 2 * Real.exp (-2 * a * y) := by
      rw [show -2 * a * y = -((a * y) + (a * y)) by ring,
        Real.exp_neg, Real.exp_add]
      field_simp [Real.exp_ne_zero]
      ring

/-- The far part of `y²/sinh²(ay)` is integrable. -/
private lemma integrableOn_sq_div_sinh_sq_far {a T : ℝ} (ha : 0 < a)
    (hT0 : 0 ≤ T) (hTinv : 1 / a ≤ T) :
    IntegrableOn (fun y : ℝ => y ^ 2 / Real.sinh (a * y) ^ 2) (Ioi T) := by
  have hq : IntegrableOn (fun y : ℝ => 16 * y ^ 2 * Real.exp (-2 * a * y))
      (Ioi T) := by
    have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 2) (b := 2 * a) (by norm_num) (by norm_num) (by positivity)
    have h : IntegrableOn (fun y : ℝ => y ^ 2 * Real.exp (-2 * a * y))
        (Ioi 0) := by
      apply h0.congr
      filter_upwards with y
      simp only [Real.rpow_two, Real.rpow_one]
      congr 2
      ring
    have h' : IntegrableOn (fun y : ℝ => 16 * y ^ 2 * Real.exp (-2 * a * y))
        (Ioi 0) := by
      apply (h.const_mul 16).congr
      filter_upwards with y
      ring
    exact h'.mono_set (Ioi_subset_Ioi hT0)
  apply hq.mono'
  · exact (by measurability : Measurable (fun y : ℝ =>
      y ^ 2 / Real.sinh (a * y) ^ 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hay : 1 ≤ a * y := by
      calc
        1 = a * (1 / a) := by field_simp
        _ ≤ a * y := mul_le_mul_of_nonneg_left (hTinv.trans hy.le) ha.le
    exact sq_div_sinh_sq_le_exp hay

/-- For `y > 0`, `y²/sinh²(ay) ≤ 1/a²`. -/
private lemma sq_div_sinh_sq_le {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    y ^ 2 / Real.sinh (a * y) ^ 2 ≤ 1 / a ^ 2 := by
  have hsy : 0 < Real.sinh (a * y) := Real.sinh_pos_iff.mpr (mul_pos ha hy)
  have hsq := sq_le_sinh_sq (a * y)
  exact (div_le_div_iff₀ (sq_pos_of_pos hsy) (sq_pos_of_pos ha)).mpr
    (by nlinarith [hsq])

/-- `y²/sinh²(ay)` is integrable on `(0, ∞)` for `a > 0`: it is at most `1/a²` by
`sq_le_sinh_sq`, and `O(y² e^{-2ay})` at infinity. Since `1 - cos 2yz ≤ 2y²z²`, it dominates
the cosine kernel of Ruijsenaars (1997), equation (2.66). -/
theorem integrableOn_sq_div_sinh_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => y ^ 2 / Real.sinh (a * y) ^ 2) (Ioi 0) := by
  let T := max 1 (1 / a)
  have hT0 : 0 ≤ T := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hTinv : 1 / a ≤ T := le_max_right _ _
  have hnear : IntegrableOn (fun y : ℝ => y ^ 2 / Real.sinh (a * y) ^ 2)
      (Ioc 0 T) := by
    apply (integrableOn_const (C := 1 / a ^ 2) (s := Ioc 0 T) (by simp)).mono'
    · exact (by measurability : Measurable (fun y : ℝ =>
        y ^ 2 / Real.sinh (a * y) ^ 2)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact sq_div_sinh_sq_le ha hy.1
  rw [← Ioc_union_Ioi_eq_Ioi hT0]
  exact hnear.union (integrableOn_sq_div_sinh_sq_far ha hT0 hTinv)

/-! ### Exponential integrals -/

/-- For `b > 0`, `(A+y)e^{-by}` is integrable on `(0,∞)`. -/
lemma integrableOn_add_mul_exp_neg_mul (A : ℝ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun y : ℝ => (A + y) * Real.exp (-(b * y))) (Ioi 0) := by
  have h0 : IntegrableOn (fun y : ℝ => Real.exp (-(b * y))) (Ioi 0) := by
    simpa only [neg_mul] using (integrableOn_exp_mul_Ioi (a := -b) (by linarith) 0)
  have h1 : IntegrableOn (fun y : ℝ => y * Real.exp (-(b * y))) (Ioi 0) := by
    simpa only [Real.rpow_one, pow_one, one_mul, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := b)
        (by norm_num) (by norm_num) hb)
  exact ((h0.const_mul A).add h1).congr
    (Filter.Eventually.of_forall fun y => by simp only [Pi.add_apply]; ring)

/-- For `b > 0`, the integral of `(A+y)e^{-by}` on `(0,∞)` is `A/b + 1/b²`. -/
lemma integral_add_mul_exp_neg_mul (A : ℝ) {b : ℝ} (hb : 0 < b) :
    (∫ y in Ioi (0 : ℝ), (A + y) * Real.exp (-(b * y))) = A / b + 1 / b ^ 2 := by
  have h0 : IntegrableOn (fun y : ℝ => Real.exp (-(b * y))) (Ioi 0) := by
    simpa only [neg_mul] using (integrableOn_exp_mul_Ioi (a := -b) (by linarith) 0)
  have h1 : IntegrableOn (fun y : ℝ => y * Real.exp (-(b * y))) (Ioi 0) := by
    simpa only [Real.rpow_one, pow_one, one_mul, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := b)
        (by norm_num) (by norm_num) hb)
  have hExp : (∫ y in Ioi (0 : ℝ), Real.exp (-(b * y))) = 1 / b := by
    simpa [neg_mul] using (integral_exp_mul_Ioi (a := -b) (by linarith) 0)
  have hMul : (∫ y in Ioi (0 : ℝ), y * Real.exp (-(b * y))) = 1 / b ^ 2 := by
    have hgamma : Real.Gamma (2 : ℝ) = 1 := by
      simpa only [Nat.cast_one, one_add_one_eq_two, Nat.factorial_one] using
        (Real.Gamma_nat_eq_factorial 1)
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := b) (by norm_num) hb
    simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
      hgamma, mul_one] at h
    simpa [div_eq_mul_inv, inv_pow, neg_mul] using h
  calc
    (∫ y in Ioi (0 : ℝ), (A + y) * Real.exp (-(b * y))) =
        ∫ y in Ioi (0 : ℝ), A * Real.exp (-(b * y)) + y * Real.exp (-(b * y)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro y hy
          ring
    _ = A / b + 1 / b ^ 2 := by
      rw [integral_add (h0.const_mul A) h1, integral_const_mul, hExp, hMul]
      ring

/-! ### The cosine transform: equation (2.66) -/

/-- The cosine kernel in (2.66) is nonnegative. -/
private lemma cosineKernel_nonneg (a y z : ℝ) :
    0 ≤ (1 - Real.cos (2 * y * z)) / Real.sinh (a * y) ^ 2 := by
  exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (sq_nonneg _)

/-- The cosine kernel is bounded by `2z² y²/sinh²(ay)`. -/
lemma one_sub_cos_div_sinh_sq_le (a y z : ℝ) :
    (1 - Real.cos (2 * y * z)) / Real.sinh (a * y) ^ 2 ≤
      2 * z ^ 2 * (y ^ 2 / Real.sinh (a * y) ^ 2) := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := 2 * y * z)
  have hnum : 1 - Real.cos (2 * y * z) ≤ 2 * z ^ 2 * y ^ 2 := by nlinarith [hc]
  calc
    _ ≤ (2 * z ^ 2 * y ^ 2) / Real.sinh (a * y) ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = 2 * z ^ 2 * (y ^ 2 / Real.sinh (a * y) ^ 2) := by ring

/-- The integrand `(1 - cos 2yz)/sinh²(ay)` of Ruijsenaars (1997), equation (2.66), is
integrable on `(0, ∞)` for `a > 0` and real `z`. -/
theorem integrableOn_one_sub_cos_div_sinh_sq {a : ℝ} (ha : 0 < a) (z : ℝ) :
    IntegrableOn (fun y : ℝ => (1 - Real.cos (2 * y * z)) / Real.sinh (a * y) ^ 2)
      (Ioi 0) := by
  let f : ℝ → ℝ := fun y => (1 - Real.cos (2 * y * z)) / Real.sinh (a * y) ^ 2
  have hmeas : Measurable f := by
    dsimp [f]
    exact (measurable_const.sub (Real.measurable_cos.comp
      ((measurable_const.mul measurable_id).mul measurable_const))).div
      (Real.measurable_sinh.comp (measurable_const.mul measurable_id) |>.pow_const 2)
  apply Integrable.mono' ((integrableOn_sq_div_sinh_sq ha).const_mul (2 * z ^ 2))
    hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (cosineKernel_nonneg a y z)]
  exact one_sub_cos_div_sinh_sq_le a y z

/-- Exponential times cosine is integrable on `(0, ∞)` for positive decay. -/
private lemma integrableOn_exp_mul_cos {b : ℝ} (hb : 0 < b) (c : ℝ) :
    IntegrableOn (fun y : ℝ => Real.exp (-(b * y)) * Real.cos (c * y)) (Ioi 0) := by
  have hbase : IntegrableOn (fun y : ℝ => Real.exp (-(b * y))) (Ioi 0) := by
    simpa only [neg_mul] using (integrableOn_exp_mul_Ioi (a := -b) (by linarith) 0)
  apply Integrable.mono' hbase (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

/-- Laplace transform of a cosine: `∫₀^∞ e^{-by} cos(cy) dy = b/(b²+c²)`. -/
private lemma integral_exp_mul_cos {b : ℝ} (hb : 0 < b) (c : ℝ) :
    ∫ y in Ioi (0 : ℝ), Real.exp (-(b * y)) * Real.cos (c * y) =
      b / (b ^ 2 + c ^ 2) := by
  let A : ℂ := -(b : ℂ) + (c : ℂ) * Complex.I
  have hA : A.re < 0 := by simp [A]; linarith
  have hcomplex : IntegrableOn (fun y : ℝ => Complex.exp (A * y)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hA 0
  have hre : ∀ y : ℝ, (Complex.exp (A * y)).re =
      Real.exp (-(b * y)) * Real.cos (c * y) := by
    intro y
    rw [Complex.exp_re]
    simp [A, Complex.mul_re, Complex.mul_im]
  calc
    ∫ y in Ioi (0 : ℝ), Real.exp (-(b * y)) * Real.cos (c * y) =
        ∫ y in Ioi (0 : ℝ), (Complex.exp (A * y)).re := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact (hre y).symm
    _ = (∫ y in Ioi (0 : ℝ), Complex.exp (A * y)).re := integral_re hcomplex
    _ = b / (b ^ 2 + c ^ 2) := by
      rw [integral_exp_mul_complex_Ioi hA 0]
      simp only [neg_div]
      simp [A, Complex.normSq_apply]
      ring

/-- Integrability of an exponential cosine difference used in (2.66). -/
private lemma integrableOn_exp_mul_one_sub_cos {b : ℝ} (hb : 0 < b) (c : ℝ) :
    IntegrableOn (fun y : ℝ => Real.exp (-(b * y)) * (1 - Real.cos (c * y)))
      (Ioi 0) := by
  have hExp : IntegrableOn (fun y : ℝ => Real.exp (-(b * y))) (Ioi 0) := by
    simpa only [neg_mul] using (integrableOn_exp_mul_Ioi (a := -b) (by linarith) 0)
  have h := hExp.sub (integrableOn_exp_mul_cos hb c)
  have heq : (fun y : ℝ => Real.exp (-(b * y)) * (1 - Real.cos (c * y))) =
      (fun y : ℝ => Real.exp (-(b * y)) -
        Real.exp (-(b * y)) * Real.cos (c * y)) := by
    funext y
    ring
  rw [heq]
  exact h

/-- The Laplace transform of `1-cos(cy)` used in (2.66). -/
private lemma integral_exp_mul_one_sub_cos {b : ℝ} (hb : 0 < b) (c : ℝ) :
    ∫ y in Ioi (0 : ℝ), Real.exp (-(b * y)) * (1 - Real.cos (c * y)) =
      1 / b - b / (b ^ 2 + c ^ 2) := by
  have hExp : IntegrableOn (fun y : ℝ => Real.exp (-(b * y))) (Ioi 0) := by
    simpa only [neg_mul] using (integrableOn_exp_mul_Ioi (a := -b) (by linarith) 0)
  have hExpVal : (∫ y in Ioi (0 : ℝ), Real.exp (-(b * y))) = 1 / b := by
    simpa [neg_mul] using (integral_exp_mul_Ioi (a := -b) (by linarith) 0)
  calc
    _ = ∫ y in Ioi (0 : ℝ),
        (Real.exp (-(b * y)) - Real.exp (-(b * y)) * Real.cos (c * y)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      ring
    _ = (∫ y in Ioi (0 : ℝ), Real.exp (-(b * y))) -
        (∫ y in Ioi (0 : ℝ), Real.exp (-(b * y)) * Real.cos (c * y)) := by
      rw [integral_sub hExp (integrableOn_exp_mul_cos hb c)]
    _ = _ := by rw [hExpVal, integral_exp_mul_cos hb c]

/-- The differentiated geometric series, indexed from one, used in (2.66). -/
private lemma tsum_succ_coe_mul_geometric {q : ℝ} (hq : ‖q‖ < 1) :
    (∑' n : ℕ, ((n : ℝ) + 1) * q ^ (n + 1)) = q / (1 - q) ^ 2 := by
  have hgeom := tsum_coe_mul_geometric_of_norm_lt_one (r := q) hq
  have hshift := (hasSum_coe_mul_geometric_of_norm_lt_one hq).summable.sum_add_tsum_nat_add 1
  simpa [hgeom] using hshift

/-- Geometric expansion of `1/sinh² y` for positive `y`, used in (2.66). -/
private lemma inv_sinh_sq_eq_tsum (y : ℝ) (hy : 0 < y) :
    1 / Real.sinh y ^ 2 =
      ∑' n : ℕ, 4 * ((n : ℝ) + 1) * Real.exp (-(2 * ((n : ℝ) + 1) * y)) := by
  let q := Real.exp (-(2 * y))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hqnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hs : Real.sinh y ≠ 0 := (Real.sinh_ne_zero).mpr hy.ne'
  have he : Real.exp (-y) ≠ 0 := (Real.exp_pos _).ne'
  have hqden : 1 - q = 2 * Real.exp (-y) * Real.sinh y := SIC.one_sub_exp_neg_two_mul y
  calc
    1 / Real.sinh y ^ 2 = 4 * (q / (1 - q) ^ 2) := by
      rw [hqden]
      field_simp
      dsimp [q]
      rw [show -(2 * y) = -y + -y by ring, Real.exp_add]
      ring
    _ = 4 * (∑' n : ℕ, ((n : ℝ) + 1) * q ^ (n + 1)) := by
      rw [tsum_succ_coe_mul_geometric hqnorm]
    _ = ∑' n : ℕ, 4 * ((n : ℝ) + 1) * Real.exp (-(2 * ((n : ℝ) + 1) * y)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [show -(2 * ((n : ℝ) + 1) * y) = -(2 * y) * (n + 1 : ℕ) by push_cast; ring,
        mul_comm (-(2 * y)) (n + 1 : ℕ), Real.exp_nat_mul]
      dsimp [q]
      ring

/-- The `m = n+1` exponential summand of the cosine kernel in equation (2.66). -/
private def cosineSeriesTerm (v : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  4 * ((n : ℝ) + 1) * Real.exp (-(2 * ((n : ℝ) + 1) * y)) *
    (1 - Real.cos (2 * y * v))

/-- Each cosine series summand is integrable on the positive half line. -/
private lemma cosineSeriesTerm_integrableOn (v : ℝ) (n : ℕ) :
    IntegrableOn (cosineSeriesTerm v n) (Ioi 0) := by
  let m : ℝ := (n : ℝ) + 1
  have hm : 0 < m := by dsimp [m]; positivity
  have hb : 0 < 2 * m := by positivity
  have h := (integrableOn_exp_mul_one_sub_cos hb (2 * v)).const_mul (4 * m)
  have heq : cosineSeriesTerm v n =
      (fun y : ℝ => (4 * m) *
        (Real.exp (-(2 * m * y)) * (1 - Real.cos ((2 * v) * y)))) := by
    funext y
    dsimp [cosineSeriesTerm, m]
    rw [show (2 * v) * y = 2 * y * v by ring]
    ring
  rw [heq]
  exact h

/-- `∫₀^∞ 4m e^{-2my}(1-cos 2vy) dy = 2v²/(m²+v²)` for `m=n+1`. -/
private lemma cosineSeriesTerm_integral (v : ℝ) (n : ℕ) :
    ∫ y in Ioi (0 : ℝ), cosineSeriesTerm v n y =
      2 * v ^ 2 / (((n : ℝ) + 1) ^ 2 + v ^ 2) := by
  let m : ℝ := (n : ℝ) + 1
  have hm : 0 < m := by dsimp [m]; positivity
  have hb : 0 < 2 * m := by positivity
  calc
    ∫ y in Ioi (0 : ℝ), cosineSeriesTerm v n y =
        (4 * m) * ∫ y in Ioi (0 : ℝ),
          Real.exp (-(2 * m * y)) * (1 - Real.cos ((2 * v) * y)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp [cosineSeriesTerm, m]
      rw [show (2 * v) * y = 2 * y * v by ring]
      ring
    _ = (4 * m) * (1 / (2 * m) -
        (2 * m) / ((2 * m) ^ 2 + (2 * v) ^ 2)) := by
      rw [integral_exp_mul_one_sub_cos hb (2 * v)]
    _ = 2 * v ^ 2 / (((n : ℝ) + 1) ^ 2 + v ^ 2) := by
      dsimp [m]
      have hm' : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring

/-- A nonzero imaginary real is outside the embedded integers. -/
private lemma mul_I_mem_integerComplement {v : ℝ} (hv : v ≠ 0) :
    (v : ℂ) * Complex.I ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have him := congrArg Complex.im hn
  have : v = 0 := by simpa [Complex.mul_im] using him.symm
  exact hv this

/-- The cotangent summand at `iv`, multiplied by `iv`, is real and positive. -/
private lemma mul_I_cot_summand {v : ℝ} (hv : v ≠ 0) (n : ℕ) :
    ((v : ℂ) * Complex.I) *
      (1 / ((v : ℂ) * Complex.I - ((n : ℂ) + 1)) +
        1 / ((v : ℂ) * Complex.I + ((n : ℂ) + 1))) =
      (2 * v ^ 2 / (((n : ℝ) + 1) ^ 2 + v ^ 2) : ℝ) := by
  let x : ℂ := (v : ℂ) * Complex.I
  have hx : x ∈ Complex.integerComplement := mul_I_mem_integerComplement hv
  have hterm := cotTerm_identity hx n
  have hx2 : x ^ 2 = -((v : ℂ) ^ 2) := by
    dsimp [x]
    rw [mul_pow, Complex.I_sq]
    ring
  have hd2 : (x + ((n : ℂ) + 1)) * (x - ((n : ℂ) + 1)) =
      -(((n : ℂ) + 1) ^ 2 + (v : ℂ) ^ 2) := by
    calc
      _ = x ^ 2 - ((n : ℂ) + 1) ^ 2 := by ring
      _ = _ := by rw [hx2]; ring
  change x * (1 / (x - ((n : ℂ) + 1)) + 1 / (x + ((n : ℂ) + 1))) = _
  rw [← cotTerm, hterm]
  calc
    x * (2 * x * (1 / ((x + ((n : ℂ) + 1)) * (x - ((n : ℂ) + 1))))) =
        2 * x ^ 2 / ((x + ((n : ℂ) + 1)) * (x - ((n : ℂ) + 1))) := by ring
    _ = (2 * v ^ 2 / (((n : ℝ) + 1) ^ 2 + v ^ 2) : ℝ) := by
      rw [hx2, hd2]
      push_cast
      rw [show (2 : ℂ) * -(v : ℂ) ^ 2 = -(2 * (v : ℂ) ^ 2) by ring, neg_div_neg_eq]

/-- Cotangent at an imaginary argument becomes a hyperbolic cotangent. -/
private lemma mul_I_cot_eq_hyperbolic {v : ℝ} (hv : v ≠ 0) :
    ((v : ℂ) * Complex.I) *
      Complex.cot ((π : ℂ) * ((v : ℂ) * Complex.I)) =
        (v * (Real.cosh (π * v) / Real.sinh (π * v)) : ℝ) := by
  have hsh : Real.sinh (π * v) ≠ 0 :=
    (Real.sinh_ne_zero).mpr (mul_ne_zero Real.pi_ne_zero hv)
  have harg : (π : ℂ) * ((v : ℂ) * Complex.I) =
      ((π * v : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [harg, Complex.cot, Complex.cos_mul_I, Complex.sin_mul_I,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  push_cast
  field_simp

/-- The left side of the cotangent partial fraction formula at `iv`. -/
private lemma mul_I_cot_lhs {v : ℝ} (hv : v ≠ 0) :
    ((v : ℂ) * Complex.I) *
      ((π : ℂ) * Complex.cot ((π : ℂ) * ((v : ℂ) * Complex.I)) -
        1 / ((v : ℂ) * Complex.I)) =
      (π * v * (Real.cosh (π * v) / Real.sinh (π * v)) - 1 : ℝ) := by
  have hx : ((v : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (by simpa using hv) Complex.I_ne_zero
  have hc := mul_I_cot_eq_hyperbolic hv
  calc
    ((v : ℂ) * Complex.I) *
        ((π : ℂ) * Complex.cot ((π : ℂ) * ((v : ℂ) * Complex.I)) -
          1 / ((v : ℂ) * Complex.I)) =
        (π : ℂ) * (((v : ℂ) * Complex.I) *
          Complex.cot ((π : ℂ) * ((v : ℂ) * Complex.I))) - 1 := by
      have hcancel : ((v : ℂ) * Complex.I) * (1 / ((v : ℂ) * Complex.I)) = 1 := by
        simpa only [one_div] using (mul_inv_cancel₀ hx)
      rw [mul_sub, hcancel]
      ring
    _ = (π * v * (Real.cosh (π * v) / Real.sinh (π * v)) - 1 : ℝ) := by
      rw [hc]
      push_cast
      ring

/-- Mittag-Leffler summation of the cosine-transform terms in equation (2.66). -/
private lemma tsum_cosineSeriesTerm_integral {v : ℝ} (hv : v ≠ 0) :
    (∑' n : ℕ, 2 * v ^ 2 / (((n : ℝ) + 1) ^ 2 + v ^ 2)) =
      π * v * (Real.cosh (π * v) / Real.sinh (π * v)) - 1 := by
  let x : ℂ := (v : ℂ) * Complex.I
  have hx : x ∈ Complex.integerComplement := mul_I_mem_integerComplement hv
  have hcomplex :
      ((π * v * (Real.cosh (π * v) / Real.sinh (π * v)) - 1 : ℝ) : ℂ) =
      ∑' n : ℕ, (2 * v ^ 2 / (((n : ℝ) + 1) ^ 2 + v ^ 2) : ℝ) := by
    rw [← mul_I_cot_lhs hv]
    change x * ((π : ℂ) * Complex.cot ((π : ℂ) * x) - 1 / x) = _
    rw [cot_series_rep' hx, ← tsum_mul_left, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    exact mul_I_cot_summand hv n
  apply Complex.ofReal_injective
  
  exact hcomplex.symm

/-- Summability of the positive-index inverse squares used by (2.66). -/
private lemma shifted_zeta_two_summable :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
  convert (summable_nat_add_iff 1).2 hasSum_zeta_two.summable using 1 with n
  push_cast
  ring

/-- The integrated cosine summands have summable values. -/
private lemma summable_cosineSeriesTerm_integral (v : ℝ) :
    Summable (fun n : ℕ => 2 * v ^ 2 / (((n : ℝ) + 1) ^ 2 + v ^ 2)) := by
  have hbase : Summable (fun n : ℕ => 2 * v ^ 2 / ((n : ℝ) + 1) ^ 2) := by
    convert shifted_zeta_two_summable.mul_left (2 * v ^ 2) using 1 with n
    ring_nf
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (le_add_of_nonneg_right (sq_nonneg v))

/-- The norm of a cosine series summand has the same integral as the summand. -/
private lemma integral_norm_cosineSeriesTerm (v : ℝ) (n : ℕ) :
    ∫ y in Ioi (0 : ℝ), ‖cosineSeriesTerm v n y‖ =
      2 * v ^ 2 / (((n : ℝ) + 1) ^ 2 + v ^ 2) := by
  rw [← cosineSeriesTerm_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  change ‖cosineSeriesTerm v n y‖ = cosineSeriesTerm v n y
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    dsimp [cosineSeriesTerm]
    exact mul_nonneg
      (mul_nonneg (by positivity) (Real.exp_pos _).le)
      (sub_nonneg.mpr (Real.cos_le_one _)))]

/-- Pointwise geometric expansion of the cosine kernel in (2.66). -/
private lemma cosineKernel_eq_tsum (v : ℝ) {y : ℝ} (hy : 0 < y) :
    (1 - Real.cos (2 * y * v)) / Real.sinh y ^ 2 =
      ∑' n, cosineSeriesTerm v n y := by
  calc
    (1 - Real.cos (2 * y * v)) / Real.sinh y ^ 2 =
        (1 - Real.cos (2 * y * v)) * (1 / Real.sinh y ^ 2) := by ring
    _ = (1 - Real.cos (2 * y * v)) *
        (∑' n : ℕ, 4 * ((n : ℝ) + 1) * Real.exp (-(2 * ((n : ℝ) + 1) * y))) := by
      rw [inv_sinh_sq_eq_tsum y hy]
    _ = ∑' n, cosineSeriesTerm v n y := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      dsimp [cosineSeriesTerm]
      ring

/-- Integration of the geometric cosine expansion for period parameter one. -/
private lemma integral_cosineKernel_one_eq_tsum (v : ℝ) :
    ∫ y in Ioi (0 : ℝ), (1 - Real.cos (2 * y * v)) / Real.sinh y ^ 2 =
      ∑' n : ℕ, 2 * v ^ 2 / (((n : ℝ) + 1) ^ 2 + v ^ 2) := by
  let F : ℕ → ℝ → ℝ := cosineSeriesTerm v
  have hterm : ∀ n, IntegrableOn (F n) (Ioi 0) := cosineSeriesTerm_integrableOn v
  have hsum : Summable (fun n => ∫ y in Ioi (0 : ℝ), ‖F n y‖) := by
    simp_rw [show ∀ n, (∫ y in Ioi (0 : ℝ), ‖F n y‖) =
      2 * v ^ 2 / (((n : ℝ) + 1) ^ 2 + v ^ 2) from integral_norm_cosineSeriesTerm v]
    exact summable_cosineSeriesTerm_integral v
  calc
    ∫ y in Ioi (0 : ℝ), (1 - Real.cos (2 * y * v)) / Real.sinh y ^ 2 =
        ∫ y in Ioi (0 : ℝ), ∑' n, F n y := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact cosineKernel_eq_tsum v hy
    _ = ∑' n, ∫ y in Ioi (0 : ℝ), F n y :=
      (integral_tsum_of_summable_integral_norm hterm hsum).symm
    _ = ∑' n : ℕ, 2 * v ^ 2 / (((n : ℝ) + 1) ^ 2 + v ^ 2) := by
      apply tsum_congr
      intro n
      exact cosineSeriesTerm_integral v n

/-- `π z coth(πz/a) = a + a² ∫₀^∞ (1 - cos 2yz)/sinh²(ay) dy` for `a > 0` and real `z ≠ 0`,
Ruijsenaars (1997), equation (2.66). At `z = 0` the left side is the limit `a`. -/
theorem mul_coth_eq_add_integral_one_sub_cos_div_sinh_sq {a : ℝ} (ha : 0 < a) {z : ℝ}
    (hz : z ≠ 0) :
    π * z * (Real.cosh (π * z / a) / Real.sinh (π * z / a)) =
      a + a ^ 2 * ∫ y in Ioi (0 : ℝ), (1 - Real.cos (2 * y * z)) / Real.sinh (a * y) ^ 2 := by
  have ha0 : a ≠ 0 := ha.ne'
  have hv : z / a ≠ 0 := div_ne_zero hz ha0
  let g : ℝ → ℝ := fun x => (1 - Real.cos (2 * x * (z / a))) / Real.sinh x ^ 2
  have hscale :
      (∫ y in Ioi (0 : ℝ), (1 - Real.cos (2 * y * z)) / Real.sinh (a * y) ^ 2) =
        a⁻¹ * ∫ x in Ioi (0 : ℝ), g x := by
    calc
      _ = ∫ y in Ioi (0 : ℝ), g (a * y) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        dsimp [g]
        rw [show 2 * (a * y) * (z / a) = 2 * y * z by field_simp]
      _ = a⁻¹ • ∫ x in Ioi (a * 0), g x := integral_comp_mul_left_Ioi g 0 ha
      _ = a⁻¹ * ∫ x in Ioi (0 : ℝ), g x := by simp [smul_eq_mul]
  have hunit : (∫ x in Ioi (0 : ℝ), g x) =
      π * (z / a) * (Real.cosh (π * (z / a)) / Real.sinh (π * (z / a))) - 1 := by
    dsimp [g]
    rw [integral_cosineKernel_one_eq_tsum, tsum_cosineSeriesTerm_integral hv]
  rw [hscale, hunit]
  have harg : π * (z / a) = π * z / a := by ring
  rw [harg]
  field_simp
  ring

/-! ### Ruijsenaars' constant `c₊`: equation (3.45) -/

/-- The geometric expansion of `e^{-t}/sinh t` in equation (3.45). -/
private lemma exp_neg_div_sinh_eq_tsum (t : ℝ) (ht : 0 < t) :
    Real.exp (-t) / Real.sinh t =
      ∑' n : ℕ, 2 * Real.exp (-(2 * ((n : ℝ) + 1) * t)) := by
  let q := Real.exp (-(2 * t))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hs : Real.sinh t ≠ 0 := (Real.sinh_ne_zero).mpr ht.ne'
  have he : Real.exp (-t) ≠ 0 := (Real.exp_pos _).ne'
  have hq : 1 - q = 2 * Real.exp (-t) * Real.sinh t := SIC.one_sub_exp_neg_two_mul t
  have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (2 * q)
  calc
    Real.exp (-t) / Real.sinh t = 2 * q / (1 - q) := by
      rw [hq]
      field_simp
      change Real.exp (-t) ^ 2 = Real.exp (-(2 * t))
      rw [show -(2 * t) = -t + -t by ring, Real.exp_add]
      ring
    _ = ∑' n : ℕ, (2 * q) * q ^ n := by
      simpa [div_eq_mul_inv] using hg.tsum_eq.symm
    _ = ∑' n : ℕ, 2 * Real.exp (-(2 * ((n : ℝ) + 1) * t)) := by
      apply tsum_congr
      intro n
      rw [show -(2 * ((n : ℝ) + 1) * t) = -(2 * t) * (n + 1 : ℕ) by push_cast; ring,
        mul_comm (-(2 * t)) (n + 1 : ℕ), Real.exp_nat_mul, pow_succ]
      dsimp only [q]
      ring

/-- The positive-index form of the Basel sum used in equation (3.45). -/
private lemma shifted_zeta_two :
    (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2) = π ^ 2 / 6 := by
  have h := hasSum_zeta_two.summable.sum_add_tsum_nat_add 1
  simp only [one_div] at h
  have heval : (∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹) = π ^ 2 / 6 := by
    simpa only [one_div] using hasSum_zeta_two.tsum_eq
  simpa only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by decide : (2:ℕ) ≠ 0),
    inv_zero, zero_add, Nat.cast_add, Nat.cast_one, one_div] using h.trans heval

/-- The value of one term in the series for equation (3.45). -/
private lemma integral_exp_series_term (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), 2 * t * Real.exp (-(2 * ((n : ℝ) + 1) * t)) =
      1 / (2 * ((n : ℝ) + 1) ^ 2) := by
  have hb : 0 < 2 * ((n : ℝ) + 1) := by positivity
  have hlin := integral_add_mul_exp_neg_mul 0 hb
  have heq : (∫ t in Ioi (0 : ℝ), 2 * t * Real.exp (-(2 * ((n : ℝ) + 1) * t))) =
      2 * ∫ t in Ioi (0 : ℝ), ((0 : ℝ) + t) * Real.exp (-(2 * ((n : ℝ) + 1) * t)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    ring
  rw [heq, hlin]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Integrability of one term in the series for equation (3.45). -/
private lemma integrableOn_exp_series_term (n : ℕ) :
    IntegrableOn (fun t : ℝ => 2 * t * Real.exp (-(2 * ((n : ℝ) + 1) * t))) (Ioi 0) :=
  by
    have h := (integrableOn_add_mul_exp_neg_mul 0
      (show 0 < 2 * ((n : ℝ) + 1) by positivity)).const_mul 2
    apply h.congr
    filter_upwards with t
    ring

/-- The norm of a nonnegative term in the series for equation (3.45). -/
private lemma integral_norm_exp_series_term (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖2 * t * Real.exp (-(2 * ((n : ℝ) + 1) * t))‖) =
      1 / (2 * ((n : ℝ) + 1) ^ 2) := by
  rw [← integral_exp_series_term n]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change ‖2 * t * Real.exp (-(2 * ((n : ℝ) + 1) * t))‖ =
    2 * t * Real.exp (-(2 * ((n : ℝ) + 1) * t))
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    exact mul_nonneg (mul_nonneg (by norm_num) ht.le) (Real.exp_pos _).le)]

/-- The pointwise series of the integrand in equation (3.45). -/
private lemma mul_exp_neg_div_sinh_eq_tsum (t : ℝ) (ht : 0 < t) :
    t * Real.exp (-t) / Real.sinh t =
      ∑' n : ℕ, 2 * t * Real.exp (-(2 * ((n : ℝ) + 1) * t)) := by
  calc
    t * Real.exp (-t) / Real.sinh t = t * (Real.exp (-t) / Real.sinh t) := by ring
    _ = t * (∑' n : ℕ, 2 * Real.exp (-(2 * ((n : ℝ) + 1) * t))) := by
      rw [exp_neg_div_sinh_eq_tsum t ht]
    _ = ∑' n : ℕ, 2 * t * Real.exp (-(2 * ((n : ℝ) + 1) * t)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      ring

/-- The integrand `t e^{-t}/sinh t` of Ruijsenaars (1997), equation (3.45), is integrable on
`(0, ∞)`. -/
theorem integrableOn_mul_exp_neg_div_sinh :
    IntegrableOn (fun t : ℝ => t * Real.exp (-t) / Real.sinh t) (Ioi 0) := by
  apply Integrable.mono' (integrableOn_exp_neg_Ioi 0) (by
    exact ((measurable_id.mul (Real.measurable_exp.comp measurable_neg)).div
      Real.measurable_sinh).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    exact div_nonneg (mul_nonneg ht.le (Real.exp_pos _).le)
      (Real.sinh_nonneg_iff.mpr ht.le))]
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have hle : t ≤ Real.sinh t := Real.self_le_sinh_iff.mpr ht.le
  exact (div_le_iff₀ hs).2 (by nlinarith [mul_le_mul_of_nonneg_right hle (Real.exp_pos (-t)).le])

/-- `c₊ = ∫₀^∞ t e^{-t}/sinh t dt = π²/12`, Ruijsenaars (1997), equation (3.45). -/
theorem integral_mul_exp_neg_div_sinh :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-t) / Real.sinh t = π ^ 2 / 12 := by
  let F : ℕ → ℝ → ℝ := fun n t => 2 * t * Real.exp (-(2 * ((n : ℝ) + 1) * t))
  have hterm : ∀ n, IntegrableOn (F n) (Ioi 0) := integrableOn_exp_series_term
  have hsum : Summable (fun n => ∫ t in Ioi (0 : ℝ), ‖F n t‖) := by
    simp_rw [show ∀ n, (∫ t in Ioi (0 : ℝ), ‖F n t‖) =
      1 / (2 * ((n : ℝ) + 1) ^ 2) from integral_norm_exp_series_term]
    convert shifted_zeta_two_summable.mul_left (1 / 2) using 1 with n
    simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
  calc
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-t) / Real.sinh t =
        ∫ t in Ioi (0 : ℝ), ∑' n, F n t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact mul_exp_neg_div_sinh_eq_tsum t ht
    _ = ∑' n, ∫ t in Ioi (0 : ℝ), F n t :=
      (integral_tsum_of_summable_integral_norm hterm hsum).symm
    _ = π ^ 2 / 12 := by
      simp_rw [show ∀ n, (∫ t in Ioi (0 : ℝ), F n t) =
        1 / (2 * ((n : ℝ) + 1) ^ 2) from integral_exp_series_term]
      simp_rw [one_div, mul_inv_rev, tsum_mul_right]
      rw [show (∑' n : ℕ, (((n : ℝ) + 1) ^ 2)⁻¹) = π ^ 2 / 6 by
        simpa only [one_div] using shifted_zeta_two]
      ring

end SIC

end
