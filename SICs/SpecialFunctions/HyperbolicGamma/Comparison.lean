/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.FourierContourShift
import SICs.SpecialFunctions.HyperbolicGamma.ComplexPeriodComparison

/-!
# Ruijsenaars' comparison with equal periods

The removable-origin kernel comparing `g(a₊,a₋;·)` with the equal-period function, and the
exponential decay of the comparison integral by a contour shift.

This module follows S. N. M. Ruijsenaars, *First order analytic difference equations and
integrable quantum systems*, J. Math. Phys. 38 (1997), 1069–1146, proof of Proposition III.4,
pp. 1096–1097, [doi:10.1063/1.531809](https://doi.org/10.1063/1.531809). With
`a = ((a₊² + a₋²)/2)^{1/2}`, equation (3.52), and the kernel

```text
I(y) = (1/(2y)) (a₊a₋/(sinh(a₊y) sinh(a₋y)) - a²/sinh²(ay)),        (3.54)
```

the comparison `a₊a₋ g(a₊,a₋;z) = a² g(a,a;z) + d(z)` holds with
`d(z) = ∫₀^∞ I(y) sin 2yz dy`, equations (3.51) and (3.53), and the contour shift
`2i d(z) = e^{-2rz} ∫_ℝ I(u + ir) e^{2iuz} du`, equation (3.56), shows `d(z) = O(e^{-2r Re z})`
for every `0 < r < π/max(a₊,a₋)`. The consumer is
`SICs.SpecialFunctions.HyperbolicGamma.Asymptotics`.

## The argument

The comparison (3.51) is linearity of the integral: the difference of the two integrands of
equation (3.1) is `I(y) sin 2yz` pointwise, and both are integrable on the strip (3.2) because
`a ≥ (a₊+a₋)/2`. The choice of `a` cancels the Laurent terms `1/y²` and `-(a₊²+a₋²)/6` of
`a₊a₋/(sinh(a₊y) sinh(a₋y))` against those of `a²/sinh²(ay)`, so the bracket is `O(y²)` and
`I(y) = O(y)` at the origin, equation (3.55); Lean's value `I(0) = 0` is the removable value.
Since `a ≤ max(a₊,a₋)`, every nonzero zero of the three hyperbolic sines has imaginary part of
absolute value at least `π/max(a₊,a₋)`, so `I` is holomorphic on the strip
`|Im y| < π/max(a₊,a₋)`. There
`|sinh(x+iy)| ≥ |sinh x|` gives `|I(y)| = O(e^{-(a₊+a₋)|Re y|})`. Because `I` is odd,
`2i d(z) = ∫_ℝ I(y) e^{2iyz} dy`; the integrand is holomorphic on the strip
`0 ≤ Im y ≤ r` and decays at both ends while `|Im z| < (a₊+a₋)/2`, so Cauchy's theorem on the
strip (`integral_horizontal_eq_of_integrable`) moves the line to `Im y = r`, where
`|e^{2i(u+ir)z}| = e^{-2r Re z} e^{-2u Im z}`.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace SIC

/-! ### The comparison period: equation (3.52)

The quadratic mean `a` of the two periods lies between their arithmetic mean and their
maximum. -/

/-- The comparison period `a = ((a₊² + a₋²)/2)^{1/2}` of Ruijsenaars (1997), equation (3.52),
with `a₁ = a₊` and `a₂ = a₋`. -/
noncomputable def hyperbolicComparisonPeriod (a₁ a₂ : ℝ) : ℝ :=
  Real.sqrt ((a₁ ^ 2 + a₂ ^ 2) / 2)

/-- The square of the comparison period is its defining quadratic mean. -/
theorem sq_hyperbolicComparisonPeriod (a₁ a₂ : ℝ) :
    hyperbolicComparisonPeriod a₁ a₂ ^ 2 = (a₁ ^ 2 + a₂ ^ 2) / 2 := by
  unfold hyperbolicComparisonPeriod
  exact Real.sq_sqrt (by positivity)

/-- The comparison period is positive for positive periods. -/
theorem hyperbolicComparisonPeriod_pos {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    0 < hyperbolicComparisonPeriod a₁ a₂ := by
  unfold hyperbolicComparisonPeriod
  apply Real.sqrt_pos.2
  positivity

/-- The comparison period is at least the arithmetic mean: `(a₊+a₋)/2 ≤ a`, the inequality
`a₊ + a₋ ≤ 2a` noted after Ruijsenaars (1997), equation (3.54). -/
theorem add_div_two_le_hyperbolicComparisonPeriod (a₁ a₂ : ℝ) :
    (a₁ + a₂) / 2 ≤ hyperbolicComparisonPeriod a₁ a₂ := by
  unfold hyperbolicComparisonPeriod
  by_cases h : 0 ≤ (a₁ + a₂) / 2
  · rw [Real.le_sqrt h (by positivity)]
    nlinarith [sq_nonneg (a₁ - a₂)]
  · exact (le_of_lt (lt_of_not_ge h)).trans (Real.sqrt_nonneg _)

/-- The comparison period is at most the larger period: `a ≤ max(a₊,a₋)`. -/
theorem hyperbolicComparisonPeriod_le_max {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    hyperbolicComparisonPeriod a₁ a₂ ≤ max a₁ a₂ := by
  unfold hyperbolicComparisonPeriod
  rw [Real.sqrt_le_iff]
  constructor
  · exact le_trans h₁.le (le_max_left _ _)
  · have hmax₁ : a₁ ≤ max a₁ a₂ := le_max_left _ _
    have hmax₂ : a₂ ≤ max a₁ a₂ := le_max_right _ _
    nlinarith [sq_nonneg (max a₁ a₂ - a₁), sq_nonneg (max a₁ a₂ - a₂),
      mul_nonneg h₁.le (sub_nonneg.mpr hmax₁),
      mul_nonneg h₂.le (sub_nonneg.mpr hmax₂)]

/-! ### The comparison kernel: equations (3.54) and (3.55)

The kernel is defined for complex `y`; on the real axis it is the kernel of (3.54). -/

/-- The comparison kernel `I(y) = (1/(2y)) (a₊a₋/(sinh(a₊y) sinh(a₋y)) - a²/sinh²(ay))` of
Ruijsenaars (1997), equation (3.54), for complex `y`, with `a` the comparison period (3.52).
Its totalized value at `y = 0` is `0`, the removable value of equation (3.55). -/
noncomputable def hyperbolicComparisonKernel (a₁ a₂ : ℝ) (y : ℂ) : ℂ :=
  1 / (2 * y) * (a₁ * a₂ / (Complex.sinh (a₁ * y) * Complex.sinh (a₂ * y)) -
    (hyperbolicComparisonPeriod a₁ a₂ : ℂ) ^ 2 /
      Complex.sinh (hyperbolicComparisonPeriod a₁ a₂ * y) ^ 2)

/-- The comparison kernel is odd, `I(-y) = -I(y)`. -/
theorem hyperbolicComparisonKernel_neg (a₁ a₂ : ℝ) (y : ℂ) :
    hyperbolicComparisonKernel a₁ a₂ (-y) = -hyperbolicComparisonKernel a₁ a₂ y := by
  simp [hyperbolicComparisonKernel, mul_neg, sinh_neg, neg_mul]

/-- A hyperbolic sine with positive period has no nonzero zero inside the strip used by
`differentiableOn_hyperbolicComparisonKernel`. -/
private lemma sinh_ne_zero_of_strip {b M : ℝ} (hb : 0 < b) (hbM : b ≤ M)
    {y : ℂ} (hy : |y.im| < Real.pi / M) (hy0 : y ≠ 0) :
    Complex.sinh (b * y) ≠ 0 := by
  apply sinh_mul_ne_zero_of_abs_im_mul_normSq_lt (by simpa using hb) hy0
  have hM : 0 < M := hb.trans_le hbM
  have hMim : M * |y.im| < Real.pi := by
    simpa [mul_comm] using (lt_div_iff₀ hM).mp hy
  have hbim : b * |y.im| < Real.pi :=
    (mul_le_mul_of_nonneg_right hbM (abs_nonneg _)).trans_lt hMim
  have := mul_lt_mul_of_pos_left hbim hb
  simpa [Complex.normSq_apply, mul_assoc, mul_comm, mul_left_comm] using this

/-- The comparison kernel has its removable value at the origin, as in Ruijsenaars (1997),
equation (3.55); this supplies continuity for `differentiableOn_hyperbolicComparisonKernel`. -/
private lemma continuousAt_hyperbolicComparisonKernel_zero {a₁ a₂ : ℝ}
    (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    ContinuousAt (hyperbolicComparisonKernel a₁ a₂) 0 := by
  let a := hyperbolicComparisonPeriod a₁ a₂
  have ha : 0 < a := hyperbolicComparisonPeriod_pos h₁ h₂
  have hquad : (1 : ℂ) * (a : ℂ) ^ 2 + 0 * (a : ℂ) ^ 2 =
      ((a₁ : ℂ) ^ 2 + (a₂ : ℂ) ^ 2) / 2 := by
    rw [one_mul, zero_mul, add_zero]
    exact_mod_cast sq_hyperbolicComparisonPeriod a₁ a₂
  have h := continuousAt_complexComparisonKernel_zero
    (by exact_mod_cast h₁.ne') (by exact_mod_cast h₂.ne') ha.ne' ha.ne'
    (by norm_num) hquad
  have hfun :
      complexComparisonKernel (a₁ : ℂ) (a₂ : ℂ) a a 1 0 =
        hyperbolicComparisonKernel a₁ a₂ := by
    funext y
    simp [a, complexComparisonKernel, hyperbolicComparisonKernel]
  rw [hfun] at h
  exact h

/-- The comparison kernel is holomorphic on the strip `|Im y| < π/max(a₊,a₋)`, including the
origin, where its singularity is removable: Ruijsenaars (1997), equation (3.55) and the
sentence after it. -/
theorem differentiableOn_hyperbolicComparisonKernel {a₁ a₂ : ℝ} (h₁ : 0 < a₁)
    (h₂ : 0 < a₂) :
    DifferentiableOn ℂ (hyperbolicComparisonKernel a₁ a₂)
      {y : ℂ | |y.im| < Real.pi / max a₁ a₂} := by
  have hM : 0 < max a₁ a₂ := h₁.trans_le (le_max_left _ _)
  have hs : {y : ℂ | |y.im| < Real.pi / max a₁ a₂} ∈ 𝓝 (0 : ℂ) := by
    have hopen : IsOpen {y : ℂ | |y.im| < Real.pi / max a₁ a₂} := by
      exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
    apply hopen.mem_nhds
    simp [div_pos Real.pi_pos hM]
  apply (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hs).mp
  constructor
  · intro y hy
    have hy0 : y ≠ 0 := by simpa using hy.2
    have hystrip : |y.im| < Real.pi / max a₁ a₂ := hy.1
    have h₁ne : Complex.sinh (a₁ * y) ≠ 0 :=
      sinh_ne_zero_of_strip h₁ (le_max_left _ _) hystrip hy0
    have h₂ne : Complex.sinh (a₂ * y) ≠ 0 :=
      sinh_ne_zero_of_strip h₂ (le_max_right _ _) hystrip hy0
    have hane : Complex.sinh (hyperbolicComparisonPeriod a₁ a₂ * y) ≠ 0 :=
      sinh_ne_zero_of_strip (hyperbolicComparisonPeriod_pos h₁ h₂)
        (hyperbolicComparisonPeriod_le_max h₁ h₂) hystrip hy0
    have htwo : (2 : ℂ) * y ≠ 0 := mul_ne_zero (by norm_num) hy0
    have hprod : Complex.sinh (a₁ * y) * Complex.sinh (a₂ * y) ≠ 0 :=
      mul_ne_zero h₁ne h₂ne
    have hsq : Complex.sinh (hyperbolicComparisonPeriod a₁ a₂ * y) ^ 2 ≠ 0 :=
      pow_ne_zero _ hane
    apply DifferentiableAt.differentiableWithinAt
    unfold hyperbolicComparisonKernel
    fun_prop (disch := assumption)
  · exact continuousAt_hyperbolicComparisonKernel_zero h₁ h₂

/-- Positivity of the exponential denominator used by `comparisonExpConstant_pos`. -/
private lemma one_sub_exp_neg_two_pos {b : ℝ} (hb : 0 < b) :
    0 < 1 - Real.exp (-2 * b) := by
  have : -2 * b < 0 := by linarith
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr this)

/-- The reciprocal-sinh constant used by `norm_inv_sinh_le_exp` and the two terms of
`norm_hyperbolicComparisonKernel_le`. -/
private def comparisonExpConstant (b : ℝ) : ℝ := 2 / (1 - Real.exp (-2 * b))

/-- The reciprocal-sinh constant is positive; used by `norm_inv_sinh_le_exp`. -/
private lemma comparisonExpConstant_pos {b : ℝ} (hb : 0 < b) :
    0 < comparisonExpConstant b :=
  div_pos (by norm_num) (one_sub_exp_neg_two_pos hb)

/-- The positive-period specialization of `norm_inv_sinh_le_exp_of_abs_re` supplies each
denominator in `norm_hyperbolicComparisonKernel_le`. -/
private lemma norm_inv_sinh_le_exp {a : ℝ} (ha : 0 < a) {y : ℂ}
    (hy : 1 ≤ |y.re|) :
    ‖(Complex.sinh (a * y))⁻¹‖ ≤
      comparisonExpConstant a * Real.exp (-a * |y.re|) := by
  have habs : |(a * y).re| = a * |y.re| := by
    simp [Complex.mul_re, abs_mul, abs_of_pos ha]
  have hbound : a ≤ |(a * y).re| := by
    rw [habs]
    calc
      a = a * 1 := by ring
      _ ≤ a * |y.re| := mul_le_mul_of_nonneg_left hy ha.le
  simpa only [comparisonExpConstant, habs, neg_mul] using
    (norm_inv_sinh_le_exp_of_abs_re (w := a * y) (d := a) ha hbound)

/-- The prefactor `1/(2y)` is bounded for `|Re y| ≥ 1`; used by
`norm_hyperbolicComparisonKernel_le`. -/
private lemma norm_comparisonKernel_prefactor_le {y : ℂ} (hy : 1 ≤ |y.re|) :
    ‖(1 : ℂ) / (2 * y)‖ ≤ 1 := by
  have hnormy : 1 ≤ ‖y‖ := hy.trans (Complex.abs_re_le_norm y)
  rw [norm_div, norm_one, norm_mul]
  norm_num at *
  have hinv : ‖y‖⁻¹ ≤ 1 := by
    simpa [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnormy)
  nlinarith

/-- The mixed-period term has the required decay; used by
`norm_hyperbolicComparisonKernel_le`. -/
private lemma norm_comparisonKernel_mixed_le {a₁ a₂ : ℝ}
    (h₁ : 0 < a₁) (h₂ : 0 < a₂) {y : ℂ} (hy : 1 ≤ |y.re|) :
    ‖(a₁ * a₂ : ℂ) / (Complex.sinh (a₁ * y) * Complex.sinh (a₂ * y))‖ ≤
      (a₁ * a₂ * comparisonExpConstant a₁ * comparisonExpConstant a₂) *
        Real.exp (-(a₁ + a₂) * |y.re|) := by
  have hsin₁ := norm_inv_sinh_le_exp h₁ hy
  have hsin₂ := norm_inv_sinh_le_exp h₂ hy
  have hK₁ : 0 ≤ comparisonExpConstant a₁ := (comparisonExpConstant_pos h₁).le
  calc
    _ = (a₁ * a₂) * ‖(Complex.sinh (a₁ * y))⁻¹‖ *
        ‖(Complex.sinh (a₂ * y))⁻¹‖ := by
          simp [div_eq_mul_inv, mul_inv_rev, Complex.norm_real,
            abs_of_pos h₁, abs_of_pos h₂]
          ring
    _ ≤ (a₁ * a₂) * (comparisonExpConstant a₁ * Real.exp (-a₁ * |y.re|)) *
        (comparisonExpConstant a₂ * Real.exp (-a₂ * |y.re|)) := by gcongr
    _ = _ := by
      rw [show -(a₁ + a₂) * |y.re| = -a₁ * |y.re| + -a₂ * |y.re| by ring,
        Real.exp_add]
      ring

/-- The equal-period term decays at least as fast as the mixed-period term; used by
`norm_hyperbolicComparisonKernel_le`. -/
private lemma norm_comparisonKernel_equal_le {a₁ a₂ : ℝ}
    (h₁ : 0 < a₁) (h₂ : 0 < a₂) {y : ℂ} (hy : 1 ≤ |y.re|) :
    let a := hyperbolicComparisonPeriod a₁ a₂
    ‖(a : ℂ) ^ 2 / Complex.sinh (a * y) ^ 2‖ ≤
      (a ^ 2 * comparisonExpConstant a ^ 2) *
        Real.exp (-(a₁ + a₂) * |y.re|) := by
  dsimp only
  let a := hyperbolicComparisonPeriod a₁ a₂
  have ha : 0 < a := hyperbolicComparisonPeriod_pos h₁ h₂
  have hsum : a₁ + a₂ ≤ 2 * a := by
    have := add_div_two_le_hyperbolicComparisonPeriod a₁ a₂
    dsimp [a]
    linarith
  have hsina := norm_inv_sinh_le_exp ha hy
  calc
    _ = a ^ 2 * ‖(Complex.sinh (a * y))⁻¹‖ ^ 2 := by
      simp [a, div_eq_mul_inv, norm_pow, Complex.norm_real]
    _ ≤ a ^ 2 * (comparisonExpConstant a * Real.exp (-a * |y.re|)) ^ 2 := by gcongr
    _ = (a ^ 2 * comparisonExpConstant a ^ 2) * Real.exp (-(2 * a) * |y.re|) := by
      rw [show -(2 * a) * |y.re| = -a * |y.re| + -a * |y.re| by ring, Real.exp_add]
      ring
    _ ≤ (a ^ 2 * comparisonExpConstant a ^ 2) *
        Real.exp (-(a₁ + a₂) * |y.re|) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hsum) (abs_nonneg y.re)]

/-- The comparison kernel decays like `e^{-(a₊+a₋)|Re y|}`: there is `C` with
`‖I(y)‖ ≤ C e^{-(a₊+a₋)|Re y|}` whenever `|Re y| ≥ 1`, for every imaginary part. -/
theorem norm_hyperbolicComparisonKernel_le {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    ∃ C : ℝ, ∀ y : ℂ, 1 ≤ |y.re| →
      ‖hyperbolicComparisonKernel a₁ a₂ y‖ ≤ C * Real.exp (-(a₁ + a₂) * |y.re|) := by
  let a := hyperbolicComparisonPeriod a₁ a₂
  refine ⟨a₁ * a₂ * comparisonExpConstant a₁ * comparisonExpConstant a₂ +
    a ^ 2 * comparisonExpConstant a ^ 2, ?_⟩
  intro y hy
  have hfirst := norm_comparisonKernel_mixed_le h₁ h₂ hy
  have hsecond := norm_comparisonKernel_equal_le h₁ h₂ hy
  calc
    ‖hyperbolicComparisonKernel a₁ a₂ y‖ ≤
        ‖(a₁ * a₂ : ℂ) / (Complex.sinh (a₁ * y) * Complex.sinh (a₂ * y))‖ +
          ‖(a : ℂ) ^ 2 / Complex.sinh (a * y) ^ 2‖ := by
      unfold hyperbolicComparisonKernel
      rw [norm_mul]
      calc
        _ ≤ 1 * ‖(a₁ * a₂ : ℂ) /
            (Complex.sinh (a₁ * y) * Complex.sinh (a₂ * y)) -
              (a : ℂ) ^ 2 / Complex.sinh (a * y) ^ 2‖ := by
            gcongr
            exact norm_comparisonKernel_prefactor_le hy
        _ ≤ _ := by simpa only [one_mul] using (norm_sub_le _ _)
    _ ≤ (a₁ * a₂ * comparisonExpConstant a₁ * comparisonExpConstant a₂) *
          Real.exp (-(a₁ + a₂) * |y.re|) +
        (a ^ 2 * comparisonExpConstant a ^ 2) *
          Real.exp (-(a₁ + a₂) * |y.re|) := add_le_add hfirst hsecond
    _ = _ := by ring

/-! ### The comparison: equations (3.51) and (3.53) -/

/-- The comparison integral `d(z) = ∫₀^∞ I(y) sin 2yz dy` of Ruijsenaars (1997),
equation (3.53). -/
noncomputable def hyperbolicComparisonIntegral (a₁ a₂ : ℝ) (z : ℂ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), hyperbolicComparisonKernel a₁ a₂ y * Complex.sin (2 * y * z)

/-- Pointwise form of the comparison identity used by `hyperbolicGammaLog_comparison`. -/
private lemma comparison_integrand_eq {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂)
    (z : ℂ) {y : ℝ} (hy : 0 < y) :
    hyperbolicComparisonKernel a₁ a₂ y * Complex.sin (2 * y * z) =
      (a₁ * a₂ : ℂ) * hyperbolicGammaLogIntegrand a₁ a₂ z y -
        (hyperbolicComparisonPeriod a₁ a₂ : ℂ) ^ 2 *
          hyperbolicGammaLogIntegrand (hyperbolicComparisonPeriod a₁ a₂)
            (hyperbolicComparisonPeriod a₁ a₂) z y := by
  have ha : 0 < hyperbolicComparisonPeriod a₁ a₂ :=
    hyperbolicComparisonPeriod_pos h₁ h₂
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have h₁0 : (a₁ : ℂ) ≠ 0 := by exact_mod_cast h₁.ne'
  have h₂0 : (a₂ : ℂ) ≠ 0 := by exact_mod_cast h₂.ne'
  have ha0 : (hyperbolicComparisonPeriod a₁ a₂ : ℂ) ≠ 0 := by
    exact_mod_cast ha.ne'
  have hs₁ : Complex.sinh ((a₁ : ℂ) * y) ≠ 0 := by
    simpa [← Complex.ofReal_mul] using
      sinh_ofReal_ne_zero (mul_ne_zero h₁.ne' hy.ne')
  have hs₂ : Complex.sinh ((a₂ : ℂ) * y) ≠ 0 := by
    simpa [← Complex.ofReal_mul] using
      sinh_ofReal_ne_zero (mul_ne_zero h₂.ne' hy.ne')
  have hsa : Complex.sinh ((hyperbolicComparisonPeriod a₁ a₂ : ℂ) * y) ≠ 0 := by
    simpa [← Complex.ofReal_mul] using
      sinh_ofReal_ne_zero (mul_ne_zero ha.ne' hy.ne')
  unfold hyperbolicComparisonKernel hyperbolicGammaLogIntegrand
  field_simp
  ring

/-- The comparison `a₊a₋ g(a₊,a₋;z) = a² g(a,a;z) + d(z)` of Ruijsenaars (1997),
equation (3.51), for `z` in the strip `|Im z| < (a₊+a₋)/2` of equation (3.2). -/
theorem hyperbolicGammaLog_comparison {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) {z : ℂ}
    (hz : |z.im| < (a₁ + a₂) / 2) :
    a₁ * a₂ * hyperbolicGammaLog a₁ a₂ z =
      (hyperbolicComparisonPeriod a₁ a₂ : ℂ) ^ 2 *
          hyperbolicGammaLog (hyperbolicComparisonPeriod a₁ a₂)
            (hyperbolicComparisonPeriod a₁ a₂) z +
        hyperbolicComparisonIntegral a₁ a₂ z := by
  have ha := hyperbolicComparisonPeriod_pos h₁ h₂
  have hz' : |z.im| <
      (hyperbolicComparisonPeriod a₁ a₂ + hyperbolicComparisonPeriod a₁ a₂) / 2 := by
    have hle := add_div_two_le_hyperbolicComparisonPeriod a₁ a₂
    linarith
  have hG := integrableOn_hyperbolicGammaLogIntegrand h₁ h₂ hz
  have hG' := integrableOn_hyperbolicGammaLogIntegrand ha ha hz'
  have hD : hyperbolicComparisonIntegral a₁ a₂ z =
      (a₁ * a₂ : ℂ) * hyperbolicGammaLog a₁ a₂ z -
        (hyperbolicComparisonPeriod a₁ a₂ : ℂ) ^ 2 *
          hyperbolicGammaLog (hyperbolicComparisonPeriod a₁ a₂)
            (hyperbolicComparisonPeriod a₁ a₂) z := by
    unfold hyperbolicComparisonIntegral hyperbolicGammaLog
    rw [show (∫ y in Ioi (0 : ℝ),
        hyperbolicComparisonKernel a₁ a₂ y * Complex.sin (2 * y * z)) =
        ∫ y in Ioi (0 : ℝ),
          (a₁ * a₂ : ℂ) * hyperbolicGammaLogIntegrand a₁ a₂ z y -
            (hyperbolicComparisonPeriod a₁ a₂ : ℂ) ^ 2 *
              hyperbolicGammaLogIntegrand (hyperbolicComparisonPeriod a₁ a₂)
                (hyperbolicComparisonPeriod a₁ a₂) z y from
      setIntegral_congr_fun measurableSet_Ioi (fun y hy =>
        comparison_integrand_eq h₁ h₂ z hy)]
    rw [integral_sub (hG.const_mul _) (hG'.const_mul _), integral_const_mul,
      integral_const_mul]
  linear_combination -hD

/-! ### The contour shift: equation (3.56)

The shared odd-kernel Fourier contour theorem supplies the Cauchy argument. It remains only to
verify its strip hypotheses for the comparison kernel and to construct the weighted majorant used
by the uniform estimate.
-/

/-- Restriction of the comparison kernel to a horizontal line inside its holomorphic strip;
used to construct the majorant for `norm_hyperbolicComparisonIntegral_le`. -/
private lemma continuous_hyperbolicComparisonKernel_horizontal {a₁ a₂ : ℝ}
    (h₁ : 0 < a₁) (h₂ : 0 < a₂) {s : ℝ}
    (hs : |s| < Real.pi / max a₁ a₂) :
    Continuous (fun u : ℝ => hyperbolicComparisonKernel a₁ a₂ (u + s * I)) := by
  have hopen : IsOpen {y : ℂ | |y.im| < Real.pi / max a₁ a₂} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  apply continuous_iff_continuousAt.mpr
  intro u
  have hmem : (u + s * I : ℂ) ∈
      {y : ℂ | |y.im| < Real.pi / max a₁ a₂} := by
    simpa [Complex.add_im, Complex.mul_im] using hs
  have hdiff := (differentiableOn_hyperbolicComparisonKernel h₁ h₂).differentiableAt
    (hopen.mem_nhds hmem)
  have hline : ContinuousAt (fun v : ℝ => (v : ℂ) + (s : ℂ) * I) u := by fun_prop
  exact ContinuousAt.comp (f := fun v : ℝ => (v : ℂ) + (s : ℂ) * I)
    hdiff.continuousAt hline

/-- Absolute integrability of the comparison kernel on a horizontal line after an
exponential weight; this is the shifted-line majorant in Ruijsenaars (1997), equation (3.56). -/
private lemma integrable_weighted_hyperbolicComparisonKernel {a₁ a₂ : ℝ}
    (h₁ : 0 < a₁) (h₂ : 0 < a₂) {s c : ℝ}
    (hs : |s| < Real.pi / max a₁ a₂) (hc : 2 * c < a₁ + a₂) :
    Integrable (fun u : ℝ =>
      ‖hyperbolicComparisonKernel a₁ a₂ (u + s * I)‖ * Real.exp (2 * c * |u|)) := by
  obtain ⟨C, hC⟩ := norm_hyperbolicComparisonKernel_le h₁ h₂
  have hcont : Continuous (fun u : ℝ =>
      ‖hyperbolicComparisonKernel a₁ a₂ (u + s * I)‖ * Real.exp (2 * c * |u|)) :=
    (continuous_hyperbolicComparisonKernel_horizontal h₁ h₂ hs).norm.mul (by fun_prop)
  refine integrable_of_continuous_norm_le_mul_exp_neg_abs
    (C := C) (T := 1) hcont (show 0 < a₁ + a₂ - 2 * c by linarith) ?_
  intro u hu
  have hu' : 1 ≤ |(u + s * I : ℂ).re| := by
    simpa [Complex.add_re, Complex.mul_re] using hu
  have hb := hC (u + s * I) hu'
  have hb' := mul_le_mul_of_nonneg_right hb (Real.exp_pos (2 * c * |u|)).le
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
  calc
    ‖hyperbolicComparisonKernel a₁ a₂ (u + s * I)‖ * Real.exp (2 * c * |u|) ≤
        C * Real.exp (-(a₁ + a₂) * |u|) * Real.exp (2 * c * |u|) := by
      simpa [Complex.add_re, Complex.mul_re] using hb'
    _ = C * Real.exp (-(a₁ + a₂ - 2 * c) * |u|) := by
      rw [show -(a₁ + a₂ - 2 * c) * |u| =
          -(a₁ + a₂) * |u| + 2 * c * |u| by ring, Real.exp_add]
      ring

/-- The contour shift `2i d(z) = e^{-2rz} ∫_ℝ I(u + ir) e^{2iuz} du` of Ruijsenaars (1997),
equation (3.56), for `|Im z| < (a₊+a₋)/2` and `0 < r < π/max(a₊,a₋)`. -/
theorem two_mul_I_mul_hyperbolicComparisonIntegral {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂)
    {z : ℂ} (hz : |z.im| < (a₁ + a₂) / 2) {r : ℝ} (hr : 0 < r)
    (hrπ : r < Real.pi / max a₁ a₂) :
    2 * I * hyperbolicComparisonIntegral a₁ a₂ z =
      Complex.exp (-2 * r * z) *
        ∫ u : ℝ, hyperbolicComparisonKernel a₁ a₂ (u + r * I) * Complex.exp (2 * I * u * z) := by
  obtain ⟨C, hC⟩ := norm_hyperbolicComparisonKernel_le h₁ h₂
  have hsubset : {w : ℂ | 0 ≤ w.im ∧ w.im ≤ r} ⊆
      {w : ℂ | |w.im| < Real.pi / max a₁ a₂} := by
    intro w hw
    change |w.im| < Real.pi / max a₁ a₂
    rw [abs_of_nonneg hw.1]
    exact hw.2.trans_lt hrπ
  have hJ := (differentiableOn_hyperbolicComparisonKernel h₁ h₂).mono hsubset
  have hbound : ∀ x : ℝ, 1 ≤ |x| → ∀ s ∈ Icc 0 r,
      ‖hyperbolicComparisonKernel a₁ a₂ (x + s * I)‖ ≤
        C * Real.exp (-(a₁ + a₂) * |x|) := by
    intro x hx s _hs
    have hx' : 1 ≤ |(x + s * I : ℂ).re| := by
      simpa [Complex.add_re, Complex.mul_re] using hx
    simpa [Complex.add_re, Complex.mul_re] using hC (x + s * I) hx'
  simpa [hyperbolicComparisonIntegral] using
    integral_mul_sin_eq_exp_mul_integral_of_odd
      (hyperbolicComparisonKernel a₁ a₂) hr hJ
      (hyperbolicComparisonKernel_neg a₁ a₂) hbound
      (show 2 * |z.im| < a₁ + a₂ by linarith)

/-- The comparison integral decays like `e^{-2r Re z}` on closed substrips: for
`c < (a₊+a₋)/2` and `0 < r < π/max(a₊,a₋)` there is `C` with `‖d(z)‖ ≤ C e^{-2r Re z}`
whenever `|Im z| ≤ c`. This is the bound read off from Ruijsenaars (1997), equation (3.56). -/
theorem norm_hyperbolicComparisonIntegral_le {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) {c : ℝ}
    (hc : c < (a₁ + a₂) / 2) {r : ℝ} (hr : 0 < r) (hrπ : r < Real.pi / max a₁ a₂) :
    ∃ C : ℝ, ∀ z : ℂ, |z.im| ≤ c →
      ‖hyperbolicComparisonIntegral a₁ a₂ z‖ ≤ C * Real.exp (-2 * r * z.re) := by
  have hsr : |r| < Real.pi / max a₁ a₂ := by simpa [abs_of_pos hr] using hrπ
  let W (u : ℝ) : ℝ :=
    ‖hyperbolicComparisonKernel a₁ a₂ (u + r * I)‖ * Real.exp (2 * c * |u|)
  have hW : Integrable W :=
    integrable_weighted_hyperbolicComparisonKernel h₁ h₂ hsr (by linarith)
  refine ⟨(∫ u : ℝ, W u) / 2, ?_⟩
  intro z hz
  have hidentity : 2 * I * (∫ u in Ioi (0 : ℝ),
      hyperbolicComparisonKernel a₁ a₂ u * Complex.sin (2 * u * z)) =
      Complex.exp (-2 * r * z) *
        ∫ u : ℝ, hyperbolicComparisonKernel a₁ a₂ (u + r * I) *
          Complex.exp (2 * I * u * z) := by
    simpa [hyperbolicComparisonIntegral] using
      two_mul_I_mul_hyperbolicComparisonIntegral h₁ h₂ (hz.trans_lt hc) hr hrπ
  simpa [hyperbolicComparisonIntegral, W] using
    norm_integral_mul_sin_le_of_integrable_majorant
      (hyperbolicComparisonKernel a₁ a₂) r c W hW (fun _ => le_rfl) hz hidentity

end SIC

end
