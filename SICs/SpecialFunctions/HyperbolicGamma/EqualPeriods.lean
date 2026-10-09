/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.HyperbolicGamma.Basic
import SICs.Analysis.HyperbolicIntegrals

/-!
# The hyperbolic gamma function with equal periods

The closed form of `g(a,a;z)` through the integral of `t coth t`, and its exponentially
accurate quadratic asymptotics.

This module follows S. N. M. Ruijsenaars, *First order analytic difference equations and
integrable quantum systems*, J. Math. Phys. 38 (1997), 1069–1146, equations (3.41)–(3.47),
[doi:10.1063/1.531809](https://doi.org/10.1063/1.531809). There

```text
g(a,a;z) = -(1/π) b(πz/a),     b(w) = ∫₀^w t coth t dt = w²/2 + c₊ - b₊(w),
b₊(w) = ∫_w^∞ t e^{-t}/sinh t dt,     c₊ = π²/12,
```

equations (3.41)–(3.45), so that `g(a,a;z) = -πz²/(2a²) - π/12 + b₊(πz/a)/π` and
`b₊(w) = O(e^{(ε-2)w})` as `Re w → ∞`, equation (3.46). This is the equal-period case of
Proposition III.4, which `SICs.SpecialFunctions.HyperbolicGamma.Asymptotics` extends to
unequal periods by Ruijsenaars' comparison argument.

## The argument

For real `x`, differentiation under the integral in (3.1) with `a₊ = a₋ = a` gives
`g'(x) = ∫₀^∞ (cos 2xy/sinh²(ay) - 1/(a²y²)) dy`. On a bounded interval of `x`, the
derivative kernel is dominated by the integrable sum of the absolute value of the subtracted
kernel in (2.69) and a multiple of `y²/sinh²(ay)`. Splitting `cos 2xy = 1 - (1 - cos 2xy)`
and applying equations (2.66) and (2.69) of `SICs.Analysis.HyperbolicIntegrals` gives
`g'(s) = -(πs/a²) coth(πs/a)`; this is Ruijsenaars' derivation of (3.41). Writing
`coth t = 1 + e^{-t}/sinh t`, the substitution `t = πs/a`, and `c₊ = π²/12`, equation (3.45),
give `g(a,a;x) = -πx²/(2a²) - π/12 + b₊(πx/a)/π` for `x > 0`, where `b₊` is integrated along
the horizontal ray from `πx/a`. Both sides are holomorphic on the half-strip
`Re z > 0`, `|Im z| < a`: the left side by `differentiableOn_hyperbolicGammaLog`, the right
side because `sinh` has no zero with positive real part. The identity theorem extends the
formula to the half-strip. Finally `|t e^{-t}/sinh t| ≤ 4|t| e^{-2 Re t}` for `Re t ≥ 1/2`
bounds `b₊(w)` by `(1 + 2|w|) e^{-2 Re w}`, which is `O(e^{(ε-2) Re w})` uniformly for
bounded `Im w`; near the imaginary axis continuity bounds the remainder.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Real

namespace SIC

/-! ### Ruijsenaars' tail integral `b₊`

For `Re w > 0` the ray `w + [0, ∞)` avoids the zeros of `sinh`, and the integrand decays
like `e^{-2t}`. -/

/-- Ruijsenaars' tail `b₊(w) = ∫_w^∞ t e^{-t}/sinh t dt` of equation (3.44), integrated along
the horizontal ray `w + [0, ∞)`; Ruijsenaars (1997), equation (3.44), for `Re w > 0`. -/
noncomputable def hyperbolicGammaTail (w : ℂ) : ℂ :=
  ∫ s in Ioi (0 : ℝ), (w + s) * Complex.exp (-(w + s)) / Complex.sinh (w + s)

/-- The pointwise estimate used by `norm_hyperbolicGammaTail_le`. -/
private lemma norm_mul_exp_neg_div_sinh_le {u : ℂ} (hu : (1 : ℝ) / 2 ≤ u.re) :
    ‖u * Complex.exp (-u) / Complex.sinh u‖ ≤
      4 * ‖u‖ * Real.exp (-2 * u.re) := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hneg : Real.exp (-(1 : ℝ)) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num) he)
  have hd : 0 < 1 - Real.exp (-(1 : ℝ)) := by linarith
  have hc : 2 / (1 - Real.exp (-(1 : ℝ))) ≤ 4 :=
    (div_le_iff₀ hd).2 (by linarith)
  have hsm : Real.exp u.re ≤
      2 / (1 - Real.exp (-(1 : ℝ))) * Real.sinh u.re :=
    by simpa only [show (-(2 : ℝ)) * ((1 : ℝ) / 2) = -(1 : ℝ) by norm_num] using
      (exp_le_mul_sinh (by norm_num : (0 : ℝ) < 1 / 2) hu)
  have hspos : 0 ≤ Real.sinh u.re :=
    (Real.sinh_pos_iff.mpr (by linarith : 0 < u.re)).le
  have hden : Real.exp u.re / 4 ≤ ‖Complex.sinh u‖ := by
    apply le_trans (b := Real.sinh u.re)
    · nlinarith [hsm, mul_le_mul_of_nonneg_right hc hspos]
    · exact (le_abs_self _).trans (abs_sinh_re_le_norm_sinh u)
  have hdenpos : 0 < Real.exp u.re / 4 := by positivity
  have hnum : 0 ≤ ‖u‖ * Real.exp (-u.re) := by positivity
  calc
    ‖u * Complex.exp (-u) / Complex.sinh u‖ =
        ‖u‖ * Real.exp (-u.re) / ‖Complex.sinh u‖ := by
      rw [norm_div, norm_mul, Complex.norm_exp, Complex.neg_re]
    _ ≤ (‖u‖ * Real.exp (-u.re)) / (Real.exp u.re / 4) :=
      div_le_div₀ hnum le_rfl hdenpos hden
    _ = 4 * ‖u‖ * Real.exp (-2 * u.re) := by
      rw [show -2 * u.re = -u.re - u.re by ring, Real.exp_sub]
      field_simp

/-- A local estimate for the parametric integral in
`differentiableOn_hyperbolicGammaTail`. -/
private lemma norm_mul_exp_neg_div_sinh_le_of_re {u : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hu : δ ≤ u.re) :
    ‖u * Complex.exp (-u) / Complex.sinh u‖ ≤
      ‖u‖ * Real.exp (-u.re) / Real.sinh δ := by
  have hden : Real.sinh δ ≤ ‖Complex.sinh u‖ :=
    (Real.sinh_le_sinh.mpr hu).trans
      ((le_abs_self _).trans (abs_sinh_re_le_norm_sinh u))
  have hδs : 0 < Real.sinh δ := Real.sinh_pos_iff.mpr hδ
  calc
    ‖u * Complex.exp (-u) / Complex.sinh u‖ =
        ‖u‖ * Real.exp (-u.re) / ‖Complex.sinh u‖ := by
      rw [norm_div, norm_mul, Complex.norm_exp, Complex.neg_re]
    _ ≤ ‖u‖ * Real.exp (-u.re) / Real.sinh δ :=
      div_le_div₀ (by positivity) le_rfl hδs hden

/-- The pointwise shifted estimate used in `norm_hyperbolicGammaTail_le`. -/
private lemma norm_tail_shift_le {w : ℂ} (hw : (1 : ℝ) / 2 ≤ w.re)
    {s : ℝ} (hs : 0 ≤ s) :
    ‖(w + s) * Complex.exp (-(w + s)) / Complex.sinh (w + s)‖ ≤
      4 * Real.exp (-2 * w.re) * ((‖w‖ + s) * Real.exp (-2 * s)) := by
  have hu : (1 : ℝ) / 2 ≤ (w + (s : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hnorm : ‖w + (s : ℂ)‖ ≤ ‖w‖ + s := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs] using
      (norm_add_le w (s : ℂ))
  calc
    ‖(w + s) * Complex.exp (-(w + s)) / Complex.sinh (w + s)‖ ≤
        4 * ‖w + (s : ℂ)‖ * Real.exp (-2 * (w + (s : ℂ)).re) :=
      norm_mul_exp_neg_div_sinh_le hu
    _ = 4 * Real.exp (-2 * w.re) *
        (‖w + (s : ℂ)‖ * Real.exp (-2 * s)) := by
      rw [Complex.add_re, Complex.ofReal_re,
        show -2 * (w.re + s) = -2 * w.re + -2 * s by ring, Real.exp_add]
      ring
    _ ≤ _ := by gcongr

/-- The local closed-ball bound used by `differentiableOn_hyperbolicGammaTail`. -/
private lemma norm_tail_shift_local_le {z₀ z : ℂ} {r s : ℝ}
    (hr : 0 < r) (hcenter : z₀.re = 2 * r)
    (hz : z ∈ Metric.closedBall z₀ r) (hs : 0 ≤ s) :
    ‖(z + s) * Complex.exp (-(z + s)) / Complex.sinh (z + s)‖ ≤
      (‖z₀‖ + r + s) * Real.exp (-s) / Real.sinh r := by
  have hzre : r ≤ z.re := by
    have h := abs_re_sub_le_of_mem_closedBall hz
    have := neg_le_of_abs_le h
    linarith
  have huz : r ≤ (z + (s : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hznorm : ‖z‖ ≤ ‖z₀‖ + r := by
    have hd : ‖z - z₀‖ ≤ r := mem_closedBall_iff_norm.mp hz
    calc
      ‖z‖ = ‖(z - z₀) + z₀‖ := by congr 1; abel
      _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ ≤ ‖z₀‖ + r := by linarith
  have hunorm : ‖z + (s : ℂ)‖ ≤ ‖z₀‖ + r + s := by
    calc
      ‖z + (s : ℂ)‖ ≤ ‖z‖ + ‖(s : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖z₀‖ + r + s := by
        simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs] using
          (add_le_add_right hznorm s)
  have hexp : Real.exp (-(z + (s : ℂ)).re) ≤ Real.exp (-s) :=
    Real.exp_le_exp.mpr (by simp only [Complex.add_re, Complex.ofReal_re]; linarith)
  calc
    ‖(z + s) * Complex.exp (-(z + s)) / Complex.sinh (z + s)‖ ≤
        ‖z + (s : ℂ)‖ * Real.exp (-(z + (s : ℂ)).re) / Real.sinh r :=
      norm_mul_exp_neg_div_sinh_le_of_re hr huz
    _ ≤ _ := by gcongr

/-- The integrand is holomorphic in the parameter, as used by
`differentiableOn_hyperbolicGammaTail`. -/
private lemma differentiableAt_tailIntegrand {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : 0 < z.re) :
    DifferentiableAt ℂ
      (fun w : ℂ => (w + s) * Complex.exp (-(w + s)) / Complex.sinh (w + s)) z := by
  have hnon : Complex.sinh (z + (s : ℂ)) ≠ 0 := by
    intro h
    have hpos : 0 < Real.sinh (z + (s : ℂ)).re :=
      Real.sinh_pos_iff.mpr (by simpa using add_pos hz hs)
    have hbound := abs_sinh_re_le_norm_sinh (z + (s : ℂ))
    rw [h, norm_zero] at hbound
    linarith [le_abs_self (Real.sinh (z + (s : ℂ)).re)]
  fun_prop (disch := assumption)

/-- The tail `b₊` is holomorphic on the half-plane `Re w > 0`. -/
theorem differentiableOn_hyperbolicGammaTail :
    DifferentiableOn ℂ hyperbolicGammaTail {w : ℂ | 0 < w.re} := by
  change DifferentiableOn ℂ
    (fun w : ℂ => ∫ s in Ioi (0 : ℝ),
      (w + s) * Complex.exp (-(w + s)) / Complex.sinh (w + s))
    {w : ℂ | 0 < w.re}
  apply differentiableOn_integral_of_locally_bounded
  · intro z hz
    exact (by measurability : Measurable (fun s : ℝ =>
      (z + s) * Complex.exp (-(z + s)) / Complex.sinh (z + s))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro z hz
    exact differentiableAt_tailIntegrand hs hz
  · intro z₀ hz₀
    change 0 < z₀.re at hz₀
    let r := z₀.re / 2
    have hr : 0 < r := by dsimp [r]; linarith
    have hrU : Metric.closedBall z₀ r ⊆ {w : ℂ | 0 < w.re} := by
      intro z hz
      have h := abs_re_sub_le_of_mem_closedBall hz
      change 0 < z.re
      dsimp [r] at h
      linarith [neg_le_of_abs_le h]
    let A : ℝ := ‖z₀‖ + r
    let g : ℝ → ℝ := fun s => (A + s) * Real.exp (-s) / Real.sinh r
    refine ⟨r, hr, hrU, g, ?_, ?_⟩
    · have h := integrableOn_add_mul_exp_neg_mul A (b := 1) (by norm_num)
      simpa only [one_mul] using h.div_const (Real.sinh r)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      intro z hz
      exact norm_tail_shift_local_le hr (by dsimp [r]; ring) hz hs.le

/-- The bound `‖b₊(w)‖ ≤ (1 + 2‖w‖) e^{-2 Re w}` for `Re w ≥ 1/2`, from which
Ruijsenaars (1997), equation (3.46), reads off `b₊(w) = O(e^{(ε-2)w})`. -/
theorem norm_hyperbolicGammaTail_le {w : ℂ} (hw : 1 / 2 ≤ w.re) :
    ‖hyperbolicGammaTail w‖ ≤ (1 + 2 * ‖w‖) * Real.exp (-2 * w.re) := by
  let g : ℝ → ℝ := fun s =>
    4 * Real.exp (-2 * w.re) * ((‖w‖ + s) * Real.exp (-2 * s))
  have hform (s : ℝ) : Real.exp (-2 * s) = Real.exp (-(2 * s)) := by
    congr 1
    ring
  have hg : IntegrableOn g (Ioi 0) := by
    apply ((integrableOn_add_mul_exp_neg_mul ‖w‖ (b := 2) (by norm_num)).const_mul
      (4 * Real.exp (-2 * w.re))).congr
    filter_upwards with s
    simp only [g, hform]
  have hbound : ∀ᵐ (s : ℝ) ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(w + s) * Complex.exp (-(w + s)) / Complex.sinh (w + s)‖ ≤ g s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact norm_tail_shift_le hw hs.le
  have h := norm_integral_le_of_norm_le hg hbound
  change ‖hyperbolicGammaTail w‖ ≤ _ at h
  have hlin : (∫ s in Ioi (0 : ℝ), (‖w‖ + s) * Real.exp (-2 * s)) =
      ‖w‖ / 2 + 1 / 4 := by
    simpa only [hform, show (1 : ℝ) / 2 ^ 2 = 1 / 4 by norm_num] using
      integral_add_mul_exp_neg_mul ‖w‖ (b := 2) (by norm_num)
  calc
    ‖hyperbolicGammaTail w‖ ≤ ∫ s in Ioi (0 : ℝ), g s := h
    _ = (1 + 2 * ‖w‖) * Real.exp (-2 * w.re) := by
      rw [show (∫ s in Ioi (0 : ℝ), g s) =
        4 * Real.exp (-2 * w.re) *
          ∫ s in Ioi (0 : ℝ), (‖w‖ + s) * Real.exp (-2 * s) by
            exact integral_const_mul _ _, hlin]
      ring

/-! ### The closed form: equations (3.41) and (3.43)

Proved on the positive real axis by differentiation under the integral and (2.66), (2.69),
(3.45), then extended to the half-strip by the identity theorem. -/

/-- The real restriction of equation (3.1), used in `hyperbolicGammaLog_self_eq`. -/
private def equalPeriodRealKernel (a x y : ℝ) : ℝ :=
  (Real.sin (2 * y * x) / (2 * Real.sinh (a * y) ^ 2) - x / (a ^ 2 * y)) / y

/-- The derivative of `equalPeriodRealKernel` in its middle argument, used in
`hyperbolicGammaLog_self_eq`. -/
private def equalPeriodDerivativeKernel (a x y : ℝ) : ℝ :=
  Real.cos (2 * y * x) / Real.sinh (a * y) ^ 2 - 1 / (a ^ 2 * y ^ 2)

/-- Complex and real forms of the equal-period kernel agree; a helper for
`hyperbolicGammaLog_self_eq`. -/
private lemma equalPeriodRealKernel_ofReal (a x y : ℝ) :
    hyperbolicGammaLogIntegrand a a (x : ℂ) y =
      (equalPeriodRealKernel a x y : ℂ) := by
  simp [hyperbolicGammaLogIntegrand, equalPeriodRealKernel]
  ring

/-- Pointwise differentiation of the real kernel, used in
`hyperbolicGammaLog_self_eq`. -/
private lemma hasDerivAt_equalPeriodRealKernel {a x y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun s : ℝ => equalPeriodRealKernel a s y)
      (equalPeriodDerivativeKernel a x y) x := by
  have hmul : HasDerivAt (fun s : ℝ => 2 * y * s) (2 * y) x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul (2 * y)
  have hsin := (Real.hasDerivAt_sin (2 * y * x)).comp x hmul
  have h := ((hsin.div_const (2 * Real.sinh (a * y) ^ 2)).sub
    ((hasDerivAt_id x).div_const (a ^ 2 * y))).div_const y
  have heq : equalPeriodDerivativeKernel a x y =
      (Real.cos (2 * y * x) * (2 * y) / (2 * Real.sinh (a * y) ^ 2) -
        1 / (a ^ 2 * y)) / y := by
    dsimp [equalPeriodDerivativeKernel]
    field_simp [hy]
  rw [heq]
  simpa only [equalPeriodRealKernel, Function.comp_apply, id_eq, Pi.sub_apply] using h

/-- The derivative kernel's bound on a bounded real parameter set, used in
`hyperbolicGammaLog_self_eq`. -/
private lemma norm_equalPeriodDerivativeKernel_le {a M s y : ℝ} (ha : 0 < a)
    (hy : 0 < y) (hM : |s| ≤ M) :
    |equalPeriodDerivativeKernel a s y| ≤
      |(a ^ 2 / Real.sinh (a * y) ^ 2 - 1 / y ^ 2) / a ^ 2| +
        2 * M ^ 2 * (y ^ 2 / Real.sinh (a * y) ^ 2) := by
  have hsy : 0 < Real.sinh (a * y) := Real.sinh_pos_iff.mpr (mul_pos ha hy)
  have hdecomp : equalPeriodDerivativeKernel a s y =
      (a ^ 2 / Real.sinh (a * y) ^ 2 - 1 / y ^ 2) / a ^ 2 -
        (1 - Real.cos (2 * y * s)) / Real.sinh (a * y) ^ 2 := by
    dsimp [equalPeriodDerivativeKernel]
    field_simp [ha.ne', hy.ne', hsy.ne']
    ring
  have hc0 : 0 ≤ 1 - Real.cos (2 * y * s) := sub_nonneg.mpr (Real.cos_le_one _)
  have hM0 : 0 ≤ M := (abs_nonneg s).trans hM
  have hs2 : s ^ 2 ≤ M ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hM) (add_nonneg (abs_nonneg s) hM0), sq_abs s]
  have hterm : (1 - Real.cos (2 * y * s)) / Real.sinh (a * y) ^ 2 ≤
      2 * M ^ 2 * (y ^ 2 / Real.sinh (a * y) ^ 2) :=
    (one_sub_cos_div_sinh_sq_le a y s).trans (by gcongr)
  calc
    |equalPeriodDerivativeKernel a s y| =
        |(a ^ 2 / Real.sinh (a * y) ^ 2 - 1 / y ^ 2) / a ^ 2 -
          (1 - Real.cos (2 * y * s)) / Real.sinh (a * y) ^ 2| := by rw [hdecomp]
    _ ≤ |(a ^ 2 / Real.sinh (a * y) ^ 2 - 1 / y ^ 2) / a ^ 2| +
          |(1 - Real.cos (2 * y * s)) / Real.sinh (a * y) ^ 2| := abs_sub _ _
    _ = |(a ^ 2 / Real.sinh (a * y) ^ 2 - 1 / y ^ 2) / a ^ 2| +
          (1 - Real.cos (2 * y * s)) / Real.sinh (a * y) ^ 2 := by
      rw [abs_of_nonneg (div_nonneg hc0 (sq_nonneg _))]
    _ ≤ |(a ^ 2 / Real.sinh (a * y) ^ 2 - 1 / y ^ 2) / a ^ 2| +
          2 * M ^ 2 * (y ^ 2 / Real.sinh (a * y) ^ 2) := add_le_add le_rfl hterm

/-- A common integrable bound for the derivative kernel near a real parameter, used in
`hyperbolicGammaLog_self_eq`. -/
private def equalPeriodDerivativeMajorant (a M y : ℝ) : ℝ :=
  |(a ^ 2 / Real.sinh (a * y) ^ 2 - 1 / y ^ 2) / a ^ 2| +
    2 * M ^ 2 * (y ^ 2 / Real.sinh (a * y) ^ 2)

/-- Integrability of `equalPeriodDerivativeMajorant`, used in
`hyperbolicGammaLog_self_eq`. -/
private lemma integrableOn_equalPeriodDerivativeMajorant {a M : ℝ} (ha : 0 < a) :
    IntegrableOn (equalPeriodDerivativeMajorant a M) (Ioi 0) := by
  have hbase : IntegrableOn (fun y : ℝ =>
      |(a ^ 2 / Real.sinh (a * y) ^ 2 - 1 / y ^ 2) / a ^ 2|) (Ioi 0) := by
    have h := (integrableOn_sq_div_sinh_sq_sub_inv_sq ha).div_const (a ^ 2)
    exact h.norm
  have htail : IntegrableOn (fun y : ℝ =>
      2 * M ^ 2 * (y ^ 2 / Real.sinh (a * y) ^ 2)) (Ioi 0) :=
    (integrableOn_sq_div_sinh_sq ha).const_mul _
  exact hbase.add htail

/-- The local dominated derivative bound used by
`hasDerivAt_equalPeriodRealIntegral`. -/
private lemma equalPeriodDerivativeKernel_bound_ae {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), ∀ s ∈ Metric.ball x 1,
      ‖equalPeriodDerivativeKernel a s y‖ ≤
        equalPeriodDerivativeMajorant a (|x| + 1) y := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  intro s hs
  have hsx : |s - x| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hs
  have hsM : |s| ≤ |x| + 1 := by
    have h := abs_add_le (s - x) x
    rw [sub_add_cancel] at h
    linarith
  change |equalPeriodDerivativeKernel a s y| ≤
    equalPeriodDerivativeMajorant a (|x| + 1) y
  exact norm_equalPeriodDerivativeKernel_le ha hy hsM

/-- Integrability of the real kernel used by `hasDerivAt_equalPeriodRealIntegral`. -/
private lemma integrableOn_equalPeriodRealKernel {a : ℝ} (ha : 0 < a) (x : ℝ) :
    IntegrableOn (equalPeriodRealKernel a x) (Ioi 0) := by
  apply (IntegrableOn.iff_ofReal (𝕜 := ℂ)).2
  have h := integrableOn_hyperbolicGammaLogIntegrand ha ha
    (z := (x : ℂ)) (by simp [ha])
  exact h.congr (Filter.Eventually.of_forall fun y =>
    equalPeriodRealKernel_ofReal a x y)

/-- Differentiation under equation (3.1) on the real axis, used in
`hyperbolicGammaLog_self_eq`. -/
private lemma hasDerivAt_equalPeriodRealIntegral {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt
      (fun s : ℝ => ∫ y in Ioi (0 : ℝ), equalPeriodRealKernel a s y)
      (∫ y in Ioi (0 : ℝ), equalPeriodDerivativeKernel a x y) x := by
  let F : ℝ → ℝ → ℝ := fun s y => equalPeriodRealKernel a s y
  let F' : ℝ → ℝ → ℝ := fun s y => equalPeriodDerivativeKernel a s y
  let M : ℝ := |x| + 1
  let B : ℝ → ℝ := equalPeriodDerivativeMajorant a M
  have hmeas : ∀ᶠ s in 𝓝 x,
      AEStronglyMeasurable (F s) (volume.restrict (Ioi (0 : ℝ))) :=
    Filter.Eventually.of_forall fun s =>
      (by dsimp [F, equalPeriodRealKernel]; measurability :
        Measurable (F s)).aestronglyMeasurable
  have hFint : IntegrableOn (F x) (Ioi 0) :=
    integrableOn_equalPeriodRealKernel ha x
  have hF'meas : AEStronglyMeasurable (F' x)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (by dsimp [F', equalPeriodDerivativeKernel]; measurability :
      Measurable (F' x)).aestronglyMeasurable
  have hbound : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ s ∈ Metric.ball x 1, ‖F' s y‖ ≤ B y :=
    equalPeriodDerivativeKernel_bound_ae ha x
  have hdiff : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ s ∈ Metric.ball x 1, HasDerivAt (F · y) (F' s y) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    intro s hs
    exact hasDerivAt_equalPeriodRealKernel hy.ne'
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := B) (s := Metric.ball x 1)
    (Metric.ball_mem_nhds x (by norm_num)) hmeas hFint hF'meas hbound
    (integrableOn_equalPeriodDerivativeMajorant ha) hdiff).2
  exact h

/-- Translation of a half-line integral, used to identify the real tail in
`hyperbolicGammaLog_self_eq`. -/
private lemma integral_add_left_Ioi (f : ℝ → ℝ) (w : ℝ) :
    ∫ s in Ioi (0 : ℝ), f (w + s) = ∫ t in Ioi w, f t := by
  have h := integral_add_right_eq_self (μ := volume)
    ((Ioi (0 : ℝ)).indicator (fun s => f (w + s))) (-w)
  rw [integral_indicator measurableSet_Ioi] at h
  have heq : (fun t : ℝ => (Ioi (0 : ℝ)).indicator
      (fun s => f (w + s)) (t - w)) = (Ioi w).indicator f := by
    funext t
    simp only [indicator_apply, mem_Ioi, sub_pos]
    split_ifs
    · congr 1; ring
    · rfl
  have hh : ∫ t : ℝ, (Ioi (0 : ℝ)).indicator (fun s => f (w + s)) (t - w) =
      ∫ s in Ioi (0 : ℝ), f (w + s) := by simpa only [sub_eq_add_neg] using h
  rw [heq, integral_indicator measurableSet_Ioi] at hh
  exact hh.symm

/-- For real `w`, `b₊(w)` is the real integral from `w` to infinity; a helper for
`hyperbolicGammaLog_self_eq`. -/
private lemma hyperbolicGammaTail_ofReal (w : ℝ) :
    hyperbolicGammaTail (w : ℂ) =
      ((∫ t in Ioi w, t * Real.exp (-t) / Real.sinh t : ℝ) : ℂ) := by
  have hcast : hyperbolicGammaTail (w : ℂ) =
      ((∫ s in Ioi (0 : ℝ),
        (w + s) * Real.exp (-(w + s)) / Real.sinh (w + s) : ℝ) : ℂ) := by
    unfold hyperbolicGammaTail
    have heq (s : ℝ) :
        ((w : ℂ) + s) * Complex.exp (-((w : ℂ) + s)) /
            Complex.sinh ((w : ℂ) + s) =
          (((w + s) * Real.exp (-(w + s)) / Real.sinh (w + s) : ℝ) : ℂ) := by
      norm_cast
    simp_rw [heq]
    exact integral_ofReal
  rw [hcast]
  exact congrArg (fun r : ℝ => (r : ℂ))
    (integral_add_left_Ioi (fun t => t * Real.exp (-t) / Real.sinh t) w)

/-- The constant `c₊ = π²/12` from equation (3.45) fixes the value of the real tail;
a helper for `hyperbolicGammaLog_self_eq`. -/
private lemma hyperbolicGammaTail_real_eq_const_sub_integral {w : ℝ} (hw : 0 ≤ w) :
    (∫ t in Ioi w, t * Real.exp (-t) / Real.sinh t) =
      Real.pi ^ 2 / 12 - ∫ t in (0 : ℝ)..w, t * Real.exp (-t) / Real.sinh t := by
  have h0 := integrableOn_mul_exp_neg_div_sinh
  have hwint := h0.mono_set (Ioi_subset_Ioi hw)
  have h := intervalIntegral.integral_interval_add_Ioi h0 hwint
  rw [integral_mul_exp_neg_div_sinh] at h
  linarith

/-- The integrable decomposition used by `integral_equalPeriodDerivativeKernel`. -/
private lemma integral_equalPeriodDerivativeKernel_decomp {a : ℝ} (ha : 0 < a)
    (x : ℝ) :
    (∫ y in Ioi (0 : ℝ), equalPeriodDerivativeKernel a x y) =
      (∫ y in Ioi (0 : ℝ),
        (a ^ 2 / Real.sinh (a * y) ^ 2 - 1 / y ^ 2) / a ^ 2) -
      (∫ y in Ioi (0 : ℝ),
        (1 - Real.cos (2 * y * x)) / Real.sinh (a * y) ^ 2) := by
  have hbase := (integrableOn_sq_div_sinh_sq_sub_inv_sq ha).div_const (a ^ 2)
  have hcos := integrableOn_one_sub_cos_div_sinh_sq ha x
  calc
    (∫ y in Ioi (0 : ℝ), equalPeriodDerivativeKernel a x y) =
        ∫ y in Ioi (0 : ℝ),
          (a ^ 2 / Real.sinh (a * y) ^ 2 - 1 / y ^ 2) / a ^ 2 -
            (1 - Real.cos (2 * y * x)) / Real.sinh (a * y) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      simp only [mem_Ioi] at hy
      have hsy : Real.sinh (a * y) ≠ 0 :=
        (Real.sinh_pos_iff.mpr (mul_pos ha hy)).ne'
      dsimp [equalPeriodDerivativeKernel]
      field_simp [ha.ne', hy.ne', hsy]
      ring
    _ = _ := integral_sub hbase hcos

/-- Ruijsenaars' equations (2.66) and (2.69) evaluate the real derivative of
`g(a,a;·)`; a helper for `hyperbolicGammaLog_self_eq`. -/
private lemma integral_equalPeriodDerivativeKernel {a : ℝ} (ha : 0 < a)
    {x : ℝ} (hx : x ≠ 0) :
    ∫ y in Ioi (0 : ℝ), equalPeriodDerivativeKernel a x y =
      -π * x / a ^ 2 *
        (Real.cosh (π * x / a) / Real.sinh (π * x / a)) := by
  let J : ℝ := ∫ y in Ioi (0 : ℝ),
    (1 - Real.cos (2 * y * x)) / Real.sinh (a * y) ^ 2
  have h66 := mul_coth_eq_add_integral_one_sub_cos_div_sinh_sq ha hx
  have h69 := integral_sq_div_sinh_sq_sub_inv_sq ha
  rw [integral_equalPeriodDerivativeKernel_decomp ha x, integral_div, h69]
  change -a / a ^ 2 - J = _
  calc
    -a / a ^ 2 - J = -(a + a ^ 2 * J) / a ^ 2 := by
      field_simp [ha.ne']
      ring
    _ = -(π * x * (Real.cosh (π * x / a) / Real.sinh (π * x / a))) / a ^ 2 := by
      rw [h66]
    _ = _ := by ring

/-- The finite-integral form of Ruijsenaars' equation (3.41), used in
`hyperbolicGammaLog_self_eq`. -/
private def equalPeriodCumulative (a x : ℝ) : ℝ :=
  -π * x ^ 2 / (2 * a ^ 2) -
    (1 / π) * ∫ t in (0 : ℝ)..(π * x / a),
      t * Real.exp (-t) / Real.sinh t

/-- Derivative of the finite-integral side of equation (3.41) on `x > 0`, used in
`hyperbolicGammaLog_self_eq`. -/
private lemma hasDerivAt_equalPeriodCumulative {a x : ℝ} (ha : 0 < a)
    (hx : 0 < x) :
    HasDerivAt (equalPeriodCumulative a)
      (-π * x / a ^ 2 -
        (1 / π) * ((π * x / a) * Real.exp (-(π * x / a)) /
          Real.sinh (π * x / a) * (π / a))) x := by
  let f : ℝ → ℝ := fun t => t * Real.exp (-t) / Real.sinh t
  let b : ℝ := π * x / a
  have hb : 0 < b := by dsimp [b]; positivity
  have hInt : IntervalIntegrable f volume 0 b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr
    exact integrableOn_mul_exp_neg_div_sinh.mono_set
      (Ioc_subset_Ioi_self)
  have hcont : ContinuousAt f b := by
    have hnon : Real.sinh b ≠ 0 := (Real.sinh_pos_iff.mpr hb).ne'
    dsimp [f]
    fun_prop (disch := assumption)
  have hFTC := intervalIntegral.integral_hasDerivAt_right hInt
    ((by measurability : Measurable f).stronglyMeasurable.stronglyMeasurableAtFilter)
    hcont
  have hmul : HasDerivAt (fun s : ℝ => π * s / a) (π / a) x := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul π).div_const a
  have hI := hFTC.comp x hmul
  have hpoly : HasDerivAt (fun s : ℝ => -π * s ^ 2 / (2 * a ^ 2))
      (-π * x / a ^ 2) x := by
    convert (((hasDerivAt_id x).pow 2).const_mul (-π / (2 * a ^ 2))) using 1
    · funext s
      simp only [Pi.pow_apply, id_eq]
      ring
    · simp only [id_eq]
      ring
  have h := hpoly.sub (hI.const_mul (1 / π))
  convert h using 1
  funext s
  dsimp [equalPeriodCumulative]

/-- The real logarithm is the real integral of `equalPeriodRealKernel`, used in
`hyperbolicGammaLog_self_eq`. -/
private lemma hyperbolicGammaLog_ofReal_eq_realIntegral (a x : ℝ) :
    hyperbolicGammaLog a a (x : ℂ) =
      ((∫ y in Ioi (0 : ℝ), equalPeriodRealKernel a x y : ℝ) : ℂ) := by
  unfold hyperbolicGammaLog
  simp_rw [equalPeriodRealKernel_ofReal]
  exact integral_ofReal

/-- The two real derivatives in equation (3.41) agree for `x > 0`; a helper for
`hyperbolicGammaLog_self_eq`. -/
private lemma equalPeriod_derivatives_eq {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    -π * x / a ^ 2 * (Real.cosh (π * x / a) / Real.sinh (π * x / a)) =
      -π * x / a ^ 2 - (1 / π) *
        ((π * x / a) * Real.exp (-(π * x / a)) /
          Real.sinh (π * x / a) * (π / a)) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsin : Real.sinh (π * x / a) ≠ 0 := by
    apply (Real.sinh_pos_iff.mpr ?_).ne'
    positivity
  have hc := Real.cosh_sub_sinh (π * x / a)
  field_simp [ha.ne', hpi, hsin]
  nlinarith [hc]

/-- The difference between the real logarithm and the finite-integral expression is
constant on `(0, ∞)`; a helper for `hyperbolicGammaLog_self_eq`. -/
private lemma equalPeriod_real_difference_const {a : ℝ} (ha : 0 < a)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t in Ioi (0 : ℝ), equalPeriodRealKernel a x t) - equalPeriodCumulative a x =
      (∫ t in Ioi (0 : ℝ), equalPeriodRealKernel a y t) - equalPeriodCumulative a y := by
  let G : ℝ → ℝ := fun s => ∫ t in Ioi (0 : ℝ), equalPeriodRealKernel a s t
  let H : ℝ → ℝ := equalPeriodCumulative a
  have hderiv (s : ℝ) (hs : 0 < s) : HasDerivAt (fun t => G t - H t) 0 s := by
    have hG := hasDerivAt_equalPeriodRealIntegral ha s
    rw [integral_equalPeriodDerivativeKernel ha hs.ne'] at hG
    have hH := hasDerivAt_equalPeriodCumulative ha hs
    have heq := equalPeriod_derivatives_eq ha hs
    convert hG.sub hH using 1
    rw [heq]
    ring
  have hdiff : DifferentiableOn ℝ (fun s => G s - H s) (Ioi (0 : ℝ)) := by
    intro s hs
    exact (hderiv s hs).differentiableAt.differentiableWithinAt
  have hzero : EqOn (deriv (fun s => G s - H s)) 0 (Ioi (0 : ℝ)) := by
    intro s hs
    exact (hderiv s hs).deriv
  exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hzero hx hy

/-- The finite-integral side of equation (3.41) is continuous from the right at zero;
a helper for `hyperbolicGammaLog_self_eq`. -/
private lemma continuousWithinAt_equalPeriodCumulative_zero {a : ℝ} (ha : 0 < a) :
    ContinuousWithinAt (equalPeriodCumulative a) (Icc (0 : ℝ) 1) 0 := by
  let f : ℝ → ℝ := fun t => t * Real.exp (-t) / Real.sinh t
  let b : ℝ := π / a
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hInt : IntegrableOn f (Icc 0 b) := by
    apply (integrableOn_Icc_iff_integrableOn_Ioc).2
    exact integrableOn_mul_exp_neg_div_sinh.mono_set Ioc_subset_Ioi_self
  have hPrim : ContinuousOn (fun u => ∫ t in (0 : ℝ)..u, f t) (Icc 0 b) := by
    have hInt' : IntegrableOn f (uIcc (0 : ℝ) b) := by
      simpa only [uIcc_of_le hb] using hInt
    have h := intervalIntegral.continuousOn_primitive_interval hInt'
    simpa only [uIcc_of_le hb] using h
  have hB : ContinuousOn (fun s : ℝ => π * s / a) (Icc (0 : ℝ) 1) := by fun_prop
  have hmap : MapsTo (fun s : ℝ => π * s / a) (Icc (0 : ℝ) 1) (Icc 0 b) := by
    intro s hs
    rcases hs with ⟨hs0, hs1⟩
    constructor
    · positivity
    · dsimp [b]
      exact div_le_div_of_nonneg_right
        (by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hs1 Real.pi_pos.le) ha.le
  have hH : ContinuousOn (equalPeriodCumulative a) (Icc (0 : ℝ) 1) := by
    have hpoly : ContinuousOn (fun s : ℝ => -π * s ^ 2 / (2 * a ^ 2))
        (Icc (0 : ℝ) 1) := by fun_prop
    exact hpoly.sub ((hPrim.comp hB hmap).const_mul (1 / π))
  exact hH.continuousWithinAt (by simp)

/-- The common derivative has zero integration constant, fixed by `g(a,a;0) = 0`;
a helper for `hyperbolicGammaLog_self_eq`. -/
private lemma equalPeriod_real_eq_cumulative {a x : ℝ} (ha : 0 < a)
    (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), equalPeriodRealKernel a x t) =
      equalPeriodCumulative a x := by
  let G : ℝ → ℝ := fun s => ∫ t in Ioi (0 : ℝ), equalPeriodRealKernel a s t
  let H : ℝ → ℝ := equalPeriodCumulative a
  have hG0 : G 0 = 0 := by simp [G, equalPeriodRealKernel]
  have hH0 : H 0 = 0 := by simp [H, equalPeriodCumulative]
  have hmem : Icc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    apply eventually_nhdsWithin_iff.mpr
    filter_upwards [isOpen_Iio.mem_nhds (show (0 : ℝ) ∈ Iio 1 by norm_num)]
      with s hs1 hs0
    exact ⟨hs0.le, hs1.le⟩
  have hGtend : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (G 0)) :=
    (hasDerivAt_equalPeriodRealIntegral ha 0).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hHtend : Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 (H 0)) :=
    (continuousWithinAt_equalPeriodCumulative_zero ha).tendsto.mono_left
      (nhdsWithin_le_of_mem hmem)
  have hDtend : Tendsto (fun s => G s - H s) (𝓝[>] (0 : ℝ))
      (𝓝 (G 0 - H 0)) := hGtend.sub hHtend
  have hevent : (fun s => G s - H s) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ => G 1 - H 1) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact equalPeriod_real_difference_const ha hs (by norm_num)
  have hCtend : Tendsto (fun s => G s - H s) (𝓝[>] (0 : ℝ))
      (𝓝 (G 1 - H 1)) := tendsto_const_nhds.congr' hevent.symm
  have hval : G 0 - H 0 = G 1 - H 1 := tendsto_nhds_unique hDtend hCtend
  have hconst := equalPeriod_real_difference_const ha hx (by norm_num : (0 : ℝ) < 1)
  rw [hG0, hH0] at hval
  linarith

/-- Ruijsenaars' equations (3.41), (3.43), and (3.45) on the positive real axis;
a helper for `hyperbolicGammaLog_self_eq`. -/
private lemma equalPeriod_real_identity {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    (∫ y in Ioi (0 : ℝ), equalPeriodRealKernel a x y) =
      -π * x ^ 2 / (2 * a ^ 2) - π / 12 +
        (∫ t in Ioi (π * x / a), t * Real.exp (-t) / Real.sinh t) / π := by
  have hb : 0 ≤ π * x / a := by positivity
  have htail := hyperbolicGammaTail_real_eq_const_sub_integral hb
  rw [equalPeriod_real_eq_cumulative ha hx, equalPeriodCumulative, htail]
  field_simp [Real.pi_ne_zero]
  ring

/-- The real-axis form of `hyperbolicGammaLog_self_eq`. -/
private lemma hyperbolicGammaLog_self_eq_ofReal {a x : ℝ} (ha : 0 < a)
    (hx : 0 < x) :
    hyperbolicGammaLog a a (x : ℂ) =
      -π * (x : ℂ) ^ 2 / (2 * a ^ 2) - π / 12 +
        hyperbolicGammaTail (π * (x : ℂ) / a) / π := by
  have hreal := equalPeriod_real_identity ha hx
  have htail := hyperbolicGammaTail_ofReal (π * x / a)
  have harg : π * (x : ℂ) / a = ((π * x / a : ℝ) : ℂ) := by norm_cast
  rw [hyperbolicGammaLog_ofReal_eq_realIntegral, harg, htail]
  norm_cast

/-- The half-strip where `hyperbolicGammaLog_self_eq` is proved by analytic continuation. -/
private def equalPeriodHalfStrip (a : ℝ) : Set ℂ :=
  ({w : ℂ | 0 < w.re} ∩ {w : ℂ | -a < w.im}) ∩ {w : ℂ | w.im < a}

/-- Openness of the domain in `hyperbolicGammaLog_self_eq`. -/
private lemma isOpen_equalPeriodHalfStrip (a : ℝ) :
    IsOpen (equalPeriodHalfStrip a) := by
  dsimp [equalPeriodHalfStrip]
  exact ((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)).inter
    (isOpen_lt Complex.continuous_im continuous_const)

/-- Convexity of the domain in `hyperbolicGammaLog_self_eq`. -/
private lemma convex_equalPeriodHalfStrip (a : ℝ) :
    Convex ℝ (equalPeriodHalfStrip a) := by
  dsimp [equalPeriodHalfStrip]
  exact ((convex_halfSpace_re_gt 0).inter
    (convex_halfSpace_im_gt (-a))).inter (convex_halfSpace_im_lt a)

/-- Inclusion in the original strip, used by `hyperbolicGammaLog_self_eq`. -/
private lemma equalPeriodHalfStrip_subset_strip (a : ℝ) :
    equalPeriodHalfStrip a ⊆ {w : ℂ | |w.im| < (a + a) / 2} := by
  intro w hw
  rcases hw with ⟨⟨hwr, hwl⟩, hwu⟩
  change |w.im| < (a + a) / 2
  have him : |w.im| < a := abs_lt.mpr ⟨hwl, hwu⟩
  linarith

/-- Holomorphy of the closed form used in `hyperbolicGammaLog_self_eq`. -/
private lemma differentiableOn_equalPeriodClosedForm {a : ℝ} (ha : 0 < a) :
    DifferentiableOn ℂ
      (fun w : ℂ => -π * w ^ 2 / (2 * a ^ 2) - π / 12 +
        hyperbolicGammaTail (π * w / a) / π) (equalPeriodHalfStrip a) := by
  have hlin : DifferentiableOn ℂ (fun w : ℂ => π * w / a)
      (equalPeriodHalfStrip a) := by fun_prop
  have hmaps : MapsTo (fun w : ℂ => π * w / a)
      (equalPeriodHalfStrip a) {w : ℂ | 0 < w.re} := by
    intro w hw
    change 0 < (π * w / a).re
    have hre : (π * w / a).re = Real.pi * w.re / a := by simp
    rw [hre]
    exact div_pos (mul_pos Real.pi_pos hw.1.1) ha
  have htail : DifferentiableOn ℂ
      (fun w : ℂ => hyperbolicGammaTail (π * w / a))
      (equalPeriodHalfStrip a) := by
    simpa only [Function.comp_def] using
      differentiableOn_hyperbolicGammaTail.comp hlin hmaps
  have hpoly : DifferentiableOn ℂ
      (fun w : ℂ => -π * w ^ 2 / (2 * a ^ 2) - π / 12)
      (equalPeriodHalfStrip a) := by fun_prop
  exact hpoly.add (htail.div_const π)

/-- `g(a,a;z) = -πz²/(2a²) - π/12 + b₊(πz/a)/π` for `a > 0`, `Re z > 0`, `|Im z| < a`:
Ruijsenaars (1997), equation (3.41), `g(a,a;z) = -(1/π) b(πz/a)`, combined with
equation (3.43), `b(w) = w²/2 + c₊ - b₊(w)`, and `c₊ = π²/12`, equation (3.45). -/
theorem hyperbolicGammaLog_self_eq {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.re)
    (hzim : |z.im| < a) :
    hyperbolicGammaLog a a z =
      -π * z ^ 2 / (2 * a ^ 2) - π / 12 + hyperbolicGammaTail (π * z / a) / π := by
  let U : Set ℂ := equalPeriodHalfStrip a
  have hUopen : IsOpen U := isOpen_equalPeriodHalfStrip a
  have hUconvex : Convex ℝ U := convex_equalPeriodHalfStrip a
  have hUstrip : U ⊆ {w : ℂ | |w.im| < (a + a) / 2} :=
    equalPeriodHalfStrip_subset_strip a
  have hF : DifferentiableOn ℂ (hyperbolicGammaLog a a) U :=
    (differentiableOn_hyperbolicGammaLog ha ha).mono hUstrip
  have hR : DifferentiableOn ℂ
      (fun w : ℂ => -π * w ^ 2 / (2 * a ^ 2) - π / 12 +
        hyperbolicGammaTail (π * w / a) / π) U :=
    differentiableOn_equalPeriodClosedForm ha
  have hreal : ∀ x : ℝ, (x : ℂ) ∈ U →
      hyperbolicGammaLog a a x =
        -π * (x : ℂ) ^ 2 / (2 * a ^ 2) - π / 12 +
          hyperbolicGammaTail (π * x / a) / π := by
    intro x hx
    exact hyperbolicGammaLog_self_eq_ofReal ha (by simpa [U] using hx.1.1)
  have hpoint : (z : ℂ) ∈ U := by
    dsimp [U, equalPeriodHalfStrip]
    exact ⟨⟨hz, (abs_lt.mp hzim).1⟩,
      (abs_lt.mp hzim).2⟩
  have hseed : ((1 : ℝ) : ℂ) ∈ U := by
    dsimp [U, equalPeriodHalfStrip]
    simp [ha]
  exact (eqOn_of_differentiableOn_of_eqOn_real hUopen hUconvex.isPreconnected
    hF hR hseed hreal) hpoint

/-! ### The equal-period asymptotics

Ruijsenaars (1997), Proposition III.4, equation (3.49), in the case `a₊ = a₋ = a`, is
immediate from (3.41) and (3.46). -/

/-- Continuity of the remainder on the rectangle used by
`norm_hyperbolicGammaLog_self_add_le_small`. -/
private lemma continuousOn_equalPeriodRemainder_rectangle {a c : ℝ}
    (ha : 0 < a) (hc : c < a) :
    ContinuousOn
      (fun z : ℂ => hyperbolicGammaLog a a z + π * z ^ 2 / (2 * a ^ 2) + π / 12)
      (Icc (0 : ℝ) (a / (2 * Real.pi)) ×ℂ Icc (-c) c) := by
  have hsub : (Icc (0 : ℝ) (a / (2 * Real.pi)) ×ℂ Icc (-c) c) ⊆
      {z : ℂ | |z.im| < (a + a) / 2} := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    change |z.im| < (a + a) / 2
    have him : |z.im| ≤ c := abs_le.mpr hz.2
    linarith
  have hg : ContinuousOn (hyperbolicGammaLog a a)
      (Icc (0 : ℝ) (a / (2 * Real.pi)) ×ℂ Icc (-c) c) :=
    (differentiableOn_hyperbolicGammaLog ha ha).continuousOn.mono hsub
  exact (hg.add (by fun_prop)).add (by fun_prop)

/-- The compact-rectangle bound used in `norm_hyperbolicGammaLog_self_add_le`. -/
private lemma norm_hyperbolicGammaLog_self_add_le_small {a ε c : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hc : c < a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, 0 ≤ z.re → z.re ≤ a / (2 * Real.pi) →
      |z.im| ≤ c →
      ‖hyperbolicGammaLog a a z + π * z ^ 2 / (2 * a ^ 2) + π / 12‖ ≤
        M * Real.exp ((ε - 2 * Real.pi / a) * z.re) := by
  let R := a / (2 * Real.pi)
  let S : Set ℂ := Icc (0 : ℝ) R ×ℂ Icc (-c) c
  have hcompact : IsCompact S := IsCompact.reProdIm isCompact_Icc isCompact_Icc
  have hcont : ContinuousOn
      (fun z : ℂ => hyperbolicGammaLog a a z + π * z ^ 2 / (2 * a ^ 2) + π / 12)
      S := continuousOn_equalPeriodRemainder_rectangle ha hc
  obtain ⟨M₀, hM₀⟩ := hcompact.exists_bound_of_continuousOn hcont
  let M : ℝ := max M₀ 0 * Real.exp 1
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro z hz hzR hzim
  have hzS : z ∈ S := by
    rw [Complex.mem_reProdIm]
    exact ⟨⟨hz, hzR⟩, abs_le.mp hzim⟩
  have hbound := hM₀ z hzS
  have hKR : (2 * Real.pi / a) * R = 1 := by dsimp [R]; field_simp
  have he : 1 ≤ Real.exp (1 + (ε - 2 * Real.pi / a) * z.re) := by
    apply Real.one_le_exp
    have hKpos : 0 ≤ 2 * Real.pi / a := by positivity
    have hprod := mul_le_mul_of_nonneg_left hzR hKpos
    nlinarith [mul_nonneg hε.le hz]
  calc
    ‖hyperbolicGammaLog a a z + π * z ^ 2 / (2 * a ^ 2) + π / 12‖ ≤ M₀ := hbound
    _ ≤ max M₀ 0 := le_max_left _ _
    _ ≤ max M₀ 0 * Real.exp (1 + (ε - 2 * Real.pi / a) * z.re) :=
      le_mul_of_one_le_right (le_max_right _ _) he
    _ = M * Real.exp ((ε - 2 * Real.pi / a) * z.re) := by
      dsimp [M]
      rw [Real.exp_add]
      ring

/-- The direct tail bound on the remainder, used by
`norm_hyperbolicGammaLog_self_add_le_large`. -/
private lemma norm_equalPeriodRemainder_le_tail {a c : ℝ}
    (ha : 0 < a) (hc : c < a) {z : ℂ}
    (hz : a / (2 * Real.pi) ≤ z.re) (hzim : |z.im| ≤ c) :
    ‖hyperbolicGammaLog a a z + π * z ^ 2 / (2 * a ^ 2) + π / 12‖ ≤
      ((1 + (2 * Real.pi / a) * ‖z‖) / Real.pi) *
        Real.exp (-(2 * Real.pi / a) * z.re) := by
  let w : ℂ := π * z / a
  have hR : 0 < a / (2 * Real.pi) := by positivity
  have hzpos : 0 < z.re := hR.trans_le hz
  have him : |z.im| < a := hzim.trans_lt hc
  have heq := hyperbolicGammaLog_self_eq ha hzpos him
  have hF : hyperbolicGammaLog a a z + π * z ^ 2 / (2 * a ^ 2) + π / 12 =
      hyperbolicGammaTail w / π := by
    rw [heq]
    dsimp [w]
    ring
  have hwre : w.re = Real.pi * z.re / a := by simp [w]
  have hwnorm : ‖w‖ = Real.pi * ‖z‖ / a := by
    simp [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hhalf : (1 : ℝ) / 2 ≤ w.re := by
    rw [hwre]
    have hconst : (Real.pi / a) * (a / (2 * Real.pi)) = 1 / 2 := by field_simp
    calc
      (1 : ℝ) / 2 = (Real.pi / a) * (a / (2 * Real.pi)) := hconst.symm
      _ ≤ (Real.pi / a) * z.re := mul_le_mul_of_nonneg_left hz (by positivity)
      _ = Real.pi * z.re / a := by ring
  have htail := norm_hyperbolicGammaTail_le hhalf
  rw [hF, norm_div]
  have h := div_le_div_of_nonneg_right htail Real.pi_pos.le
  rw [show ‖(π : ℂ)‖ = Real.pi by simp] at *
  rw [hwre, hwnorm] at h
  convert h using 1
  ring_nf

/-- A linear coefficient is absorbed by a positive exponential, used by
`norm_hyperbolicGammaLog_self_add_le_large`. -/
private lemma equalPeriod_linear_coefficient_le_exp {a ε c : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hc0 : 0 ≤ c)
    {z : ℂ} (hz : 0 ≤ z.re) (hzim : |z.im| ≤ c) :
    1 + (2 * Real.pi / a) * ‖z‖ ≤
      (1 + (2 * Real.pi / a) * c + (2 * Real.pi / a) / ε) *
        Real.exp (ε * z.re) := by
  let K : ℝ := 2 * Real.pi / a
  have hnorm : ‖z‖ ≤ z.re + c := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_nonneg hz] at h
    linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have he : 1 ≤ Real.exp (ε * z.re) := Real.one_le_exp (mul_nonneg hε.le hz)
  have hlin : z.re ≤ Real.exp (ε * z.re) / ε := by
    apply (le_div_iff₀ hε).mpr
    nlinarith [Real.add_one_le_exp (ε * z.re)]
  have hcst : 0 ≤ 1 + K * c := by positivity
  calc
    1 + K * ‖z‖ ≤ (1 + K * c) + K * z.re := by
      nlinarith [mul_le_mul_of_nonneg_left hnorm hK]
    _ ≤ (1 + K * c) * Real.exp (ε * z.re) +
        (K / ε) * Real.exp (ε * z.re) := by
      apply add_le_add
      · exact le_mul_of_one_le_right hcst he
      · have h := mul_le_mul_of_nonneg_left hlin hK
        convert h using 1
        ring
    _ = (1 + (2 * Real.pi / a) * c + (2 * Real.pi / a) / ε) *
        Real.exp (ε * z.re) := by dsimp [K]; ring

/-- The tail estimate used beyond `Re z = a/(2π)` in
`norm_hyperbolicGammaLog_self_add_le`. -/
private lemma norm_hyperbolicGammaLog_self_add_le_large {a ε c : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hc : c < a) (hc0 : 0 ≤ c)
    {z : ℂ} (hz : a / (2 * Real.pi) ≤ z.re) (hzim : |z.im| ≤ c) :
    ‖hyperbolicGammaLog a a z + π * z ^ 2 / (2 * a ^ 2) + π / 12‖ ≤
      ((1 + (2 * Real.pi / a) * c + (2 * Real.pi / a) / ε) / Real.pi) *
        Real.exp ((ε - 2 * Real.pi / a) * z.re) := by
  let K : ℝ := 2 * Real.pi / a
  have hzpos : 0 ≤ z.re := (by positivity : 0 ≤ a / (2 * Real.pi)).trans hz
  have hbase := norm_equalPeriodRemainder_le_tail ha hc hz hzim
  have hcoeff := equalPeriod_linear_coefficient_le_exp ha hε hc0 hzpos hzim
  calc
    ‖hyperbolicGammaLog a a z + π * z ^ 2 / (2 * a ^ 2) + π / 12‖ ≤
        ((1 + K * ‖z‖) / Real.pi) * Real.exp (-K * z.re) := hbase
    _ ≤ (((1 + K * c + K / ε) * Real.exp (ε * z.re)) / Real.pi) *
        Real.exp (-K * z.re) := by gcongr
    _ = ((1 + (2 * Real.pi / a) * c + (2 * Real.pi / a) / ε) / Real.pi) *
        Real.exp ((ε - 2 * Real.pi / a) * z.re) := by
      dsimp [K]
      rw [show (ε - 2 * Real.pi / a) * z.re =
        ε * z.re + -(2 * Real.pi / a * z.re) by ring, Real.exp_add]
      ring_nf

/-- For `a > 0`, `ε > 0`, and `c < a`, there is `C` with
`‖g(a,a;z) + πz²/(2a²) + π/12‖ ≤ C e^{(ε - 2π/a) Re z}` whenever `Re z ≥ 0` and
`|Im z| ≤ c`: Ruijsenaars (1997), Proposition III.4, equation (3.49) with `a₊ = a₋ = a`, as
derived there from equations (3.41) and (3.46), on closed substrips of the strip (3.2). -/
theorem norm_hyperbolicGammaLog_self_add_le {a : ℝ} (ha : 0 < a) {ε c : ℝ} (hε : 0 < ε)
    (hc : c < a) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → |z.im| ≤ c →
      ‖hyperbolicGammaLog a a z + π * z ^ 2 / (2 * a ^ 2) + π / 12‖ ≤
        C * Real.exp ((ε - 2 * π / a) * z.re) := by
  by_cases hc0 : 0 ≤ c
  · obtain ⟨M, hM0, hM⟩ := norm_hyperbolicGammaLog_self_add_le_small ha hε hc
    let C : ℝ := max M ((1 + (2 * Real.pi / a) * c +
      (2 * Real.pi / a) / ε) / Real.pi)
    refine ⟨C, ?_⟩
    intro z hz hzim
    by_cases hzR : z.re ≤ a / (2 * Real.pi)
    · exact (hM z hz hzR hzim).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
    · exact (norm_hyperbolicGammaLog_self_add_le_large ha hε hc hc0
        (le_of_lt (lt_of_not_ge hzR)) hzim).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _))
  · refine ⟨0, ?_⟩
    intro z hz hzim
    exfalso
    linarith [abs_nonneg z.im]

end SIC

end
