/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.IdentityTheorem
import SICs.Analysis.HolomorphicParametricIntegral
import SICs.Analysis.HyperbolicBounds
import SICs.SpecialFunctions.DoubleSine.IntegralIdentities
import Mathlib.Analysis.Complex.Convex

/-!
# The shift integral of the complex double sine

The shift integral `H(τ,β)` and the evaluation `exp H(τ,β)=2cos(πβ/(2τ))`.

This file evaluates the integral

```text
H(τ, β) = ∫₀^∞ (1/(τt) - cosh(βt)/sinh(τt)) dt/t,      Re τ > |Re β|,
```

as `exp(H(τ, β)) = 2 cos(πβ/(2τ))`. The kernel `h(τ, β, t)` is half the difference of two
consecutive double-sine kernels of [AFK25, equation (8.7), `eq:dsintrep`]: shifting the argument
of the double-sine kernel by `1` changes it by `2h(τ, τ-2z, t)`, and shifting by `τ` changes it
by `2h(1, 1-2z, t)`. The two difference equations of the integral representation of the double
sine, `S₂(z+1) = S₂(z)/(2 sin(πz/τ))` and `S₂(z+τ) = S₂(z)/(2 sin(πz))`, are therefore this one
evaluation, read at `β = τ - 2z` and at `(τ, β) = (1, 1 - 2z)`.

## Mathematical argument

For real `τ > 0` and real `β` with `|β| < τ`, the substitution `s = τt` reduces `H(τ, β)` to
`H(1, β/τ)`, and `H(1, α) = log(2 cos(πα/2))` for real `|α| < 1` is
`integral_inv_sq_sub_cosh_div_sinh` of `SICs.SpecialFunctions.DoubleSine.IntegralIdentities`.
Both extensions to complex parameters are by the identity theorem: `H` is holomorphic in each
parameter on the domain `Re τ > |Re β|`, by differentiation under the integral sign from a
locally uniform integrable bound (`differentiableOn_integral_of_locally_bounded`). The bound
combines the exact estimate `‖h(τ, β, t)‖ ≤ (1/(at) + cosh(bt)/sinh(at))/t` for
`Re τ ≥ a > b ≥ |Re β|`, whose inverse-square term `1/(at²)` and exponentially decaying
term are integrable at infinity, with the Taylor bound
`‖h(τ, β, t)‖ ≤ 4T³/a²` for `‖τ‖, ‖β‖ ≤ T` and `Tt ≤ 1`, which controls the removable singularity
at `t = 0`: the numerator `sinh(τt) - τt cosh(βt)` is `O(t³)` and the denominator
`τt² sinh(τt)` is at least `a²t³` in modulus. First `α ↦ exp(H(1, α))` is continued from the real
segment to the strip `|Re α| < 1`, then `τ ↦ exp(H(τ, β))` from the real ray `τ > |Re β|` to
the half-plane `Re τ > |Re β|`. The exponentiated form is used because `2 cos(πβ/(2τ))` need not
lie in the slit plane on that half-plane.
-/

noncomputable section

open Complex Real MeasureTheory Set Filter Topology Metric

namespace SIC

/-! ### The shift kernel and its integral -/

/-- The shift kernel

```text
h(τ, β, t) = (1/(τt) - cosh(βt)/sinh(τt)) / t.
```

Half the difference of consecutive double-sine kernels; see the module docstring. -/
def doubleSineShiftKernel (tau beta : ℂ) (t : ℝ) : ℂ :=
  (1 / (tau * t) - Complex.cosh (beta * t) / Complex.sinh (tau * t)) / t

/-- The shift integral `H(τ, β) = ∫₀^∞ h(τ, β, t) dt`. Lean's Bochner integral totalizes it
outside the convergence domain `Re τ > |Re β|`; no result reads that value. -/
def doubleSineShiftLogIntegral (tau beta : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), doubleSineShiftKernel tau beta t

/-- The scaling law `h(τ, β, t) = τ h(1, β/τ, τt)` for real `τ > 0`. -/
lemma doubleSineShiftKernel_ofReal_mul (tau : ℝ) (htau : 0 < tau) (beta : ℂ) (t : ℝ) :
    doubleSineShiftKernel tau beta t =
      tau * doubleSineShiftKernel 1 (beta / tau) (tau * t) := by
  have htauC : (tau : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt htau)
  by_cases ht : t = 0
  · simp [doubleSineShiftKernel, ht]
  · have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    simp only [doubleSineShiftKernel, ofReal_mul, one_mul]
    field_simp [htauC, htC]

/-- For `Re τ > 0`, the shift kernel is continuous on `(0, ∞)`: `sinh(τt) ≠ 0` there because
`|sinh(τt)| ≥ sinh(Re τ · t) > 0`. -/
lemma continuousOn_doubleSineShiftKernel (tau beta : ℂ) (htau : 0 < tau.re) :
    ContinuousOn (doubleSineShiftKernel tau beta) (Ioi 0) := by
  intro t ht
  have hsinh : Complex.sinh (tau * (t : ℂ)) ≠ 0 := sinh_mul_ofReal_ne_zero_of_re_pos tau htau ht
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have htauC : tau * (t : ℂ) ≠ 0 := mul_ne_zero (Complex.ne_zero_of_re_pos htau) htC
  have ct : ContinuousAt (fun s : ℝ => (s : ℂ)) t :=
    Complex.continuous_ofReal.continuousAt
  have ctau : ContinuousAt (fun s : ℝ => tau * (s : ℂ)) t := continuousAt_const.mul ct
  have cbeta : ContinuousAt (fun s : ℝ => beta * (s : ℂ)) t := continuousAt_const.mul ct
  apply ContinuousAt.continuousWithinAt
  unfold doubleSineShiftKernel
  exact ((continuousAt_const.div₀ ctau htauC).sub
    ((Complex.continuous_cosh.continuousAt.comp_of_eq cbeta rfl).div₀
      (Complex.continuous_sinh.continuousAt.comp_of_eq ctau rfl) hsinh)).div₀ ct htC

/-! ### Bounds -/

/-- The exact bound `‖h(τ, β, t)‖ ≤ (1/(at) + cosh(Re β · t)/sinh(at))/t` for `Re τ ≥ a > 0`
and `t > 0`, from `‖τ‖ ≥ Re τ`, `‖cosh(βt)‖ ≤ cosh(Re β · t)`, and
`‖sinh(τt)‖ ≥ sinh(Re τ · t) ≥ sinh(at)`. -/
lemma norm_doubleSineShiftKernel_le (tau beta : ℂ) {a : ℝ} (ha : 0 < a) (htau : a ≤ tau.re)
    (t : ℝ) (ht : 0 < t) :
    ‖doubleSineShiftKernel tau beta t‖ ≤
      (1 / (a * t) + Real.cosh (beta.re * t) / Real.sinh (a * t)) / t := by
  have hat : 0 < a * t := mul_pos ha ht
  have hatSinh : 0 < Real.sinh (a * t) := Real.sinh_pos_iff.mpr hat
  have htauNorm : a ≤ ‖tau‖ := htau.trans (Complex.re_le_norm tau)
  have hsinh : Real.sinh (a * t) ≤ ‖Complex.sinh (tau * (t : ℂ))‖ :=
    sinh_mul_le_norm_sinh_mul_ofReal tau htau ht.le
  rw [doubleSineShiftKernel, norm_div, Complex.norm_real, Real.norm_of_nonneg ht.le]
  apply div_le_div_of_nonneg_right _ ht.le
  calc
    ‖1 / (tau * (t : ℂ)) - Complex.cosh (beta * (t : ℂ)) /
        Complex.sinh (tau * (t : ℂ))‖ ≤
        ‖1 / (tau * (t : ℂ))‖ +
          ‖Complex.cosh (beta * (t : ℂ)) / Complex.sinh (tau * (t : ℂ))‖ :=
      norm_sub_le _ _
    _ = 1 / (‖tau‖ * t) +
        ‖Complex.cosh (beta * (t : ℂ))‖ / ‖Complex.sinh (tau * (t : ℂ))‖ := by
      rw [Complex.norm_div, Complex.norm_div, norm_one, one_div, norm_mul, norm_real,
        Real.norm_of_nonneg ht.le]
      simp only [one_div]
    _ ≤ 1 / (a * t) + Real.cosh (beta.re * t) / Real.sinh (a * t) := by
      apply add_le_add
      · exact one_div_le_one_div_of_le hat
          (mul_le_mul_of_nonneg_right htauNorm ht.le)
      · apply div_le_div₀ (zero_le_one.trans (Real.one_le_cosh _)) _ hatSinh hsinh
        simpa using norm_cosh_le_cosh_re (beta * (t : ℂ))

/-- The numerator `sinh(τt) - τt cosh(βt)` of the shift kernel is `O(t³)`: for
`‖τ‖, ‖β‖ ≤ T` and `Tt ≤ 1`, its modulus is at most `3T³t³`. This is the cancellation of the
`t` terms in the Taylor expansions `sinh(τt) = τt + (τt)³/6 + O(t⁵)` and
`cosh(βt) = 1 + (βt)²/2 + O(t⁴)`. -/
private lemma norm_shift_numerator_le (tau beta : ℂ) {T : ℝ} (htau : ‖tau‖ ≤ T)
    (hbeta : ‖beta‖ ≤ T) (t : ℝ) (ht : 0 < t) (htT : T * t ≤ 1) :
    ‖Complex.sinh (tau * t) - tau * t * Complex.cosh (beta * t)‖ ≤ 3 * T ^ 3 * t ^ 3 := by
  let x : ℂ := tau * t
  let y : ℂ := beta * t
  let u : ℝ := T * t
  have hT : 0 ≤ T := (norm_nonneg tau).trans htau
  have hu : 0 ≤ u := mul_nonneg hT ht.le
  have hx : ‖x‖ ≤ u := by
    simp only [x, u, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    exact mul_le_mul_of_nonneg_right htau ht.le
  have hy : ‖y‖ ≤ u := by
    simp only [y, u, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    exact mul_le_mul_of_nonneg_right hbeta ht.le
  have hx1 : ‖x‖ ≤ 1 := hx.trans htT
  have hy1 : ‖y‖ ≤ 1 := hy.trans htT
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [sq_nonneg (u - 1)]
  have hu5 : u ^ 5 ≤ u ^ 3 := by
    calc
      u ^ 5 = u ^ 3 * u ^ 2 := by ring
      _ ≤ u ^ 3 * 1 := mul_le_mul_of_nonneg_left hu2 (pow_nonneg hu 3)
      _ = u ^ 3 := mul_one _
  have hA : ‖Complex.sinh x - (x + x ^ 3 / 6)‖ ≤ u ^ 3 :=
    (norm_sinh_sub_cubic_le hx1).trans <|
      (pow_le_pow_left₀ (norm_nonneg x) hx 5).trans hu5
  have hB : ‖x ^ 3 / 6‖ ≤ u ^ 3 / 6 := by
    rw [Complex.norm_div, norm_pow]
    norm_num
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg x) hx 3) (by norm_num)
  have hC : ‖x * (Complex.cosh y - (1 + y ^ 2 / 2))‖ ≤ u ^ 3 := by
    calc
      ‖x * (Complex.cosh y - (1 + y ^ 2 / 2))‖ =
          ‖x‖ * ‖Complex.cosh y - (1 + y ^ 2 / 2)‖ := norm_mul _ _
      _ ≤ ‖x‖ * ‖y‖ ^ 4 := mul_le_mul_of_nonneg_left
        (norm_cosh_sub_quadratic_le hy1) (norm_nonneg x)
      _ ≤ u * u ^ 4 := mul_le_mul hx (pow_le_pow_left₀ (norm_nonneg y) hy 4)
        (pow_nonneg (norm_nonneg y) _) hu
      _ = u ^ 5 := by ring
      _ ≤ u ^ 3 := hu5
  have hD : ‖x * y ^ 2 / 2‖ ≤ u ^ 3 / 2 := by
    rw [Complex.norm_div, norm_mul, norm_pow]
    norm_num
    apply div_le_div_of_nonneg_right _ (by norm_num)
    calc
      ‖x‖ * ‖y‖ ^ 2 ≤ u * u ^ 2 := mul_le_mul hx
        (pow_le_pow_left₀ (norm_nonneg y) hy 2) (pow_nonneg (norm_nonneg y) _) hu
      _ = u ^ 3 := by ring
  have hdecomp : Complex.sinh x - x * Complex.cosh y =
      (Complex.sinh x - (x + x ^ 3 / 6)) + x ^ 3 / 6 -
        x * (Complex.cosh y - (1 + y ^ 2 / 2)) - x * y ^ 2 / 2 := by
    ring
  change ‖Complex.sinh x - x * Complex.cosh y‖ ≤ _
  rw [hdecomp]
  calc
    ‖(Complex.sinh x - (x + x ^ 3 / 6)) + x ^ 3 / 6 -
        x * (Complex.cosh y - (1 + y ^ 2 / 2)) - x * y ^ 2 / 2‖ ≤
        ‖Complex.sinh x - (x + x ^ 3 / 6)‖ + ‖x ^ 3 / 6‖ +
          ‖x * (Complex.cosh y - (1 + y ^ 2 / 2))‖ + ‖x * y ^ 2 / 2‖ := by
      grw [norm_sub_le, norm_sub_le, norm_add_le]
    _ ≤ u ^ 3 + u ^ 3 / 6 + u ^ 3 + u ^ 3 / 2 := by gcongr
    _ ≤ 3 * T ^ 3 * t ^ 3 := by
      dsimp [u]
      ring_nf
      nlinarith [pow_nonneg hT 3, pow_nonneg ht.le 3]

/-- The Taylor bound near `t = 0`: `‖h(τ, β, t)‖ ≤ 4T³/a²` when `Re τ ≥ a > 0`,
`‖τ‖, ‖β‖ ≤ T`, `t > 0`, and `Tt ≤ 1`. The kernel is `(sinh(τt) - τt cosh(βt)) / (τt² sinh(τt))`,
whose denominator has modulus at least `a t² sinh(at) ≥ a²t³`. -/
lemma norm_doubleSineShiftKernel_le_of_mul_le_one (tau beta : ℂ) {a T : ℝ} (ha : 0 < a)
    (htau : a ≤ tau.re) (htauT : ‖tau‖ ≤ T) (hbeta : ‖beta‖ ≤ T) (t : ℝ) (ht : 0 < t)
    (htT : T * t ≤ 1) :
    ‖doubleSineShiftKernel tau beta t‖ ≤ 4 * T ^ 3 / a ^ 2 := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have htauC : tau ≠ 0 := Complex.ne_zero_of_re_pos (ha.trans_le htau)
  have hsinhC : Complex.sinh (tau * (t : ℂ)) ≠ 0 :=
    sinh_mul_ofReal_ne_zero_of_re_pos tau (ha.trans_le htau) ht
  have hkernel : doubleSineShiftKernel tau beta t =
      (Complex.sinh (tau * t) - tau * t * Complex.cosh (beta * t)) /
        (tau * t ^ 2 * Complex.sinh (tau * t)) := by
    unfold doubleSineShiftKernel
    field_simp [htC, htauC, hsinhC]
  have hT : 0 ≤ T := (norm_nonneg tau).trans htauT
  have hnum : ‖Complex.sinh (tau * t) - tau * t * Complex.cosh (beta * t)‖ ≤
      3 * T ^ 3 * t ^ 3 := norm_shift_numerator_le tau beta htauT hbeta t ht htT
  have hat : 0 < a * t := mul_pos ha ht
  have hsinh : Real.sinh (a * t) ≤ ‖Complex.sinh (tau * (t : ℂ))‖ :=
    sinh_mul_le_norm_sinh_mul_ofReal tau htau ht.le
  have hden : a ^ 2 * t ^ 3 ≤ ‖tau * (t : ℂ) ^ 2 * Complex.sinh (tau * t)‖ := by
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le]
    calc
      a ^ 2 * t ^ 3 = a * t ^ 2 * (a * t) := by ring
      _ ≤ ‖tau‖ * t ^ 2 * Real.sinh (a * t) := by
        gcongr
        · exact htau.trans (Complex.re_le_norm tau)
        · exact Real.self_le_sinh_iff.mpr hat.le
      _ ≤ ‖tau‖ * t ^ 2 * ‖Complex.sinh (tau * (t : ℂ))‖ := by gcongr
  have hdenPos : 0 < a ^ 2 * t ^ 3 := mul_pos (sq_pos_of_pos ha) (pow_pos ht 3)
  rw [hkernel, Complex.norm_div]
  calc
    ‖Complex.sinh (tau * ↑t) - tau * ↑t * Complex.cosh (beta * ↑t)‖ /
        ‖tau * ↑t ^ 2 * Complex.sinh (tau * ↑t)‖ ≤
        (3 * T ^ 3 * t ^ 3) / (a ^ 2 * t ^ 3) :=
      div_le_div₀ (by positivity) hnum hdenPos hden
    _ = 3 * T ^ 3 / a ^ 2 := by field_simp [ha.ne', ht.ne']
    _ ≤ 4 * T ^ 3 / a ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg a)
      nlinarith [pow_nonneg hT 3]

/-- The tail bound `(1/(at) + cosh(bt)/sinh(at))/t` is integrable on `(c, ∞)` for every `c > 0`
when `|b| < a`: it is at most `1/(at²)` plus a constant multiple of `exp(-(a - |b|)t)`. -/
lemma integrableOn_shiftTailBound {a b c : ℝ} (ha : 0 < a) (hab : |b| < a) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (1 / (a * t) + Real.cosh (b * t) / Real.sinh (a * t)) / t)
      (Ioi c) := by
  let f := fun t : ℝ => (1 / (a * t) + Real.cosh (b * t) / Real.sinh (a * t)) / t
  let d := max c (1 / a)
  have hcd : c ≤ d := le_max_left _ _
  have hda : 1 / a ≤ d := le_max_right _ _
  have hd : 0 < d := hc.trans_le hcd
  have hcont : ContinuousOn f (Ioi 0) := by
    intro t ht
    have hat : 0 < a * t := mul_pos ha ht
    have htne : t ≠ 0 := ht.ne'
    have hatne : a * t ≠ 0 := hat.ne'
    have hsinhne : Real.sinh (a * t) ≠ 0 := (Real.sinh_pos_iff.mpr hat).ne'
    apply ContinuousAt.continuousWithinAt
    dsimp [f]
    fun_prop (disch := assumption)
  have hlocal : IntegrableOn f (Ioc c d) := by
    apply ((hcont.mono fun _ ht => hc.trans_le ht.1).integrableOn_Icc).mono_set
    exact Ioc_subset_Icc_self
  let q := fun t : ℝ => (1 / a) * t ^ (-2 : ℝ) +
    (4 / c) * Real.exp (-(a - |b|) * t)
  have hq : IntegrableOn q (Ioi d) := by
    apply Integrable.add
    · exact (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hd).const_mul _
    · exact (exp_neg_integrableOn_Ioi d (sub_pos.mpr hab)).const_mul _
  have hcontTail : ContinuousOn f (Ioi d) := hcont.mono fun _ ht => hd.trans ht
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Ioi d)) :=
    hcontTail.aestronglyMeasurable measurableSet_Ioi
  have htail : IntegrableOn f (Ioi d) := by
    apply hq.mono' hfmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htd : d < t := ht
    have ht0 : 0 < t := hd.trans htd
    have hct : c < t := hcd.trans_lt htd
    have hat : 0 < a * t := mul_pos ha ht0
    have hat1 : 1 ≤ a * t := by
      calc
        1 = a * (1 / a) := by field_simp
        _ ≤ a * t := mul_le_mul_of_nonneg_left (hda.trans_lt htd).le ha.le
    have hsinh : Real.exp (a * t) / 4 ≤ Real.sinh (a * t) :=
      exp_div_four_le_sinh hat1
    have hcosh : Real.cosh (b * t) ≤ Real.exp (|b| * t) := by
      calc
        Real.cosh (b * t) ≤ Real.exp |b * t| := cosh_le_exp_abs _
        _ = Real.exp (|b| * t) := by rw [abs_mul, abs_of_pos ht0]
    have hratio : Real.cosh (b * t) / Real.sinh (a * t) ≤
        4 * Real.exp (-(a - |b|) * t) := by
      calc
        Real.cosh (b * t) / Real.sinh (a * t) ≤
            Real.exp (|b| * t) / (Real.exp (a * t) / 4) :=
          div_le_div₀ (Real.exp_pos _).le hcosh (by positivity) hsinh
        _ = 4 * Real.exp (-(a - |b|) * t) := by
          field_simp [Real.exp_ne_zero]
          rw [← Real.exp_add]
          congr 2
          ring
    have hfnonneg : 0 ≤ f t := by
      dsimp [f]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hfnonneg]
    calc
      f t ≤ 1 / (a * t ^ 2) + (4 / c) * Real.exp (-(a - |b|) * t) := by
        dsimp [f]
        rw [add_div]
        apply add_le_add
        · field_simp [ha.ne', ht0.ne']
          norm_num
        · calc
            Real.cosh (b * t) / Real.sinh (a * t) / t ≤
                (4 * Real.exp (-(a - |b|) * t)) / c :=
              div_le_div₀ (by positivity) hratio hc hct.le
            _ = (4 / c) * Real.exp (-(a - |b|) * t) := by ring
      _ = q t := by
        dsimp [q]
        rw [Real.rpow_neg (le_of_lt ht0), Real.rpow_two]
        field_simp [ha.ne', ht0.ne']
  rw [← Ioc_union_Ioi_eq_Ioi hcd]
  exact hlocal.union htail

/-- **Locally uniform domination of the shift kernel.** For `Re τ ≥ a > b ≥ |Re β|` and
`‖τ‖, ‖β‖ ≤ T`, one integrable function of `t` dominates `‖h(τ, β, t)‖` on `(0, ∞)`: the
constant `4T³/a²` on `(0, 1/T]` and the tail bound beyond. -/
lemma doubleSineShiftKernel_dominated {a b T : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hab : b < a)
    (hT : 0 < T) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧ ∀ tau beta : ℂ, a ≤ tau.re → ‖tau‖ ≤ T →
      |beta.re| ≤ b → ‖beta‖ ≤ T → ∀ t ∈ Ioi (0 : ℝ),
        ‖doubleSineShiftKernel tau beta t‖ ≤ g t := by
  let q := fun t : ℝ => (1 / (a * t) + Real.cosh (b * t) / Real.sinh (a * t)) / t
  let g := fun t : ℝ => if t ≤ 1 / T then 4 * T ^ 3 / a ^ 2 else q t
  refine ⟨g, ?_, ?_⟩
  · have hcut : 0 < 1 / T := one_div_pos.mpr hT
    have hnear : IntegrableOn (fun _ : ℝ => 4 * T ^ 3 / a ^ 2) (Ioc 0 (1 / T)) :=
      integrableOn_const measure_Ioc_lt_top.ne
    have hnearG : IntegrableOn g (Ioc 0 (1 / T)) := hnear.congr_fun (fun t ht => by
      simp only [g, ite_eq_left ht.2]) measurableSet_Ioc
    have htail : IntegrableOn q (Ioi (1 / T)) := by
      exact integrableOn_shiftTailBound ha (by simpa [abs_of_nonneg hb] using hab) hcut
    have htailG : IntegrableOn g (Ioi (1 / T)) := htail.congr_fun (fun t ht => by
      have hlt : 1 / T < t := ht
      simp only [g, ite_eq_right (not_le_of_gt hlt)]) measurableSet_Ioi
    rw [← Ioc_union_Ioi_eq_Ioi hcut.le]
    exact hnearG.union htailG
  · intro tau beta htau htauT hbeta hbetaT t ht
    have ht0 : 0 < t := ht
    by_cases htc : t ≤ 1 / T
    · simp only [g, ite_eq_left htc]
      apply norm_doubleSineShiftKernel_le_of_mul_le_one tau beta ha htau htauT hbetaT t ht
      simpa [mul_comm] using (le_div_iff₀ hT).mp htc
    · simp only [g, ite_eq_right htc, q]
      refine (norm_doubleSineShiftKernel_le tau beta ha htau t ht).trans ?_
      apply div_le_div_of_nonneg_right _ ht.le
      apply add_le_add (le_refl _)
      apply div_le_div_of_nonneg_right _ (Real.sinh_pos_iff.mpr (mul_pos ha ht)).le
      rw [Real.cosh_le_cosh]
      simpa [abs_mul, abs_of_pos ht0, abs_of_nonneg hb] using
        mul_le_mul_of_nonneg_right hbeta ht0.le

/-- The shift kernel is integrable on `(0, ∞)` when `Re τ > |Re β|`. -/
lemma integrableOn_doubleSineShiftKernel (tau beta : ℂ) (h : |beta.re| < tau.re) :
    IntegrableOn (doubleSineShiftKernel tau beta) (Ioi 0) := by
  let a := (tau.re + |beta.re|) / 2
  let b := |beta.re|
  let T := max ‖tau‖ ‖beta‖
  have htauRe : 0 < tau.re := (abs_nonneg beta.re).trans_lt h
  have ha : 0 < a := by dsimp [a]; nlinarith [abs_nonneg beta.re]
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hab : b < a := by dsimp [a, b]; linarith
  have hT : 0 < T := (norm_pos_iff.mpr (Complex.ne_zero_of_re_pos htauRe)).trans_le
    (le_max_left _ _)
  obtain ⟨g, hg, hdom⟩ := doubleSineShiftKernel_dominated ha hb hab hT
  apply hg.mono'
  · exact (continuousOn_doubleSineShiftKernel tau beta htauRe).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply hdom tau beta
    · dsimp [a]
      linarith
    · exact le_max_left _ _
    · exact le_rfl
    · exact le_max_right _ _
    · exact ht

/-! ### Holomorphy in each parameter -/

/-- `τ ↦ H(τ, β)` is holomorphic on the half-plane `Re τ > |Re β|`, by
`differentiableOn_integral_of_locally_bounded` and `doubleSineShiftKernel_dominated`. -/
theorem differentiableOn_doubleSineShiftLogIntegral_left (beta : ℂ) :
    DifferentiableOn ℂ (fun tau => doubleSineShiftLogIntegral tau beta)
      {tau : ℂ | |beta.re| < tau.re} := by
  let U : Set ℂ := {tau : ℂ | |beta.re| < tau.re}
  apply differentiableOn_integral_of_locally_bounded (U := U)
  · intro tau htau
    exact (continuousOn_doubleSineShiftKernel tau beta
      ((abs_nonneg beta.re).trans_lt htau)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro tau htau
    have ht0 : 0 < t := ht
    have htauRe : 0 < tau.re := (abs_nonneg beta.re).trans_lt htau
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    have htauC : tau * (t : ℂ) ≠ 0 :=
      mul_ne_zero (Complex.ne_zero_of_re_pos htauRe) htC
    have hsinh : Complex.sinh (tau * (t : ℂ)) ≠ 0 :=
      sinh_mul_ofReal_ne_zero_of_re_pos tau htauRe ht0
    unfold doubleSineShiftKernel
    fun_prop (disch := aesop)
  · intro tau₀ htau₀
    have htau₀' : |beta.re| < tau₀.re := htau₀
    let r := (tau₀.re - |beta.re|) / 2
    let a := |beta.re| + r
    let b := |beta.re|
    let T := max (‖tau₀‖ + r) ‖beta‖
    have hr : 0 < r := by dsimp [r]; linarith
    have ha : 0 < a := by dsimp [a]; nlinarith [abs_nonneg beta.re]
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have hab : b < a := by dsimp [a, b]; linarith
    have htau₀Re : 0 < tau₀.re := (abs_nonneg beta.re).trans_lt htau₀'
    have hT : 0 < T := by
      apply lt_of_lt_of_le (norm_pos_iff.mpr (Complex.ne_zero_of_re_pos htau₀Re))
      exact le_max_of_le_left (le_add_of_nonneg_right hr.le)
    refine ⟨r, hr, ?_, ?_⟩
    · intro tau htau
      have hre := abs_re_sub_le_of_mem_closedBall htau
      dsimp [U]
      dsimp [r] at hre ⊢
      rw [abs_le] at hre
      linarith [htau₀']
    · obtain ⟨g, hg, hdom⟩ := doubleSineShiftKernel_dominated ha hb hab hT
      refine ⟨g, hg, ?_⟩
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro tau htau
      have hre := abs_re_sub_le_of_mem_closedBall htau
      apply hdom tau beta
      · dsimp [a, r] at hre ⊢
        rw [abs_le] at hre
        linarith
      · exact (norm_le_of_mem_closedBall htau).trans (le_max_left _ _)
      · exact le_rfl
      · exact le_max_right _ _
      · exact ht

/-- `β ↦ H(τ, β)` is holomorphic on the strip `|Re β| < Re τ`, by
`differentiableOn_integral_of_locally_bounded` and `doubleSineShiftKernel_dominated`. -/
theorem differentiableOn_doubleSineShiftLogIntegral_right (tau : ℂ) :
    DifferentiableOn ℂ (fun beta => doubleSineShiftLogIntegral tau beta)
      {beta : ℂ | |beta.re| < tau.re} := by
  let U : Set ℂ := {beta : ℂ | |beta.re| < tau.re}
  apply differentiableOn_integral_of_locally_bounded (U := U)
  · intro beta hbeta
    exact (continuousOn_doubleSineShiftKernel tau beta
      ((abs_nonneg beta.re).trans_lt hbeta)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro beta hbeta
    have htauRe : 0 < tau.re := (abs_nonneg beta.re).trans_lt hbeta
    have ht0 : 0 < t := ht
    have hsinh : Complex.sinh (tau * (t : ℂ)) ≠ 0 :=
      sinh_mul_ofReal_ne_zero_of_re_pos tau htauRe ht0
    unfold doubleSineShiftKernel
    fun_prop (disch := aesop)
  · intro beta₀ hbeta₀
    have hbeta₀' : |beta₀.re| < tau.re := hbeta₀
    let r := (tau.re - |beta₀.re|) / 2
    let a := tau.re
    let b := |beta₀.re| + r
    let T := max ‖tau‖ (‖beta₀‖ + r)
    have hr : 0 < r := by dsimp [r]; linarith
    have ha : 0 < a := by dsimp [a]; exact (abs_nonneg beta₀.re).trans_lt hbeta₀'
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have hab : b < a := by dsimp [a, b, r]; linarith
    have hT : 0 < T := by
      apply lt_of_lt_of_le (norm_pos_iff.mpr (Complex.ne_zero_of_re_pos ha))
      exact le_max_left _ _
    have habs : ∀ beta ∈ closedBall beta₀ r, |beta.re| ≤ |beta₀.re| + r := fun beta hbeta => by
      linarith [abs_re_sub_le_of_mem_closedBall hbeta, abs_sub_abs_le_abs_sub beta.re beta₀.re]
    refine ⟨r, hr, ?_, ?_⟩
    · intro beta hbeta
      have := habs beta hbeta
      dsimp [U]
      dsimp [r] at this ⊢
      linarith
    · obtain ⟨g, hg, hdom⟩ := doubleSineShiftKernel_dominated ha hb hab hT
      refine ⟨g, hg, ?_⟩
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro beta hbeta
      apply hdom tau beta
      · exact le_rfl
      · exact le_max_left _ _
      · exact habs beta hbeta
      · exact (norm_le_of_mem_closedBall hbeta).trans (le_max_right _ _)
      · exact ht

/-! ### Evaluation -/

/-- The real case `H(1, α) = log(2 cos(πα/2))` for real `|α| < 1`, which is
`integral_inv_sq_sub_cosh_div_sinh` read in `ℂ`. -/
lemma doubleSineShiftLogIntegral_one_ofReal (alpha : ℝ) (h : |alpha| < 1) :
    doubleSineShiftLogIntegral 1 alpha = (Real.log (2 * Real.cos (π * alpha / 2)) : ℂ) := by
  let f := fun t : ℝ => 1 / t ^ 2 - Real.cosh (alpha * t) / (t * Real.sinh t)
  calc
    doubleSineShiftLogIntegral 1 alpha = ∫ t in Ioi (0 : ℝ), (f t : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : t ≠ 0 := ht.ne'
      have hsinh : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.mpr ht).ne'
      dsimp [f, doubleSineShiftKernel]
      push_cast
      field_simp [ht0, hsinh]
    _ = ((((∫ t in Ioi (0 : ℝ), f t) : ℝ)) : ℂ) := integral_ofReal
    _ = (Real.log (2 * Real.cos (π * alpha / 2)) : ℂ) := by
      rw [integral_inv_sq_sub_cosh_div_sinh alpha h]

/-- `exp(H(1, α)) = 2 cos(πα/2)` on the strip `|Re α| < 1`, by the identity theorem from the
real segment `(-1, 1)` (`eqOn_of_differentiableOn_of_eqOn_real`). -/
theorem exp_doubleSineShiftLogIntegral_one (alpha : ℂ) (h : |alpha.re| < 1) :
    Complex.exp (doubleSineShiftLogIntegral 1 alpha) = 2 * Complex.cos (π * alpha / 2) := by
  let U : Set ℂ := {z : ℂ | |z.re| < 1}
  have hU : IsOpen U := isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hUc : IsPreconnected U := by
    have hUeq : U = {z : ℂ | (-1 : ℝ) < z.re} ∩ {z : ℂ | z.re < 1} := by
      ext z
      simp only [U, mem_ofPred_eq, mem_inter_iff, abs_lt]
    rw [hUeq]
    exact ((convex_halfSpace_re_gt (-1)).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hf : DifferentiableOn ℂ (fun z => Complex.exp (doubleSineShiftLogIntegral 1 z)) U :=
    differentiableOn_doubleSineShiftLogIntegral_right 1 |>.cexp
  have hg : DifferentiableOn ℂ (fun z : ℂ => 2 * Complex.cos (π * z / 2)) U := by
    fun_prop
  have hreal : ∀ x : ℝ, (x : ℂ) ∈ U →
      Complex.exp (doubleSineShiftLogIntegral 1 x) = 2 * Complex.cos (π * x / 2) := by
    intro x hx
    have hx' : |x| < 1 := by simpa [U] using hx
    have hangle : -(π / 2) < π * x / 2 ∧ π * x / 2 < π / 2 := by
      obtain ⟨hxl, hxu⟩ := abs_lt.mp hx'
      constructor <;> nlinarith [Real.pi_pos]
    have hcos : 0 < 2 * Real.cos (π * x / 2) := mul_pos two_pos <|
      Real.cos_pos_of_mem_Ioo hangle
    rw [doubleSineShiftLogIntegral_one_ofReal x hx']
    rw [← Complex.ofReal_exp, Real.exp_log hcos]
    push_cast
    rfl
  exact eqOn_of_differentiableOn_of_eqOn_real hU hUc hf hg (x₀ := 0) (by simp [U]) hreal h

/-- The scaling law `H(τ, β) = H(1, β/τ)` for real `τ > 0`, by the substitution `s = τt`
(`integral_comp_mul_left_Ioi`). -/
lemma doubleSineShiftLogIntegral_ofReal (tau : ℝ) (htau : 0 < tau) (beta : ℂ) :
    doubleSineShiftLogIntegral tau beta = doubleSineShiftLogIntegral 1 (beta / tau) := by
  unfold doubleSineShiftLogIntegral
  conv_lhs =>
    enter [2, t]
    rw [doubleSineShiftKernel_ofReal_mul tau htau beta t]
  rw [integral_const_mul]
  rw [integral_comp_mul_left_Ioi (doubleSineShiftKernel 1 (beta / tau)) 0 htau, mul_zero]
  simp [htau.ne']

/-- **Evaluation of the shift integral.** For `Re τ > |Re β|`,

```text
exp(H(τ, β)) = 2 cos(πβ/(2τ)).
```

The real case is the scaling law and `exp_doubleSineShiftLogIntegral_one`; the half-plane
follows by the identity theorem from the real ray (`eqOn_of_differentiableOn_of_eqOn_real`).
This evaluation is the analytic content of both difference equations of the double-sine integral
representation [AFK25, equation (8.7), `eq:dsintrep`]. -/
theorem exp_doubleSineShiftLogIntegral (tau beta : ℂ) (h : |beta.re| < tau.re) :
    Complex.exp (doubleSineShiftLogIntegral tau beta) =
      2 * Complex.cos (π * beta / (2 * tau)) := by
  let U : Set ℂ := {z : ℂ | |beta.re| < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt |beta.re|).isPreconnected
  have hf : DifferentiableOn ℂ (fun z => Complex.exp (doubleSineShiftLogIntegral z beta)) U :=
    (differentiableOn_doubleSineShiftLogIntegral_left beta).cexp
  have hg : DifferentiableOn ℂ (fun z : ℂ => 2 * Complex.cos (π * beta / (2 * z))) U := by
    intro z hz
    have hzRe : 0 < z.re := (abs_nonneg beta.re).trans_lt hz
    have hzne : z ≠ 0 := Complex.ne_zero_of_re_pos hzRe
    have htwoz : (2 : ℂ) * z ≠ 0 := mul_ne_zero (by norm_num) hzne
    fun_prop (disch := assumption)
  have hreal : ∀ x : ℝ, (x : ℂ) ∈ U →
      Complex.exp (doubleSineShiftLogIntegral x beta) =
        2 * Complex.cos (π * beta / (2 * x)) := by
    intro x hx
    have hx' : |beta.re| < x := by simpa [U] using hx
    have hx0 : 0 < x := (abs_nonneg beta.re).trans_lt hx'
    have hquot : |(beta / (x : ℂ)).re| < 1 := by
      rw [Complex.div_ofReal_re, abs_div, abs_of_pos hx0, div_lt_one hx0]
      exact hx'
    rw [doubleSineShiftLogIntegral_ofReal x hx0 beta]
    convert exp_doubleSineShiftLogIntegral_one (beta / (x : ℂ)) hquot using 1
    field_simp [Complex.ofReal_ne_zero.mpr hx0.ne']
  exact eqOn_of_differentiableOn_of_eqOn_real hU hUc hf hg
    (x₀ := |beta.re| + 1) (by simp [U]) hreal h

/-- The evaluation at `β = τ - 2z`, for `0 < Re z < Re τ`:

```text
exp(H(τ, τ - 2z)) = 2 sin(πz/τ).
```

This is the factor by which the double-sine integral changes under `z ↦ z + 1`. -/
theorem exp_doubleSineShiftLogIntegral_sub_two_mul (z tau : ℂ) (hz : 0 < z.re)
    (hzUpper : z.re < tau.re) :
    Complex.exp (doubleSineShiftLogIntegral tau (tau - 2 * z)) =
      2 * Complex.sin (π * z / tau) := by
  have htau0 : tau ≠ 0 := Complex.ne_zero_of_re_pos (hz.trans hzUpper)
  have hbeta : |(tau - 2 * z).re| < tau.re := by
    simp only [sub_re, mul_re, Complex.re_ofNat, Complex.im_ofNat]
    rw [abs_lt]
    constructor <;> linarith
  rw [exp_doubleSineShiftLogIntegral tau (tau - 2 * z) hbeta,
    show π * (tau - 2 * z) / (2 * tau) = π / 2 - π * z / tau by field_simp,
    Complex.cos_pi_div_two_sub]

/-- The evaluation at `(τ, β) = (1, 1 - 2z)`, for `0 < Re z < 1`:

```text
exp(H(1, 1 - 2z)) = 2 sin(πz).
```

This is the factor by which the double-sine integral changes under `z ↦ z + τ`. -/
theorem exp_doubleSineShiftLogIntegral_one_sub_two_mul (z : ℂ) (hz : 0 < z.re)
    (hzUpper : z.re < 1) :
    Complex.exp (doubleSineShiftLogIntegral 1 (1 - 2 * z)) = 2 * Complex.sin (π * z) := by
  have hbeta : |(1 - 2 * z).re| < (1 : ℂ).re := by
    simp only [sub_re, one_re, mul_re, Complex.re_ofNat, Complex.im_ofNat]
    rw [abs_lt]
    constructor <;> linarith
  rw [exp_doubleSineShiftLogIntegral 1 (1 - 2 * z) hbeta,
    show π * (1 - 2 * z) / (2 * 1) = π / 2 - π * z by ring, Complex.cos_pi_div_two_sub]

end SIC

end
