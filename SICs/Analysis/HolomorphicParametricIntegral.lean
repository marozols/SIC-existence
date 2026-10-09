/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Holomorphic dependence of integrals on a complex parameter

Holomorphy of a parametric integral from a locally uniform integrable bound.

This module supplies differentiation under the integral sign for a holomorphic integrand
with a locally uniform integrable majorant. It is used to identify the double-sine integral
representation [AFK25, equation (8.7), `eq:dsintrep`] with the Barnes double-gamma ratio.
The parameter derivative is measurable as an almost-everywhere limit of measurable
difference quotients; a closed-ball estimate supplies its integrable bound.

## The argument

Fix `z₀ ∈ U` and `r > 0` with `closedBall z₀ r ⊆ U` and `‖f(z, t)‖ ≤ g(t)` for `z` in that
ball and almost every `t`. For `z` in the open ball of radius `r/2` about `z₀`, the closed disc
of radius `r/2` about `z` lies in the original ball. Cauchy's estimate
(`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) therefore gives
`‖∂_z f(z, t)‖ ≤ 2 g(t)/r`, the integrable domination required by
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
-/

noncomputable section

open Complex Filter Topology MeasureTheory Set Metric

namespace SIC

/-! ### Differentiation under the integral sign from a uniform bound -/

/-- The derivative of a parametric integrand with respect to its complex parameter is
measurable in the integration variable: it is the almost-everywhere limit of the measurable
difference quotients at the steps `ε/(n+1)`. -/
lemma aestronglyMeasurable_deriv_param {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℂ → α → ℂ} (z₀ : ℂ) (hmeas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (f z) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableAt ℂ (fun w => f w t) z₀) :
    AEStronglyMeasurable (fun t => deriv (fun w => f w t) z₀) μ := by
  rcases Metric.mem_nhds_iff.mp hmeas with ⟨ε, hε, hmeasε⟩
  let q : ℕ → α → ℂ := fun n t =>
    (f (z₀ + (ε : ℂ) / (n + 2)) t - f z₀ t) / ((ε : ℂ) / (n + 2))
  apply aestronglyMeasurable_of_tendsto_ae atTop (f := q)
  · intro n
    have hz : z₀ + (ε : ℂ) / (n + 2) ∈ ball z₀ ε := by
      rw [mem_ball, dist_eq, add_sub_cancel_left, norm_div]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hden : (0 : ℝ) < n + 2 := by linarith
      have hnorm : ‖(n : ℂ) + 2‖ = (n : ℝ) + 2 := by
        rw [show (n : ℂ) + 2 = (((n : ℝ) + 2 : ℝ) : ℂ) by norm_num,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
      rw [hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      exact div_lt_self hε (by linarith)
    have hq :=
      ((hmeasε hz).sub (hmeasε (mem_ball_self hε))).mul_const (((ε : ℂ) / (n + 2))⁻¹)
    exact hq.congr (Eventually.of_forall (fun t => by simp only [q, Pi.sub_apply, div_eq_mul_inv]))
  · filter_upwards [hdiff] with t ht
    have hstep : Tendsto (fun n : ℕ => (ε : ℂ) / (n + 2)) atTop (𝓝 0) :=
      by
        have hraw :=
          (tendsto_const_div_atTop_nhds_zero_nat (ε : ℂ)).comp (tendsto_add_atTop_nat 2)
        exact hraw.congr' (Eventually.of_forall (fun n => by simp [Function.comp_apply]))
    have hstep_ne : ∀ n : ℕ, (ε : ℂ) / (n + 2) ≠ 0 := by
      intro n
      exact div_ne_zero (ofReal_ne_zero.mpr hε.ne') (by exact_mod_cast (by omega : n + 2 ≠ 0))
    have hstep' : Tendsto (fun n : ℕ => (ε : ℂ) / (n + 2)) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hstep, Eventually.of_forall hstep_ne⟩
    have hlim := ht.hasDerivAt.tendsto_slope_zero.comp hstep'
    exact hlim.congr' (Eventually.of_forall (fun n => by
      simp only [q, Function.comp_apply, div_eq_mul_inv, smul_eq_mul]
      rw [mul_comm]))

/-- **Holomorphy of a parametric integral from a locally uniform integrable bound.** If the
integrand `f(z, t)` is measurable in `t` for each `z ∈ U`, holomorphic in `z ∈ U` for almost
every `t`, and every `z₀ ∈ U` has a closed ball in `U` on which `‖f(z, t)‖` is dominated by an
integrable function of `t`, then `z ↦ ∫ f(z, t) dμ(t)` is holomorphic on `U`. The closed-ball
hypothesis already supplies a neighborhood of every point of `U`. -/
theorem differentiableOn_integral_of_locally_bounded {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℂ → α → ℂ} {U : Set ℂ}
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (f z) μ)
    (hdiff : ∀ᵐ t ∂μ, ∀ z ∈ U, DifferentiableAt ℂ (fun w => f w t) z)
    (hbound : ∀ z₀ ∈ U, ∃ r > 0, closedBall z₀ r ⊆ U ∧
      ∃ g : α → ℝ, Integrable g μ ∧ ∀ᵐ t ∂μ, ∀ z ∈ closedBall z₀ r, ‖f z t‖ ≤ g t) :
    DifferentiableOn ℂ (fun z => ∫ t, f z t ∂μ) U := by
  intro z₁ hz₁
  obtain ⟨r, hr, hrU, g, hg, hfg⟩ := hbound z₁ hz₁
  have hmeas' : ∀ᶠ z in 𝓝 z₁, AEStronglyMeasurable (f z) μ := by
    filter_upwards [closedBall_mem_nhds z₁ hr] with z hz
    exact hmeas z (hrU hz)
  have hf_int : Integrable (f z₁) μ := by
    apply hg.mono' (hmeas z₁ hz₁)
    filter_upwards [hfg] with t ht
    exact ht z₁ (mem_closedBall_self hr.le)
  let F' : ℂ → α → ℂ := fun z t => deriv (fun w => f w t) z
  have hF'_meas : AEStronglyMeasurable (F' z₁) μ := by
    apply aestronglyMeasurable_deriv_param z₁ hmeas'
    filter_upwards [hdiff] with t ht
    exact ht z₁ hz₁
  have hderiv_bound : ∀ᵐ t ∂μ, ∀ z ∈ ball z₁ (r / 2), ‖F' z t‖ ≤ 2 * g t / r := by
    filter_upwards [hdiff, hfg] with t hdt hgt
    intro z hz
    have hzr : closedBall z (r / 2) ⊆ closedBall z₁ r := by
      intro w hw
      rw [mem_closedBall] at hw ⊢
      calc
        dist w z₁ ≤ dist w z + dist z z₁ := dist_triangle _ _ _
        _ ≤ r / 2 + r / 2 := add_le_add hw hz.le
        _ = r := by ring
    have hdiffOn : DifferentiableOn ℂ (fun w => f w t) U := by
      intro w hw
      exact (hdt w hw).differentiableWithinAt
    have hcauchy : ‖deriv (fun w => f w t) z‖ ≤ g t / (r / 2) :=
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hr)
        (hdiffOn.diffContOnCl_ball (hzr.trans hrU)) fun w hw =>
          hgt w (hzr (sphere_subset_closedBall hw))
    change ‖deriv (fun w => f w t) z‖ ≤ 2 * g t / r
    convert hcauchy using 1
    field_simp
  have hbound_int : Integrable (fun t => 2 * g t / r) μ := (hg.const_mul 2).div_const r
  have hhasDeriv : ∀ᵐ t ∂μ, ∀ z ∈ ball z₁ (r / 2), HasDerivAt (f · t) (F' z t) z := by
    filter_upwards [hdiff] with t ht
    intro z hz
    apply (ht z (hrU ?_)).hasDerivAt
    rw [mem_closedBall]
    exact hz.le.trans (half_le_self hr.le)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := f) (F' := F') (bound := fun t => 2 * g t / r) (s := ball z₁ (r / 2))
    (ball_mem_nhds z₁ (half_pos hr)) hmeas' hf_int hF'_meas hderiv_bound hbound_int
    hhasDeriv).2.differentiableAt.differentiableWithinAt

/-! ### Real parts on a closed ball

The domination hypothesis of `differentiableOn_integral_of_locally_bounded` is checked on a closed
ball, whose points have real parts within the radius of the centre's. -/

/-- `|Re z - Re z₀| ≤ r` for `z` in the closed ball of radius `r` about `z₀`. -/
lemma abs_re_sub_le_of_mem_closedBall {z z₀ : ℂ} {r : ℝ} (hz : z ∈ closedBall z₀ r) :
    |z.re - z₀.re| ≤ r := by
  simpa using (Complex.abs_re_le_norm (z - z₀)).trans (mem_closedBall_iff_norm.mp hz)

end SIC

end
