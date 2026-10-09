/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrating inverse Mellin transforms

Integrating an inverse Mellin transform from zero.

This file supplies the integration step in [95, Shintani (1977), proof of Lemma 1,
p. 171, first display for the digamma function after equation (1.3)]. On a line
`Re(s)=sigma<1`, the norm of `x^(-s) F(s)` is `x^(-sigma)|F(s)|` for `x>0`.
The first factor is integrable on `(0,t]` and the second on the vertical line.
Fubini therefore permits integration from zero to `t` inside the inverse transform.
The power integral replaces `x^(-s)` by `t^(1-s)/(1-s)`.

The reflection identity also supplies the common change of variable in Shintani's two
remainder transformations. These statements are general integral API. Integration requires
absolute convergence on the vertical line, but no holomorphy of the transform.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace SIC

/-! ### Absolute convergence of the double integral -/

/-- Multiplication by `t^(-s)` preserves vertical absolute convergence for `t>0`.
Its norm is the constant `t^(-sigma)` on `Re(s)=sigma`. -/
theorem verticalIntegrable_mul_cpow {F : ℂ → ℂ} {σ : ℝ}
    (hF : VerticalIntegrable F σ) (t : ℝ) (ht : 0 < t) :
    VerticalIntegrable (fun s => F s * (t : ℂ) ^ (-s)) σ := by
  have hc : Continuous (fun y : ℝ => (t : ℂ) ^ (-((σ : ℂ) + y * I))) :=
    Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr ht.ne'))
  exact hF.mul_bdd hc.aestronglyMeasurable (c := t ^ (-σ)) (by
    filter_upwards with y
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp)

/-- The inverse Mellin kernel is integrable on `(0,t]` times its vertical line
when `sigma<1`. This is the Fubini hypothesis for `integral_mellinInv_zero_to`. -/
private lemma integrable_mellinInv_kernel_prod {F : ℂ → ℂ} {σ : ℝ}
    (hσ : σ < 1) (hF : VerticalIntegrable F σ) (t : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      (p.1 : ℂ) ^ (-((σ : ℂ) + p.2 * I)) * F (σ + p.2 * I))
      ((volume.restrict (Ioc 0 t)).prod volume) := by
  have hr : IntegrableOn (fun x : ℝ => x ^ (-σ)) (Ioc 0 t) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -σ)).1
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Complex.exp (-((σ : ℂ) + p.2 * I) * Real.log p.1) * F (σ + p.2 * I))
      ((volume.restrict (Ioc 0 t)).prod volume) := by
    apply AEStronglyMeasurable.mul _ hF.aestronglyMeasurable.comp_snd
    exact (show Measurable (fun p : ℝ × ℝ =>
      Complex.exp (-((σ : ℂ) + p.2 * I) * Real.log p.1)) by fun_prop).aestronglyMeasurable
  have he : (fun p : ℝ × ℝ =>
      Complex.exp (-((σ : ℂ) + p.2 * I) * Real.log p.1) * F (σ + p.2 * I)) =ᵐ[
      (volume.restrict (Ioc 0 t)).prod volume] (fun p : ℝ × ℝ =>
      (p.1 : ℂ) ^ (-((σ : ℂ) + p.2 * I)) * F (σ + p.2 * I)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem measurableSet_Ioc)] with p hp
    have hx : p.1 ∈ Ioc 0 t := hp
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.1.ne'),
      Complex.ofReal_log hx.1.le]
    congr 2
    exact mul_comm _ _
  apply ((hr.mul_prod hF.norm).mono' (hm.congr he) ?_)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (ae_restrict_mem measurableSet_Ioc)] with p hp
  have hx : p.1 ∈ Ioc 0 t := hp
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
  simp

/-! ### Reflection of the inverse transform

Changing the height variable to its negative reflects the vertical line. A symmetric transform
therefore acquires only the real-power factor from the Mellin kernel. -/

/-- Reflection of an inverse Mellin transform: if `F(c-s)=F(s)` and `t>0`, then
`mellinInv(c-σ,F)(t)=t^(-c) mellinInv(σ,F)(t⁻¹)`. This is the change of variable
`y ↦ -y` used by Shintani for both remainder transforms in [95, Shintani (1977),
proof of Lemma 1, p. 171]. It also holds for totalized nonconvergent integrals. -/
theorem mellinInv_reflection {F : ℂ → ℂ} (c : ℝ)
    (hF : ∀ s : ℂ, F (c - s) = F s) (σ t : ℝ) (ht : 0 < t) :
    mellinInv (c - σ) F t = (t : ℂ) ^ (-(c : ℂ)) * mellinInv σ F t⁻¹ := by
  have hp (s : ℂ) : (t : ℂ) ^ (-(c - s)) =
      (t : ℂ) ^ (-(c : ℂ)) * ((t⁻¹ : ℝ) : ℂ) ^ (-s) := by
    rw [show -((c : ℂ) - s) = -(c : ℂ) + s by ring,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne'),
      ofReal_inv, Complex.inv_cpow_ofReal_nonneg ht.le]
    simp only [Complex.cpow_neg, inv_inv]
  simp only [mellinInv, smul_eq_mul, Complex.real_smul]
  rw [← integral_neg_eq_self (fun y : ℝ =>
    (t : ℂ) ^ (-((c - σ : ℝ) + y * I)) * F ((c - σ : ℝ) + y * I))]
  have he (y : ℝ) : ((c - σ : ℝ) : ℂ) + (-y : ℝ) * I = c - ((σ : ℂ) + y * I) := by
    push_cast
    ring
  simp_rw [he, hF, hp]
  simp only [mul_assoc, integral_const_mul]
  ring

/-! ### The integrated inverse transform -/

/-- For `sigma<1` and `t>0`, integration of an absolutely convergent inverse
Mellin transform gives `integral_0^t mellinInv(sigma,F)(x) dx =
t mellinInv(sigma, s ↦ F(s)/(1-s))(t)`. This justifies the integrated form of
[95, Shintani (1977), equation (1.3), proof of Lemma 1, p. 171]. -/
theorem integral_mellinInv_zero_to {F : ℂ → ℂ} {σ : ℝ}
    (hσ : σ < 1) (hF : VerticalIntegrable F σ) (t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ in 0..t, mellinInv σ F x) =
      (t : ℂ) * mellinInv σ (fun s => F s / (1 - s)) t := by
  simp only [mellinInv, smul_eq_mul, Complex.real_smul]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le ht.le,
    integral_integral_swap (integrable_mellinInv_kernel_prod hσ hF t)]
  have hi (y : ℝ) : (∫ x : ℝ in Ioc 0 t,
      (x : ℂ) ^ (-((σ : ℂ) + y * I)) * F (σ + y * I)) =
      (t : ℂ) * ((t : ℂ) ^ (-((σ : ℂ) + y * I)) *
        (F (σ + y * I) / (1 - ((σ : ℂ) + y * I)))) := by
    rw [integral_mul_const, ← intervalIntegral.integral_of_le ht.le,
      integral_cpow (Or.inl (by simp; linarith))]
    have hn : -((σ : ℂ) + y * I) + 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    rw [Complex.ofReal_zero, Complex.zero_cpow hn, sub_zero,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.cpow_one]
    ring
  simp_rw [hi]
  rw [integral_const_mul]
  ring

end SIC

end
