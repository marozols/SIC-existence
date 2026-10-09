/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Mellin.TrigammaInversion
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# The integrated trigamma inversion and digamma remainder

Integrated trigamma inversion representing `ψ(t)-log t+(2t)⁻¹`.

This file follows [95, Shintani (1977), proof of Lemma 1, p. 171, the two
digamma displays preceding equation (1.4)]. Integrating the first part of
(1.3) from zero to `t` gives `psi(t)+t⁻¹+gamma`. The endpoint at zero is
handled by writing the integrand as `psi'(x+1)`.

We use `s` for Shintani's integration variable minus one. Thus the integrated
transform is `D(s)=-zeta(1-s) Gamma(s) Gamma(1-s)`, its initial line is
`-1<Re(s)<0`, and the final line is `1<Re(s)<2`. Shifting across zero and
one gives the corrected digamma function `psi(t)-log(t)+(2t)⁻¹`.
This is the inverse representation needed to sum the second remainder.
-/

noncomputable section

open Complex Real Filter MeasureTheory Set
open scoped Topology

namespace SIC

/-! ### The integrated form of equation (1.3) -/

/-- The integrated transform `D(s)=-zeta(1-s) Gamma(s) Gamma(1-s)`.
This is the kernel in [95, Shintani (1977), proof of Lemma 1, p. 171,
digamma displays before equation (1.4)], with the integration variable shifted by one. -/
def digammaMellinTransform (s : ℂ) : ℂ :=
  -riemannZeta (1 - s) * Complex.Gamma s * Complex.Gamma (1 - s)

/-- Integrating `psi'(x+1)` from zero to `t` gives `psi(t)+t⁻¹+gamma`.
This supplies the nonsingular endpoint in `mellinInv_digamma_add_inv`. -/
private lemma integral_trigamma_add_one (t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ in 0..t, deriv Complex.digamma ((x : ℂ) + 1)) =
      Complex.digamma t + (t : ℂ)⁻¹ + Real.eulerMascheroniConstant := by
  have ha (x : ℝ) (hx : x ∈ uIcc 0 t) :
      AnalyticAt ℂ Complex.digamma ((x : ℂ) + 1) := by
    rw [uIcc_of_le ht.le] at hx
    apply analyticAt_digamma_of_re_pos
    simp only [add_re, ofReal_re, one_re]
    linarith [hx.1]
  have hd (x : ℝ) (hx : x ∈ uIcc 0 t) :
      HasDerivAt (fun x : ℝ => Complex.digamma ((x : ℂ) + 1))
        (deriv Complex.digamma ((x : ℂ) + 1)) x := by
    simpa using ((ha x hx).differentiableAt.hasDerivAt.comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).add_const 1)).comp_ofReal
  have hc : ContinuousOn (fun x : ℝ => deriv Complex.digamma ((x : ℂ) + 1)) (uIcc 0 t) :=
    fun x hx => ((ha x hx).deriv.continuousAt.comp
      (f := fun x : ℝ => (x : ℂ) + 1) (by fun_prop)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable,
    Complex.ofReal_zero, zero_add, Complex.digamma_one,
    Complex.digamma_apply_add_one _ (fun n hn => by
      have := congrArg Complex.re hn
      simp at this
      have := Nat.cast_nonneg (α := ℝ) n
      linarith)]
  ring

/-- Integration changes Shintani's trigamma kernel to `digammaMellinTransform`
after translating the vertical line by one. This is the algebraic step in
`mellinInv_digamma_add_inv`. -/
private lemma mellinInv_digamma_translate (σ : ℝ) (hσ : σ ≠ 0)
    (t : ℝ) (ht : 0 < t) :
    (t : ℂ) * mellinInv (σ + 1) (fun s =>
      (riemannZeta (2 - s) * Complex.Gamma s * Complex.Gamma (2 - s)) / (1 - s)) t =
      mellinInv σ digammaMellinTransform t := by
  simp only [mellinInv, smul_eq_mul, Complex.real_smul]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  have hs : (σ : ℂ) + y * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    exact hσ (by simpa using this)
  have he : ((σ + 1 : ℝ) : ℂ) + y * I = ((σ : ℂ) + y * I) + 1 := by
    push_cast
    ring
  rw [he, show (2 : ℂ) - (((σ : ℂ) + y * I) + 1) = 1 - ((σ : ℂ) + y * I) by ring,
    Complex.Gamma_add_one _ hs,
    show -(((σ : ℂ) + y * I) + 1) = -((σ : ℂ) + y * I) + (-1) by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.cpow_neg_one]
  unfold digammaMellinTransform
  rw [show (1 : ℂ) - (((σ : ℂ) + y * I) + 1) = -((σ : ℂ) + y * I) by ring]
  field_simp [hs, Complex.ofReal_ne_zero.mpr ht.ne']

/-- For `t>0` and `-1<sigma<0`,
`mellinInv(sigma,D)(t)=psi(t)+t⁻¹+gamma`.
This is [95, Shintani (1977), proof of Lemma 1, p. 171, first digamma display
after equation (1.3)], with `s` replaced by `s+1`. -/
theorem mellinInv_digamma_add_inv (σ : ℝ) (hσ : -1 < σ) (hσ0 : σ < 0)
    (t : ℝ) (ht : 0 < t) :
    mellinInv σ digammaMellinTransform t =
      Complex.digamma t + (t : ℂ)⁻¹ + Real.eulerMascheroniConstant := by
  rw [← mellinInv_digamma_translate σ hσ0.ne t ht,
    ← integral_mellinInv_zero_to (by linarith : σ + 1 < 1)
      (verticalIntegrable_trigamma_mellin (σ + 1) (by linarith) (by linarith)
        (by linarith)) t ht,
    ← integral_trigamma_add_one t ht]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x hx
  rw [uIoc_of_le ht.le] at hx
  rw [mellinInv_trigamma_sub_inv_sq _ (by linarith) (by linarith) x hx.1,
    deriv_digamma_add_one_of_re_pos _ (by simpa using hx.1)]

/-! ### Convergence on the strip containing both poles

The completed-zeta and duplication estimate applies to `zeta(1-s) Gamma(1-s)`
throughout `Re(s)<2`. A gamma recurrence bounds the remaining `Gamma(s)`
throughout `Re(s)>-1`. Their product has uniform quadratic decay away from the
real axis, justifying all horizontal and vertical contours below.
-/

/-- Gamma is differentiable for `Re(s)>-1` away from zero. This identifies
the gamma poles that can occur in `digammaMellinTransform`. -/
private lemma differentiableAt_Gamma_of_neg_one_lt (s : ℂ) (hs : -1 < s.re)
    (hs0 : s ≠ 0) : DifferentiableAt ℂ Complex.Gamma s := by
  apply Complex.differentiableAt_Gamma
  intro n hn
  cases n with
  | zero => exact hs0 (by simpa using hn)
  | succ n =>
    have := congrArg Complex.re hn
    simp only [Nat.cast_add, Nat.cast_one, neg_re, add_re, natCast_re, one_re] at this
    have := Nat.cast_nonneg (α := ℝ) n
    linarith

/-- The integrated transform is holomorphic for `-1<Re(s)<2` away from zero
and one. This supplies the regularity assumptions in its two contour shifts. -/
theorem differentiableAt_digammaMellinTransform (s : ℂ) (hs : -1 < s.re)
    (hs2 : s.re < 2) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ digammaMellinTransform s := by
  have hz : 1 - s ≠ 1 := by intro h; apply hs0; linear_combination -h
  have hd : DifferentiableAt ℂ (fun s : ℂ => 1 - s) s :=
    differentiableAt_id.const_sub 1
  exact (((differentiableAt_riemannZeta hz).comp s hd).neg.mul
    (differentiableAt_Gamma_of_neg_one_lt s hs hs0)).mul
      ((differentiableAt_Gamma_of_neg_one_lt (1 - s) (by simp; linarith)
        (sub_ne_zero.mpr hs1.symm)).comp s hd)

/-- On `-1<a≤Re(s)≤b<2` and `|Im(s)|≥1`, the integrated transform satisfies
`|D(s)|≤C/(1+Im(s)²)`. This justifies the contours in
[95, Shintani (1977), proof of Lemma 1, p. 171, digamma displays before (1.4)]. -/
theorem exists_norm_digammaMellinTransform_le (a b : ℝ) (ha : -1 < a) (hb : b < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖digammaMellinTransform s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨Cg, hCg0, hCg⟩ := exists_norm_Gamma_le a b ha
  obtain ⟨Cz, hCz0, hCz⟩ := exists_norm_zeta_mul_Gamma_le (1 - b) (1 - a) (by linarith)
  refine ⟨Cg * Cz, mul_nonneg hCg0 hCz0, fun s hsa hsb hsi => ?_⟩
  have hz : ‖riemannZeta (1 - s) * Complex.Gamma (1 - s)‖ ≤ Cz / (1 + s.im ^ 2) := by
    simpa using hCz (1 - s) (by simp; linarith) (by simp; linarith) (by simpa)
  calc
    _ = ‖Complex.Gamma s‖ * ‖riemannZeta (1 - s) * Complex.Gamma (1 - s)‖ := by
      simp [digammaMellinTransform, mul_comm, mul_left_comm]
    _ ≤ Cg * (Cz / (1 + s.im ^ 2)) :=
      mul_le_mul (hCg s hsa hsb hsi) hz (norm_nonneg _) hCg0
    _ = _ := by ring

/-- The integrated transform is absolutely integrable on every line
`-1<sigma<2`, `sigma≠0,1`. This supplies both sides of its contour shifts. -/
theorem verticalIntegrable_digammaMellinTransform (σ : ℝ) (hσ : -1 < σ)
    (hσ2 : σ < 2) (hσ0 : σ ≠ 0) (hσ1 : σ ≠ 1) :
    VerticalIntegrable digammaMellinTransform σ := by
  obtain ⟨C, _, hC⟩ := exists_norm_digammaMellinTransform_le σ σ hσ hσ2
  apply verticalIntegrable_of_quadratic_decay digammaMellinTransform σ C
  · apply continuous_iff_continuousAt.mpr
    intro y
    apply (differentiableAt_digammaMellinTransform (σ + y * I)
      (by simpa) (by simpa) (by
        intro h; apply hσ0; simpa using congrArg Complex.re h) (by
        intro h; apply hσ1; simpa using congrArg Complex.re h)).continuousAt.comp
      (f := fun y : ℝ => (σ : ℂ) + y * I)
    fun_prop
  · intro y hy
    simpa using hC (σ + y * I) (by simp) (by simp) (by simpa)

/-! ### The two pole contributions

At zero, `s² D(s)=Z(1-s) Gamma(s+1) Gamma(1-s)`, where
`Z(u)=(u-1)zeta(u)` is filled at one. Its value is one and its derivative
is `-gamma`; the two gamma derivatives cancel. Including `t^(-s)` gives
residue `-gamma-log(t)`. At one, the gamma recurrence gives residue `-1/(2t)`.
These are the contributions in Shintani's integrated contour shift on p. 171.
-/

/-- Multiplying `D(s)t^(-s)` by `s²` removes the pole at zero.
This identifies the regular expression used in `tendsto_digammaMellinTransform_residue_zero`
and in the corresponding second-remainder residue. -/
theorem digammaMellinTransform_regularized_zero (s : ℂ) (hs : s ≠ 0) (t : ℝ) :
    s ^ 2 * (digammaMellinTransform s * (t : ℂ) ^ (-s)) =
      riemannZeta₁ (1 - s) * Complex.Gamma (s + 1) * Complex.Gamma (1 - s) *
        (t : ℂ) ^ (-s) := by
  have h : 1 - s ≠ 1 := by intro h; apply hs; linear_combination -h
  rw [digammaMellinTransform, riemannZeta_eq_inv_sub_mul h, Complex.Gamma_add_one s hs]
  rw [show (1 : ℂ) - s - 1 = -s by ring]
  field_simp

/-- The regularized kernel at zero has derivative `-gamma-log(t)`.
This supplies the double-pole residues in `tendsto_digammaMellinTransform_residue_zero`
and, after multiplying by `zeta(s)`, in the second-remainder transformation. -/
theorem hasDerivAt_digammaMellinTransform_regularized_zero (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℂ => riemannZeta₁ (1 - s) * Complex.Gamma (s + 1) *
      Complex.Gamma (1 - s) * (t : ℂ) ^ (-s))
      (-(Real.eulerMascheroniConstant : ℂ) - Real.log t) 0 := by
  have hz : HasDerivAt riemannZeta₁ (Real.eulerMascheroniConstant : ℂ) (1 - 0) := by
    simpa using (differentiable_riemannZeta₁ 1).hasDerivAt
  have hg₁ : HasDerivAt Complex.Gamma (deriv Complex.Gamma 1) ((0 : ℂ) + 1) := by
    simpa using Complex.differentiableAt_Gamma_one.hasDerivAt
  have hg₂ : HasDerivAt Complex.Gamma (deriv Complex.Gamma 1) (1 - (0 : ℂ)) := by
    simpa using Complex.differentiableAt_Gamma_one.hasDerivAt
  have hp := (hasDerivAt_id (0 : ℂ)).neg.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr ht.ne'))
  convert! (((hz.comp 0 ((hasDerivAt_id (0 : ℂ)).const_sub 1)).mul
    (hg₁.comp 0 ((hasDerivAt_id (0 : ℂ)).add_const 1))).mul
    (hg₂.comp 0 ((hasDerivAt_id (0 : ℂ)).const_sub 1))).mul hp using 1
  simp [Complex.ofReal_log ht.le]
  ring

/-- After removing `s⁻²`, the residue of `D(s)t^(-s)` at zero is
`-gamma-log(t)`. This gives the first pole contribution in
[95, Shintani (1977), proof of Lemma 1, p. 171, second digamma display before (1.4)]. -/
theorem tendsto_digammaMellinTransform_residue_zero (t : ℝ) (ht : 0 < t) :
    Tendsto (fun s : ℂ => s *
      (digammaMellinTransform s * (t : ℂ) ^ (-s) - 1 / s ^ 2))
      (𝓝[≠] 0) (𝓝 (-(Real.eulerMascheroniConstant : ℂ) - Real.log t)) := by
  apply (hasDerivAt_digammaMellinTransform_regularized_zero t ht).tendsto_slope.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := hs
  simp only [slope, vsub_eq_sub, smul_eq_mul, sub_zero, zero_add, neg_zero,
    riemannZeta₁_one, Complex.Gamma_one, Complex.cpow_zero, mul_one]
  rw [← digammaMellinTransform_regularized_zero s hs0 t]
  field_simp

/-- The simple pole of `D(s)t^(-s)` at one has residue `-1/(2t)`.
This gives the second pole contribution in
[95, Shintani (1977), proof of Lemma 1, p. 171, second digamma display before (1.4)]. -/
theorem tendsto_digammaMellinTransform_residue_one (t : ℝ) (ht : 0 < t) :
    Tendsto (fun s : ℂ => (s - 1) * digammaMellinTransform s * (t : ℂ) ^ (-s))
      (𝓝[≠] 1) (𝓝 (-(t : ℂ)⁻¹ / 2)) := by
  have hz : ContinuousAt (fun s : ℂ => riemannZeta (1 - s)) 1 :=
    (differentiableAt_riemannZeta (by norm_num : (1 : ℂ) - 1 ≠ 1)).continuousAt.comp
      (f := fun s : ℂ => 1 - s) (by fun_prop)
  have hg : ContinuousAt (fun s : ℂ => Complex.Gamma (2 - s)) 1 := by
    apply (show ContinuousAt Complex.Gamma (2 - (1 : ℂ)) by
      rw [show (2 : ℂ) - 1 = 1 by norm_num]
      exact Complex.continuousAt_Gamma_one).comp
        (f := fun s : ℂ => 2 - s)
    fun_prop
  have hp : ContinuousAt (fun s : ℂ => (t : ℂ) ^ (-s)) 1 :=
    ContinuousAt.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr ht.ne'))
  have hh := (((hz.mul Complex.continuousAt_Gamma_one).mul hg).mul hp).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {(1 : ℂ)}ᶜ))
  simp only [Pi.mul_apply, sub_self, riemannZeta_zero, Complex.Gamma_one,
    show (2 : ℂ) - 1 = 1 by norm_num, mul_one, Complex.cpow_neg_one] at hh
  convert! hh.congr' ?_ using 1
  · congr 1
    ring
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ 1 := hs
  dsimp only [Pi.mul_apply]
  rw [show (2 : ℂ) - s = (1 - s) + 1 by ring,
    Complex.Gamma_add_one _ (sub_ne_zero.mpr hs1.symm), digammaMellinTransform]
  ring

/-! ### Shifting the integrated inverse transform

An intermediate line `0<Re(s)<1` separates the two poles, so the shared
single-pole contour theorem applies twice. The first shift contributes
`-gamma-log(t)` and the second `-1/(2t)`. Substituting the initial integrated
formula leaves precisely the corrected digamma function.
-/

/-- For `t>0`, the horizontal integrals of `D(s)t^(-s)` vanish at both ends
of every closed strip `-1<a≤b<2`. This supplies the horizontal hypotheses
of the two digamma contour shifts. -/
theorem tendsto_integral_digammaMellinTransform_horizontal (a b : ℝ)
    (ha : -1 < a) (hb : b < 2) (hab : a ≤ b) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun y : ℝ => ∫ x : ℝ in a..b,
      digammaMellinTransform (x + y * I) * (t : ℂ) ^ (-(x + y * I)))
      (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_norm_digammaMellinTransform_le a b ha hb
  apply tendsto_integral_horizontal_mul_cpow
    digammaMellinTransform a b C _ t ht
  intro s hs hsi
  rw [uIcc_of_le hab] at hs
  exact hC s hs.1 hs.2 hsi

/-- Shifting across zero adds `-gamma-log(t)` to the integrated inverse
transform. This supplies the first shift in `mellinInv_digamma_sub_log_add_half_inv`. -/
private lemma mellinInv_digamma_shift_zero (a b : ℝ)
    (ha : -1 < a) (ha0 : a < 0) (hb0 : 0 < b) (hb : b < 1) (t : ℝ) (ht : 0 < t) :
    mellinInv b digammaMellinTransform t = mellinInv a digammaMellinTransform t +
      (-(Real.eulerMascheroniConstant : ℂ) - Real.log t) := by
  apply mellinInv_eq_add_of_double_pole digammaMellinTransform a b 0 1 _ ha0 hb0 t ht
  · intro s hsa hsb hs0
    apply differentiableAt_digammaMellinTransform s (by linarith) (by linarith)
      (by simpa using hs0)
    intro h
    have := congrArg Complex.re h
    simp only [one_re] at this
    linarith
  · simpa using tendsto_digammaMellinTransform_residue_zero t ht
  · exact verticalIntegrable_digammaMellinTransform a ha (by linarith) ha0.ne (by linarith)
  · exact verticalIntegrable_digammaMellinTransform b (by linarith) (by linarith) hb0.ne' hb.ne
  · exact tendsto_integral_digammaMellinTransform_horizontal a b ha (by linarith)
      (by linarith) t ht

/-- Shifting across one adds `-1/(2t)` to the integrated inverse transform.
This supplies the second shift in `mellinInv_digamma_sub_log_add_half_inv`. -/
private lemma mellinInv_digamma_shift_one (a b : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hb1 : 1 < b) (hb : b < 2) (t : ℝ) (ht : 0 < t) :
    mellinInv b digammaMellinTransform t = mellinInv a digammaMellinTransform t -
      (t : ℂ)⁻¹ / 2 := by
  rw [sub_eq_add_neg, ← neg_div]
  apply mellinInv_eq_add_of_double_pole digammaMellinTransform a b 1 0 _ ha1 hb1 t ht
  · intro s hsa hsb hs1
    apply differentiableAt_digammaMellinTransform s (by linarith) (by linarith)
      _ (by simpa using hs1)
    intro h
    simp [h] at hsa
    linarith
  · simpa [mul_assoc] using tendsto_digammaMellinTransform_residue_one t ht
  · exact verticalIntegrable_digammaMellinTransform a (by linarith) (by linarith) ha.ne' ha1.ne
  · exact verticalIntegrable_digammaMellinTransform b (by linarith) hb (by linarith) hb1.ne'
  · exact tendsto_integral_digammaMellinTransform_horizontal a b (by linarith) hb
      (by linarith) t ht

/-- For `t>0` and `1<sigma<2`,
`mellinInv(sigma,D)(t)=psi(t)-log(t)+(2t)⁻¹`.
This is [95, Shintani (1977), proof of Lemma 1, p. 171, second digamma display
before equation (1.4)], with the integration variable shifted by one. -/
theorem mellinInv_digamma_sub_log_add_half_inv (σ : ℝ) (hσ1 : 1 < σ) (hσ2 : σ < 2)
    (t : ℝ) (ht : 0 < t) :
    mellinInv σ digammaMellinTransform t =
      Complex.digamma t - Complex.log t + (t : ℂ)⁻¹ / 2 := by
  rw [mellinInv_digamma_shift_one (1 / 2) σ (by norm_num) (by norm_num) hσ1 hσ2 t ht,
    mellinInv_digamma_shift_zero (-(1 / 2)) (1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) t ht,
    mellinInv_digamma_add_inv (-(1 / 2)) (by norm_num) (by norm_num) t ht,
    Complex.ofReal_log ht.le]
  ring

end SIC

end
