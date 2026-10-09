/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Mellin.TrigammaInversion
import SICs.SpecialFunctions.Mellin.Summation
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Shintani's first remainder transformation

The first remainder series and its transformation under `t ↦ t⁻¹`.

This file follows [95, Shintani (1977), proof of Lemma 1, p. 171, immediately after
equation (1.3)]. For `t>0`, put `f₁(t)=sum_{n>=1}(psi'(nt)-(nt)⁻¹)`.
The shifted inverse transform (1.3) expresses each summand as `(nt)⁻²` plus an
inverse Mellin integral on `1<Re(s)<2`. Summing the reciprocal squares gives
`pi²/(6t²)`. The integral-series interchange in
`SICs.SpecialFunctions.Mellin.Summation` inserts `zeta(s)` in the other term and
proves convergence of the remainder series at the same time. Thus

```text
f₁(t) = pi²/(6t²) + mellinInv(sigma, zeta(2-s) zeta(s) Gamma(s) Gamma(2-s))(t).
```

The reflection `s ↦ 2-s` preserves the transform. Changing the height variable
from `y` to `-y` therefore gives its inverse-transform reflection and absolute
convergence on the left line. At one, removing both zeta poles gives a holomorphic
product whose reflected derivatives cancel; the full kernel has principal part
`-t⁻¹/(s-1)² + t⁻¹ log(t)/(s-1)`.

The quadratic strip bound for `zeta(s) Gamma(s)` gives vanishing horizontal
integrals. Applying `mellinInv_eq_add_of_double_pole` and reflection yields

```text
f₁(t) + pi²/6 = pi²/(6t²) + t⁻¹ log(t) + t⁻² f₁(t⁻¹).
```

This is the transformation used to prove symmetry of the Barnes coefficient `gamma₂₁`.
All series use `n+1` to index positive integers.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace SIC

/-! ### The remainder series and its inverse transform

The complex-valued trigamma function represents Shintani's function on the positive
real axis. The series definition is total; convergence is asserted only for `t>0`.
-/

/-- Shintani's first remainder sum `f₁(t)=sum_{n>=1}(psi'(nt)-(nt)⁻¹)`.
This is the definition in [95, Shintani (1977), proof of Lemma 1, p. 171,
immediately after equation (1.3)]. Its convergence for `t>0` is part of
`hasSum_trigamma_remainder`. -/
def trigammaRemainderSum (t : ℝ) : ℂ :=
  ∑' n : ℕ, (deriv Complex.digamma (((n + 1 : ℕ) : ℂ) * t) -
    (((n + 1 : ℕ) : ℂ) * t)⁻¹)

/-- The first remainder transform `H(s)=ζ(2-s)ζ(s)Γ(s)Γ(2-s)` in
[95, Shintani (1977), proof of Lemma 1, p. 171, first display for `f₁`]. -/
def trigammaRemainderMellinTransform (s : ℂ) : ℂ :=
  riemannZeta (2 - s) * riemannZeta s * Complex.Gamma s * Complex.Gamma (2 - s)

/-- The first remainder transform satisfies `H(2-s)=H(s)`. -/
theorem trigammaRemainderMellinTransform_reflect (s : ℂ) :
    trigammaRemainderMellinTransform (2 - s) = trigammaRemainderMellinTransform s := by
  simp only [trigammaRemainderMellinTransform, sub_sub_cancel]
  ring

/-- The transform `zeta(2-s) zeta(s) Gamma(s) Gamma(2-s)` is absolutely
integrable on `0<Re(s)=sigma<2`, `sigma≠1`. On the right this follows from
`verticalIntegrable_trigamma_mellin` and the Dirichlet-series bound for `zeta(s)`;
reflection `s ↦ 2-s` gives the left line used in Shintani's contour shift. -/
theorem verticalIntegrable_trigamma_remainder_mellin (σ : ℝ)
    (hσ : 0 < σ) (hσ2 : σ < 2) (hσ1 : σ ≠ 1) :
    VerticalIntegrable trigammaRemainderMellinTransform σ := by
  have hr (x : ℝ) (hx1 : 1 < x) (hx2 : x < 2) :
      VerticalIntegrable trigammaRemainderMellinTransform x := by
    simpa only [VerticalIntegrable, trigammaRemainderMellinTransform, mul_assoc, mul_left_comm,
      mul_comm] using
      verticalIntegrable_riemannZeta_mul hx1
        (verticalIntegrable_trigamma_mellin x (by linarith) hx2 hx1.ne')
  rcases lt_or_gt_of_ne hσ1 with hleft | hright
  · have hi := (hr (2 - σ) (by linarith) (by linarith)).comp_neg
    apply hi.congr
    filter_upwards with y
    have he : ((2 - σ : ℝ) : ℂ) + (-y : ℝ) * I = 2 - ((σ : ℂ) + y * I) := by
      push_cast
      ring
    simpa only [he] using trigammaRemainderMellinTransform_reflect ((σ : ℂ) + y * I)
  · exact hr σ hright hσ2

/-- The dilated reciprocal squares sum to `pi²/(6t²)`.
This specializes Mathlib's evaluation `hasSum_zeta_two` for
`hasSum_trigamma_remainder`. -/
private lemma hasSum_nat_mul_inv_sq (t : ℝ) :
    HasSum (fun n : ℕ => (((n + 1 : ℕ) : ℂ) * t)⁻¹ ^ 2)
      ((Real.pi : ℂ) ^ 2 / (6 * (t : ℂ) ^ 2)) := by
  have hreal : HasSum (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2)
      (Real.pi ^ 2 / 6) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  have hsq : HasSum (fun n : ℕ => (((n + 1 : ℕ) : ℂ)⁻¹ ^ 2))
      ((Real.pi : ℂ) ^ 2 / 6) := by
    have h := Complex.hasSum_ofReal.mpr hreal
    push_cast at h
    simpa only [one_div, inv_pow, Nat.cast_add, Nat.cast_one] using h
  convert! hsq.mul_right ((t : ℂ)⁻¹ ^ 2) using 1
  · ext n
    simp [mul_pow, mul_comm]
  · simp only [div_eq_mul_inv, mul_inv, inv_pow]
    ring

/-- Each trigamma correction is its shifted inverse Mellin transform plus `(nt)⁻²`.
This rearranges `trigamma_sub_inv_sq_eq_mellinInv_add_inv` for
`hasSum_trigamma_remainder`. -/
private lemma trigamma_remainder_term (σ : ℝ) (hσ1 : 1 < σ) (hσ2 : σ < 2)
    (t : ℝ) (ht : 0 < t) (n : ℕ) :
    deriv Complex.digamma (((n + 1 : ℕ) : ℂ) * t) - (((n + 1 : ℕ) : ℂ) * t)⁻¹ =
      (((n + 1 : ℕ) : ℂ) * t)⁻¹ ^ 2 +
        mellinInv σ (fun s => riemannZeta (2 - s) * Complex.Gamma s *
          Complex.Gamma (2 - s)) (((n + 1 : ℕ) : ℝ) * t) := by
  have h := trigamma_sub_inv_sq_eq_mellinInv_add_inv σ hσ1 hσ2
    (((n + 1 : ℕ) : ℝ) * t) (mul_pos (by positivity) ht)
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at h
  linear_combination h

/-- The series `sum_{n>=1}(psi'(nt)-(nt)⁻¹)` converges to
`pi²/(6t²) + mellinInv(sigma, zeta(2-s) zeta(s) Gamma(s) Gamma(2-s))(t)`
for `t>0` and `1<sigma<2`. This is [95, Shintani (1977), proof of Lemma 1,
p. 171, first equality for `f₁` after equation (1.3)], including convergence. -/
theorem hasSum_trigamma_remainder (σ : ℝ) (hσ1 : 1 < σ) (hσ2 : σ < 2)
    (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ => deriv Complex.digamma (((n + 1 : ℕ) : ℂ) * t) -
      (((n + 1 : ℕ) : ℂ) * t)⁻¹)
      ((Real.pi : ℂ) ^ 2 / (6 * (t : ℂ) ^ 2) + mellinInv σ
        (fun s => trigammaRemainderMellinTransform s) t) := by
  have hm := hasSum_mellinInv_nat_mul hσ1
    (verticalIntegrable_trigamma_mellin σ (by linarith) hσ2 hσ1.ne') t ht
  simpa only [trigammaRemainderMellinTransform, mul_assoc, mul_left_comm, mul_comm] using
    ((hasSum_nat_mul_inv_sq t).add hm).congr_fun (trigamma_remainder_term σ hσ1 hσ2 t ht)

/-- The inverse Mellin representation of `f₁(t)`, as a value of `trigammaRemainderSum`.
This is the sum identity from `hasSum_trigamma_remainder`. -/
theorem trigammaRemainderSum_eq_mellinInv (σ : ℝ) (hσ1 : 1 < σ) (hσ2 : σ < 2)
    (t : ℝ) (ht : 0 < t) :
    trigammaRemainderSum t = (Real.pi : ℂ) ^ 2 / (6 * (t : ℂ) ^ 2) +
      mellinInv σ trigammaRemainderMellinTransform t :=
  (hasSum_trigamma_remainder σ hσ1 hσ2 t ht).tsum_eq

/-! ### Reflection of the inverse transform

Changing the height variable from `y` to `-y` sends the line `Re(s)=2-sigma`
to the reflection of `Re(s)=sigma`. The transform is unchanged, while
`t^(-s)` becomes `t⁻² (t⁻¹)^(-s)`. This is the third equality for `f₁`
in [95, Shintani (1977), proof of Lemma 1, p. 171].
-/

/-- For `t>0`, reflection of the remainder's inverse transform gives
`mellinInv(2-sigma,F)(t)=t⁻² mellinInv(sigma,F)(t⁻¹)`, where
`F(s)=zeta(2-s) zeta(s) Gamma(s) Gamma(2-s)`.
This is [95, Shintani (1977), proof of Lemma 1, p. 171, third equality for `f₁`
after equation (1.3)]. The identity also holds for totalized nonconvergent integrals. -/
theorem mellinInv_trigamma_remainder_reflection (σ : ℝ) (t : ℝ) (ht : 0 < t) :
    mellinInv (2 - σ) trigammaRemainderMellinTransform t =
    (t : ℂ)⁻¹ ^ 2 * mellinInv σ trigammaRemainderMellinTransform t⁻¹ := by
  simpa [Complex.cpow_neg, inv_pow] using
    mellinInv_reflection 2 trigammaRemainderMellinTransform_reflect σ t ht

/-! ### The double pole at one

Write `Z(s)=(s-1) zeta(s)`, filling its removable value at one by `Z(1)=1`.
The function `Z(s) Z(2-s) Gamma(s) Gamma(2-s)` is holomorphic near one,
with value one and derivative zero there: the derivatives of each reflected pair cancel.
Consequently the full kernel has principal part
`-t⁻¹/(s-1)² + t⁻¹ log(t)/(s-1)`. This is the local calculation behind
the second equality for `f₁` in [95, Shintani (1977), proof of Lemma 1, p. 171].
-/

/-- Multiplying the remainder kernel by `(s-1)²` gives the holomorphic
expression `-Z(s) Z(2-s) Gamma(s) Gamma(2-s) t^(-s)` away from one.
This identifies the divided difference in `tendsto_trigamma_remainder_mellin_residue`. -/
private lemma trigamma_remainder_mellin_regularized (s : ℂ) (hs : s ≠ 1) (t : ℝ) :
    (s - 1) ^ 2 * (trigammaRemainderMellinTransform s * (t : ℂ) ^ (-s)) =
      -(riemannZeta₁ s * riemannZeta₁ (2 - s) *
        Complex.Gamma s * Complex.Gamma (2 - s) * (t : ℂ) ^ (-s)) := by
  unfold trigammaRemainderMellinTransform
  have hs' : 2 - s ≠ 1 := by intro h; apply hs; linear_combination -h
  rw [riemannZeta_eq_inv_sub_mul hs, riemannZeta_eq_inv_sub_mul hs',
    show (2 : ℂ) - s - 1 = -(s - 1) by ring]
  field_simp

/-- The derivative at one of the regularized kernel is `t⁻¹ log(t)`.
The reflected zeta and gamma derivatives cancel, leaving the derivative of `t^(-s)`.
This supplies `tendsto_trigamma_remainder_mellin_residue`. -/
private lemma hasDerivAt_trigamma_remainder_mellin_regularized (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℂ => -(riemannZeta₁ s * riemannZeta₁ (2 - s) *
      Complex.Gamma s * Complex.Gamma (2 - s) * (t : ℂ) ^ (-s)))
      ((t : ℂ)⁻¹ * Real.log t) 1 := by
  have hz := (differentiable_riemannZeta₁ 1).hasDerivAt
  have hg := Complex.differentiableAt_Gamma_one.hasDerivAt
  have hd : HasDerivAt (fun s : ℂ => 2 - s) (-1) 1 := by
    simpa using (hasDerivAt_id (1 : ℂ)).const_sub 2
  have hz' := (show HasDerivAt riemannZeta₁ (deriv riemannZeta₁ 1) (2 - 1) by
    convert! hz using 1; norm_num).comp 1 hd
  have hg' := (show HasDerivAt Complex.Gamma (deriv Complex.Gamma 1) (2 - 1) by
    convert! hg using 1; norm_num).comp 1 hd
  have hp := (hasDerivAt_id (1 : ℂ)).neg.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr ht.ne'))
  convert! (((hz.mul hz').mul hg).mul hg').mul hp |>.neg using 1
  norm_num [Complex.cpow_neg_one, Complex.ofReal_log ht.le]

/-- After removing the double-pole term `-t⁻¹/(s-1)²`, the residue of
`zeta(2-s) zeta(s) Gamma(s) Gamma(2-s) t^(-s)` at one is `t⁻¹ log(t)` for `t>0`.
This gives the pole contribution in [95, Shintani (1977), proof of Lemma 1,
p. 171, second equality for `f₁` after equation (1.3)]. -/
theorem tendsto_trigamma_remainder_mellin_residue (t : ℝ) (ht : 0 < t) :
    Tendsto (fun s : ℂ => (s - 1) *
      (trigammaRemainderMellinTransform s * (t : ℂ) ^ (-s) - (-(t : ℂ)⁻¹) / (s - 1) ^ 2))
      (𝓝[≠] 1) (𝓝 ((t : ℂ)⁻¹ * Real.log t)) := by
  apply (hasDerivAt_trigamma_remainder_mellin_regularized t ht).tendsto_slope.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ 1 := hs
  simp only [slope, vsub_eq_sub, smul_eq_mul]
  simp only [riemannZeta₁_one,
    show (2 : ℂ) - 1 = 1 by norm_num,
    Complex.Gamma_one, one_mul, mul_one, Complex.cpow_neg_one]
  rw [← trigamma_remainder_mellin_regularized s hs1 t]
  field_simp

/-! ### The contour shift and first remainder transformation

The product `zeta(s) Gamma(s)` decays quadratically on every closed strip in
the right half-plane. Applying this at both `s` and `2-s` gives uniform decay
for the remainder kernel and vanishing horizontal integrals. The double-pole
contour theorem then contributes `t⁻¹ log(t)`. Reflection of the left line,
followed by the already proved inverse representation, gives the transformation
of `f₁` in [95, Shintani (1977), proof of Lemma 1, p. 171].
-/

/-- For `0<a≤Re(s)≤b<2` and `|Im(s)|≥1`, the remainder transform satisfies
`|zeta(2-s) zeta(s) Gamma(s) Gamma(2-s)| ≤ C/(1+Im(s)²)`.
This specializes `exists_norm_zeta_mul_Gamma_mul_reflected_le` at `c = 2` and
supplies the horizontal limit in `tendsto_integral_trigamma_remainder_horizontal`. -/
theorem exists_norm_trigamma_remainder_mellin_le (a b : ℝ) (ha : 0 < a) (hb : b < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖trigammaRemainderMellinTransform s‖ ≤
        C / (1 + s.im ^ 2) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_norm_zeta_mul_Gamma_mul_reflected_le 2 a b (by linarith) (by linarith)
  refine ⟨C, hC0, fun s hsa hsb hsi => ?_⟩
  rw [show trigammaRemainderMellinTransform s =
      (riemannZeta s * Complex.Gamma s) *
        (riemannZeta (2 - s) * Complex.Gamma (2 - s)) by
    unfold trigammaRemainderMellinTransform
    ring]
  exact hC s hsa hsb hsi

/-- For `t>0` and `0<a≤b<2`, the horizontal integrals of
`zeta(2-s) zeta(s) Gamma(s) Gamma(2-s) t^(-s)` tend to zero as `|Im(s)|→∞`.
This supplies the horizontal-contour limit in [95, Shintani (1977), proof of
Lemma 1, p. 171, second equality for `f₁`]. -/
theorem tendsto_integral_trigamma_remainder_horizontal
    (a b : ℝ) (ha : 0 < a) (hb : b < 2) (hab : a ≤ b) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun y : ℝ => ∫ x : ℝ in a..b,
      trigammaRemainderMellinTransform (x + y * I) *
        (t : ℂ) ^ (-(x + y * I))) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_norm_trigamma_remainder_mellin_le a b ha hb
  apply tendsto_integral_horizontal_mul_cpow
    (fun s => trigammaRemainderMellinTransform s) a b C _ t ht
  intro s hs hsi
  rw [uIcc_of_le hab] at hs
  exact hC s hs.1 hs.2 hsi

/-- The remainder kernel is holomorphic on `0<Re(s)<2` away from one.
This multiplies `differentiableAt_trigamma_mellin_kernel` by the extra zeta
factor, for `mellinInv_trigamma_remainder_shift`. -/
private lemma differentiableAt_remainder_mellin_kernel (s : ℂ)
    (hs : 0 < s.re) (hs2 : s.re < 2) (hs1 : s ≠ 1) (t : ℝ) (ht : 0 < t) :
    DifferentiableAt ℂ (fun s => trigammaRemainderMellinTransform s * (t : ℂ) ^ (-s)) s := by
  unfold trigammaRemainderMellinTransform
  convert! (differentiableAt_trigamma_mellin_kernel s hs hs2 hs1 t ht).mul
    (differentiableAt_riemannZeta hs1) using 1
  ext z
  dsimp only [Pi.mul_apply]
  ring

/-- For `0<a<1<b<2`, the remainder's inverse transforms satisfy
`mellinInv(b,F)(t)=mellinInv(a,F)(t)+t⁻¹ log(t)`.
This is the double-pole contour comparison used in `trigammaRemainderSum_add_eq`. -/
private lemma mellinInv_trigamma_remainder_shift (a b : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hb1 : 1 < b) (hb : b < 2) (t : ℝ) (ht : 0 < t) :
    mellinInv b trigammaRemainderMellinTransform t =
    mellinInv a trigammaRemainderMellinTransform t + (t : ℂ)⁻¹ * Real.log t := by
  apply mellinInv_eq_add_of_double_pole trigammaRemainderMellinTransform a b 1
    (-(t : ℂ)⁻¹) ((t : ℂ)⁻¹ * Real.log t) ha1 hb1 t ht
  · intro s hsa hsb hs1
    simpa using differentiableAt_remainder_mellin_kernel s
      (ha.trans_le hsa) (hsb.trans_lt hb) (by simpa using hs1) 1 zero_lt_one
  · simpa using tendsto_trigamma_remainder_mellin_residue t ht
  · exact verticalIntegrable_trigamma_remainder_mellin a ha (by linarith) ha1.ne
  · exact verticalIntegrable_trigamma_remainder_mellin b (by linarith) hb hb1.ne'
  · exact tendsto_integral_trigamma_remainder_horizontal a b ha hb (by linarith) t ht

/-- Shintani's first remainder transformation, for `t>0`:
`f₁(t)+pi²/6 = pi²/(6t²)+t⁻¹ log(t)+t⁻² f₁(t⁻¹)`.
This is [95, Shintani (1977), proof of Lemma 1, p. 171, identity
immediately before the derivation of the second remainder transformation]. -/
theorem trigammaRemainderSum_add_eq (t : ℝ) (ht : 0 < t) :
    trigammaRemainderSum t + (Real.pi : ℂ) ^ 2 / 6 =
      (Real.pi : ℂ) ^ 2 / (6 * (t : ℂ) ^ 2) +
        (t : ℂ)⁻¹ * Real.log t + (t : ℂ)⁻¹ ^ 2 * trigammaRemainderSum t⁻¹ := by
  rw [trigammaRemainderSum_eq_mellinInv (3 / 2) (by norm_num) (by norm_num) t ht,
    trigammaRemainderSum_eq_mellinInv (3 / 2) (by norm_num) (by norm_num) t⁻¹ (inv_pos.mpr ht),
    mellinInv_trigamma_remainder_shift (2 - 3 / 2) (3 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) t ht,
    mellinInv_trigamma_remainder_reflection (3 / 2) t ht]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
  ring

end SIC

end
