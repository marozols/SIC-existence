/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Mellin.DigammaInversion
import SICs.SpecialFunctions.Mellin.Summation

/-!
# Shintani's second remainder transformation

The second remainder series and Shintani's equation (1.4).

This file follows [95, Shintani (1977), proof of Lemma 1, equation (1.4), p. 171].
For `t>0`, put `f₂(t)=sum_{n>=1}(psi(nt)-log(nt)+(2nt)⁻¹)`.
The integrated trigamma inversion expresses each summand as an inverse Mellin
transform on `1<Re(s)<2`. Absolute convergence permits summing the dilations,
inserting `zeta(s)` into the transform. We use Shintani's integration variable
minus one, so the resulting kernel is
`H(s)=-zeta(s) zeta(1-s) Gamma(s) Gamma(1-s)`.

The reflection `s ↦ 1-s` preserves `H`. Shifting from `1<Re(s)<2` to
`-1<Re(s)<0` crosses double poles at zero and one. Their principal parts follow
from the regularized zeta function, `zeta(0)=-1/2`, `zeta'(0)=-log(2pi)/2`,
and cancellation of the reflected gamma derivatives. Uniform quadratic decay
justifies the shifts; reflection of the resulting line yields equation (1.4).
-/

noncomputable section

open Complex Real Filter MeasureTheory Set
open scoped Topology

namespace SIC

/-! ### The series and its inverse representation -/

/-- Shintani's second remainder `f₂(t)=sum_{n>=1}(psi(nt)-log(nt)+(2nt)⁻¹)`.
This is [95, Shintani (1977), proof of Lemma 1, p. 171, definition before (1.4)].
Its convergence for positive `t` is part of `hasSum_digamma_remainder`. -/
def digammaRemainderSum (t : ℝ) : ℂ :=
  ∑' n : ℕ, (Complex.digamma (((n + 1 : ℕ) : ℂ) * t) -
    Complex.log (((n + 1 : ℕ) : ℂ) * t) + (((n + 1 : ℕ) : ℂ) * t)⁻¹ / 2)

/-- The second remainder transform `H(s)=zeta(s)D(s)`.
This is the summed kernel in [95, Shintani (1977), proof of Lemma 1, p. 171,
first display for `f₂`], with Shintani's integration variable replaced by `s+1`. -/
def digammaRemainderMellinTransform (s : ℂ) : ℂ :=
  riemannZeta s * digammaMellinTransform s

/-- The second remainder series converges to `mellinInv(sigma,H)(t)` for
`t>0` and `1<sigma<2`. This is [95, Shintani (1977), proof of Lemma 1,
p. 171, first equality for `f₂` before (1.4)], including absolute convergence. -/
theorem hasSum_digamma_remainder (σ : ℝ) (hσ1 : 1 < σ) (hσ2 : σ < 2)
    (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ => Complex.digamma (((n + 1 : ℕ) : ℂ) * t) -
      Complex.log (((n + 1 : ℕ) : ℂ) * t) + (((n + 1 : ℕ) : ℂ) * t)⁻¹ / 2)
      (mellinInv σ digammaRemainderMellinTransform t) := by
  have h := hasSum_mellinInv_nat_mul hσ1
    (verticalIntegrable_digammaMellinTransform σ (by linarith) hσ2
      (by linarith) hσ1.ne') t ht
  apply h.congr_fun
  intro n
  simpa using (mellinInv_digamma_sub_log_add_half_inv σ hσ1 hσ2
    (((n + 1 : ℕ) : ℝ) * t) (mul_pos (by positivity) ht)).symm

/-- The inverse representation of `digammaRemainderSum`, extracted from
`hasSum_digamma_remainder`. -/
theorem digammaRemainderSum_eq_mellinInv (σ : ℝ) (hσ1 : 1 < σ) (hσ2 : σ < 2)
    (t : ℝ) (ht : 0 < t) :
    digammaRemainderSum t = mellinInv σ digammaRemainderMellinTransform t :=
  (hasSum_digamma_remainder σ hσ1 hσ2 t ht).tsum_eq

/-! ### Reflection and convergence of the transform -/

/-- The second remainder kernel satisfies `H(1-s)=H(s)`.
This algebraic symmetry supplies its inverse-transform reflection. -/
theorem digammaRemainderMellinTransform_reflect (s : ℂ) :
    digammaRemainderMellinTransform (1 - s) = digammaRemainderMellinTransform s := by
  simp only [digammaRemainderMellinTransform, digammaMellinTransform, sub_sub_cancel]
  ring

/-- For `t>0`, `t^(-(1-s))=t⁻¹(t⁻¹)^(-s)`.
This supplies `mellinInv_digamma_remainder_reflection` and the reflected residue. -/
private lemma cpow_reflected_digamma_kernel (t : ℝ) (ht : 0 < t) (s : ℂ) :
    (t : ℂ) ^ (-(1 - s)) = (t : ℂ)⁻¹ * ((t⁻¹ : ℝ) : ℂ) ^ (-s) := by
  rw [show -(1 - s) = (-1 : ℂ) + s by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne'),
    ofReal_inv, Complex.inv_cpow_ofReal_nonneg ht.le]
  simp only [Complex.cpow_neg, Complex.cpow_one, inv_inv]

/-- Reflection of the second remainder integral gives
`mellinInv(1-sigma,H)(t)=t⁻¹ mellinInv(sigma,H)(t⁻¹)` for `t>0`.
This is the reflection used in [95, Shintani (1977), proof of Lemma 1,
p. 171, passage from the second display for `f₂` to equation (1.4)]. -/
theorem mellinInv_digamma_remainder_reflection (σ : ℝ) (t : ℝ) (ht : 0 < t) :
    mellinInv (1 - σ) digammaRemainderMellinTransform t =
      (t : ℂ)⁻¹ * mellinInv σ digammaRemainderMellinTransform t⁻¹ := by
  simpa [Complex.cpow_neg_one] using
    mellinInv_reflection 1 digammaRemainderMellinTransform_reflect σ t ht

/-- The second remainder transform is holomorphic for `-1<Re(s)<2` away
from zero and one. This supplies the contour shifts for `f₂`. -/
private lemma differentiableAt_digammaRemainderMellinTransform (s : ℂ)
    (hs : -1 < s.re) (hs2 : s.re < 2) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ digammaRemainderMellinTransform s :=
  (differentiableAt_riemannZeta hs1).mul
    (differentiableAt_digammaMellinTransform s hs hs2 hs0 hs1)

/-- The bound `|H(s)|≤C/(1+Im(s)²)` holds on every closed strip
`-1<a≤Re(s)≤b<2` at `|Im(s)|≥1`. This supplies absolute convergence and
the horizontal limits in Shintani's contour transformation of `f₂`. It is the
`c = 1` specialization of `exists_norm_zeta_mul_Gamma_mul_reflected_le`. -/
theorem exists_norm_digammaRemainderMellinTransform_le (a b : ℝ)
    (ha : -1 < a) (hb : b < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖digammaRemainderMellinTransform s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_norm_zeta_mul_Gamma_mul_reflected_le 1 a b ha (by linarith)
  refine ⟨C, hC0, fun s hsa hsb hsi => ?_⟩
  simpa [digammaRemainderMellinTransform, digammaMellinTransform, mul_assoc,
    mul_left_comm] using hC s hsa hsb hsi

/-- The transform `H` is absolutely integrable on `-1<sigma<2`, `sigma≠0,1`.
This supplies the vertical hypotheses for both remainder contour shifts. -/
theorem verticalIntegrable_digammaRemainderMellinTransform (σ : ℝ)
    (hσ : -1 < σ) (hσ2 : σ < 2) (hσ0 : σ ≠ 0) (hσ1 : σ ≠ 1) :
    VerticalIntegrable digammaRemainderMellinTransform σ := by
  obtain ⟨C, _, hC⟩ := exists_norm_digammaRemainderMellinTransform_le σ σ hσ hσ2
  apply verticalIntegrable_of_quadratic_decay digammaRemainderMellinTransform σ C
  · apply continuous_iff_continuousAt.mpr
    intro y
    apply (differentiableAt_digammaRemainderMellinTransform (σ + y * I)
      (by simpa) (by simpa) (by
        intro h; apply hσ0; simpa using congrArg Complex.re h) (by
        intro h; apply hσ1; simpa using congrArg Complex.re h)).continuousAt.comp
      (f := fun y : ℝ => (σ : ℂ) + y * I)
    fun_prop
  · intro y hy
    simpa using hC (σ + y * I) (by simp) (by simp) (by simpa)

/-! ### The double poles at zero and one

The regularized integrated kernel has value one and derivative `-gamma-log(t)`
at zero. Multiplication by `zeta(s)` gives leading coefficient `-1/2` and
residue `(log(t)+gamma-log(2pi))/2`. Reflecting `s ↦ 1-s` gives the pole at
one, with leading coefficient `-1/(2t)` and residue
`(log(t)-gamma+log(2pi))/(2t)`.
-/

/-- The derivative of `s²H(s)t^(-s)` at zero, evaluated using the regularized
expression. This supplies `tendsto_digamma_remainder_residue_zero`. -/
private lemma hasDerivAt_digamma_remainder_regularized_zero (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℂ => riemannZeta s * (riemannZeta₁ (1 - s) *
      Complex.Gamma (s + 1) * Complex.Gamma (1 - s) * (t : ℂ) ^ (-s)))
      (((Real.log t : ℂ) + Real.eulerMascheroniConstant - Complex.log (2 * Real.pi)) / 2)
      0 := by
  have hz := (differentiableAt_riemannZeta (by norm_num : (0 : ℂ) ≠ 1)).hasDerivAt
  rw [deriv_riemannZeta_zero] at hz
  convert! hz.mul (hasDerivAt_digammaMellinTransform_regularized_zero t ht) using 1
  norm_num [riemannZeta_zero]
  ring

/-- The pole of `H(s)t^(-s)` at zero has principal part
`-1/(2s²)+(log(t)+gamma-log(2pi))/(2s)`.
This is the zero-pole contribution in [95, Shintani (1977), proof of Lemma 1,
p. 171, second equality for `f₂` before (1.4)], in the translated variable. -/
theorem tendsto_digamma_remainder_residue_zero (t : ℝ) (ht : 0 < t) :
    Tendsto (fun s : ℂ => s * (digammaRemainderMellinTransform s * (t : ℂ) ^ (-s) -
      (-1 / 2) / s ^ 2)) (𝓝[≠] 0)
      (𝓝 (((Real.log t : ℂ) + Real.eulerMascheroniConstant - Complex.log (2 * Real.pi)) / 2)) := by
  apply (hasDerivAt_digamma_remainder_regularized_zero t ht).tendsto_slope.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := hs
  simp only [slope, vsub_eq_sub, smul_eq_mul, sub_zero, zero_add, neg_zero,
    riemannZeta_zero, riemannZeta₁_one, Complex.Gamma_one, Complex.cpow_zero, mul_one]
  rw [← digammaMellinTransform_regularized_zero s hs0 t, digammaRemainderMellinTransform]
  field_simp

/-- Reflection maps the punctured neighborhood of one to that of zero.
This supplies the change of variable in `tendsto_digamma_remainder_residue_one`. -/
private lemma tendsto_one_sub_nhds_ne_zero :
    Tendsto (fun s : ℂ => 1 - s) (𝓝[≠] 1) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Tendsto (fun s : ℂ => 1 - s) (𝓝 1) (𝓝 (1 - 1)) :=
      tendsto_const_nhds.sub tendsto_id
    simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    change 1 - s ≠ 0
    exact sub_ne_zero.mpr (show s ≠ 1 from hs).symm

/-- The pole of `H(s)t^(-s)` at one has principal part
`-1/(2t(s-1)²)+(log(t)-gamma+log(2pi))/(2t(s-1))`.
This is the one-pole contribution in [95, Shintani (1977), proof of Lemma 1,
p. 171, second equality for `f₂` before (1.4)], in the translated variable. -/
theorem tendsto_digamma_remainder_residue_one (t : ℝ) (ht : 0 < t) :
    Tendsto (fun s : ℂ => (s - 1) *
      (digammaRemainderMellinTransform s * (t : ℂ) ^ (-s) - (-(t : ℂ)⁻¹ / 2) / (s - 1) ^ 2))
      (𝓝[≠] 1) (𝓝 ((t : ℂ)⁻¹ *
        ((Real.log t : ℂ) - Real.eulerMascheroniConstant + Complex.log (2 * Real.pi)) / 2)) := by
  have h := ((tendsto_digamma_remainder_residue_zero t⁻¹ (inv_pos.mpr ht)).comp
    tendsto_one_sub_nhds_ne_zero).const_mul (-(t : ℂ)⁻¹)
  rw [Real.log_inv, Complex.ofReal_neg] at h
  convert! h.congr' ?_ using 1
  · congr 1
    ring
  filter_upwards with s
  dsimp only [Function.comp_def]
  rw [digammaRemainderMellinTransform_reflect,
    show (t : ℂ) ^ (-s) = (t : ℂ)⁻¹ * ((t⁻¹ : ℝ) : ℂ) ^ (-(1 - s)) by
      simpa using cpow_reflected_digamma_kernel t ht (1 - s),
    show ((1 : ℂ) - s) ^ 2 = (s - 1) ^ 2 by ring]
  ring

/-! ### Contour shifts and equation (1.4)

Split the contour shift at a line between zero and one, adding the two residues.
Reflection of the leftmost line turns its integral into `t⁻¹ f₂(t⁻¹)`.
Rearranging the elementary terms gives Shintani's second remainder transformation.
-/

/-- The horizontal integrals of `H(s)t^(-s)` vanish on closed strips
`-1<a≤b<2`, for `t>0`. This supplies both remainder contour shifts. -/
private lemma tendsto_integral_digamma_remainder_horizontal (a b : ℝ)
    (ha : -1 < a) (hb : b < 2) (hab : a ≤ b) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun y : ℝ => ∫ x : ℝ in a..b,
      digammaRemainderMellinTransform (x + y * I) * (t : ℂ) ^ (-(x + y * I)))
      (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_norm_digammaRemainderMellinTransform_le a b ha hb
  apply tendsto_integral_horizontal_mul_cpow
    digammaRemainderMellinTransform a b C _ t ht
  intro s hs hsi
  rw [uIcc_of_le hab] at hs
  exact hC s hs.1 hs.2 hsi

/-- The zero-pole shift adds `(log(t)+gamma-log(2pi))/2` to the inverse
transform. This supplies the first residue in `digammaRemainderSum_add_eq`. -/
private lemma mellinInv_digamma_remainder_shift_zero (a b : ℝ)
    (ha : -1 < a) (ha0 : a < 0) (hb0 : 0 < b) (hb : b < 1) (t : ℝ) (ht : 0 < t) :
    mellinInv b digammaRemainderMellinTransform t =
      mellinInv a digammaRemainderMellinTransform t +
        ((Real.log t : ℂ) + Real.eulerMascheroniConstant - Complex.log (2 * Real.pi)) / 2 := by
  apply mellinInv_eq_add_of_double_pole digammaRemainderMellinTransform a b 0 (-1 / 2)
    _ ha0 hb0 t ht
  · intro s hsa hsb hs0
    apply differentiableAt_digammaRemainderMellinTransform s (by linarith) (by linarith)
      (by simpa using hs0)
    intro h
    have := congrArg Complex.re h
    simp only [one_re] at this
    linarith
  · simpa using tendsto_digamma_remainder_residue_zero t ht
  · exact verticalIntegrable_digammaRemainderMellinTransform a ha (by linarith)
      ha0.ne (by linarith)
  · exact verticalIntegrable_digammaRemainderMellinTransform b (by linarith) (by linarith)
      hb0.ne' hb.ne
  · exact tendsto_integral_digamma_remainder_horizontal a b ha (by linarith)
      (by linarith) t ht

/-- The one-pole shift adds `(log(t)-gamma+log(2pi))/(2t)` to the inverse
transform. This supplies the second residue in `digammaRemainderSum_add_eq`. -/
private lemma mellinInv_digamma_remainder_shift_one (a b : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hb1 : 1 < b) (hb : b < 2) (t : ℝ) (ht : 0 < t) :
    mellinInv b digammaRemainderMellinTransform t =
      mellinInv a digammaRemainderMellinTransform t + (t : ℂ)⁻¹ *
        ((Real.log t : ℂ) - Real.eulerMascheroniConstant + Complex.log (2 * Real.pi)) / 2 := by
  apply mellinInv_eq_add_of_double_pole digammaRemainderMellinTransform a b 1
    (-(t : ℂ)⁻¹ / 2) _ ha1 hb1 t ht
  · intro s hsa hsb hs1
    apply differentiableAt_digammaRemainderMellinTransform s (by linarith) (by linarith)
      _ (by simpa using hs1)
    intro h
    simp [h] at hsa
    linarith
  · simpa using tendsto_digamma_remainder_residue_one t ht
  · exact verticalIntegrable_digammaRemainderMellinTransform a (by linarith)
      (by linarith) ha.ne' ha1.ne
  · exact verticalIntegrable_digammaRemainderMellinTransform b (by linarith) hb
      (by linarith) hb1.ne'
  · exact tendsto_integral_digamma_remainder_horizontal a b (by linarith) hb
      (by linarith) t ht

/-- Shintani's second remainder transformation for `t>0`:
`f₂(t)+log(sqrt(2pi))-gamma/2-log(t)/2 =
t⁻¹(f₂(t⁻¹)+log(sqrt(2pi))-gamma/2-log(t⁻¹)/2)`.
This is [95, Shintani (1977), equation (1.4), p. 171]. We write
`log(sqrt(2pi))` as `log(2pi)/2`. -/
@[source "95, equation (1.4), p. 171"]
theorem digammaRemainderSum_add_eq (t : ℝ) (ht : 0 < t) :
    digammaRemainderSum t + Complex.log (2 * Real.pi) / 2 -
        (Real.eulerMascheroniConstant : ℂ) / 2 - (Real.log t : ℂ) / 2 =
      (t : ℂ)⁻¹ * (digammaRemainderSum t⁻¹ + Complex.log (2 * Real.pi) / 2 -
        (Real.eulerMascheroniConstant : ℂ) / 2 - (Real.log t⁻¹ : ℂ) / 2) := by
  rw [digammaRemainderSum_eq_mellinInv (3 / 2) (by norm_num) (by norm_num) t ht,
    digammaRemainderSum_eq_mellinInv (3 / 2) (by norm_num) (by norm_num) t⁻¹ (inv_pos.mpr ht),
    mellinInv_digamma_remainder_shift_one (1 / 2) (3 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) t ht,
    mellinInv_digamma_remainder_shift_zero (1 - 3 / 2) (1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) t ht,
    mellinInv_digamma_remainder_reflection (3 / 2) t ht,
    Real.log_inv, Complex.ofReal_neg]
  ring

end SIC

end
