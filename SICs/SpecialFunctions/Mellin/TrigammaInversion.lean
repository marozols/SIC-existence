/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.GammaZetaBounds
import SICs.SpecialFunctions.Mellin.TrigammaTransform
import SICs.SpecialFunctions.Mellin.ContourShift
import Mathlib.Analysis.MellinInversion
import SICs.Source

/-!
# Mellin inversion and the first contour shift for the trigamma tail

Both equalities of Shintani's equation (1.3).

This file follows [95, Shintani (1977), proof of Lemma 1, equation (1.3), p. 170].
The forward transform in `hasMellin_trigamma_sub_inv_sq`, together with vertical
absolute convergence, gives the inverse formula on `0<Re(s)<1`.

To prepare the shift to `1<Re(s)<2`, the gamma and completed-zeta estimates of
`SICs.SpecialFunctions.GammaZetaBounds` give quadratic decay for
`zeta(2-s) Gamma(s) Gamma(2-s)` on closed strips. This proves vertical absolute
convergence on both sides of one and the vanishing of the horizontal contour
integrals. The residue at one is `-t⁻¹`. The rectangle contour theorem in
`mellinInv_eq_add_of_double_pole`, with zero quadratic coefficient, then shifts
the inverse transform to
`1<Re(s)<2`, with correction `+t⁻¹`. This completes both equalities of (1.3);
Shintani's subsequent remainder-sum transformations remain separate steps.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace SIC

/-! ### Vertical convergence of the trigamma transform

The bounded zeta--gamma factor leaves one integrable gamma factor.
-/

/-- Gamma is absolutely integrable on `Re(s)=sigma>0`.
This gives the integrable factor in `verticalIntegrable_trigamma_mellin`. -/
private lemma verticalIntegrable_Gamma (σ : ℝ) (hσ : 0 < σ) :
    VerticalIntegrable Complex.Gamma σ := by
  have hcont : Continuous (fun y : ℝ => Complex.Gamma (σ + y * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    apply (analyticAt_Gamma_of_re_pos _ (by simpa using hσ)).continuousAt.comp
    fun_prop
  apply ((integrable_inv_sq_add_sq σ hσ.ne').const_mul (Real.Gamma (σ + 2))).mono'
    hcont.aestronglyMeasurable
  filter_upwards with y
  have h := norm_Gamma_le_div_norm_sq (σ + y * I) (by simpa using hσ)
  rw [Complex.sq_norm] at h
  simpa [Complex.normSq_apply, div_eq_mul_inv, pow_two] using h

/-- The function `zeta(2-s) Gamma(2-s)` is continuous on `Re(s)=sigma`
when `sigma<2` and `sigma≠1`, giving measurability in `verticalIntegrable_trigamma_mellin`. -/
private lemma continuous_zeta_mul_Gamma_vertical (σ : ℝ)
    (hσ2 : σ < 2) (hσ1 : σ ≠ 1) :
    Continuous (fun y : ℝ => riemannZeta (2 - (σ + y * I)) *
      Complex.Gamma (2 - (σ + y * I))) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hz : 2 - ((σ : ℂ) + y * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hσ1 (by linarith)
  apply ContinuousAt.mul
  · apply (differentiableAt_riemannZeta hz).continuousAt.comp
      (f := fun y : ℝ => 2 - ((σ : ℂ) + y * I))
    fun_prop
  · apply (analyticAt_Gamma_of_re_pos _ (by simp; linarith)).continuousAt.comp
    fun_prop

/-- The transform `zeta(2-s) Gamma(s) Gamma(2-s)` is absolutely integrable on
`Re(s)=sigma` for `0<sigma<2`, `sigma≠1`. This supplies both vertical contours in
[95, Shintani (1977), equation (1.3), p. 170]. -/
theorem verticalIntegrable_trigamma_mellin (σ : ℝ)
    (hσ : 0 < σ) (hσ2 : σ < 2) (hσ1 : σ ≠ 1) :
    VerticalIntegrable
      (fun s => riemannZeta (2 - s) * Complex.Gamma s * Complex.Gamma (2 - s)) σ := by
  obtain ⟨C, hC⟩ := exists_norm_completedRiemannZeta_vertical_le (2 - σ)
    (by linarith) (by intro h; apply hσ1; linarith)
  have hint := (verticalIntegrable_Gamma σ hσ).mul_bdd
    (continuous_zeta_mul_Gamma_vertical σ hσ2 hσ1).aestronglyMeasurable
    (c := C * gammaZetaBound (2 - σ)) (by
      filter_upwards with y
      have hb := norm_zeta_mul_Gamma_le (2 - (σ + y * I)) (by simp; linarith)
      simp only [sub_re, re_ofNat, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, zero_mul, sub_zero, add_zero] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right (hC _ (by simp))
        (gammaZetaBound_nonneg (by linarith))))
  simpa only [VerticalIntegrable, mul_left_comm, mul_comm, mul_assoc] using hint

/-! ### Mellin inversion

Trigamma is continuous at positive arguments since gamma is analytic and
nonvanishing there. Mathlib's Mellin inversion theorem, applied to the forward
transform and the vertical convergence above, proves the first equality of
[95, Shintani (1977), equation (1.3)].
-/

/-- Trigamma is continuous on the right half-plane. This supplies the pointwise
regularity required by `mellinInv_trigamma_sub_inv_sq`. -/
private lemma continuousAt_trigamma_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    ContinuousAt (deriv Complex.digamma) s :=
  (analyticAt_digamma_of_re_pos s hs).deriv.continuousAt

/-- For `t>0` and `0<sigma<1`, the inverse Mellin transform of
`zeta(2-s) Gamma(s) Gamma(2-s)` equals `psi'(t)-t⁻²`.
This is [95, Shintani (1977), equation (1.3), first equality, p. 170]. Mathlib's
`mellinInv` parametrizes the upward vertical contour by `s=sigma+iy`, so its
normalization `1/(2*pi)` incorporates `ds=i dy` in Shintani's `1/(2*pi*i)` integral. -/
@[source "95, equation (1.3), p. 170 (first equality)"]
theorem mellinInv_trigamma_sub_inv_sq (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (t : ℝ) (ht : 0 < t) :
    mellinInv σ (fun s => riemannZeta (2 - s) * Complex.Gamma s * Complex.Gamma (2 - s)) t =
      deriv Complex.digamma (t : ℂ) - (t : ℂ)⁻¹ ^ 2 := by
  let f : ℝ → ℂ := fun x => deriv Complex.digamma (x : ℂ) - (x : ℂ)⁻¹ ^ 2
  have hline (y : ℝ) : mellin f (σ + y * I) =
      riemannZeta (2 - (σ + y * I)) * Complex.Gamma (σ + y * I) *
        Complex.Gamma (2 - (σ + y * I)) :=
    (hasMellin_trigamma_sub_inv_sq _ (by simpa using hσ) (by simpa using hσ1)).2
  have hvertical : VerticalIntegrable (mellin f) σ := by
    simpa only [VerticalIntegrable, hline] using
      verticalIntegrable_trigamma_mellin σ hσ (by linarith) (ne_of_lt hσ1)
  have hcont : ContinuousAt f t :=
    ((continuousAt_trigamma_of_re_pos _ (by simpa using ht)).comp
      Complex.continuous_ofReal.continuousAt).sub
        ((Complex.continuous_ofReal.continuousAt.inv₀
          (Complex.ofReal_ne_zero.mpr ht.ne')).pow 2)
  convert mellinInv_mellin_eq σ f ht
    (hasMellin_trigamma_sub_inv_sq (σ : ℂ) (by simpa) (by simpa)).1 hvertical hcont using 1
  simp only [mellinInv, hline]

/-! ### Horizontal decay

The same estimates hold uniformly as the real part varies over a compact
interval in `(0,2)`, once `|Im(s)|≥1`. The factor `t^(-s)` has norm
`t^(-Re(s))`, so it is uniformly bounded on the strip for fixed `t>0`.
The horizontal integral is bounded by the interval length times a quantity
that tends to zero. These are the contour estimates used in
[95, Shintani (1977), equation (1.3)].
-/

/-- Multiplying `norm_zeta_mul_Gamma_le` by the quadratic gamma bound leaves
`|Lambda(2-s)|` times a real-part coefficient divided by `|s|²`.
This is the pointwise estimate used in `exists_norm_trigamma_mellin_le`. -/
private lemma norm_trigamma_mellin_le_completed (s : ℂ) (hs : 0 < s.re) (hs2 : s.re < 2) :
    ‖riemannZeta (2 - s) * Complex.Gamma s * Complex.Gamma (2 - s)‖ ≤
      ‖completedRiemannZeta (2 - s)‖ *
        (gammaZetaBound (2 - s.re) * Real.Gamma (s.re + 2)) / ‖s‖ ^ 2 := by
  have hz := norm_zeta_mul_Gamma_le (2 - s) (by simp; linarith)
  have hzr : (2 - s).re = 2 - s.re := by simp
  rw [hzr] at hz
  calc
    _ = ‖riemannZeta (2 - s) * Complex.Gamma (2 - s)‖ * ‖Complex.Gamma s‖ := by
      rw [← norm_mul]; congr 1; ring
    _ ≤ ‖completedRiemannZeta (2 - s)‖ * gammaZetaBound (2 - s.re) *
        (Real.Gamma (s.re + 2) / ‖s‖ ^ 2) :=
      mul_le_mul hz (norm_Gamma_le_div_norm_sq s hs) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (gammaZetaBound_nonneg (by linarith)))
    _ = _ := by ring

/-- The real-part coefficient in `norm_trigamma_mellin_le_completed` is bounded
on a compact interval inside `(0,2)`, for `exists_norm_trigamma_mellin_le`. -/
private lemma exists_gammaZetaBound_mul_Gamma_le (a b : ℝ) (ha : 0 < a) (hb : b < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc a b,
      gammaZetaBound (2 - x) * Real.Gamma (x + 2) ≤ C := by
  have hc : ContinuousOn (fun x : ℝ => gammaZetaBound (2 - x) * Real.Gamma (x + 2))
      (Icc a b) := by
    apply ContinuousOn.mul
    · exact continuousOn_gammaZetaBound.comp (by fun_prop)
        (fun x hx => show -1 < 2 - x by linarith [hx.2])
    · exact Real.differentiableOn_Gamma_Ioi.continuousOn.comp (by fun_prop)
        (fun x hx => show 0 < x + 2 by linarith [hx.1])
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc
  exact ⟨max C 0, le_max_right _ _, fun x hx =>
    (hC (mem_image_of_mem _ hx)).trans (le_max_left _ _)⟩

/-- For `|Im(s)|≥1`, `1+Im(s)²≤2|s|²`.
This puts `exists_norm_trigamma_mellin_le` in the integrable Cauchy-kernel form. -/
private lemma one_add_im_sq_le_two_norm_sq (s : ℂ) (hs : 1 ≤ |s.im|) :
    1 + s.im ^ 2 ≤ 2 * ‖s‖ ^ 2 := by
  have him : 1 ≤ s.im ^ 2 := by nlinarith [sq_abs s.im, sq_nonneg (|s.im| - 1)]
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg s.re]

/-- For `0<a≤Re(s)≤b<2` and `|Im(s)|≥1`,
`|zeta(2-s) Gamma(s) Gamma(2-s)| ≤ C/(1+Im(s)²)` for one strip-dependent constant.
This supplies the horizontal-contour decay implicit in
[95, Shintani (1977), equation (1.3), second equality, p. 170]. -/
theorem exists_norm_trigamma_mellin_le (a b : ℝ) (ha : 0 < a) (hb : b < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖riemannZeta (2 - s) * Complex.Gamma s * Complex.Gamma (2 - s)‖ ≤
        C / (1 + s.im ^ 2) := by
  obtain ⟨Cz, hCz0, hCz⟩ := exists_norm_completedRiemannZeta_strip_le (2 - b) (2 - a)
  obtain ⟨Cg, hCg0, hCg⟩ := exists_gammaZetaBound_mul_Gamma_le a b ha hb
  refine ⟨2 * Cz * Cg, by positivity, fun s hsa hsb hsi => ?_⟩
  have hs : 0 < s.re := ha.trans_le hsa
  have hn : 0 < ‖s‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (by intro h; simp [h] at hs))
  have hC : ‖completedRiemannZeta (2 - s)‖ ≤ Cz :=
    hCz _ (by simp; linarith) (by simp; linarith) (by simpa)
  have hG : 0 ≤ gammaZetaBound (2 - s.re) * Real.Gamma (s.re + 2) :=
    mul_nonneg (gammaZetaBound_nonneg (by linarith)) (Real.Gamma_pos_of_pos (by linarith)).le
  calc
    _ ≤ ‖completedRiemannZeta (2 - s)‖ *
        (gammaZetaBound (2 - s.re) * Real.Gamma (s.re + 2)) / ‖s‖ ^ 2 :=
      norm_trigamma_mellin_le_completed s hs (by linarith)
    _ ≤ Cz * Cg / ‖s‖ ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul hC (hCg _ ⟨hsa, hsb⟩) hG hCz0) hn.le
    _ ≤ 2 * Cz * Cg / (1 + s.im ^ 2) := by
      rw [div_le_div_iff₀ hn (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left (one_add_im_sq_le_two_norm_sq s hsi)
        (mul_nonneg hCz0 hCg0)]

/-- For `t>0` and `0<a≤b<2`, the horizontal integrals
`∫_a^b zeta(2-x-iy) Gamma(x+iy) Gamma(2-x-iy) t^(-x-iy) dx` tend to zero
as `|y|` tends to infinity. This is the horizontal-contour limit needed for
[95, Shintani (1977), equation (1.3), second equality, p. 170].
The filter `cocompact ℝ` expresses both ends of the real line at once. -/
theorem tendsto_integral_trigamma_mellin_horizontal
    (a b : ℝ) (ha : 0 < a) (hb : b < 2) (hab : a ≤ b) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun y : ℝ => ∫ x : ℝ in a..b,
      riemannZeta (2 - (x + y * I)) * Complex.Gamma (x + y * I) *
        Complex.Gamma (2 - (x + y * I)) * (t : ℂ) ^ (-(x + y * I)))
      (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_norm_trigamma_mellin_le a b ha hb
  apply tendsto_integral_horizontal_mul_cpow
    (fun s => riemannZeta (2 - s) * Complex.Gamma s * Complex.Gamma (2 - s)) a b C _ t ht
  intro s hs hsi
  rw [uIcc_of_le hab] at hs
  exact hC s hs.1 hs.2 hsi

/-! ### The pole at one

The change `w=2-s` negates the residue of zeta at one. The two gamma
factors are both one there, and `t^(-s)` tends to `t⁻¹`. This computes the
residue for [95, Shintani (1977), equation (1.3)]. The next section applies
the contour theorem to compare the two vertical integrals.
-/

/-- The map `s ↦ 2-s` preserves punctured convergence to one.
This transports the zeta residue in `tendsto_trigamma_mellin_residue`. -/
private lemma tendsto_two_sub_nhds_ne_one : Tendsto (fun s : ℂ => 2 - s) (𝓝[≠] 1) (𝓝[≠] 1) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have h : Tendsto (fun s : ℂ => 2 - s) (𝓝 (1 : ℂ)) (𝓝 (2 - 1 : ℂ)) :=
      tendsto_const_nhds.sub tendsto_id
    convert h.mono_left nhdsWithin_le_nhds using 1
    norm_num
  · filter_upwards [self_mem_nhdsWithin] with s hs
    change s ≠ 1 at hs
    change 2 - s ≠ 1
    intro h
    apply hs
    linear_combination -h

/-- For `t>0`, the residue of
`zeta(2-s) Gamma(s) Gamma(2-s) t^(-s)` at `s=1` is `-t⁻¹`, stated as
`(s-1) zeta(2-s) Gamma(s) Gamma(2-s) t^(-s) → -t⁻¹`.
This is the pole contribution in [95, Shintani (1977), equation (1.3), p. 170]:
moving the upward contour to the right produces the source's `+t⁻¹` term. -/
theorem tendsto_trigamma_mellin_residue (t : ℝ) (ht : 0 < t) :
    Tendsto (fun s : ℂ => (s - 1) * (riemannZeta (2 - s) * Complex.Gamma s *
      Complex.Gamma (2 - s) * (t : ℂ) ^ (-s))) (𝓝[≠] 1) (𝓝 (-(t : ℂ)⁻¹)) := by
  have hc : ContinuousAt (fun s : ℂ => Complex.Gamma s * Complex.Gamma (2 - s) *
      (t : ℂ) ^ (-s)) 1 := by
    apply ContinuousAt.mul
    · apply ContinuousAt.mul
      · exact Complex.continuousAt_Gamma_one
      · apply (analyticAt_Gamma_of_re_pos _ (by norm_num)).continuousAt.comp
        fun_prop
    · apply (continuousAt_const_cpow (Complex.ofReal_ne_zero.mpr ht.ne')).comp
      fun_prop
  have h := ((riemannZeta_residue_one.comp tendsto_two_sub_nhds_ne_one).neg).mul
    (hc.tendsto.mono_left nhdsWithin_le_nhds)
  convert h using 1
  · funext s
    simp only [Function.comp_apply]
    ring
  · norm_num [Complex.cpow_neg_one]

/-! ### The shifted inverse transform

Apply `mellinInv_eq_add_of_double_pole` with zero quadratic coefficient. Its
vertical absolute convergence, horizontal decay and residue were proved above.
The normalized shift contributes the correction `+t⁻¹`, giving the second equality of
[95, Shintani (1977), equation (1.3)].
-/

/-- For `t>0`, the full Mellin kernel is holomorphic on `0<Re(s)<2` away from
`s=1`. This supplies the regularity for the trigamma inversion and remainder contour shifts. -/
theorem differentiableAt_trigamma_mellin_kernel (s : ℂ)
    (hs : 0 < s.re) (hs2 : s.re < 2) (hs1 : s ≠ 1) (t : ℝ) (ht : 0 < t) :
    DifferentiableAt ℂ (fun s => riemannZeta (2 - s) * Complex.Gamma s *
      Complex.Gamma (2 - s) * (t : ℂ) ^ (-s)) s := by
  have hz : 2 - s ≠ 1 := by intro h; apply hs1; linear_combination -h
  have hd : DifferentiableAt ℂ (fun s : ℂ => 2 - s) s :=
    (differentiableAt_const (2 : ℂ)).sub differentiableAt_id
  exact (((differentiableAt_riemannZeta hz).comp s hd).mul
    (analyticAt_Gamma_of_re_pos s hs).differentiableAt |>.mul
      ((analyticAt_Gamma_of_re_pos (2 - s) (by simp; linarith)).differentiableAt.comp s hd)).mul
    (differentiableAt_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr ht.ne')))

/-- Moving the inverse Mellin contour from `0<a<1` to `1<b<2` gives
`mellinInv(a)=mellinInv(b)+t⁻¹`. This is the contour comparison used by
`trigamma_sub_inv_sq_eq_mellinInv_add_inv`. -/
private lemma mellinInv_trigamma_shift (a b : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hb1 : 1 < b) (hb : b < 2) (t : ℝ) (ht : 0 < t) :
    mellinInv a (fun s => riemannZeta (2 - s) * Complex.Gamma s * Complex.Gamma (2 - s)) t =
      mellinInv b (fun s => riemannZeta (2 - s) * Complex.Gamma s * Complex.Gamma (2 - s)) t +
        (t : ℂ)⁻¹ := by
  have h := mellinInv_eq_add_of_double_pole
    (fun s => riemannZeta (2 - s) * Complex.Gamma s * Complex.Gamma (2 - s))
    a b 1 0 (-(t : ℂ)⁻¹) ha1 hb1 t ht
    (fun s hsa hsb hs1 => by
      simpa using differentiableAt_trigamma_mellin_kernel s
        (ha.trans_le hsa) (hsb.trans_lt hb) (by simpa using hs1) 1 zero_lt_one)
    (by simpa using tendsto_trigamma_mellin_residue t ht)
    (verticalIntegrable_trigamma_mellin a ha (by linarith) ha1.ne)
    (verticalIntegrable_trigamma_mellin b (by linarith) hb hb1.ne')
    (tendsto_integral_trigamma_mellin_horizontal a b ha hb (by linarith) t ht)
  linear_combination -h

/-- For `t>0` and `1<sigma<2`,
`psi'(t)-t⁻² = mellinInv(sigma, zeta(2-s) Gamma(s) Gamma(2-s))(t)+t⁻¹`.
This is [95, Shintani (1977), equation (1.3), second equality, p. 170].
As in `mellinInv_trigamma_sub_inv_sq`, `mellinInv` includes the normalization
`1/(2*pi)` for the upward parameterization `s=sigma+iy`. -/
@[source "95, equation (1.3), p. 170 (second equality)"]
theorem trigamma_sub_inv_sq_eq_mellinInv_add_inv (σ : ℝ) (hσ1 : 1 < σ) (hσ2 : σ < 2)
    (t : ℝ) (ht : 0 < t) :
    deriv Complex.digamma (t : ℂ) - (t : ℂ)⁻¹ ^ 2 =
      mellinInv σ (fun s => riemannZeta (2 - s) * Complex.Gamma s * Complex.Gamma (2 - s)) t +
        (t : ℂ)⁻¹ := by
  rw [← mellinInv_trigamma_sub_inv_sq (1 / 2) (by norm_num) (by norm_num) t ht]
  exact mellinInv_trigamma_shift (1 / 2) σ (by norm_num) (by norm_num) hσ1 hσ2 t ht

end SIC

end
