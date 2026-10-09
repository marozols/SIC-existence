/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.RectangleResidues
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# Shifting vertical contours across simple and double poles

Vertical contour shifts across real simple and double poles, with quantitative closing-side bounds.

This file supplies the contour argument used in
[95, Shintani (1977), proof of Lemma 1, equation (1.3), p. 170].
It compares integrals along `Re(z)=a` and `Re(z)=b` across a single real pole
`c` with residue `r`, assuming vertical absolute convergence and vanishing
horizontal integrals.

Apply the residue theorem to `f` on the rectangle `[a,b] × [-Y,Y]`, with its
single pole `c`. As `Y` tends to infinity, the horizontal integrals vanish and
the vertical integrals converge to the two line integrals. Their difference is
the residue correction. The vertical integrals use `dy` in `z=a+iy`, so the
factor `i` from `dz=i dy` cancels from the final identity.

For a double pole with leading coefficient `q`, subtract `q/(z-c)²` first.
This term has zero integral on each vertical line and vanishing horizontal
integrals, by the fundamental theorem of calculus. The simple-pole theorem
then gives the same residue correction. This supplies the contour theorem
for Shintani's subsequent transformation of the first remainder sum `f₁`.
The shared horizontal-limit lemmas turn uniform quadratic strip bounds into
the vanishing integrals required by both contour theorems.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace SIC

/-! ### Horizontal limits from strip bounds

A bound `C/(1+Im(s)²)` makes the horizontal integral tend to zero at both
ends of a vertical strip. The same quadratic majorant gives absolute integrability
on each vertical line. These estimates supply the convergence hypotheses for contour shifts.
-/

/-- A continuous function on a vertical line is absolutely integrable there if
`|F(sigma+iy)| ≤ C/(1+y²)` for `|y|≥1`. This turns the strip bounds used for
horizontal limits into the vertical hypotheses of the contour theorems. -/
theorem verticalIntegrable_of_quadratic_decay (F : ℂ → ℂ) (σ C : ℝ)
    (hc : Continuous (fun y : ℝ => F (σ + y * I)))
    (hC : ∀ y : ℝ, 1 ≤ |y| → ‖F (σ + y * I)‖ ≤ C / (1 + y ^ 2)) :
    VerticalIntegrable F σ := by
  apply hc.locallyIntegrable.integrable_of_isBigO_cocompact
    (g := fun y : ℝ => (1 + y ^ 2)⁻¹)
  · apply Asymptotics.IsBigO.of_bound C
    filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop 1] with y hy
    simpa [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 + y ^ 2),
      div_eq_mul_inv] using hC y (by simpa using hy)
  · exact integrable_inv_one_add_sq.integrableAtFilter _

/-- A uniform bound `|f(s)| ≤ C/(1+Im(s)²)` on the strip between `a` and `b`,
for `|Im(s)|≥1`, makes its horizontal integrals tend to zero.
This bridges strip estimates to the hypotheses of the contour-shift theorems. -/
theorem tendsto_integral_horizontal_of_quadratic_decay (f : ℂ → ℂ) (a b C : ℝ)
    (hC : ∀ s : ℂ, s.re ∈ uIcc a b → 1 ≤ |s.im| →
      ‖f s‖ ≤ C / (1 + s.im ^ 2)) :
    Tendsto (fun y : ℝ => ∫ x : ℝ in a..b, f (x + y * I))
      (cocompact ℝ) (𝓝 0) := by
  have hbound (y : ℝ) (hy : 1 ≤ |y|) :
      ‖∫ x : ℝ in a..b, f (x + y * I)‖ ≤ (C / (1 + y ^ 2)) * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    simpa using hC (x + y * I) (by simpa using uIoc_subset_uIcc hx) (by simpa)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    ((tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop 1 |>.mono
      (fun y hy => hbound y (by simpa using hy)))
  have hnorm : Tendsto (fun y : ℝ => y ^ 2) (cocompact ℝ) atTop := by
    simpa only [Function.comp_def, Real.norm_eq_abs, sq_abs] using
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
        (tendsto_norm_cocompact_atTop (E := ℝ))
  have hinv : Tendsto (fun y : ℝ => (1 + y ^ 2)⁻¹) (cocompact ℝ) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 hnorm)
  simpa [div_eq_mul_inv] using (hinv.const_mul C).mul_const |b - a|

/-! ### Rectangle limits and the contour shift

Apply the residue theorem on `[a,b] × [-Y,Y]` with the single pole `c`.
The horizontal sides vanish as `Y → ∞`, and the vertical sides converge to the
whole-line integrals; `dz=i dy` then gives the residue correction.
-/

/-- The residue theorem on `[a,b] × [-Y,Y]` with the single real pole `c`.
This supplies the finite-rectangle identity in `integral_vertical_eq_sub_of_simple_pole`. -/
private lemma boundary_rect_simple_pole (f : ℂ → ℂ) (a b c : ℝ) (r : ℂ)
    (hac : a < c) (hcb : c < b)
    (hd : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ c → DifferentiableAt ℂ f z)
    (hr : Tendsto (fun z : ℂ => (z - c) * f z) (𝓝[≠] (c : ℂ)) (𝓝 r))
    (Y : ℝ) (hY : 0 < Y) :
    (∫ t : ℝ in a..b, f ((t : ℂ) + (-Y) * I)) -
      (∫ t : ℝ in a..b, f ((t : ℂ) + Y * I)) +
      I • (∫ t : ℝ in -Y..Y, f ((b : ℂ) + t * I)) -
      I • (∫ t : ℝ in -Y..Y, f ((a : ℂ) + t * I)) =
      2 * Real.pi * I * r := by
  have hab : a ≤ b := (hac.trans hcb).le
  have hS : ∀ s ∈ ({(c : ℂ)} : Finset ℂ),
      (((a : ℂ) + (-Y) * I)).re < s.re ∧
        s.re < (((b : ℂ) + Y * I)).re ∧
        (((a : ℂ) + (-Y) * I)).im < s.im ∧
        s.im < (((b : ℂ) + Y * I)).im := by
    intro s hs
    rcases Finset.mem_singleton.mp hs with rfl
    simpa using (show a < c ∧ c < b ∧ -Y < (0 : ℝ) ∧ (0 : ℝ) < Y from
      ⟨hac, hcb, neg_lt_zero.mpr hY, hY⟩)
  have hdiff : DifferentiableOn ℂ f
      ((Icc a b ×ℂ Icc (-Y) Y) \ ({(c : ℂ)} : Set ℂ)) := by
    intro ζ hζ
    have hbox : ζ.re ∈ Icc a b ∧ ζ.im ∈ Icc (-Y) Y := by
      simpa only [mem_reProdIm] using hζ.1
    have hne : ζ ≠ (c : ℂ) := by simpa using hζ.2
    exact (hd ζ hbox.1.1 hbox.1.2 hne).differentiableWithinAt
  have h := integral_boundary_rect_eq_sum_residues f
    ((a : ℂ) + (-Y) * I) ((b : ℂ) + Y * I)
    ({(c : ℂ)} : Finset ℂ) (fun _ => r) hS
    (by simpa [uIcc_of_le hab, uIcc_of_le (by linarith : -Y ≤ Y)] using hdiff)
    (by
      intro s hs
      rcases Finset.mem_singleton.mp hs with rfl
      simpa using hr)
  simpa using h

/-- Shift the upward contour across a real simple pole `c` of residue `r`:
`∫ f(a+iy) dy = ∫ f(b+iy) dy - 2*pi*r` for `a<c<b`.
The boundary integrals must converge absolutely, and the horizontal integrals
must tend to zero at both imaginary ends. This is the rectangle contour argument
used in [95, Shintani (1977), equation (1.3), second equality, p. 170], separated
from the special-function estimates. The integrals use `dy`, with `dz=i dy`.
The residue may be zero, so removable singularities are included. -/
theorem integral_vertical_eq_sub_of_simple_pole (f : ℂ → ℂ) (a b c : ℝ) (r : ℂ)
    (hac : a < c) (hcb : c < b)
    (hd : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ c → DifferentiableAt ℂ f z)
    (hr : Tendsto (fun z : ℂ => (z - c) * f z) (𝓝[≠] (c : ℂ)) (𝓝 r))
    (ha : Integrable (fun y : ℝ => f (a + y * I)))
    (hb : Integrable (fun y : ℝ => f (b + y * I)))
    (hh : Tendsto (fun y : ℝ => ∫ x : ℝ in a..b, f (x + y * I))
      (cocompact ℝ) (𝓝 0)) :
    (∫ y : ℝ, f (a + y * I)) = (∫ y : ℝ, f (b + y * I)) - 2 * Real.pi * r := by
  have hrect : ∀ᶠ Y : ℝ in atTop,
      (∫ t : ℝ in a..b, f ((t : ℂ) + (-Y) * I)) -
        (∫ t : ℝ in a..b, f ((t : ℂ) + Y * I)) +
        I • (∫ t : ℝ in -Y..Y, f ((b : ℂ) + t * I)) -
        I • (∫ t : ℝ in -Y..Y, f ((a : ℂ) + t * I)) =
        2 * Real.pi * I * r := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    exact boundary_rect_simple_pole f a b c r hac hcb hd hr Y hY
  have hbottom' := hh.comp (tendsto_neg_atTop_atBot.mono_right atBot_le_cocompact)
  have hbottom : Tendsto (fun Y : ℝ => ∫ t : ℝ in a..b, f ((t : ℂ) + (-Y) * I))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ofReal_neg] using hbottom'
  have htop : Tendsto (fun Y : ℝ => ∫ t : ℝ in a..b, f ((t : ℂ) + Y * I))
      atTop (𝓝 0) := hh.mono_left atTop_le_cocompact
  have h := integral_vertical_sub_eq_neg_residue_of_rectangle f a b r ha hb
    hbottom htop hrect
  simp only [integral_mul_const] at h
  have hc : ((∫ y : ℝ, f (a + y * I)) - (∫ y : ℝ, f (b + y * I)) +
      2 * Real.pi * r) * I = 0 := by
    linear_combination h
  have hc' := (mul_eq_zero.mp hc).resolve_right I_ne_zero
  linear_combination hc'

/-! ### A double pole

Subtract `q/(z-c)²` before applying the simple-pole theorem. This term is
absolutely integrable on each vertical line avoiding `c`, and its integral
is zero: a primitive is `i/(d-c+iy)`, which vanishes at both ends.
Its horizontal integrals also tend to zero. Thus only the coefficient of
`(z-c)⁻¹` contributes to the contour shift, as in Shintani's next shift for `f₁`.
-/

/-- For `a≠0`, `y ↦ (a+iy)⁻¹` is continuous.
This supplies the integrability argument for `integrable_vertical_inv_sq`. -/
private lemma continuous_vertical_inv (a : ℝ) (ha : a ≠ 0) :
    Continuous (fun y : ℝ => ((a : ℂ) + y * I)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro y h
  have := congrArg Complex.re h
  exact ha (by simpa using this)

/-- The function `1/(a²+y²)` is integrable for `a≠0`, by rescaling Mathlib's
Cauchy kernel. This is shared by the contour principal parts and the gamma bounds. -/
lemma integrable_inv_sq_add_sq (a : ℝ) (ha : a ≠ 0) :
    Integrable (fun y : ℝ => (a ^ 2 + y ^ 2)⁻¹) := by
  have h := (integrable_inv_one_add_sq.comp_div ha).const_mul (a ^ 2)⁻¹
  convert h using 1
  ext y
  field_simp

/-- The double-pole kernel `(a+iy)⁻²` is absolutely integrable for `a≠0`.
This supplies `integral_vertical_eq_sub_of_double_pole`. -/
private lemma integrable_vertical_inv_sq (a : ℝ) (ha : a ≠ 0) :
    Integrable (fun y : ℝ => (((a : ℂ) + y * I) ^ 2)⁻¹) := by
  simp_rw [← inv_pow]
  apply (integrable_norm_iff ((continuous_vertical_inv a ha).pow 2).aestronglyMeasurable).mp
  change Integrable (fun y : ℝ => ‖((a : ℂ) + y * I)⁻¹ ^ 2‖)
  simp only [norm_pow, norm_inv, inv_pow, Complex.sq_norm]
  simpa [Complex.normSq_apply, pow_two] using integrable_inv_sq_add_sq a ha

/-- The reciprocal `(a+iy)⁻¹` tends to zero as `|y|→∞`.
This supplies the whole-line integral in `integral_vertical_inv_sq`. -/
private lemma tendsto_vertical_inv (a : ℝ) :
    Tendsto (fun y : ℝ => ((a : ℂ) + y * I)⁻¹) (cocompact ℝ) (𝓝 0) := by
  apply tendsto_inv₀_cobounded.comp
  apply tendsto_norm_atTop_iff_cobounded.mp
  apply tendsto_atTop_mono (fun y => ?_) (tendsto_norm_cocompact_atTop (E := ℝ))
  simpa using Complex.abs_im_le_norm ((a : ℂ) + y * I)

/-- For `a≠0`, `∫ (a+iy)⁻² dy=0` along the whole vertical line.
The primitive `i/(a+iy)` vanishes at both ends. This removes the leading
principal part in `integral_vertical_eq_sub_of_double_pole`. -/
private lemma integral_vertical_inv_sq (a : ℝ) (ha : a ≠ 0) :
    (∫ y : ℝ, (((a : ℂ) + y * I) ^ 2)⁻¹) = 0 := by
  have hd (y : ℝ) : HasDerivAt (fun y : ℝ => I * ((a : ℂ) + y * I)⁻¹)
      ((((a : ℂ) + y * I) ^ 2)⁻¹) y := by
    have hn : (a : ℂ) + y * I ≠ 0 := by
      intro h
      exact ha (by simpa using congrArg Complex.re h)
    convert! (((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add (a : ℂ)).inv hn
      |>.const_mul I using 1
    simp [div_eq_mul_inv, ← mul_assoc]
  have ht := (tendsto_vertical_inv a).const_mul I
  simpa using integral_of_hasDerivAt_of_tendsto hd (integrable_vertical_inv_sq a ha)
    (ht.mono_left atBot_le_cocompact) (ht.mono_left atTop_le_cocompact)

/-- The horizontal integrals of `(z-c)⁻²` vanish at both imaginary ends.
The primitive `-(z-c)⁻¹` reduces this to `tendsto_vertical_inv` at the endpoints,
for `integral_vertical_eq_sub_of_double_pole`. -/
private lemma tendsto_integral_horizontal_inv_sq (a b c : ℝ) :
    Tendsto (fun y : ℝ => ∫ x : ℝ in a..b, (((x : ℂ) + y * I - c) ^ 2)⁻¹)
      (cocompact ℝ) (𝓝 0) := by
  have ht := (tendsto_vertical_inv (a - c)).sub (tendsto_vertical_inv (b - c))
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop 1] with y hy
  have hn (x : ℝ) : (x : ℂ) + y * I - c ≠ 0 := by
    intro h
    have : y = 0 := by simpa using congrArg Complex.im h
    norm_num [this] at hy
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => -((x : ℂ) + y * I - c)⁻¹)
      ((((x : ℂ) + y * I - c) ^ 2)⁻¹) x := by
    convert! (((Complex.ofRealCLM.hasDerivAt (x := x)).add_const (y * I)).sub_const
      (c : ℂ)).inv (hn x) |>.neg using 1
    simp [div_eq_mul_inv]
  have hc : Continuous (fun x : ℝ => (((x : ℂ) + y * I - c) ^ 2)⁻¹) :=
    ((by fun_prop : Continuous (fun x : ℝ => (x : ℂ) + y * I - c)).pow 2).inv₀
      (fun x => pow_ne_zero 2 (hn x))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hc.intervalIntegrable a b)]
  simp only [ofReal_sub, sub_add_eq_add_sub, sub_neg_eq_add]
  ring

/-- Subtracting `q/(z-c)²` preserves vanishing horizontal integrals on a strip.
This supplies `integral_vertical_eq_sub_of_double_pole`. -/
private lemma tendsto_integral_horizontal_sub_inv_sq (f : ℂ → ℂ)
    (a b c : ℝ) (q : ℂ) (hab : a ≤ b)
    (hd : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ c → DifferentiableAt ℂ f z)
    (hh : Tendsto (fun y : ℝ => ∫ x : ℝ in a..b, f (x + y * I))
      (cocompact ℝ) (𝓝 0)) :
    Tendsto (fun y : ℝ => ∫ x : ℝ in a..b,
      f (x + y * I) - q / ((x : ℂ) + y * I - c) ^ 2) (cocompact ℝ) (𝓝 0) := by
  have ht := hh.sub ((tendsto_integral_horizontal_inv_sq a b c).const_mul q)
  simp only [mul_zero, sub_zero] at ht
  apply ht.congr'
  filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop 1] with y hy
  have hn (x : ℝ) : (x : ℂ) + y * I ≠ c := by
    intro h
    have : y = 0 := by simpa using congrArg Complex.im h
    norm_num [this] at hy
  have hf : ContinuousOn (fun x : ℝ => f (x + y * I)) (uIcc a b) := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hc : Continuous (fun x : ℝ => (x : ℂ) + y * I) := by fun_prop
    have hf := (hd _ (by simpa using hx.1) (by simpa using hx.2) (hn x)).continuousAt
    exact hf.comp_continuousWithinAt
      (f := fun x : ℝ => (x : ℂ) + y * I) hc.continuousWithinAt
  have hq : Continuous (fun x : ℝ => q / ((x : ℂ) + y * I - c) ^ 2) :=
    continuous_const.div
      ((by fun_prop : Continuous (fun x : ℝ => (x : ℂ) + y * I - c)).pow 2)
      (fun x => pow_ne_zero 2 (sub_ne_zero.mpr (hn x)))
  rw [intervalIntegral.integral_sub hf.intervalIntegrable (hq.intervalIntegrable a b)]
  simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul]

/-- Shift the upward contour across a real pole of order at most two:
`∫ f(a+iy) dy = ∫ f(b+iy) dy - 2*pi*r` for `a<c<b`, when
`(z-c)(f(z)-q/(z-c)²) → r`. The vertical integrals converge absolutely and the
horizontal integrals vanish at both ends. This is the rectangle argument in
[95, Shintani (1977), proof of Lemma 1, p. 171, second equality for `f₁` after
equation (1.3)], reduced to `integral_vertical_eq_sub_of_simple_pole` by subtracting
the leading principal part. The coefficients `q` and `r` may be zero. -/
theorem integral_vertical_eq_sub_of_double_pole (f : ℂ → ℂ) (a b c : ℝ) (q r : ℂ)
    (hac : a < c) (hcb : c < b)
    (hd : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ c → DifferentiableAt ℂ f z)
    (hr : Tendsto (fun z : ℂ => (z - c) * (f z - q / (z - c) ^ 2))
      (𝓝[≠] (c : ℂ)) (𝓝 r))
    (ha : Integrable (fun y : ℝ => f (a + y * I)))
    (hb : Integrable (fun y : ℝ => f (b + y * I)))
    (hh : Tendsto (fun y : ℝ => ∫ x : ℝ in a..b, f (x + y * I))
      (cocompact ℝ) (𝓝 0)) :
    (∫ y : ℝ, f (a + y * I)) = (∫ y : ℝ, f (b + y * I)) - 2 * Real.pi * r := by
  have hi (d : ℝ) (hdc : d ≠ c) :
      Integrable (fun y : ℝ => q / ((d : ℂ) + y * I - c) ^ 2) := by
    simpa only [div_eq_mul_inv, ofReal_sub, sub_add_eq_add_sub] using
      (integrable_vertical_inv_sq (d - c) (sub_ne_zero.mpr hdc)).const_mul q
  have hz (d : ℝ) (hdc : d ≠ c) :
      (∫ y : ℝ, q / ((d : ℂ) + y * I - c) ^ 2) = 0 := by
    simpa only [div_eq_mul_inv, ofReal_sub, sub_add_eq_add_sub, integral_const_mul,
      mul_zero] using congrArg (q * ·) (integral_vertical_inv_sq (d - c) (sub_ne_zero.mpr hdc))
  have hd' (z : ℂ) (hza : a ≤ z.re) (hzb : z.re ≤ b) (hzc : z ≠ c) :
      DifferentiableAt ℂ (fun z => f z - q / (z - c) ^ 2) z := by
    apply (hd z hza hzb hzc).sub
    exact (differentiableAt_const q).div ((differentiableAt_id.sub_const _).pow 2)
      (pow_ne_zero 2 (sub_ne_zero.mpr hzc))
  have h := integral_vertical_eq_sub_of_simple_pole
    (fun z => f z - q / (z - c) ^ 2) a b c r hac hcb hd' hr (ha.sub (hi a hac.ne))
    (hb.sub (hi b hcb.ne'))
    (tendsto_integral_horizontal_sub_inv_sq f a b c q (hac.trans hcb).le hd hh)
  simpa only [integral_sub ha (hi a hac.ne), integral_sub hb (hi b hcb.ne'),
    hz a hac.ne, hz b hcb.ne', sub_zero] using h

end SIC

end
