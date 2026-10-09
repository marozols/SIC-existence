/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.ModularGrowth
import SICs.SpecialFunctions.Faddeev.FiveTerm.Kernel

/-!
# Bounds for the five-term kernel on the upper half plane

A bound for the kernel of the modular five-term integral away from its poles, and its forms in the
regions that the contour argument meets.

This module quantifies the convergence statements in the proof of [RW26, Radchenko, Wheeler
(2026), Theorem 3, `thm:5term.mod.fad`] in Appendix A.2, `app:mod.fad`, for the kernel
`K_m(z) = Φ_{γ,m+1,0}(z;τ)/Φ_{γ,m+p,0}(z+y;τ) · e(λz + m(ℓτ+w))` of equation (23),
`eq:5term.int`, at `n = h = 0`, with `λ = cw/ε + ℓ`. Throughout, `γ = (a b; c d) ∈ SL₂(ℤ)`,
`τ ∈ ℍ`, `ε = j_γ(τ)`, `σ = γτ`, `Γ = qPochhammerGrowth`, and `μ = c(w+y)/ε + ℓ + p - 1`. The
source asserts that the asymptotics are those of its Lemma 1 in two sectors and are governed by a
quotient of θ-functions in between; the bounds below make this quantitative on `ℍ`.

## The argument

The global bound multiplies the bound of `exists_norm_faddeevModularUHP_le` at `n = m + 1` by
that of `exists_norm_inv_faddeevModularUHP_le` at `n = m + p` and the argument `z + y`, and the
norm `exp(-2π Im(λz))` of the exponential up to a constant. Its hypotheses are the distances to
the right poles, the poles of `Φ_{γ,m+1,0}`, and to the left poles, the zeros of `Φ_{γ,m+p,0}`
shifted by `-y`; the removable singularities need no hypothesis.

The two genuine pole sets are closed. At every point outside them, a small neighborhood has a
uniform positive distance from both sets, so the continuous global majorant bounds the kernel
there, including near totalized removable values.

In each region the four growth exponents simplify.

- High in both variables (`Im z` and `Im(z/ε)` large) all four vanish, and the poles are far away:
  `‖K_m(z)‖ ≤ C exp(-2π Im(λz))`.
- Low in both variables all four arguments lie in the lower half plane, where `Γ` is the Gaussian
  exponent, and the poles are again far away. The quadratic terms cancel in pairs, and the linear
  ones combine exactly:
  `Im(λz) - Im z Im(α-β)/Im τ - Im(z/ε) Im(y/ε)/Im σ = Im(μz)` with `α = (m+1)τ` and
  `β = y + (m+p)τ`, because `Im y Im z - |ε|² Im(y/ε) Im(z/ε) = Im ε Im(yz/ε)`,
  `Im ε = c Im τ`, and `|ε|² Im σ = Im τ`. So `‖K_m(z)‖ ≤ C exp(-2π Im(μz))`.
- High in `z` only, the `τ`-exponents vanish and the shift estimate
  `exists_abs_qPochhammerGrowth_add_sub_le` bounds the `σ`-exponents by
  `2π Im(y/ε) min(Im(z/ε), 0)/Im σ`.
- In a horizontal strip, for `c > 0` and `Re z` large, `Im(z/ε) → -∞`, the `τ`-exponents are
  bounded, and the same shift estimate gives the decay `exp(-2πc Im((w+y)/ε) Re z)`.
-/

noncomputable section

open Complex Real Filter
open scoped MatrixGroups Topology

namespace SIC

/-! ### Common estimates and the global bound

Imaginary separation gives distance estimates used in the regions. The kernel is bounded by the
product of the growth bounds of its two modular q-products. -/

/-- The affine phase of the kernel, used by `fiveTerm_kernel_norm`. -/
private lemma fiveTermKernel_phase (γ : SL(2, ℤ)) (ℓ m : ℤ) (w τ z : ℂ)
    (hε : fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0) :
    ((((γ 1 0 : ℤ) : ℂ) * z + fltDenominator (γ : Mat(2, ℤ)) τ * m) * w /
        fltDenominator (γ : Mat(2, ℤ)) τ + ℓ * (z + m * τ)) =
      (((γ 1 0 : ℤ) : ℂ) * w / fltDenominator (γ : Mat(2, ℤ)) τ + ℓ) * z +
        m * (ℓ * τ + w) := by
  field_simp [hε]
  ring

/-- Three exponential factors combine under addition of their exponents; used by
`exists_norm_fiveTermKernelUHP_le`. -/
private lemma three_exp_mul (A B E F G b T : ℝ) (h : E + F + G = b + T) :
    (A * Real.exp E) * (B * Real.exp F) * Real.exp G =
      (A * B * Real.exp b) * Real.exp T := by
  calc
    _ = A * B * Real.exp (E + F + G) := by rw [Real.exp_add, Real.exp_add]; ring
    _ = _ := by rw [h, Real.exp_add]; ring

/-- Imaginary separation controls distance, used by `fiveTerm_norm_of_im_gap`. -/
private lemma norm_sub_ge_im (z u : ℂ) : |z.im - u.im| ≤ ‖z - u‖ := by
  simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - u)

/-- Separation after division by the modular denominator controls distance, used by the
scaled gap estimate `fiveTerm_norm_of_scaled_im_gap`. -/
private lemma norm_sub_ge_scaled_im (e z u : ℂ) (he : e ≠ 0) :
    ‖e‖ * |(z / e).im - (u / e).im| ≤ ‖z - u‖ := by
  have h := Complex.abs_im_le_norm ((z - u) / e)
  rw [sub_div, Complex.sub_im, ← sub_div, Complex.norm_div] at h
  have he' : 0 < ‖e‖ := norm_pos_iff.mpr he
  calc
    _ ≤ ‖e‖ * (‖z - u‖ / ‖e‖) := mul_le_mul_of_nonneg_left h he'.le
    _ = _ := by field_simp

/-- An imaginary gap gives an unscaled distance bound; used by `fiveTerm_high_zeros_far` and
`fiveTerm_low_poles_far`. -/
private lemma fiveTerm_norm_of_im_gap (z u : ℂ) {δ : ℝ}
    (hgap : δ ≤ z.im - u.im) : δ ≤ ‖z - u‖ := by
  calc
    δ ≤ z.im - u.im := hgap
    _ ≤ |z.im - u.im| := le_abs_self _
    _ ≤ ‖z - u‖ := norm_sub_ge_im z u

/-- A gap of `δ/‖e‖` after division by `e` gives distance `δ`; used by
`fiveTerm_high_poles_far`, `fiveTerm_low_zeros_far`, and `fiveTerm_right_zeros_far`. -/
private lemma fiveTerm_norm_of_scaled_im_gap (e z u : ℂ) (he : e ≠ 0) {δ : ℝ}
    (hgap : δ / ‖e‖ ≤ (z / e).im - (u / e).im) : δ ≤ ‖z - u‖ := by
  have hen : 0 < ‖e‖ := norm_pos_iff.mpr he
  calc
    δ = ‖e‖ * (δ / ‖e‖) := by field_simp
    _ ≤ ‖e‖ * ((z / e).im - (u / e).im) :=
      mul_le_mul_of_nonneg_left hgap hen.le
    _ ≤ ‖e‖ * |(z / e).im - (u / e).im| := by
      gcongr
      exact le_abs_self _
    _ ≤ ‖z - u‖ := norm_sub_ge_scaled_im e z u he

/-- The imaginary part is at least minus the norm; used by `fiveTerm_high_zeros_far`,
`fiveTerm_high_tau_growth`, and `fiveTerm_high_sigma_growth`. -/
private lemma fiveTerm_neg_norm_le_im (a : ℂ) : -‖a‖ ≤ a.im := by
  simpa using (neg_le_neg (Complex.im_le_norm (-a)))

/-- The kernel norm factors into the two modular q-product norms and its phase; used by
`exists_norm_fiveTermKernelUHP_le`. -/
private lemma fiveTerm_kernel_norm (γ : SL(2, ℤ)) (ℓ p m : ℤ) (w y τ z : ℂ)
    (he : fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0) :
    ‖fiveTermKernelUHP γ ℓ p w y τ m z‖ =
      ‖faddeevModularUHP γ (m + 1) 0 z τ‖ *
      ‖(faddeevModularUHP γ (m + p) 0 (z + y) τ)⁻¹‖ *
      Real.exp (-2 * π *
        (((((γ 1 0 : ℤ) : ℂ) * w /
          fltDenominator (γ : Mat(2, ℤ)) τ + ℓ) * z) +
          m * (ℓ * τ + w)).im) := by
  unfold fiveTermKernelUHP
  rw [div_eq_mul_inv, norm_mul, norm_mul, norm_exp_two_pi_I_mul,
    fiveTermKernel_phase γ ℓ m w τ z he]

/-- Multiply two modular growth bounds while replacing their constants by absolute values; used by
`exists_norm_fiveTermKernelUHP_le`. -/
private lemma fiveTerm_two_growth {x y A B E F : ℝ}
    (hx : x ≤ A * Real.exp E) (hy : y ≤ B * Real.exp F) (hy0 : 0 ≤ y) :
    x * y ≤ (|A| * Real.exp E) * (|B| * Real.exp F) := by
  have hx' := hx.trans
    (mul_le_mul_of_nonneg_right (le_abs_self A) (Real.exp_pos _).le)
  have hy' := hy.trans
    (mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_pos _).le)
  exact mul_le_mul hx' hy' hy0 (by positivity)

/-- The exponent of the global five-term kernel bound:
`-2π Im(λz) + Γ_τ(z+(m+1)τ) - Γ_σ(z/ε) + Γ_σ((z+y)/ε) -
Γ_τ(z+y+(m+p)τ)`, where `λ = cw/ε + ℓ`, `ε = j_γ(τ)`, `σ = γτ`, and
`Γ = qPochhammerGrowth`. From the bounds used in [RW26, Radchenko, Wheeler (2026),
Appendix A.2, `app:mod.fad`] for the kernel of equation (23), `eq:5term.int`;
used by `exists_norm_fiveTermKernelUHP_le` and its local and contour bounds. -/
def fiveTermGrowthExponent (γ : SL(2, ℤ)) (ℓ p m : ℤ)
    (w y τ z : ℂ) : ℝ :=
  -2 * π * ((((γ 1 0 : ℤ) : ℂ) * w /
    fltDenominator (γ : Mat(2, ℤ)) τ + ℓ) * z).im +
    qPochhammerGrowth (z + ((m + 1 : ℤ) : ℂ) * τ) τ -
    qPochhammerGrowth (z / fltDenominator (γ : Mat(2, ℤ)) τ)
      (flt (γ : Mat(2, ℤ)) τ) +
    qPochhammerGrowth ((z + y) / fltDenominator (γ : Mat(2, ℤ)) τ)
      (flt (γ : Mat(2, ℤ)) τ) -
    qPochhammerGrowth (z + y + ((m + p : ℤ) : ℂ) * τ) τ

/-- Away from its right poles and its left poles, the kernel of
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`, equation (23), `eq:5term.int`]
at `n = h = 0` satisfies `‖K_m(z)‖ ≤ C exp(-2π Im(λz) + Γ_τ(z+(m+1)τ) - Γ_σ(z/ε) + Γ_σ((z+y)/ε) -
Γ_τ(z+y+(m+p)τ))`, with `λ = cw/ε + ℓ` and `Γ = qPochhammerGrowth`. -/
theorem exists_norm_fiveTermKernelUHP_le (γ : SL(2, ℤ)) (ℓ p : ℤ) (w y τ : ℂ)
    (hτ : 0 < τ.im) (m : ℤ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C, ∀ z : ℂ, (∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, δ ≤ ‖z - u‖) →
      (∀ u ∈ faddeevModularUHPZeros γ (m + p) τ, δ ≤ ‖z + y - u‖) →
      ‖fiveTermKernelUHP γ ℓ p w y τ m z‖ ≤
        C * Real.exp (fiveTermGrowthExponent γ ℓ p m w y τ z) := by
  obtain ⟨A, hA⟩ := exists_norm_faddeevModularUHP_le γ (m + 1) τ hτ δ hδ
  obtain ⟨B, hB⟩ := exists_norm_inv_faddeevModularUHP_le γ (m + p) τ hτ δ hδ
  let b : ℝ := -2 * π * (m * (ℓ * τ + w)).im
  refine ⟨|A| * |B| * Real.exp b, ?_⟩
  intro z hp hz
  have he := fltDenominator_ne_zero_of_im_ne_zero γ hτ.ne'
  let E := qPochhammerGrowth (z + ((m + 1 : ℤ) : ℂ) * τ) τ -
    qPochhammerGrowth (z / fltDenominator (γ : Mat(2, ℤ)) τ)
      (flt (γ : Mat(2, ℤ)) τ)
  let F := qPochhammerGrowth ((z + y) / fltDenominator (γ : Mat(2, ℤ)) τ)
    (flt (γ : Mat(2, ℤ)) τ) -
    qPochhammerGrowth (z + y + ((m + p : ℤ) : ℂ) * τ) τ
  let G := -2 * π * (((((γ 1 0 : ℤ) : ℂ) * w /
    fltDenominator (γ : Mat(2, ℤ)) τ + ℓ) * z) + m * (ℓ * τ + w)).im
  have hprod : ‖faddeevModularUHP γ (m + 1) 0 z τ‖ *
      ‖(faddeevModularUHP γ (m + p) 0 (z + y) τ)⁻¹‖ ≤
      (|A| * Real.exp E) * (|B| * Real.exp F) :=
    fiveTerm_two_growth (hA z hp) (hB (z + y) hz) (norm_nonneg _)
  rw [fiveTerm_kernel_norm γ ℓ p m w y τ z he]
  calc
    _ ≤ (|A| * Real.exp E) * (|B| * Real.exp F) * Real.exp G :=
      mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
    _ = _ := by
      apply three_exp_mul
      dsimp [fiveTermGrowthExponent, E, F, G, b]
      ring

/-- The four-growth-term exponent in `exists_norm_fiveTermKernelUHP_le` is continuous;
this controls its majorant on finite intervals and near removable points. -/
theorem continuous_fiveTermKernelUHP_growthExponent
    (γ : SL(2, ℤ)) (ℓ p m : ℤ) (w y τ : ℂ) :
    Continuous (fun z : ℂ => fiveTermGrowthExponent γ ℓ p m w y τ z) := by
  have h₁ := (continuous_qPochhammerGrowth τ).comp
    (show Continuous (fun z : ℂ => z + ((m + 1 : ℤ) : ℂ) * τ) by fun_prop)
  have h₂ := (continuous_qPochhammerGrowth (flt (γ : Mat(2, ℤ)) τ)).comp
    (show Continuous (fun z : ℂ => z / fltDenominator (γ : Mat(2, ℤ)) τ) by fun_prop)
  have h₃ := (continuous_qPochhammerGrowth (flt (γ : Mat(2, ℤ)) τ)).comp
    (show Continuous (fun z : ℂ => (z + y) / fltDenominator (γ : Mat(2, ℤ)) τ) by fun_prop)
  have h₄ := (continuous_qPochhammerGrowth τ).comp
    (show Continuous (fun z : ℂ => z + y + ((m + p : ℤ) : ℂ) * τ) by fun_prop)
  have hphase : Continuous (fun z : ℂ => -2 * π *
      (((((γ 1 0 : ℤ) : ℂ) * w / fltDenominator (γ : Mat(2, ℤ)) τ + ℓ) * z)).im) :=
    by fun_prop
  exact (((hphase.add h₁).sub h₂).add h₃).sub h₄

/-! ### Local boundedness away from genuine poles

Closedness of the two pole families gives a common positive distance in a neighborhood of any
point away from them. The continuous global majorant is then locally bounded. -/

/-- A point outside a closed subset has a neighborhood at a fixed positive distance from it;
used by `fiveTerm_punctured_separation`. -/
private lemma exists_eventually_norm_sub_ge_of_isClosed {S : Set ℂ} (hS : IsClosed S)
    {e : ℂ} (he : e ∉ S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ z in 𝓝 e, ∀ u ∈ S, δ ≤ ‖z - u‖ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hS.isOpen_compl e he
  refine ⟨r / 2, by positivity, ?_⟩
  filter_upwards [Metric.ball_mem_nhds e (by positivity : 0 < r / 2)] with z hz u hu
  have heu : r ≤ dist u e := by
    by_contra h
    exact (hball (Metric.mem_ball.mpr (lt_of_not_ge h))) hu
  have hze : dist z e < r / 2 := Metric.mem_ball.mp hz
  have hzu : r / 2 ≤ dist z u := by
    have htri := dist_triangle u z e
    rw [dist_comm u z] at htri
    linarith
  simpa only [dist_eq_norm] using hzu

/-- Neighborhoods away from both genuine pole families share a positive distance bound;
used by `isBoundedUnder_fiveTermKernelUHP_punctured`. -/
private lemma fiveTerm_punctured_separation (γ : SL(2, ℤ)) (p m : ℤ)
    (y τ e : ℂ) (hτ : 0 < τ.im)
    (hR : e ∉ faddeevModularUHPPoles γ (m + 1) τ)
    (hL : e + y ∉ faddeevModularUHPZeros γ (m + p) τ) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ z in 𝓝 e, ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, δ ≤ ‖z - u‖) ∧
      (∀ᶠ z in 𝓝 e, ∀ u ∈ faddeevModularUHPZeros γ (m + p) τ,
        δ ≤ ‖z + y - u‖) := by
  obtain ⟨δR, hδR, hnearR⟩ := exists_eventually_norm_sub_ge_of_isClosed
    (isClosed_faddeevModularUHPPoles γ (m + 1) τ hτ) hR
  obtain ⟨δL, hδL, hnearL⟩ := exists_eventually_norm_sub_ge_of_isClosed
    (isClosed_faddeevModularUHPZeros γ (m + p) τ hτ) hL
  refine ⟨min δR δL, lt_min hδR hδL, ?_, ?_⟩
  · filter_upwards [hnearR] with z hz u hu
    exact (min_le_left _ _).trans (hz u hu)
  · have hnearL' := ((continuous_add_const y).tendsto e).eventually hnearL
    filter_upwards [hnearL'] with z hz u hu
    exact (min_le_right _ _).trans (hz u hu)

/-- Near a point outside both genuine pole families, the five-term kernel is bounded, even
when its totalized value at the point is not the removable extension. This supplies the
boundedness hypothesis of `integral_boundary_rect_eq_sum_residues_of_bounded`. -/
theorem isBoundedUnder_fiveTermKernelUHP_punctured
    (γ : SL(2, ℤ)) (ℓ p m : ℤ) (w y τ e : ℂ) (hτ : 0 < τ.im)
    (hR : e ∉ faddeevModularUHPPoles γ (m + 1) τ)
    (hL : e + y ∉ faddeevModularUHPZeros γ (m + p) τ) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] e)
      (fun z => ‖fiveTermKernelUHP γ ℓ p w y τ m z‖) := by
  obtain ⟨δ, hδ, hnearR, hnearL⟩ :=
    fiveTerm_punctured_separation γ p m y τ e hτ hR hL
  obtain ⟨C, hC⟩ := exists_norm_fiveTermKernelUHP_le
    γ ℓ p w y τ hτ m δ hδ
  let E : ℂ → ℝ := fiveTermGrowthExponent γ ℓ p m w y τ
  have hE : Continuous E :=
    continuous_fiveTermKernelUHP_growthExponent γ ℓ p m w y τ
  have hB : IsBoundedUnder (· ≤ ·) (𝓝 e) (fun z => C * Real.exp (E z)) :=
    (continuous_const.mul (Real.continuous_exp.comp hE)).continuousAt.isBoundedUnder_le
  obtain ⟨B, hB⟩ := hB
  have hnear : ∀ᶠ z in 𝓝 e,
      ‖fiveTermKernelUHP γ ℓ p w y τ m z‖ ≤ B := by
    filter_upwards [hnearR, hnearL, hB] with z hzR hzL hzB
    exact (hC z hzR hzL).trans hzB
  exact ⟨B, hnear.filter_mono nhdsWithin_le_nhds⟩

/-! ### The regions of the contour argument

Each bound specializes the global one; in the upper and lower regions the distance hypotheses
hold automatically. -/

/-- Poles are far above their zero rows; used by
`exists_norm_fiveTermKernelUHP_le_upper`. -/
private lemma fiveTerm_high_poles_far (γ : SL(2, ℤ)) (m : ℤ) (τ : ℂ)
    (hτ : 0 < τ.im) (T : ℝ) (z : ℂ)
    (hT : 1 / ‖fltDenominator (γ : Mat(2, ℤ)) τ‖ ≤ T)
    (hz : T ≤ (z / fltDenominator (γ : Mat(2, ℤ)) τ).im) :
    ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, 1 ≤ ‖z - u‖ := by
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  have he : e ≠ 0 := fltDenominator_ne_zero_of_im_ne_zero γ hτ.ne'
  intro u hu
  have hu0 : (u / e).im ≤ 0 :=
    im_nonpos_of_qPochhammer_eq_zero (flt_im_pos γ hτ) hu.1
  exact fiveTerm_norm_of_scaled_im_gap e z u he (by linarith)

/-- Zeros are far below their zero rows; used by `exists_norm_fiveTermKernelUHP_le_upper`
and `exists_norm_fiveTermKernelUHP_le_top`. -/
private lemma fiveTerm_high_zeros_far (γ : SL(2, ℤ)) (m p : ℤ) (y τ : ℂ)
    (hτ : 0 < τ.im) (δ T : ℝ) (z : ℂ)
    (hT : δ + ‖y + ((m + p : ℤ) : ℂ) * τ‖ ≤ T) (hz : T ≤ z.im) :
    ∀ u ∈ faddeevModularUHPZeros γ (m + p) τ, δ ≤ ‖z + y - u‖ := by
  intro u hu
  have hu0 : (u + ((m + p : ℤ) : ℂ) * τ).im ≤ 0 :=
    im_nonpos_of_qPochhammer_eq_zero hτ hu.1
  have hb := fiveTerm_neg_norm_le_im (y + ((m + p : ℤ) : ℂ) * τ)
  simp only [add_im] at hb
  apply fiveTerm_norm_of_im_gap (z + y) u
  simp only [add_im] at hu0 ⊢
  linarith

/-- Both growth exponents with period `τ` vanish high above the zero rows; used by
`exists_norm_fiveTermKernelUHP_le_upper` and
`exists_norm_fiveTermKernelUHP_le_top`. -/
private lemma fiveTerm_high_tau_growth (m p : ℤ) (y τ z : ℂ) (T : ℝ)
    (hT : ‖((m + 1 : ℤ) : ℂ) * τ‖ +
      ‖y + ((m + p : ℤ) : ℂ) * τ‖ ≤ T) (hz : T ≤ z.im) :
    qPochhammerGrowth (z + ((m + 1 : ℤ) : ℂ) * τ) τ = 0 ∧
      qPochhammerGrowth (z + y + ((m + p : ℤ) : ℂ) * τ) τ = 0 := by
  have ha := fiveTerm_neg_norm_le_im (((m + 1 : ℤ) : ℂ) * τ)
  have hb := fiveTerm_neg_norm_le_im (y + ((m + p : ℤ) : ℂ) * τ)
  simp only [add_im] at hb
  have h1 : 0 ≤ (z + ((m + 1 : ℤ) : ℂ) * τ).im := by
    simp only [add_im]
    linarith [norm_nonneg (y + ((m + p : ℤ) : ℂ) * τ)]
  have h2 : 0 ≤ (z + y + ((m + p : ℤ) : ℂ) * τ).im := by
    simp only [add_im]
    linarith [norm_nonneg (((m + 1 : ℤ) : ℂ) * τ)]
  exact ⟨qPochhammerGrowth_of_nonneg τ h1, qPochhammerGrowth_of_nonneg τ h2⟩

/-- Both growth exponents with period `σ` vanish high in the modular variable; used by
`exists_norm_fiveTermKernelUHP_le_upper`. -/
private lemma fiveTerm_high_sigma_growth (γ : SL(2, ℤ)) (y τ z : ℂ) (T : ℝ)
    (hT0 : 0 ≤ T) (hTy : ‖y / fltDenominator (γ : Mat(2, ℤ)) τ‖ ≤ T)
    (hz : T ≤ (z / fltDenominator (γ : Mat(2, ℤ)) τ).im) :
    qPochhammerGrowth (z / fltDenominator (γ : Mat(2, ℤ)) τ)
        (flt (γ : Mat(2, ℤ)) τ) = 0 ∧
      qPochhammerGrowth ((z + y) / fltDenominator (γ : Mat(2, ℤ)) τ)
        (flt (γ : Mat(2, ℤ)) τ) = 0 := by
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  have hy := fiveTerm_neg_norm_le_im (y / e)
  have h1 : 0 ≤ (z / e).im := le_trans hT0 hz
  have h2 : 0 ≤ ((z + y) / e).im := by
    rw [add_div, add_im]
    linarith
  exact ⟨qPochhammerGrowth_of_nonneg _ h1, qPochhammerGrowth_of_nonneg _ h2⟩

/-- High in both variables, `‖K_m(z)‖ ≤ C exp(-2π Im(λz))` with `λ = cw/ε + ℓ`: the decay along
the contour upwards when `Re λ > 0`, the first convergence condition of
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`]. -/
theorem exists_norm_fiveTermKernelUHP_le_upper (γ : SL(2, ℤ)) (ℓ p : ℤ) (w y τ : ℂ)
    (hτ : 0 < τ.im) (m : ℤ) :
    ∃ C T : ℝ, ∀ z : ℂ, T ≤ z.im → T ≤ (z / fltDenominator (γ : Mat(2, ℤ)) τ).im →
      ‖fiveTermKernelUHP γ ℓ p w y τ m z‖ ≤
        C * Real.exp (-2 * π * ((((γ 1 0 : ℤ) : ℂ) * w / fltDenominator (γ : Mat(2, ℤ)) τ +
          ℓ) * z).im) := by
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  let α : ℂ := ((m + 1 : ℤ) : ℂ) * τ
  let β : ℂ := y + ((m + p : ℤ) : ℂ) * τ
  have he : e ≠ 0 := fltDenominator_ne_zero_of_im_ne_zero γ hτ.ne'
  have hen : 0 < ‖e‖ := norm_pos_iff.mpr he
  obtain ⟨C, hC⟩ :=
    exists_norm_fiveTermKernelUHP_le γ ℓ p w y τ hτ m 1 (by norm_num)
  let T : ℝ := max (1 / ‖e‖) (1 + ‖α‖ + ‖β‖ + ‖y / e‖)
  refine ⟨C, T, ?_⟩
  intro z hz hze
  have hTε : 1 / ‖e‖ ≤ T := le_max_left _ _
  have hT : 1 + ‖α‖ + ‖β‖ + ‖y / e‖ ≤ T := le_max_right _ _
  have hT0 : 0 ≤ T := le_trans (one_div_pos.mpr hen).le hTε
  have hp := fiveTerm_high_poles_far γ m τ hτ T z hTε hze
  have hz' := fiveTerm_high_zeros_far γ m p y τ hτ 1 T z
    (by dsimp [β] at hT ⊢; linarith [norm_nonneg α, norm_nonneg (y / e)]) hz
  obtain ⟨h1, h4⟩ := fiveTerm_high_tau_growth m p y τ z T
    (by dsimp [α, β] at hT ⊢; linarith [norm_nonneg (y / e)]) hz
  obtain ⟨h2, h3⟩ := fiveTerm_high_sigma_growth γ y τ z T hT0
    (by dsimp [α, β, e] at hT ⊢; linarith [norm_nonneg α, norm_nonneg β]) hze
  simpa only [fiveTermGrowthExponent, h1, h2, h3, h4, sub_zero,
    add_zero] using hC z hp hz'

/-- The real algebra behind the lower region phase identity; used by
`fiveTerm_im_div_identity`. -/
private lemma fiveTerm_im_mul_identity (e a b : ℂ) :
    (e * a).im * (e * b).im - Complex.normSq e * a.im * b.im =
      e.im * (e * a * b).im := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.normSq_apply]
  ring

/-- The imaginary parts of two divided arguments, used by `fiveTerm_im_c_mul_div`. -/
private lemma fiveTerm_im_div_identity (e y z : ℂ) (he : e ≠ 0) :
    y.im * z.im - Complex.normSq e * (y / e).im * (z / e).im =
      e.im * (y * z / e).im := by
  have hy : e * (y / e) = y := by field_simp
  have hz : e * (z / e) = z := by field_simp
  simpa only [hy, hz, mul_div_assoc] using fiveTerm_im_mul_identity e (y / e) (z / e)

/-- The modular denominator's imaginary part converts the cross term in
`fiveTerm_linear_generic`. -/
private lemma fiveTerm_im_c_mul_div (c : ℝ) (e y z τ : ℂ) (he : e ≠ 0)
    (hτ : 0 < τ.im) (he_im : e.im = c * τ.im) :
    (((c : ℂ) * y / e) * z).im =
      (y.im * z.im - Complex.normSq e * (y / e).im * (z / e).im) / τ.im := by
  have hcx : (((c : ℂ) * y / e) * z) = (c : ℂ) * (y * z / e) := by ring
  rw [hcx, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hi := fiveTerm_im_div_identity e y z he
  rw [he_im] at hi
  apply (eq_div_iff hτ.ne').mpr
  nlinarith

/-- The parameter identity for the lower Gaussian exponent, used by
`fiveTerm_linear_identity`. -/
private lemma fiveTerm_linear_generic (c ℓ p : ℝ) (e w y z τ σ : ℂ)
    (he : e ≠ 0) (hτ : 0 < τ.im) (he_im : e.im = c * τ.im)
    (hσ : σ.im = τ.im / Complex.normSq e) :
    ((((c : ℂ) * w / e + ℓ) * z).im -
        z.im * ((((1 - p : ℝ) : ℂ) * τ - y).im) / τ.im -
        (z / e).im * (y / e).im / σ.im) =
      ((((c : ℂ) * (w + y) / e + ℓ + p - 1) * z).im) := by
  have hcx : (((c : ℂ) * (w + y) / e + ℓ + p - 1) * z) =
      (((c : ℂ) * w / e + ℓ) * z) + (((c : ℂ) * y / e) * z) +
        (((p - 1 : ℝ) : ℂ) * z) := by push_cast; ring
  have hmu : (((c : ℂ) * (w + y) / e + ℓ + p - 1) * z).im =
      (((c : ℂ) * w / e + ℓ) * z).im + (((c : ℂ) * y / e) * z).im +
        (p - 1) * z.im := by
    rw [hcx]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
  have ha : ((((1 - p : ℝ) : ℂ) * τ - y).im) = (1 - p) * τ.im - y.im := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
  have hs : (z / e).im * (y / e).im / σ.im =
      Complex.normSq e * (z / e).im * (y / e).im / τ.im := by
    rw [hσ]
    field_simp [hτ.ne', (Complex.normSq_pos.mpr he).ne']
  rw [hmu, ha, hs, fiveTerm_im_c_mul_div c e y z τ he hτ he_im]
  field_simp [hτ.ne']
  ring

/-- The exact imaginary part identity in the lower region of the five term kernel; used by
`fiveTerm_lower_theta_exponent`. -/
private lemma fiveTerm_linear_identity (γ : SL(2, ℤ)) (ℓ p m : ℤ) (w y z τ : ℂ)
    (hτ : 0 < τ.im) :
    ((((γ 1 0 : ℤ) : ℂ) * w / fltDenominator (γ : Mat(2, ℤ)) τ + ℓ) * z).im -
      z.im * (((((m + 1 : ℤ) : ℂ) * τ) -
        (y + ((m + p : ℤ) : ℂ) * τ)).im) / τ.im -
      (z / fltDenominator (γ : Mat(2, ℤ)) τ).im *
        (y / fltDenominator (γ : Mat(2, ℤ)) τ).im /
        (flt (γ : Mat(2, ℤ)) τ).im =
      ((((γ 1 0 : ℤ) : ℂ) * (w + y) /
        fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1) * z).im := by
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  have he : e ≠ 0 := fltDenominator_ne_zero_of_im_ne_zero γ hτ.ne'
  have hei : e.im = (γ 1 0 : ℝ) * τ.im := fltDenominator_im (γ : Mat(2, ℤ)) τ
  have hs : σ.im = τ.im / Complex.normSq e := flt_im γ τ
  have h := fiveTerm_linear_generic (γ 1 0 : ℝ) (ℓ : ℝ) (p : ℝ)
    e w y z τ σ he hτ hei hs
  have hshift : ((((m + 1 : ℤ) : ℂ) * τ) -
      (y + ((m + p : ℤ) : ℂ) * τ)) = (((1 - (p : ℝ)) : ℂ) * τ - y) := by
    push_cast
    ring
  rw [hshift]
  simpa only [e, σ, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_intCast] using h

/-- The four Gaussian exponents combine into the lower region phase and a constant; used by
`exists_norm_fiveTermKernelUHP_le_lower`. -/
private lemma fiveTerm_lower_theta_exponent (γ : SL(2, ℤ)) (ℓ p m : ℤ)
    (w y z τ : ℂ) (hτ : 0 < τ.im) :
    -2 * π * ((((γ 1 0 : ℤ) : ℂ) * w /
        fltDenominator (γ : Mat(2, ℤ)) τ + ℓ) * z).im +
      qThetaGrowth (z + ((m + 1 : ℤ) : ℂ) * τ) τ -
      qThetaGrowth (z / fltDenominator (γ : Mat(2, ℤ)) τ)
        (flt (γ : Mat(2, ℤ)) τ) +
      qThetaGrowth ((z + y) / fltDenominator (γ : Mat(2, ℤ)) τ)
        (flt (γ : Mat(2, ℤ)) τ) -
      qThetaGrowth (z + y + ((m + p : ℤ) : ℂ) * τ) τ =
    -2 * π * ((((γ 1 0 : ℤ) : ℂ) * (w + y) /
        fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1) * z).im +
      (qThetaGrowth (((m + 1 : ℤ) : ℂ) * τ) τ -
        qThetaGrowth (y + ((m + p : ℤ) : ℂ) * τ) τ +
        qThetaGrowth (y / fltDenominator (γ : Mat(2, ℤ)) τ)
          (flt (γ : Mat(2, ℤ)) τ)) := by
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  let α : ℂ := ((m + 1 : ℤ) : ℂ) * τ
  let β : ℂ := y + ((m + p : ℤ) : ℂ) * τ
  let a := y / e
  let u := z / e
  have hα := qThetaGrowth_add z α τ
  have hβ := qThetaGrowth_add z β τ
  have hs := qThetaGrowth_add u a σ
  have harg : (z + y) / e = u + a := by dsimp [u, a]; ring
  rw [← harg] at hs
  have hlin := fiveTerm_linear_identity γ ℓ p m w y z τ hτ
  have hβarg : z + β = z + y + ((m + p : ℤ) : ℂ) * τ := by
    dsimp [β]
    ring
  rw [hβarg] at hβ
  dsimp [α, β, e, σ, a, u] at hα hβ hs hlin ⊢
  linear_combination -2 * π * hlin + hα - hβ + hs

/-- Poles are far above points low in `z`; used by
`exists_norm_fiveTermKernelUHP_le_lower`. -/
private lemma fiveTerm_low_poles_far (γ : SL(2, ℤ)) (m : ℤ) (τ : ℂ)
    (hτ : 0 < τ.im) (T : ℝ) (z : ℂ)
    (hT : 1 + ‖((m + 1 : ℤ) : ℂ) * τ‖ ≤ T) (hz : z.im ≤ -T) :
    ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, 1 ≤ ‖z - u‖ := by
  intro u hu
  have hui := im_le_im_add_of_mem_faddeevModularUHPPoles γ (m + 1) hτ hu
  have ha := Complex.im_le_norm (((m + 1 : ℤ) : ℂ) * τ)
  have hgap : 1 ≤ u.im - z.im := by
    simp only [add_im] at hui
    linarith
  simpa only [norm_sub_rev] using fiveTerm_norm_of_im_gap u z hgap

/-- Zeros are far below points low in the modular variable; used by
`exists_norm_fiveTermKernelUHP_le_lower`. -/
private lemma fiveTerm_low_zeros_far (γ : SL(2, ℤ)) (m p : ℤ) (y τ : ℂ)
    (hτ : 0 < τ.im) (T : ℝ) (z : ℂ)
    (hT : 1 / ‖fltDenominator (γ : Mat(2, ℤ)) τ‖ +
      ‖y / fltDenominator (γ : Mat(2, ℤ)) τ‖ ≤ T)
    (hz : (z / fltDenominator (γ : Mat(2, ℤ)) τ).im ≤ -T) :
    ∀ u ∈ faddeevModularUHPZeros γ (m + p) τ, 1 ≤ ‖z + y - u‖ := by
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  have he : e ≠ 0 := fltDenominator_ne_zero_of_im_ne_zero γ hτ.ne'
  intro u hu
  have hui := im_le_im_div_of_mem_faddeevModularUHPZeros γ (m + p) hτ hu
  have hy := Complex.im_le_norm (y / e)
  have hgap : 1 / ‖e‖ ≤ (u / e).im - ((z + y) / e).im := by
    rw [add_div, add_im]
    linarith [flt_im_pos γ hτ]
  simpa only [norm_sub_rev] using
    fiveTerm_norm_of_scaled_im_gap e u (z + y) he hgap

/-- All four growth exponents are Gaussian low in both variables; used by
`exists_norm_fiveTermKernelUHP_le_lower`. -/
private lemma fiveTerm_low_growth (γ : SL(2, ℤ)) (m p : ℤ) (y τ z : ℂ) (T : ℝ)
    (hT : ‖((m + 1 : ℤ) : ℂ) * τ‖ +
      ‖y + ((m + p : ℤ) : ℂ) * τ‖ +
      ‖y / fltDenominator (γ : Mat(2, ℤ)) τ‖ ≤ T)
    (hz : z.im ≤ -T)
    (hze : (z / fltDenominator (γ : Mat(2, ℤ)) τ).im ≤ -T) :
    qPochhammerGrowth (z + ((m + 1 : ℤ) : ℂ) * τ) τ =
        qThetaGrowth (z + ((m + 1 : ℤ) : ℂ) * τ) τ ∧
      qPochhammerGrowth (z / fltDenominator (γ : Mat(2, ℤ)) τ)
        (flt (γ : Mat(2, ℤ)) τ) =
        qThetaGrowth (z / fltDenominator (γ : Mat(2, ℤ)) τ)
          (flt (γ : Mat(2, ℤ)) τ) ∧
      qPochhammerGrowth ((z + y) / fltDenominator (γ : Mat(2, ℤ)) τ)
        (flt (γ : Mat(2, ℤ)) τ) =
        qThetaGrowth ((z + y) / fltDenominator (γ : Mat(2, ℤ)) τ)
          (flt (γ : Mat(2, ℤ)) τ) ∧
      qPochhammerGrowth (z + y + ((m + p : ℤ) : ℂ) * τ) τ =
        qThetaGrowth (z + y + ((m + p : ℤ) : ℂ) * τ) τ := by
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  have ha := Complex.im_le_norm (((m + 1 : ℤ) : ℂ) * τ)
  have hb := Complex.im_le_norm (y + ((m + p : ℤ) : ℂ) * τ)
  simp only [add_im] at hb
  have hy := Complex.im_le_norm (y / e)
  have h1 : (z + ((m + 1 : ℤ) : ℂ) * τ).im ≤ 0 := by
    simp only [add_im]
    linarith [norm_nonneg (y + ((m + p : ℤ) : ℂ) * τ), norm_nonneg (y / e)]
  have h4 : (z + y + ((m + p : ℤ) : ℂ) * τ).im ≤ 0 := by
    simp only [add_im]
    linarith [norm_nonneg (((m + 1 : ℤ) : ℂ) * τ), norm_nonneg (y / e)]
  have h2 : (z / e).im ≤ 0 := by
    linarith [norm_nonneg (((m + 1 : ℤ) : ℂ) * τ),
      norm_nonneg (y + ((m + p : ℤ) : ℂ) * τ), norm_nonneg (y / e)]
  have h3 : ((z + y) / e).im ≤ 0 := by
    rw [add_div, add_im]
    linarith [norm_nonneg (((m + 1 : ℤ) : ℂ) * τ),
      norm_nonneg (y + ((m + p : ℤ) : ℂ) * τ)]
  exact ⟨qPochhammerGrowth_of_nonpos τ h1,
    qPochhammerGrowth_of_nonpos _ h2, qPochhammerGrowth_of_nonpos _ h3,
    qPochhammerGrowth_of_nonpos τ h4⟩

/-- Absorb a bounded exponent error into the constant of a kernel estimate; used by
`exists_norm_fiveTermKernelUHP_le_lower`,
`exists_norm_fiveTermKernelUHP_le_top`, and
`exists_norm_fiveTermKernelUHP_le_right`. -/
private lemma fiveTerm_absorb_exponent {N C E F H : ℝ} (h : N ≤ C * Real.exp E)
    (hE : E ≤ F + H) : N ≤ (|C| * Real.exp H) * Real.exp F := by
  calc
    N ≤ C * Real.exp E := h
    _ ≤ |C| * Real.exp E :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    _ ≤ |C| * Real.exp (F + H) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE) (abs_nonneg C)
    _ = _ := by rw [Real.exp_add]; ring

/-- Low in both variables, `‖K_m(z)‖ ≤ C exp(-2π Im(μz))` with `μ = c(w+y)/ε + ℓ + p - 1`: the
decay along the contour downwards when `Re μ < 0`, the corrected second convergence condition of
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`], whose printed form omits `p`. -/
theorem exists_norm_fiveTermKernelUHP_le_lower (γ : SL(2, ℤ)) (ℓ p : ℤ) (w y τ : ℂ)
    (hτ : 0 < τ.im) (m : ℤ) :
    ∃ C T : ℝ, ∀ z : ℂ, z.im ≤ -T → (z / fltDenominator (γ : Mat(2, ℤ)) τ).im ≤ -T →
      ‖fiveTermKernelUHP γ ℓ p w y τ m z‖ ≤
        C * Real.exp (-2 * π * ((((γ 1 0 : ℤ) : ℂ) * (w + y) /
          fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1) * z).im) := by
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  let α : ℂ := ((m + 1 : ℤ) : ℂ) * τ
  let β : ℂ := y + ((m + p : ℤ) : ℂ) * τ
  obtain ⟨C, hC⟩ :=
    exists_norm_fiveTermKernelUHP_le γ ℓ p w y τ hτ m 1 (by norm_num)
  let B : ℝ := qThetaGrowth α τ - qThetaGrowth β τ + qThetaGrowth (y / e) σ
  let T : ℝ := 1 / ‖e‖ + 1 + ‖α‖ + ‖β‖ + ‖y / e‖ + ‖τ‖ + ‖σ‖
  refine ⟨|C| * Real.exp B, T, ?_⟩
  intro z hz hze
  have he : e ≠ 0 := fltDenominator_ne_zero_of_im_ne_zero γ hτ.ne'
  have hT1 : 1 + ‖α‖ ≤ T := by
    dsimp [T]
    linarith [norm_nonneg β, norm_nonneg (y / e), norm_nonneg τ,
      norm_nonneg σ, (one_div_pos.mpr (norm_pos_iff.mpr he))]
  have hT2 : 1 / ‖e‖ + ‖y / e‖ ≤ T := by
    dsimp [T]
    linarith [norm_nonneg α, norm_nonneg β, norm_nonneg τ, norm_nonneg σ]
  have hT3 : ‖α‖ + ‖β‖ + ‖y / e‖ ≤ T := by
    dsimp [T]
    linarith [norm_nonneg τ, norm_nonneg σ,
      (one_div_pos.mpr (norm_pos_iff.mpr he))]
  have hp := fiveTerm_low_poles_far γ m τ hτ T z hT1 hz
  have hz' := fiveTerm_low_zeros_far γ m p y τ hτ T z hT2 hze
  obtain ⟨h1, h2, h3, h4⟩ := fiveTerm_low_growth γ m p y τ z T hT3 hz hze
  have hbase := hC z hp hz'
  unfold fiveTermGrowthExponent at hbase
  rw [h1, h2, h3, h4, fiveTerm_lower_theta_exponent γ ℓ p m w y z τ hτ]
    at hbase
  exact fiveTerm_absorb_exponent hbase (le_refl _)

/-- The q-product shift estimate as a one-sided bound; used by
`exists_norm_fiveTermKernelUHP_le_top` and
`exists_norm_fiveTermKernelUHP_le_right`. -/
private lemma fiveTerm_shift_bound (a σ : ℂ) (hσ : 0 < σ.im) :
    ∃ D, ∀ u : ℂ, qPochhammerGrowth (u + a) σ - qPochhammerGrowth u σ ≤
      2 * π * a.im * min u.im 0 / σ.im + D := by
  obtain ⟨D, hD⟩ := exists_abs_qPochhammerGrowth_add_sub_le a σ hσ
  refine ⟨D, fun u => ?_⟩
  linarith [hD u, le_abs_self (qPochhammerGrowth (u + a) σ -
    qPochhammerGrowth u σ - 2 * π * a.im * min u.im 0 / σ.im)]

/-- High in `z`, away from the right poles,
`‖K_m(z)‖ ≤ C exp(-2π Im(λz) + 2π Im(y/ε) min(Im(z/ε), 0)/Im σ)`: the bound on the upper closing
side of the rectangles, in the sectors where the source's asymptotics are governed by a quotient
of θ-functions. -/
theorem exists_norm_fiveTermKernelUHP_le_top (γ : SL(2, ℤ)) (ℓ p : ℤ) (w y τ : ℂ)
    (hτ : 0 < τ.im) (m : ℤ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C T : ℝ, ∀ z : ℂ, T ≤ z.im →
      (∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, δ ≤ ‖z - u‖) →
      ‖fiveTermKernelUHP γ ℓ p w y τ m z‖ ≤
        C * Real.exp (-2 * π * ((((γ 1 0 : ℤ) : ℂ) * w / fltDenominator (γ : Mat(2, ℤ)) τ +
            ℓ) * z).im +
          2 * π * (y / fltDenominator (γ : Mat(2, ℤ)) τ).im *
            min (z / fltDenominator (γ : Mat(2, ℤ)) τ).im 0 / (flt (γ : Mat(2, ℤ)) τ).im) := by
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  let α : ℂ := ((m + 1 : ℤ) : ℂ) * τ
  let β : ℂ := y + ((m + p : ℤ) : ℂ) * τ
  obtain ⟨C, hC⟩ :=
    exists_norm_fiveTermKernelUHP_le γ ℓ p w y τ hτ m δ hδ
  obtain ⟨D, hD⟩ := fiveTerm_shift_bound (y / e) σ (flt_im_pos γ hτ)
  let T : ℝ := δ + 1 + ‖α‖ + ‖β‖
  refine ⟨|C| * Real.exp D, T, ?_⟩
  intro z hz hp
  have hz' := fiveTerm_high_zeros_far γ m p y τ hτ δ T z
    (by dsimp [T, β]; linarith [norm_nonneg α]) hz
  obtain ⟨h1, h4⟩ := fiveTerm_high_tau_growth m p y τ z T
    (by dsimp [T, α, β]; linarith [hδ]) hz
  have harg : (z + y) / e = z / e + y / e := by ring
  have hdiff := hD (z / e)
  rw [← harg] at hdiff
  have hbase := hC z hp hz'
  have hE : fiveTermGrowthExponent γ ℓ p m w y τ z ≤
      (-2 * π * ((((γ 1 0 : ℤ) : ℂ) * w / e + ℓ) * z).im +
        2 * π * (y / e).im * min (z / e).im 0 / σ.im) + D := by
    unfold fiveTermGrowthExponent
    rw [h1, h4]
    linarith [hdiff]
  exact fiveTerm_absorb_exponent hbase hE

/-- The linear phase after the modular shift, used by `fiveTerm_right_phase`. -/
private lemma fiveTerm_right_phase_generic (c : ℝ) (e σ L w y z τ : ℂ)
    (he : e ≠ 0) (hτ : 0 < τ.im) (he_im : e.im = c * τ.im)
    (hσ : σ.im = τ.im / Complex.normSq e) (hL : L.im = c * (w / e).im) :
    -2 * π * (L * z).im + 2 * π * (y / e).im * (z / e).im / σ.im =
      -2 * π * c * ((w + y) / e).im * z.re +
        (2 * π * ((y / e).im * e.re / τ.im - L.re)) * z.im := by
  have hdiv : (z / e).im / σ.im =
      (z.im * e.re - z.re * e.im) / τ.im := by
    rw [Complex.div_im, hσ]
    field_simp [hτ.ne', (Complex.normSq_pos.mpr he).ne']
  have hwy : ((w + y) / e).im = (w / e).im + (y / e).im := by
    rw [add_div, Complex.add_im]
  rw [Complex.mul_im, hwy, hL, mul_div_assoc, hdiv, he_im]
  field_simp [hτ.ne']
  ring

/-- The shifted kernel exponent is affine in `Re z` and `Im z`, with real-axis slope
`-2πc Im((w+y)/ε)`. It supplies `exists_norm_fiveTermKernelUHP_le_right` and the
right branch of the exponent in `tendsto_integral_fiveTermKernelUHP_top`. -/
theorem fiveTerm_right_phase (γ : SL(2, ℤ)) (ℓ : ℤ) (w y z τ : ℂ)
    (hτ : 0 < τ.im) :
    -2 * π * ((((γ 1 0 : ℤ) : ℂ) * w /
        fltDenominator (γ : Mat(2, ℤ)) τ + ℓ) * z).im +
      2 * π * (y / fltDenominator (γ : Mat(2, ℤ)) τ).im *
        (z / fltDenominator (γ : Mat(2, ℤ)) τ).im /
        (flt (γ : Mat(2, ℤ)) τ).im =
      -2 * π * (γ 1 0 : ℝ) *
        ((w + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im * z.re +
      (2 * π * ((y / fltDenominator (γ : Mat(2, ℤ)) τ).im *
        (fltDenominator (γ : Mat(2, ℤ)) τ).re / τ.im -
        (((γ 1 0 : ℤ) : ℂ) * w / fltDenominator (γ : Mat(2, ℤ)) τ + ℓ).re)) * z.im := by
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  let L : ℂ := ((γ 1 0 : ℤ) : ℂ) * w / e + ℓ
  have he : e ≠ 0 := fltDenominator_ne_zero_of_im_ne_zero γ hτ.ne'
  have hei : e.im = (γ 1 0 : ℝ) * τ.im := fltDenominator_im (γ : Mat(2, ℤ)) τ
  have hs : σ.im = τ.im / Complex.normSq e := flt_im γ τ
  have hL : L.im = (γ 1 0 : ℝ) * (w / e).im := by
    dsimp [L]
    rw [mul_div_assoc, Complex.mul_im]
    simp only [Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero]
  have h := fiveTerm_right_phase_generic (γ 1 0 : ℝ) e σ L w y z τ
    he hτ hei hs hL
  simpa only [e, σ, L] using h

/-- Division by a denominator with positive imaginary part sends the far right strip low; used by
`fiveTerm_right_geometry`. -/
private lemma fiveTerm_right_div_im (e z : ℂ) (Y A : ℝ)
    (he : 0 < e.im) (hn : 0 < Complex.normSq e)
    (hx : (|e.re| * Y + Complex.normSq e * A) / e.im ≤ z.re)
    (hy : |z.im| ≤ Y) : (z / e).im ≤ -A := by
  have hreal : z.im * e.re ≤ |e.re| * Y := by
    calc
      z.im * e.re ≤ |z.im * e.re| := le_abs_self _
      _ = |z.im| * |e.re| := abs_mul _ _
      _ ≤ Y * |e.re| := mul_le_mul_of_nonneg_right hy (abs_nonneg _)
      _ = |e.re| * Y := by ring
  have hXmul : |e.re| * Y + Complex.normSq e * A ≤ z.re * e.im :=
    (div_le_iff₀ he).mp hx
  rw [show (z / e).im =
    (z.im * e.re - z.re * e.im) / Complex.normSq e by
      rw [Complex.div_im]
      ring]
  apply (div_le_iff₀ hn).mpr
  nlinarith [hreal, hXmul]

/-- A lower bound on the zero row gives the left pole distance in the right region; used by
`fiveTerm_right_geometry`. -/
private lemma fiveTerm_right_zeros_far (γ : SL(2, ℤ)) (m p : ℤ) (y τ z : ℂ)
    (hτ : 0 < τ.im) (δ : ℝ)
    (hz : ((z + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im ≤
      -(flt (γ : Mat(2, ℤ)) τ).im -
        δ / ‖fltDenominator (γ : Mat(2, ℤ)) τ‖) :
    ∀ u ∈ faddeevModularUHPZeros γ (m + p) τ, δ ≤ ‖z + y - u‖ := by
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  have he : e ≠ 0 := fltDenominator_ne_zero_of_im_ne_zero γ hτ.ne'
  intro u hu
  have hui := im_le_im_div_of_mem_faddeevModularUHPZeros γ (m + p) hτ hu
  change (flt (γ : Mat(2, ℤ)) τ).im ≤ (u / e).im at hui
  change ((z + y) / e).im ≤
    -(flt (γ : Mat(2, ℤ)) τ).im - δ / ‖e‖ at hz
  have hgap : δ / ‖e‖ ≤ (u / e).im - ((z + y) / e).im := by
    linarith [flt_im_pos γ hτ]
  simpa only [norm_sub_rev] using
    fiveTerm_norm_of_scaled_im_gap e u (z + y) he hgap

/-- The right strip admits a uniform height threshold for the modular variable; used by
`exists_norm_fiveTermKernelUHP_le_right`. -/
private lemma fiveTerm_right_geometry (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (m p : ℤ) (y τ : ℂ) (hτ : 0 < τ.im) (δ Y : ℝ) (hδ : 0 < δ) :
    ∃ X : ℝ, ∀ z : ℂ, X ≤ z.re → |z.im| ≤ Y →
      (z / fltDenominator (γ : Mat(2, ℤ)) τ).im ≤ 0 ∧
      (∀ u ∈ faddeevModularUHPZeros γ (m + p) τ, δ ≤ ‖z + y - u‖) := by
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  let a := y / e
  let A : ℝ := σ.im + δ / ‖e‖ + ‖a‖ + 1
  have he : e ≠ 0 := fltDenominator_ne_zero_of_im_ne_zero γ hτ.ne'
  have hei : e.im = (γ 1 0 : ℝ) * τ.im := fltDenominator_im (γ : Mat(2, ℤ)) τ
  have hepos : 0 < e.im := by
    rw [hei]
    exact mul_pos (by exact_mod_cast hc) hτ
  refine ⟨(|e.re| * Y + Complex.normSq e * A) / e.im, ?_⟩
  intro z hx hy
  have hze := fiveTerm_right_div_im e z Y A hepos (Complex.normSq_pos.mpr he) hx hy
  have hA : 0 ≤ A := by
    dsimp [A]
    have hen : 0 < ‖e‖ := norm_pos_iff.mpr he
    have hσ : 0 < σ.im := flt_im_pos γ hτ
    positivity
  have hσz : (z / e).im ≤ 0 := by linarith
  have hzy : ((z + y) / e).im ≤ -σ.im - δ / ‖e‖ := by
    rw [add_div, add_im]
    have hay := Complex.im_le_norm a
    dsimp [A] at hze
    linarith
  exact ⟨hσz, fiveTerm_right_zeros_far γ m p y τ z hτ δ hzy⟩

/-- Bound the numerator's growth exponent on a horizontal strip; used by
`exists_norm_fiveTermKernelUHP_le_right`. -/
private lemma fiveTerm_right_num_growth (m : ℤ) (τ z : ℂ) (hτ : 0 < τ.im)
    (Y : ℝ) (hy : |z.im| ≤ Y) :
    qPochhammerGrowth (z + ((m + 1 : ℤ) : ℂ) * τ) τ ≤
      π * (Y + ‖((m + 1 : ℤ) : ℂ) * τ‖) ^ 2 / τ.im +
        π * (Y + ‖((m + 1 : ℤ) : ℂ) * τ‖) := by
  let α : ℂ := ((m + 1 : ℤ) : ℂ) * τ
  let M : ℝ := Y + ‖α‖
  have hstrip : |(z + α).im| ≤ M := by
    rw [add_im]
    calc
      |z.im + α.im| ≤ |z.im| + |α.im| := abs_add_le _ _
      _ ≤ Y + ‖α‖ := add_le_add hy (Complex.abs_im_le_norm α)
  exact qPochhammerGrowth_le_of_abs_im_le τ (z + α) hτ hstrip

/-- The global exponent has the required rightward decay up to strip constants; used by
`exists_norm_fiveTermKernelUHP_le_right`. -/
private lemma fiveTerm_right_exponent (γ : SL(2, ℤ)) (ℓ p m : ℤ)
    (w y τ z : ℂ) (hτ : 0 < τ.im) (B D Y : ℝ)
    (hnum : qPochhammerGrowth (z + ((m + 1 : ℤ) : ℂ) * τ) τ ≤ B)
    (hshift : qPochhammerGrowth ((z + y) / fltDenominator (γ : Mat(2, ℤ)) τ)
        (flt (γ : Mat(2, ℤ)) τ) -
        qPochhammerGrowth (z / fltDenominator (γ : Mat(2, ℤ)) τ)
          (flt (γ : Mat(2, ℤ)) τ) ≤
      2 * π * (y / fltDenominator (γ : Mat(2, ℤ)) τ).im *
        (z / fltDenominator (γ : Mat(2, ℤ)) τ).im /
        (flt (γ : Mat(2, ℤ)) τ).im + D)
    (hy : |z.im| ≤ Y) :
    fiveTermGrowthExponent γ ℓ p m w y τ z ≤
    -2 * π * (γ 1 0 : ℝ) *
      ((w + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im * z.re +
      (B + D + |2 * π *
        ((y / fltDenominator (γ : Mat(2, ℤ)) τ).im *
          (fltDenominator (γ : Mat(2, ℤ)) τ).re / τ.im -
          (((γ 1 0 : ℤ) : ℂ) * w /
            fltDenominator (γ : Mat(2, ℤ)) τ + ℓ).re)| * Y) := by
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  let α : ℂ := ((m + 1 : ℤ) : ℂ) * τ
  let a := y / e
  let L : ℂ := ((γ 1 0 : ℤ) : ℂ) * w / e + ℓ
  let k : ℝ := 2 * π * (a.im * e.re / τ.im - L.re)
  have hden : -qPochhammerGrowth (z + y + ((m + p : ℤ) : ℂ) * τ) τ ≤ 0 :=
    neg_nonpos.mpr (qPochhammerGrowth_nonneg τ _ hτ)
  have hphase := fiveTerm_right_phase γ ℓ w y z τ hτ
  have hE : fiveTermGrowthExponent γ ℓ p m w y τ z ≤
      -2 * π * (γ 1 0 : ℝ) * ((w + y) / e).im * z.re + B + D + k * z.im := by
    unfold fiveTermGrowthExponent
    dsimp [L, α, e, σ, a, k] at hphase hnum hden hshift ⊢
    linear_combination hnum + hshift + hden + hphase
  have hk : k * z.im ≤ |k| * Y := by
    calc
      k * z.im ≤ |k * z.im| := le_abs_self _
      _ = |k| * |z.im| := abs_mul _ _
      _ ≤ |k| * Y := mul_le_mul_of_nonneg_left hy (abs_nonneg k)
  dsimp [L, α, e, σ, a, k] at hE hk ⊢
  linarith

/-- For `c > 0`, in the strip `|Im z| ≤ Y` far to the right and away from the right poles,
`‖K_m(z)‖ ≤ C exp(-2πc Im((w+y)/ε) Re z)`: the bound on the right closing side of the rectangles,
which decays when `Im((y+w)/ε) > 0`. -/
theorem exists_norm_fiveTermKernelUHP_le_right (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (ℓ p : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im) (m : ℤ) (δ : ℝ) (hδ : 0 < δ) (Y : ℝ) :
    ∃ C X : ℝ, ∀ z : ℂ, X ≤ z.re → |z.im| ≤ Y →
      (∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, δ ≤ ‖z - u‖) →
      ‖fiveTermKernelUHP γ ℓ p w y τ m z‖ ≤
        C * Real.exp (-2 * π * (γ 1 0 : ℝ) *
          ((w + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im * z.re) := by
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  let α : ℂ := ((m + 1 : ℤ) : ℂ) * τ
  let a := y / e
  let L : ℂ := ((γ 1 0 : ℤ) : ℂ) * w / e + ℓ
  let k : ℝ := 2 * π * (a.im * e.re / τ.im - L.re)
  let M : ℝ := Y + ‖α‖
  let B : ℝ := π * M ^ 2 / τ.im + π * M
  obtain ⟨C, hC⟩ :=
    exists_norm_fiveTermKernelUHP_le γ ℓ p w y τ hτ m δ hδ
  obtain ⟨D, hD⟩ := fiveTerm_shift_bound a σ (flt_im_pos γ hτ)
  obtain ⟨X, hgeometry⟩ := fiveTerm_right_geometry γ hc m p y τ hτ δ Y hδ
  refine ⟨|C| * Real.exp (B + D + |k| * Y), X, ?_⟩
  intro z hx hy hp
  obtain ⟨hσz, hz'⟩ := hgeometry z hx hy
  have hnum := fiveTerm_right_num_growth m τ z hτ Y hy
  have harg : (z + y) / e = z / e + a := by dsimp [a]; ring
  have hshift := hD (z / e)
  rw [← harg, min_eq_left hσz] at hshift
  have hE := fiveTerm_right_exponent γ ℓ p m w y τ z hτ B D Y hnum hshift hy
  exact fiveTerm_absorb_exponent (hC z hp hz') hE

end SIC
