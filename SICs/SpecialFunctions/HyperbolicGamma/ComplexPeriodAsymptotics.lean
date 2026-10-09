/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.FourierContourShift
import SICs.SpecialFunctions.HyperbolicGamma.ComplexPeriodComparisonBounds
import SICs.SpecialFunctions.HyperbolicGamma.EqualPeriods

/-!
# Uniform complex-period asymptotics of the hyperbolic gamma logarithm

A normalized double-sine logarithmic integral is exponentially small on a fixed closed strip,
uniformly as its complex period varies near a positive real period.

This module adapts the proof of S. N. M. Ruijsenaars, *First order analytic difference
equations and integrable quantum systems*, J. Math. Phys. 38 (1997), 1069–1146,
Proposition III.4, pp. 1096–1097,
[doi:10.1063/1.531809](https://doi.org/10.1063/1.531809). That proposition assumes positive
real periods. Radchenko--Wheeler's generator estimates in [RW26, Radchenko--Wheeler (2026),
Lemma 1, `lem:asymp`] also have fixed real periods. The uniform complex-period extension below
is needed for this formalization's boundary passage in their Theorem 3; it is not stated in
either source.

## The argument

Fix two real reference periods `a = τ₀+1` and `b = τ₀+2`. The coefficients

```text
α(τ) = (b² - (τ²+1)/2)/(b²-a²),
β(τ) = ((τ²+1)/2 - a²)/(b²-a²)
```

satisfy the two Laurent cancellation equations `α+β=1` and
`αa²+βb²=(τ²+1)/2`. They remain bounded near `τ₀`. The normalized comparison identity in
`ComplexPeriodComparison` therefore expresses the mixed-period remainder as a bounded linear
combination of two fixed equal-period remainders and the sine transform of the comparison
kernel. The equal-period terms decay exponentially by Ruijsenaars' real-period estimate.

Choose one horizontal contour below the zeros of all four hyperbolic sines. The bounds in
`ComplexPeriodComparisonBounds` give both uniform tail decay throughout the contour strip and a
common integrable majorant on its upper edge. The odd-kernel Fourier shift of Ruijsenaars,
equation (3.56), then bounds the comparison integral uniformly. A smaller common exponential
rate controls all three terms, and a fixed lower bound for `|τ|` removes the leading factor
`τ` from the normalized comparison identity.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace SIC

/-! ### Fixed-reference coefficients -/

/-- The coefficient of the first fixed equal-period reference kernel. -/
private noncomputable def complexComparisonAlpha (a b : ℝ) (τ : ℂ) : ℂ :=
  ((b : ℂ) ^ 2 - (τ ^ 2 + 1) / 2) / ((b : ℂ) ^ 2 - (a : ℂ) ^ 2)

/-- The coefficient of the second fixed equal-period reference kernel. -/
private noncomputable def complexComparisonBeta (a b : ℝ) (τ : ℂ) : ℂ :=
  ((τ ^ 2 + 1) / 2 - (a : ℂ) ^ 2) / ((b : ℂ) ^ 2 - (a : ℂ) ^ 2)

/-- The fixed-reference coefficients sum to one. -/
private lemma complexComparisonAlpha_add_beta {a b : ℝ}
    (hab : (a : ℂ) ^ 2 ≠ (b : ℂ) ^ 2) (τ : ℂ) :
    complexComparisonAlpha a b τ + complexComparisonBeta a b τ = 1 := by
  unfold complexComparisonAlpha complexComparisonBeta
  have hden : (b : ℂ) ^ 2 - (a : ℂ) ^ 2 ≠ 0 := sub_ne_zero.mpr hab.symm
  field_simp [hden]
  ring

/-- The fixed-reference coefficients have the required quadratic moment. -/
private lemma complexComparisonAlpha_mul_sq_add_beta_mul_sq {a b : ℝ}
    (hab : (a : ℂ) ^ 2 ≠ (b : ℂ) ^ 2) (τ : ℂ) :
    complexComparisonAlpha a b τ * (a : ℂ) ^ 2 +
        complexComparisonBeta a b τ * (b : ℂ) ^ 2 = (τ ^ 2 + 1) / 2 := by
  unfold complexComparisonAlpha complexComparisonBeta
  have hden : (b : ℂ) ^ 2 - (a : ℂ) ^ 2 ≠ 0 := sub_ne_zero.mpr hab.symm
  field_simp [hden]
  ring

/-- Both fixed-reference coefficients have one common bound on a closed neighborhood of a
given period. -/
private lemma exists_norm_complex_comparison_coeff_le (a b : ℝ) (τ₀ : ℂ) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧ ∀ τ : ℂ, ‖τ - τ₀‖ ≤ ε →
      ‖complexComparisonAlpha a b τ‖ ≤ M ∧ ‖complexComparisonBeta a b τ‖ ≤ M := by
  let M := max ‖complexComparisonAlpha a b τ₀‖ ‖complexComparisonBeta a b τ₀‖ + 1
  have hM : 0 < M := by
    dsimp [M]
    linarith [norm_nonneg (complexComparisonAlpha a b τ₀),
      le_max_left ‖complexComparisonAlpha a b τ₀‖ ‖complexComparisonBeta a b τ₀‖]
  have hα : ContinuousAt (fun τ => ‖complexComparisonAlpha a b τ‖) τ₀ := by
    unfold complexComparisonAlpha
    fun_prop
  have hβ : ContinuousAt (fun τ => ‖complexComparisonBeta a b τ‖) τ₀ := by
    unfold complexComparisonBeta
    fun_prop
  have hnear : {τ : ℂ | ‖complexComparisonAlpha a b τ‖ < M ∧
      ‖complexComparisonBeta a b τ‖ < M} ∈ 𝓝 τ₀ := by
    apply (hα.eventually_lt continuousAt_const ?_).and
      (hβ.eventually_lt continuousAt_const ?_)
    · dsimp [M]
      linarith [le_max_left ‖complexComparisonAlpha a b τ₀‖
        ‖complexComparisonBeta a b τ₀‖]
    · dsimp [M]
      linarith [le_max_right ‖complexComparisonAlpha a b τ₀‖
        ‖complexComparisonBeta a b τ₀‖]
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ / 2, M, half_pos hδ, hM, ?_⟩
  intro τ hτ
  have hbounds := hsub (by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hτ.trans_lt (half_lt_self hδ))
  exact ⟨hbounds.1.le, hbounds.2.le⟩

/-! ### Elementary neighborhood and rate estimates -/

/-- On a sufficiently small ball around a positive real period, inversion has the uniform
bound `‖τ⁻¹‖ ≤ 2/τ₀`. -/
private lemma norm_inv_le_two_div_of_norm_sub_le {τ : ℂ} {τ₀ ε : ℝ}
    (hτ₀ : 0 < τ₀) (hε : ε ≤ τ₀ / 2) (hτ : ‖τ - (τ₀ : ℂ)‖ ≤ ε) :
    ‖τ⁻¹‖ ≤ 2 / τ₀ := by
  have htri : τ₀ ≤ ‖τ - (τ₀ : ℂ)‖ + ‖τ‖ := by
    calc
      τ₀ = ‖(τ₀ : ℂ)‖ := by simp [abs_of_pos hτ₀]
      _ = ‖τ - (τ - (τ₀ : ℂ))‖ := by ring_nf
      _ ≤ ‖τ - (τ₀ : ℂ)‖ + ‖τ‖ := by
        simpa [add_comm] using norm_sub_le τ (τ - (τ₀ : ℂ))
  have hlower : τ₀ / 2 ≤ ‖τ‖ := by linarith
  rw [norm_inv]
  calc
    ‖τ‖⁻¹ ≤ (τ₀ / 2)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le (half_pos hτ₀) hlower
    _ = 2 / τ₀ := by field_simp

/-- A common closed period ball preserves positivity, the logarithmic chamber, and a uniform
inverse-period bound. -/
private lemma period_domain_and_inv_bound_of_norm_sub_le
    {τ z : ℂ} {τ₀ c ε : ℝ} (hτ₀ : 0 < τ₀) (hc : c < (τ₀ + 1) / 2)
    (hετ : ε ≤ τ₀ / 2) (hεstrip : ε ≤ (τ₀ + 1 - 2 * c) / 2)
    (hτ : ‖τ - (τ₀ : ℂ)‖ ≤ ε) (hzim : |z.im| ≤ c) :
    0 < τ.re ∧ |z.im| < (τ.re + 1) / 2 ∧ ‖τ⁻¹‖ ≤ 2 / τ₀ := by
  have hre : τ₀ - ε ≤ τ.re :=
    (re_ge_and_abs_im_le_of_norm_sub_le (b := τ₀ - ε) (M := ε) hτ (by linarith)
      le_rfl).1
  refine ⟨by linarith [hετ], by linarith [hεstrip], ?_⟩
  exact norm_inv_le_two_div_of_norm_sub_le hτ₀ hετ hτ

/-- Weakening a positive exponential decay rate preserves a bound on the right half-plane. -/
private lemma le_max_mul_exp_neg_of_le {x C q κ t : ℝ}
    (h : x ≤ C * Real.exp (-q * t)) (hκ : κ ≤ q) (ht : 0 ≤ t) :
    x ≤ max C 0 * Real.exp (-κ * t) := by
  calc
    x ≤ C * Real.exp (-q * t) := h
    _ ≤ max C 0 * Real.exp (-q * t) :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_nonneg _)
    _ ≤ max C 0 * Real.exp (-κ * t) := by
      gcongr

/-- Two analytic neighborhoods and the chamber and inversion restrictions admit one positive
common radius. -/
private lemma exists_common_complex_period_radius {εcoeff εcomparison τ₀ c : ℝ}
    (hεcoeff : 0 < εcoeff) (hεcomparison : 0 < εcomparison) (hτ₀ : 0 < τ₀)
    (hc : c < (τ₀ + 1) / 2) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ εcoeff ∧ ε ≤ εcomparison ∧ ε ≤ τ₀ / 2 ∧
      ε ≤ (τ₀ + 1 - 2 * c) / 2 := by
  let ε := min εcoeff (min εcomparison (min (τ₀ / 2) ((τ₀ + 1 - 2 * c) / 2)))
  have hgap : 0 < τ₀ + 1 - 2 * c := by linarith
  refine ⟨ε, by dsimp [ε]; positivity, min_le_left _ _, ?_, ?_, ?_⟩
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

/-- The fixed reference periods and contour height lie below every relevant first zero. -/
private lemma fixed_comparison_contour_geometry {τ₀ : ℝ} (hτ₀ : 0 < τ₀) :
    let a := τ₀ + 1
    let b := τ₀ + 2
    let r := Real.pi / (4 * b)
    0 < a ∧ 0 < b ∧ (a : ℂ) ^ 2 ≠ (b : ℂ) ^ 2 ∧ 0 < r ∧
      2 * r < Real.pi / τ₀ ∧ 2 * r < Real.pi ∧
      2 * r < Real.pi / a ∧ 2 * r < Real.pi / b := by
  dsimp only
  have ha : 0 < τ₀ + 1 := by linarith
  have hb : 0 < τ₀ + 2 := by linarith
  have hab : τ₀ + 1 < τ₀ + 2 := by linarith
  have habC : ((τ₀ + 1 : ℝ) : ℂ) ^ 2 ≠ ((τ₀ + 2 : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast ((sq_lt_sq₀ ha.le hb.le).2 hab).ne
  have hr : 0 < Real.pi / (4 * (τ₀ + 2)) := by positivity
  have hrb : 2 * (Real.pi / (4 * (τ₀ + 2))) < Real.pi / (τ₀ + 2) := by
    have hπb : 0 < Real.pi / (τ₀ + 2) := div_pos Real.pi_pos hb
    rw [show 2 * (Real.pi / (4 * (τ₀ + 2))) =
      (Real.pi / (τ₀ + 2)) / 2 by field_simp [hb.ne']; ring]
    linarith
  have hπbτ : Real.pi / (τ₀ + 2) < Real.pi / τ₀ :=
    div_lt_div_of_pos_left Real.pi_pos hτ₀ (by linarith)
  have hπba : Real.pi / (τ₀ + 2) < Real.pi / (τ₀ + 1) :=
    div_lt_div_of_pos_left Real.pi_pos ha hab
  have hπb1 : Real.pi / (τ₀ + 2) < Real.pi := by
    apply (div_lt_iff₀ hb).2
    nlinarith [Real.pi_pos]
  exact ⟨ha, hb, habC, hr, hrb.trans hπbτ, hrb.trans hπb1,
    hrb.trans hπba, hrb⟩

/-- The chosen kernel-decay rate lies between the Fourier growth and every denominator-decay
rate. -/
private lemma fixed_comparison_decay_geometry {τ₀ c : ℝ}
    (hc0 : 0 ≤ c) (hc : c < (τ₀ + 1) / 2) :
    let a := τ₀ + 1
    let b := τ₀ + 2
    let d := c + (τ₀ + 1) / 2
    0 < d ∧ 2 * c < d ∧ d < τ₀ + 1 ∧ d < 2 * a ∧ d < 2 * b := by
  dsimp only
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The uniform horizontal bounds and the odd-kernel contour shift give one exponential bound
for the complex comparison integral. -/
private lemma norm_comparisonIntegral_le_of_bounds
    {τ z α β : ℂ} {a b r c d Cline Ctail T : ℝ}
    (hr : 0 < r) (hCline : 0 < Cline) (hcd : 2 * c < d)
    (hJ : DifferentiableOn ℂ (complexComparisonKernel τ 1 a b α β)
      {w : ℂ | 0 ≤ w.im ∧ w.im ≤ r})
    (htail : ∀ x : ℝ, T ≤ |x| → ∀ s ∈ Icc 0 r,
      ‖complexComparisonKernel τ 1 a b α β (x + s * I)‖ ≤
        Ctail * Real.exp (-d * |x|))
    (hline : ∀ x : ℝ,
      ‖complexComparisonKernel τ 1 a b α β (x + r * I)‖ ≤
        Cline * Real.exp (-d * |x|))
    (hz : |z.im| ≤ c) :
    ‖complexComparisonIntegral τ a b α β z‖ ≤
      ((∫ x : ℝ, Cline * Real.exp (-(d - 2 * c) * |x|)) / 2) *
        Real.exp (-(2 * r) * z.re) := by
  let W : ℝ → ℝ := fun x => Cline * Real.exp (-(d - 2 * c) * |x|)
  have hWint : Integrable W := by
    apply integrable_of_continuous_norm_le_mul_exp_neg_abs
      (C := Cline) (d := d - 2 * c) (T := 0) (by fun_prop) (by linarith)
    intro x _
    simp [W, Real.norm_eq_abs, abs_of_pos hCline]
  have hcontour := integral_mul_sin_eq_exp_mul_integral_of_odd
    (r := r) (C := Ctail) (d := d) (T := T)
    (complexComparisonKernel τ 1 a b α β) hr hJ
    (complexComparisonKernel_neg τ 1 a b α β) htail
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hz (by norm_num)) hcd)
  have hmajor : ∀ u : ℝ,
      ‖complexComparisonKernel τ 1 a b α β (u + r * I)‖ *
          Real.exp (2 * c * |u|) ≤ W u := by
    intro u
    calc
      _ ≤ (Cline * Real.exp (-d * |u|)) * Real.exp (2 * c * |u|) :=
        mul_le_mul_of_nonneg_right (hline u) (Real.exp_nonneg _)
      _ = W u := by
        dsimp [W]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  simpa [complexComparisonIntegral, W] using
    norm_integral_mul_sin_le_of_integrable_majorant
      (complexComparisonKernel τ 1 a b α β) r c W hWint hmajor hz hcontour

/-- Holomorphy on the symmetric open strip restricts to the chosen closed upper strip. -/
private lemma differentiableOn_closed_upper_strip_of_abs_im_lt
    {J : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hJ : DifferentiableOn ℂ J {w : ℂ | |w.im| < 2 * r}) :
    DifferentiableOn ℂ J {w : ℂ | 0 ≤ w.im ∧ w.im ≤ r} :=
  hJ.mono fun w hw => by
    change |w.im| < 2 * r
    rw [abs_lt]
    constructor <;> linarith [hw.1, hw.2]

/-- The kernel bounds and common-strip holomorphy give a comparison-integral estimate uniform
in the period and in bounded cancellation coefficients. -/
private lemma exists_norm_comparisonIntegral_le
    {τ₀ a b r c d M : ℝ} (hM : 0 ≤ M) (hr : 0 < r)
    (hrτ : 2 * r < Real.pi / τ₀)
    (hr1 : 2 * r < Real.pi) (hra : 2 * r < Real.pi / a)
    (hrb : 2 * r < Real.pi / b) (hd : 0 < d) (hcd : 2 * c < d)
    (hdτ : d < τ₀ + 1) (hda : d < 2 * a) (hdb : d < 2 * b) :
    ∃ ε A : ℝ, 0 < ε ∧ 0 ≤ A ∧ ∀ (τ α β z : ℂ),
      ‖τ - (τ₀ : ℂ)‖ ≤ ε → ‖α‖ ≤ M → ‖β‖ ≤ M → α + β = 1 →
      α * (a : ℂ) ^ 2 + β * (b : ℂ) ^ 2 = (τ ^ 2 + 1) / 2 → |z.im| ≤ c →
      ‖complexComparisonIntegral τ a b α β z‖ ≤
        A * Real.exp (-(2 * r) * z.re) := by
  have hτ₀ := (div_pos_iff_of_pos_left Real.pi_pos).mp ((mul_pos (by norm_num) hr).trans hrτ)
  have ha := (div_pos_iff_of_pos_left Real.pi_pos).mp ((mul_pos (by norm_num) hr).trans hra)
  have hb := (div_pos_iff_of_pos_left Real.pi_pos).mp ((mul_pos (by norm_num) hr).trans hrb)
  obtain ⟨εl, Cl, hεl, hCl, hl⟩ :=
    exists_norm_complexComparisonKernel_le
      hM hr (by linarith) (by linarith) (by linarith) (by linarith) hd hdτ hda hdb
  obtain ⟨εt, Ct, T, hεt, hCt, _, ht⟩ :=
    exists_norm_complexComparisonKernel_tail_le
      hτ₀ hM hr.le hd hdτ hda hdb
  obtain ⟨δ, hδ, hhol⟩ := Metric.mem_nhds_iff.mp
    (eventually_differentiableOn_complexComparisonKernel
      hτ₀ ha hb hrτ hr1 hra hrb)
  let ε := min εl (min εt (δ / 2))
  let A := (∫ x : ℝ, Cl * Real.exp (-(d - 2 * c) * |x|)) / 2
  refine ⟨ε, A, by dsimp [ε]; positivity, ?_, ?_⟩
  · exact div_nonneg (integral_nonneg fun x => mul_nonneg hCl.le (Real.exp_nonneg _)) (by norm_num)
  intro τ α β z hτ hα hβ hsum hquad hz
  have hJfull := hhol (show τ ∈ Metric.ball (τ₀ : ℂ) δ by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hτ.trans_lt ((min_le_right _ _).trans (min_le_right _ _) |>.trans_lt
      (half_lt_self hδ))) α β hsum hquad
  have hJ := differentiableOn_closed_upper_strip_of_abs_im_lt hr hJfull
  simpa [A] using norm_comparisonIntegral_le_of_bounds
    hr hCl hcd hJ
      (fun x hx s hs => ht τ (hτ.trans ((min_le_right _ _).trans (min_le_left _ _)))
        α β hα hβ s hs x hx)
      (hl τ (hτ.trans (min_le_left _ _)) α β hα hβ) hz

/-- The fixed equal-period remainder estimate remains valid after weakening its rate to any
target rate at most `π / a`. -/
private lemma exists_norm_logRemainder_self_le_rate {a c κ : ℝ}
    (ha : 0 < a) (hc : c < a) (hκ : κ ≤ Real.pi / a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, 0 ≤ z.re → |z.im| ≤ c →
      ‖hyperbolicGammaLogRemainder a a z‖ ≤ B * Real.exp (-κ * z.re) := by
  obtain ⟨C, hC⟩ := norm_hyperbolicGammaLog_self_add_le ha
    (div_pos Real.pi_pos ha) hc
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hzre hzim
  have h := hC z hzre hzim
  rw [show (Real.pi / a - 2 * Real.pi / a) * z.re =
    -(Real.pi / a) * z.re by ring] at h
  rw [hyperbolicGammaLogRemainder_self a z ha.ne']
  exact le_max_mul_exp_neg_of_le h hκ hzre

/-- The two fixed equal-period remainders admit bounds at one common target rate. -/
private lemma exists_norm_equal_period_remainders_le_rate
    {a b c κ : ℝ} (ha : 0 < a) (hb : 0 < b) (hca : c < a) (hcb : c < b)
    (hκa : κ ≤ Real.pi / a) (hκb : κ ≤ Real.pi / b) :
    ∃ Ba Bb : ℝ, 0 ≤ Ba ∧ 0 ≤ Bb ∧
      (∀ z : ℂ, 0 ≤ z.re → |z.im| ≤ c →
        ‖hyperbolicGammaLogRemainder a a z‖ ≤ Ba * Real.exp (-κ * z.re)) ∧
      ∀ z : ℂ, 0 ≤ z.re → |z.im| ≤ c →
        ‖hyperbolicGammaLogRemainder b b z‖ ≤ Bb * Real.exp (-κ * z.re) := by
  obtain ⟨Ba, hBa, hEa⟩ :=
    exists_norm_logRemainder_self_le_rate ha hca hκa
  obtain ⟨Bb, hBb, hEb⟩ :=
    exists_norm_logRemainder_self_le_rate hb hcb hκb
  exact ⟨Ba, Bb, hBa, hBb, hEa, hEb⟩

/-- Multiplying an exponentially bounded term by a bounded coefficient and a fixed real square
preserves the bound with the expected product constant. -/
private lemma norm_coeff_mul_sq_mul_le {α E : ℂ} {a M B e : ℝ}
    (hα : ‖α‖ ≤ M) (hE : ‖E‖ ≤ B * e) :
    ‖α * (a : ℂ) ^ 2 * E‖ ≤ M * a ^ 2 * B * e := by
  have hM : 0 ≤ M := (norm_nonneg α).trans hα
  calc
    _ = ‖α‖ * a ^ 2 * ‖E‖ := by
      rw [norm_mul, norm_mul]
      simp [norm_pow, Complex.norm_real, sq_abs]
    _ ≤ M * a ^ 2 * ‖E‖ := by gcongr
    _ ≤ M * a ^ 2 * (B * e) := by gcongr
    _ = _ := by ring

/-- The normalized comparison identity turns three exponential error estimates into one estimate
for the mixed-period normalized logarithm. -/
private lemma norm_remainder_le_of_comparison_errors
    {τ α β E Ea Eb D : ℂ} {a b K M Ba Bb A e : ℝ}
    (hτ : τ ≠ 0)
    (hα : ‖α‖ ≤ M) (hβ : ‖β‖ ≤ M) (hinv : ‖τ⁻¹‖ ≤ K)
    (hEa : ‖Ea‖ ≤ Ba * e) (hEb : ‖Eb‖ ≤ Bb * e) (hD : ‖D‖ ≤ A * e)
    (hidentity : τ * E = α * (a : ℂ) ^ 2 * Ea + β * (b : ℂ) ^ 2 * Eb + D) :
    ‖E‖ ≤ K * (M * a ^ 2 * Ba + M * b ^ 2 * Bb + A) * e := by
  have hK : 0 ≤ K := (norm_nonneg τ⁻¹).trans hinv
  have hsolve : E = τ⁻¹ * (α * (a : ℂ) ^ 2 * Ea + β * (b : ℂ) ^ 2 * Eb + D) := by
    rw [← hidentity]
    field_simp
  have htermA := norm_coeff_mul_sq_mul_le (a := a) hα hEa
  have htermB := norm_coeff_mul_sq_mul_le (a := b) hβ hEb
  have hterms : ‖α * (a : ℂ) ^ 2 * Ea‖ + ‖β * (b : ℂ) ^ 2 * Eb‖ + ‖D‖ ≤
      (M * a ^ 2 * Ba + M * b ^ 2 * Bb + A) * e := by
    calc
      _ ≤ M * a ^ 2 * Ba * e + M * b ^ 2 * Bb * e + A * e :=
        add_le_add (add_le_add htermA htermB) hD
      _ = _ := by ring
  rw [hsolve, norm_mul]
  calc
    _ ≤ K * (‖α * (a : ℂ) ^ 2 * Ea‖ + ‖β * (b : ℂ) ^ 2 * Eb‖ + ‖D‖) := by
      apply mul_le_mul hinv _ (norm_nonneg _) hK
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ K * ((M * a ^ 2 * Ba + M * b ^ 2 * Bb + A) * e) :=
      mul_le_mul_of_nonneg_left hterms hK
    _ = _ := by ring

/-! ### Uniform normalized logarithmic remainder -/

/-- **New.** Let `τ₀ > 0` and let `|Im z| ≤ c` be a closed substrip of
`|Im z| < (τ₀+1)/2`. There is one complex-period neighborhood and one exponential estimate for
the normalized double-sine logarithmic remainder throughout that substrip. This is the uniform
complex-period extension of the generator estimates in [RW26, Radchenko--Wheeler (2026),
Lemma 1, `lem:asymp`] needed for the boundary passage in their Theorem 3. The proof adapts the
comparison and contour shift of Ruijsenaars (1997), Proposition III.4. We searched [AFK25],
[RW26, Radchenko--Wheeler (2026), Lemma 1, `lem:asymp`, and Appendix A.2], and that proposition
with its surrounding continuation; none states this uniform near-real complex-period estimate. -/
theorem exists_norm_doubleSineComplexLogRemainder_le
    {τ₀ c : ℝ} (hτ₀ : 0 < τ₀) (hc0 : 0 ≤ c) (hc : c < (τ₀ + 1) / 2) :
    ∃ ε C κ : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧
      ∀ (τ z : ℂ), ‖τ - (τ₀ : ℂ)‖ ≤ ε → 0 ≤ z.re → |z.im| ≤ c →
        ‖doubleSineComplexLogRemainder z τ‖ ≤
          C * Real.exp (-κ * z.re) := by
  let a := τ₀ + 1; let b := τ₀ + 2; let r := Real.pi / (4 * b); let κ := 2 * r
  obtain ⟨ha, hb, hab, hr, hrτ, hr1, hra, hrb⟩ := fixed_comparison_contour_geometry hτ₀
  obtain ⟨hd, hcd, hdτ, hda, hdb⟩ := fixed_comparison_decay_geometry hc0 hc
  obtain ⟨εcoeff, M, hεcoeff, hM, hcoeff⟩ := exists_norm_complex_comparison_coeff_le a b (τ₀ : ℂ)
  obtain ⟨εcomparison, A, hεcomparison, hA, hcomparison⟩ :=
    exists_norm_comparisonIntegral_le
      hM.le hr hrτ hr1 hra hrb hd hcd hdτ hda hdb
  obtain ⟨Ba, Bb, hBa, hBb, hEa, hEb⟩ :=
    exists_norm_equal_period_remainders_le_rate (c := c) (κ := κ)
      ha hb (by linarith) (by linarith) hra.le hrb.le
  obtain ⟨ε, hε, hεcoeff', hεcomparison', hετ, hεstrip⟩ :=
    exists_common_complex_period_radius hεcoeff hεcomparison hτ₀ hc
  let C := (2 / τ₀) * (M * a ^ 2 * Ba + M * b ^ 2 * Bb + A) + 1
  refine ⟨ε, C, κ, hε, by dsimp [C]; positivity, by dsimp [κ]; positivity, ?_⟩
  intro τ z hτ hzre hzim
  have hcoeff' := hcoeff τ (hτ.trans hεcoeff')
  have hD := hcomparison τ (complexComparisonAlpha a b τ) (complexComparisonBeta a b τ) z
    (hτ.trans hεcomparison') hcoeff'.1 hcoeff'.2 (complexComparisonAlpha_add_beta hab τ)
    (complexComparisonAlpha_mul_sq_add_beta_mul_sq hab τ) hzim
  obtain ⟨hτre, hzτ, hinv⟩ := period_domain_and_inv_bound_of_norm_sub_le
    hτ₀ hc hετ hεstrip hτ hzim
  have hid := doubleSineComplexLogRemainder_comparison hτre hzτ
    (hzim.trans_lt (by linarith)) (hzim.trans_lt (by linarith))
    (complexComparisonAlpha_add_beta hab τ) (complexComparisonAlpha_mul_sq_add_beta_mul_sq hab τ)
  exact (norm_remainder_le_of_comparison_errors (fun h => by simpa [h] using hτre.ne')
    hcoeff'.1 hcoeff'.2 hinv (hEa z hzre hzim) (hEb z hzre hzim) hD hid).trans
      (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.exp_nonneg _))

end SIC

end
