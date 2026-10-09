/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.HyperbolicGamma.ComplexPeriodComparison

/-!
# Uniform bounds for complex-period comparison kernels

Uniform exponential estimates for the two-reference complex comparison kernel on shifted
horizontal lines and on the tails of a common horizontal strip.

This module follows S. N. M. Ruijsenaars, *First order analytic difference equations and
integrable quantum systems*, J. Math. Phys. 38 (1997), 1069–1146, proof of Proposition III.4,
equations (3.54)–(3.56),
[doi:10.1063/1.531809](https://doi.org/10.1063/1.531809). It supplies the bounds needed to run
the contour argument uniformly when the first period varies near a positive real period and the
two reference coefficients remain in a fixed norm ball.

## The argument

Choose decay rates below the four positive real parts `τ₀`, `1`, `a`, and `b`, while keeping
their mixed or doubled sums above the requested rate `d`. On a fixed line of height `r`, the
uniform reciprocal-sinh estimates from `SICs.Analysis.HyperbolicBounds` control all four
denominators. The factor `1/(2y)` is bounded by `1/(2r)`, and the triangle inequality gives the
kernel estimate.

For heights in `[0,r]`, insert intermediate rates with one common positive gap. Once `|x|` is
large compared with `(r+1)` divided by that gap, the elementary reciprocal-sinh tail bound is
uniform in the height. Here `1/(2y)` is bounded by `1/2`. These estimates do not use the two
coefficient cancellation equations: those equations control the removable origin, whereas the
present bounds either stay above the real axis or lie sufficiently far out in the tails.
-/

noncomputable section

open Complex Real Set
open scoped Topology

namespace SIC

/-! ### Decay bookkeeping and termwise bounds -/

/-- Chooses rates below `τ₀`, `1`, `a`, and `b` whose mixed or doubled sums exceed `d`. -/
private lemma exists_complex_period_comparison_decay_rates {τ₀ a b d : ℝ}
    (hτ₀ : 0 < τ₀) (hd : 0 < d)
    (hdτ : d < τ₀ + 1) (hda : d < 2 * a) (hdb : d < 2 * b) :
    ∃ pτ p1 pa pb : ℝ,
      0 < pτ ∧ pτ < τ₀ ∧ 0 < p1 ∧ p1 < 1 ∧ d < pτ + p1 ∧
      0 < pa ∧ pa < a ∧ d < 2 * pa ∧
      0 < pb ∧ pb < b ∧ d < 2 * pb := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  let S := τ₀ + 1
  let q := (d + S) / 2
  let pτ := q * τ₀ / S
  let p1 := q / S
  let pa := (d + 2 * a) / 4
  let pb := (d + 2 * b) / 4
  have hS : 0 < S := by dsimp [S]; linarith
  have hq : 0 < q := by dsimp [q]; linarith
  have hqS : q < S := by dsimp [q, S] at *; linarith
  have hdq : d < q := by dsimp [q, S] at *; linarith
  have hfrac : q / S < 1 := (div_lt_one hS).2 hqS
  have hpτlt : pτ < τ₀ := by
    calc
      pτ = (q / S) * τ₀ := by dsimp [pτ]; ring
      _ < 1 * τ₀ := mul_lt_mul_of_pos_right hfrac hτ₀
      _ = τ₀ := one_mul _
  have hsum : pτ + p1 = q := by
    dsimp [pτ, p1]
    field_simp
    ring
  refine ⟨pτ, p1, pa, pb, by positivity, hpτlt, by positivity, hfrac, ?_,
    by dsimp [pa]; linarith, by dsimp [pa]; linarith, by dsimp [pa]; linarith,
    by dsimp [pb]; linarith, by dsimp [pb]; linarith, by dsimp [pb]; linarith⟩
  rw [hsum]
  exact hdq

/-- Specializes the nearby-period reciprocal-sinh estimate to one positive real period. -/
private lemma exists_norm_inv_sinh_real_horizontal_le {c r p : ℝ}
    (hp : 0 < p) (hpc : p < c) (hr : 0 < r)
    (hrπ : r < Real.pi / c) :
    ∃ C > 0, ∀ x : ℝ,
      ‖(Complex.sinh ((c : ℂ) * ((x : ℂ) + (r : ℂ) * I)))⁻¹‖ ≤
        C * Real.exp (-p * |x|) := by
  have hc : 0 < c := hp.trans hpc
  obtain ⟨ε, C, hε, hC, hbound⟩ :=
    exists_norm_inv_sinh_mul_horizontal_le_near_real hc hp hpc hr hrπ
  refine ⟨C, hC, fun x => hbound c ?_ x⟩
  simpa using hε.le

/-- A closed norm ball of radius `ε` around a nonnegative real `τ₀` lies in the norm ball
of radius `τ₀ + ε` around zero. -/
private lemma norm_le_real_add_of_norm_sub_le {τ : ℂ} {τ₀ ε : ℝ}
    (hτ₀ : 0 ≤ τ₀) (hτ : ‖τ - (τ₀ : ℂ)‖ ≤ ε) : ‖τ‖ ≤ τ₀ + ε := by
  calc
    ‖τ‖ = ‖(τ - (τ₀ : ℂ)) + (τ₀ : ℂ)‖ := by ring_nf
    _ ≤ ‖τ - (τ₀ : ℂ)‖ + ‖(τ₀ : ℂ)‖ := norm_add_le _ _
    _ ≤ ε + τ₀ := by gcongr; simp [abs_of_nonneg hτ₀]
    _ = τ₀ + ε := add_comm _ _

/-- Products of two exponential bounds with rates `p` and `q` obey every smaller rate `d`. -/
private lemma mul_exp_decay_le (A B p q d x : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hrate : d ≤ p + q) :
    (A * Real.exp (-p * |x|)) * (B * Real.exp (-q * |x|)) ≤
      (A * B) * Real.exp (-d * |x|) := by
  calc
    _ = (A * B) * Real.exp (-(p + q) * |x|) := by
      rw [show -(p + q) * |x| = -p * |x| + -q * |x| by ring, Real.exp_add]
      ring
    _ ≤ (A * B) * Real.exp (-d * |x|) := by
      gcongr

/-- A sufficiently small closed ball around a positive real `τ₀` has real part at least
`B` and imaginary part of absolute value at most one. -/
private lemma exists_closedBall_re_ge_abs_im_le {τ₀ B : ℝ} (hB : B < τ₀) :
    ∃ ε > 0, ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → B ≤ τ.re ∧ |τ.im| ≤ 1 := by
  let ε := min ((τ₀ - B) / 2) 1
  have hε : 0 < ε := lt_min (half_pos (sub_pos.mpr hB)) (by norm_num)
  refine ⟨ε, hε, ?_⟩
  intro τ hτ
  have hεB : ε ≤ (τ₀ - B) / 2 := min_le_left _ _
  have hε1 : ε ≤ 1 := min_le_right _ _
  exact re_ge_and_abs_im_le_of_norm_sub_le hτ (by linarith) hε1

/-- The factor `1/(2y)` is bounded by `1/(2r)` on the horizontal line `Im y = r > 0`. -/
private lemma norm_comparison_prefactor_horizontal_le (x r : ℝ) (hr : 0 < r) :
    ‖(1 : ℂ) / (2 * ((x : ℂ) + (r : ℂ) * I))‖ ≤ 1 / (2 * r) := by
  have him : r ≤ ‖(x : ℂ) + (r : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm ((x : ℂ) + (r : ℂ) * I)
    simpa [abs_of_pos hr] using this
  rw [norm_div, norm_one, norm_mul]
  norm_num
  have htwo : 2 * r ≤ 2 * ‖(x : ℂ) + (r : ℂ) * I‖ := by nlinarith
  simpa [one_div] using one_div_le_one_div_of_le (mul_pos (by norm_num) hr) htwo

/-- The factor `1/(2y)` is bounded by `1/2` whenever `|Re y| ≥ 1`. -/
private lemma norm_comparison_prefactor_tail_le (x s : ℝ) (hx : 1 ≤ |x|) :
    ‖(1 : ℂ) / (2 * ((x : ℂ) + (s : ℂ) * I))‖ ≤ 1 / 2 := by
  have hre : 1 ≤ ‖(x : ℂ) + (s : ℂ) * I‖ := by
    exact hx.trans (by simpa using Complex.abs_re_le_norm ((x : ℂ) + (s : ℂ) * I))
  rw [norm_div, norm_one, norm_mul]
  norm_num
  simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hre

/-- Bounds the mixed-period term by bounds for its two reciprocal-sinh factors. -/
private lemma norm_comparison_mixed_le_of_inv_bounds (τ y : ℂ) (N Uτ U1 : ℝ)
    (hτ : ‖τ‖ ≤ N) (hsτ : ‖(Complex.sinh (τ * y))⁻¹‖ ≤ Uτ)
    (hs1 : ‖(Complex.sinh y)⁻¹‖ ≤ U1) :
    ‖τ * 1 / (Complex.sinh (τ * y) * Complex.sinh y)‖ ≤ N * Uτ * U1 := by
  have hUτ : 0 ≤ Uτ := (norm_nonneg _).trans hsτ
  have hU1 : 0 ≤ U1 := (norm_nonneg _).trans hs1
  have hN : 0 ≤ N := (norm_nonneg τ).trans hτ
  calc
    _ = ‖τ‖ * ‖(Complex.sinh (τ * y))⁻¹‖ * ‖(Complex.sinh y)⁻¹‖ := by
      simp [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ N * Uτ * U1 := by gcongr

/-- Bounds an equal-period comparison term by one reciprocal-sinh bound. -/
private lemma norm_comparison_equal_le_of_inv_bound (α y : ℂ) (a M U : ℝ)
    (hα : ‖α‖ ≤ M) (hs : ‖(Complex.sinh (a * y))⁻¹‖ ≤ U) :
    ‖α * (a : ℂ) ^ 2 / Complex.sinh (a * y) ^ 2‖ ≤ M * a ^ 2 * U ^ 2 := by
  have hU : 0 ≤ U := (norm_nonneg _).trans hs
  have hM : 0 ≤ M := (norm_nonneg α).trans hα
  calc
    _ = ‖α‖ * a ^ 2 * ‖(Complex.sinh (a * y))⁻¹‖ ^ 2 := by
      simp [div_eq_mul_inv, ← inv_pow, norm_pow, Complex.norm_real, sq_abs]
    _ ≤ M * a ^ 2 * U ^ 2 := by gcongr

/-- Combines reciprocal-sinh and coefficient bounds into a bound for the comparison kernel. -/
private lemma norm_kernel_le_of_inv_bounds
    (τ α β y : ℂ) (a b L N M Uτ U1 Ua Ub : ℝ)
    (hpref : ‖(1 : ℂ) / (2 * y)‖ ≤ L) (hτ : ‖τ‖ ≤ N)
    (hα : ‖α‖ ≤ M) (hβ : ‖β‖ ≤ M)
    (hsτ : ‖(Complex.sinh (τ * y))⁻¹‖ ≤ Uτ)
    (hs1 : ‖(Complex.sinh y)⁻¹‖ ≤ U1)
    (hsa : ‖(Complex.sinh (a * y))⁻¹‖ ≤ Ua)
    (hsb : ‖(Complex.sinh (b * y))⁻¹‖ ≤ Ub) :
    ‖complexComparisonKernel τ 1 a b α β y‖ ≤
      L * (N * Uτ * U1 + M * a ^ 2 * Ua ^ 2 + M * b ^ 2 * Ub ^ 2) := by
  have hL : 0 ≤ L := (norm_nonneg _).trans hpref
  have hmix := norm_comparison_mixed_le_of_inv_bounds τ y N Uτ U1 hτ hsτ hs1
  have haeq := norm_comparison_equal_le_of_inv_bound α y a M Ua hα hsa
  have hbeq := norm_comparison_equal_le_of_inv_bound β y b M Ub hβ hsb
  rw [complexComparisonKernel, one_mul, norm_mul]
  have htri :
      ‖τ * 1 / (Complex.sinh (τ * y) * Complex.sinh y) -
          α * (a : ℂ) ^ 2 / Complex.sinh (a * y) ^ 2 -
          β * (b : ℂ) ^ 2 / Complex.sinh (b * y) ^ 2‖ ≤
        (‖τ * 1 / (Complex.sinh (τ * y) * Complex.sinh y)‖ +
          ‖α * (a : ℂ) ^ 2 / Complex.sinh (a * y) ^ 2‖) +
          ‖β * (b : ℂ) ^ 2 / Complex.sinh (b * y) ^ 2‖ := by
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
  calc
    _ ≤ L * ‖τ * 1 / (Complex.sinh (τ * y) * Complex.sinh y) -
        α * (a : ℂ) ^ 2 / Complex.sinh (a * y) ^ 2 -
        β * (b : ℂ) ^ 2 / Complex.sinh (b * y) ^ 2‖ := by gcongr
    _ ≤ L * ((N * Uτ * U1 + M * a ^ 2 * Ua ^ 2) + M * b ^ 2 * Ub ^ 2) := by
      gcongr
      exact htri.trans (add_le_add (add_le_add hmix haeq) hbeq)
    _ = _ := by ring

/-- Combines the three exponential products at any common smaller decay rate. -/
private lemma complex_period_comparison_decay_sum_le
    (N M a b Cτ C1 Ca Cb pτ p1 pa pb d x : ℝ)
    (hN : 0 ≤ N) (hM : 0 ≤ M) (hCτ : 0 ≤ Cτ) (hC1 : 0 ≤ C1)
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (hdτ : d ≤ pτ + p1) (hda : d ≤ pa + pa) (hdb : d ≤ pb + pb) :
    N * (Cτ * Real.exp (-pτ * |x|)) * (C1 * Real.exp (-p1 * |x|)) +
        M * a ^ 2 * (Ca * Real.exp (-pa * |x|)) ^ 2 +
        M * b ^ 2 * (Cb * Real.exp (-pb * |x|)) ^ 2 ≤
      (N * Cτ * C1 + M * a ^ 2 * Ca ^ 2 + M * b ^ 2 * Cb ^ 2) *
        Real.exp (-d * |x|) := by
  have hmix := mul_exp_decay_le Cτ C1 pτ p1 d x hCτ hC1 hdτ
  have hae : (Ca * Real.exp (-pa * |x|)) ^ 2 ≤
      Ca ^ 2 * Real.exp (-d * |x|) := by
    simpa [pow_two] using mul_exp_decay_le Ca Ca pa pa d x hCa hCa hda
  have hbe : (Cb * Real.exp (-pb * |x|)) ^ 2 ≤
      Cb ^ 2 * Real.exp (-d * |x|) := by
    simpa [pow_two] using mul_exp_decay_le Cb Cb pb pb d x hCb hCb hdb
  have hmix' := mul_le_mul_of_nonneg_left hmix hN
  have hae' := mul_le_mul_of_nonneg_left hae (mul_nonneg hM (sq_nonneg a))
  have hbe' := mul_le_mul_of_nonneg_left hbe (mul_nonneg hM (sq_nonneg b))
  calc
    _ ≤ N * ((Cτ * C1) * Real.exp (-d * |x|)) +
        M * a ^ 2 * (Ca ^ 2 * Real.exp (-d * |x|)) +
        M * b ^ 2 * (Cb ^ 2 * Real.exp (-d * |x|)) := by
      simpa [mul_assoc] using add_le_add (add_le_add hmix' hae') hbe'
    _ = _ := by ring

/-- Turns exponential bounds for all four reciprocal-sinh factors into a comparison-kernel
bound. -/
private lemma norm_kernel_le_of_exp_bounds
    (τ α β y : ℂ) (a b L N M Cτ C1 Ca Cb pτ p1 pa pb d x : ℝ)
    (hdτ : d ≤ pτ + p1) (hda : d ≤ pa + pa) (hdb : d ≤ pb + pb)
    (hpref : ‖(1 : ℂ) / (2 * y)‖ ≤ L) (hτ : ‖τ‖ ≤ N)
    (hα : ‖α‖ ≤ M) (hβ : ‖β‖ ≤ M)
    (hsτ : ‖(Complex.sinh (τ * y))⁻¹‖ ≤ Cτ * Real.exp (-pτ * |x|))
    (hs1 : ‖(Complex.sinh y)⁻¹‖ ≤ C1 * Real.exp (-p1 * |x|))
    (hsa : ‖(Complex.sinh (a * y))⁻¹‖ ≤ Ca * Real.exp (-pa * |x|))
    (hsb : ‖(Complex.sinh (b * y))⁻¹‖ ≤ Cb * Real.exp (-pb * |x|)) :
    ‖complexComparisonKernel τ 1 a b α β y‖ ≤
      L * (N * Cτ * C1 + M * a ^ 2 * Ca ^ 2 + M * b ^ 2 * Cb ^ 2) *
        Real.exp (-d * |x|) := by
  have hL : 0 ≤ L := (norm_nonneg _).trans hpref
  have hN : 0 ≤ N := (norm_nonneg τ).trans hτ
  have hM : 0 ≤ M := (norm_nonneg α).trans hα
  have hCτ : 0 ≤ Cτ := (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp
    ((norm_nonneg _).trans hsτ)
  have hC1 : 0 ≤ C1 := (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp
    ((norm_nonneg _).trans hs1)
  have hCa : 0 ≤ Ca := (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp
    ((norm_nonneg _).trans hsa)
  have hCb : 0 ≤ Cb := (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp
    ((norm_nonneg _).trans hsb)
  have hraw := norm_kernel_le_of_inv_bounds τ α β y a b L N M
    (Cτ * Real.exp (-pτ * |x|)) (C1 * Real.exp (-p1 * |x|))
    (Ca * Real.exp (-pa * |x|)) (Cb * Real.exp (-pb * |x|))
    hpref hτ hα hβ hsτ hs1 hsa hsb
  have hsum := complex_period_comparison_decay_sum_le N M a b Cτ C1 Ca Cb
    pτ p1 pa pb d x hN hM hCτ hC1 hCa hCb hdτ hda hdb
  exact hraw.trans (by
    calc
      _ ≤ L * ((N * Cτ * C1 + M * a ^ 2 * Ca ^ 2 + M * b ^ 2 * Cb ^ 2) *
          Real.exp (-d * |x|)) := mul_le_mul_of_nonneg_left hsum hL
      _ = _ := by ring)

/-! ### Uniform bounds on a fixed shifted line -/

/-- For periods `τ` uniformly near a positive real `τ₀` and coefficients in the norm ball of
radius `M`, the two-reference comparison kernel on `x + ir` is bounded by `C exp (-d|x|)`.
The four upper bounds on `r` keep the shifted line below every relevant reciprocal-sinh zero.
This is the uniform complex-period form of the estimate in Ruijsenaars (1997), equation (3.56).
-/
theorem exists_norm_complexComparisonKernel_le
    {τ₀ a b M r d : ℝ} (hM : 0 ≤ M) (hr : 0 < r)
    (hrτ : r < Real.pi / τ₀) (hr1 : r < Real.pi)
    (hra : r < Real.pi / a) (hrb : r < Real.pi / b)
    (hd : 0 < d) (hdτ : d < τ₀ + 1) (hda : d < 2 * a) (hdb : d < 2 * b) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ (τ : ℂ), ‖τ - (τ₀ : ℂ)‖ ≤ ε →
      ∀ (α β : ℂ), ‖α‖ ≤ M → ‖β‖ ≤ M → ∀ x : ℝ,
        ‖complexComparisonKernel τ 1 a b α β
          ((x : ℂ) + (r : ℂ) * I)‖ ≤ C * Real.exp (-d * |x|) := by
  have hτ₀ : 0 < τ₀ := (div_pos_iff_of_pos_left Real.pi_pos).mp (hr.trans hrτ)
  obtain ⟨pτ, p1, pa, pb, hpτ, hpττ, hp1, hp11, hpsum,
    hpa, hpaa, hpasum, hpb, hpbb, hpbsum⟩ :=
    exists_complex_period_comparison_decay_rates hτ₀ hd hdτ hda hdb
  obtain ⟨ε, Cτ, hε, hCτ, hτinv⟩ :=
    exists_norm_inv_sinh_mul_horizontal_le_near_real hτ₀ hpτ hpττ hr hrτ
  obtain ⟨C1, hC1, h1inv⟩ :=
    exists_norm_inv_sinh_real_horizontal_le hp1 hp11 hr (by simpa using hr1)
  obtain ⟨Ca, hCa, hainv⟩ :=
    exists_norm_inv_sinh_real_horizontal_le hpa hpaa hr hra
  obtain ⟨Cb, hCb, hbinv⟩ :=
    exists_norm_inv_sinh_real_horizontal_le hpb hpbb hr hrb
  let L := 1 / (2 * r)
  let N := τ₀ + ε
  let C := L * (N * Cτ * C1 + M * a ^ 2 * Ca ^ 2 + M * b ^ 2 * Cb ^ 2)
  have hC : 0 < C := by positivity
  refine ⟨ε, C, hε, hC, ?_⟩
  intro τ hτ α β hα hβ x
  let y : ℂ := (x : ℂ) + (r : ℂ) * I
  exact norm_kernel_le_of_exp_bounds
    τ α β y a b L N M Cτ C1 Ca Cb
    pτ p1 pa pb d x hpsum.le (by nlinarith [hpasum]) (by nlinarith [hpbsum])
    (by simpa [y, L] using norm_comparison_prefactor_horizontal_le x r hr)
    (by simpa [N] using norm_le_real_add_of_norm_sub_le hτ₀.le hτ) hα hβ
    (by simpa [y] using hτinv τ hτ x)
    (by simpa [y] using h1inv x) (by simpa [y] using hainv x) (by simpa [y] using hbinv x)

/-! ### Uniform bounds on all horizontal tails -/

/-- Inserts four intermediate rates and a common positive gap below their period bounds. -/
private lemma exists_intermediate_rates_with_common_gap
    {τ₀ a b pτ p1 pa pb : ℝ}
    (hpτ : pτ < τ₀) (hp1 : p1 < 1) (hpa : pa < a) (hpb : pb < b) :
    ∃ Bτ B1 Ba Bb g : ℝ, 0 < g ∧
      pτ < Bτ ∧ Bτ < τ₀ ∧ p1 < B1 ∧ B1 < 1 ∧
      pa < Ba ∧ Ba < a ∧ pb < Bb ∧ Bb < b ∧
      g ≤ Bτ - pτ ∧ g ≤ B1 - p1 ∧ g ≤ Ba - pa ∧ g ≤ Bb - pb := by
  let Bτ := (pτ + τ₀) / 2
  let B1 := (p1 + 1) / 2
  let Ba := (pa + a) / 2
  let Bb := (pb + b) / 2
  let g := min (Bτ - pτ) (min (B1 - p1) (min (Ba - pa) (Bb - pb)))
  have hpτB : pτ < Bτ := by dsimp [Bτ]; linarith
  have hBτ : Bτ < τ₀ := by dsimp [Bτ]; linarith
  have hp1B : p1 < B1 := by dsimp [B1]; linarith
  have hB1 : B1 < 1 := by dsimp [B1]; linarith
  have hpaB : pa < Ba := by dsimp [Ba]; linarith
  have hBa : Ba < a := by dsimp [Ba]; linarith
  have hpbB : pb < Bb := by dsimp [Bb]; linarith
  have hBb : Bb < b := by dsimp [Bb]; linarith
  have hg : 0 < g := lt_min (sub_pos.mpr hpτB)
    (lt_min (sub_pos.mpr hp1B) (lt_min (sub_pos.mpr hpaB) (sub_pos.mpr hpbB)))
  exact ⟨Bτ, B1, Ba, Bb, g, hg, hpτB, hBτ, hp1B, hB1, hpaB, hBa, hpbB, hBb,
    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩

/-- Applies `norm_inv_sinh_horizontal_tail_le` uniformly for `s ∈ [0,r]` once `|x|` exceeds
a threshold determined by a common rate gap. -/
private lemma norm_inv_sinh_tail_le_of_common_gap
    {τ : ℂ} {x s r p B g T : ℝ} (hp : 0 < p) (hpB : p < B)
    (hτre : B ≤ τ.re) (hτim : |τ.im| ≤ 1) (hg : 0 < g) (hgap : g ≤ B - p)
    (hs : s ∈ Set.Icc 0 r) (hT : (r + 1) / g ≤ T) (hx : T ≤ |x|) :
    ‖(Complex.sinh (τ * ((x : ℂ) + (s : ℂ) * I)))⁻¹‖ ≤
      (2 / (1 - Real.exp (-2))) * Real.exp (-p * |x|) := by
  have hbase : s + 1 ≤ g * |x| := by
    have := (div_le_iff₀ hg).mp (hT.trans hx)
    linarith [hs.2]
  have htail : s + 1 ≤ (B - p) * |x| :=
    hbase.trans (mul_le_mul_of_nonneg_right hgap (abs_nonneg x))
  exact norm_inv_sinh_horizontal_tail_le hp hpB hτre hτim hs.1 htail

/-- The universal constant in `norm_inv_sinh_horizontal_tail_le` is positive. -/
private lemma inv_sinh_tail_constant_pos :
    0 < 2 / (1 - Real.exp (-2)) :=
  div_pos (by norm_num) (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))

/-- Combines four common-gap reciprocal-sinh tail estimates into one pointwise bound for the
complex comparison kernel. -/
private lemma norm_kernel_tail_le_of_common_gap
    {τ α β : ℂ} {x s r a b M L N d pτ p1 pa pb Bτ B1 Ba Bb g T : ℝ}
    (hpτ : 0 < pτ) (hpτB : pτ < Bτ) (hp1 : 0 < p1) (hp1B : p1 < B1)
    (hpa : 0 < pa) (hpaB : pa < Ba) (hpb : 0 < pb) (hpbB : pb < Bb)
    (hB1 : B1 ≤ 1) (hBa : Ba ≤ a) (hBb : Bb ≤ b) (hg : 0 < g)
    (hgτ : g ≤ Bτ - pτ) (hg1 : g ≤ B1 - p1) (hga : g ≤ Ba - pa) (hgb : g ≤ Bb - pb)
    (hsum : d ≤ pτ + p1) (hsuma : d ≤ pa + pa) (hsumb : d ≤ pb + pb)
    (hτbox : Bτ ≤ τ.re ∧ |τ.im| ≤ 1) (hs : s ∈ Set.Icc 0 r)
    (hT : (r + 1) / g ≤ T) (hx : T ≤ |x|)
    (hpref : ‖(1 : ℂ) / (2 * ((x : ℂ) + (s : ℂ) * I))‖ ≤ L)
    (hτnorm : ‖τ‖ ≤ N) (hα : ‖α‖ ≤ M) (hβ : ‖β‖ ≤ M) :
    ‖complexComparisonKernel τ 1 a b α β ((x : ℂ) + (s : ℂ) * I)‖ ≤
      L * (N * (2 / (1 - Real.exp (-2))) ^ 2 +
        M * a ^ 2 * (2 / (1 - Real.exp (-2))) ^ 2 +
        M * b ^ 2 * (2 / (1 - Real.exp (-2))) ^ 2) * Real.exp (-d * |x|) := by
  let y : ℂ := (x : ℂ) + (s : ℂ) * I
  let K := 2 / (1 - Real.exp (-2))
  have hsτ : ‖(Complex.sinh (τ * y))⁻¹‖ ≤ K * Real.exp (-pτ * |x|) := by
    simpa [y, K] using (norm_inv_sinh_tail_le_of_common_gap hpτ hpτB hτbox.1 hτbox.2
      hg hgτ hs hT hx)
  have hs1 : ‖(Complex.sinh y)⁻¹‖ ≤ K * Real.exp (-p1 * |x|) := by
    simpa [y, K] using (norm_inv_sinh_tail_le_of_common_gap
      (τ := (1 : ℂ)) hp1 hp1B hB1 (by simp) hg hg1 hs hT hx)
  have hsa : ‖(Complex.sinh (a * y))⁻¹‖ ≤ K * Real.exp (-pa * |x|) := by
    simpa [y, K] using (norm_inv_sinh_tail_le_of_common_gap
      (τ := (a : ℂ)) hpa hpaB hBa (by simp) hg hga hs hT hx)
  have hsb : ‖(Complex.sinh (b * y))⁻¹‖ ≤ K * Real.exp (-pb * |x|) := by
    simpa [y, K] using (norm_inv_sinh_tail_le_of_common_gap
      (τ := (b : ℂ)) hpb hpbB hBb (by simp) hg hgb hs hT hx)
  simpa [y, K, pow_two, mul_assoc] using
    norm_kernel_le_of_exp_bounds τ α β y a b L N M K K K K
      pτ p1 pa pb d x hsum hsuma hsumb (by simpa [y] using hpref)
      hτnorm hα hβ hsτ hs1 hsa hsb

/-- Constructs uniform tail constants from four chosen decay rates. -/
private lemma exists_norm_kernel_tail_le_of_rates
    {τ₀ a b M r d pτ p1 pa pb : ℝ} (hM : 0 ≤ M) (hr : 0 ≤ r)
    (hpτ : 0 < pτ) (hpττ : pτ < τ₀)
    (hp1 : 0 < p1) (hp11 : p1 < 1) (hpsum : d < pτ + p1)
    (hpa : 0 < pa) (hpaa : pa < a) (hpasum : d < 2 * pa)
    (hpb : 0 < pb) (hpbb : pb < b) (hpbsum : d < 2 * pb) :
    ∃ ε C T : ℝ, 0 < ε ∧ 0 < C ∧ 0 < T ∧
      ∀ (τ : ℂ), ‖τ - (τ₀ : ℂ)‖ ≤ ε →
      ∀ (α β : ℂ), ‖α‖ ≤ M → ‖β‖ ≤ M →
      ∀ (s : ℝ), s ∈ Set.Icc 0 r → ∀ x : ℝ, T ≤ |x| →
        ‖complexComparisonKernel τ 1 a b α β
          ((x : ℂ) + (s : ℂ) * I)‖ ≤ C * Real.exp (-d * |x|) := by
  have hτ₀ : 0 < τ₀ := hpτ.trans hpττ
  obtain ⟨Bτ, B1, Ba, Bb, g, hg, hpτB, hBτ, hp1B, hB1, hpaB, hBa,
    hpbB, hBb, hgτ, hg1, hga, hgb⟩ :=
    exists_intermediate_rates_with_common_gap hpττ hp11 hpaa hpbb
  obtain ⟨ε, hε, hnear⟩ := exists_closedBall_re_ge_abs_im_le hBτ
  let K := 2 / (1 - Real.exp (-2))
  have hK : 0 < K := inv_sinh_tail_constant_pos
  let L : ℝ := 1 / 2
  let N := τ₀ + ε
  let T := (r + 1) / g + 1
  let C := L * (N * K ^ 2 + M * a ^ 2 * K ^ 2 + M * b ^ 2 * K ^ 2)
  have hL : 0 < L := by dsimp [L]; norm_num
  have hN : 0 < N := by dsimp [N]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hT1 : 1 ≤ T := by
    dsimp [T]
    exact le_add_of_nonneg_left (by positivity)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ε, C, T, hε, hC, hT, ?_⟩
  intro τ hτ α β hα hβ s hs x hx
  have hτnorm : ‖τ‖ ≤ N := by
    simpa [N] using norm_le_real_add_of_norm_sub_le hτ₀.le hτ
  have hpref : ‖(1 : ℂ) / (2 * ((x : ℂ) + (s : ℂ) * I))‖ ≤ L := by
    simpa [L] using norm_comparison_prefactor_tail_le x s (hT1.trans hx)
  have hTdiv : (r + 1) / g ≤ T := by dsimp [T]; linarith
  simpa [C, K] using norm_kernel_tail_le_of_common_gap
    hpτ hpτB hp1 hp1B hpa hpaB hpb hpbB hB1.le hBa.le hBb.le hg hgτ hg1 hga hgb
    hpsum.le (by nlinarith [hpasum]) (by nlinarith [hpbsum]) (hnear τ hτ) hs hTdiv hx
    hpref hτnorm hα hβ

/-- Uniformly for periods `τ` near a positive real `τ₀`, bounded coefficients, and every
height `s ∈ [0,r]`, the two-reference comparison kernel is bounded by `C exp (-d|x|)` on the
tails `|x| ≥ T`. Unlike the full-line estimate, no zero-free upper bound on `r` is needed.
This is the uniform tail estimate underlying Ruijsenaars (1997), equation (3.56). -/
theorem exists_norm_complexComparisonKernel_tail_le
    {τ₀ a b M r d : ℝ} (hτ₀ : 0 < τ₀) (hM : 0 ≤ M) (hr : 0 ≤ r) (hd : 0 < d)
    (hdτ : d < τ₀ + 1) (hda : d < 2 * a) (hdb : d < 2 * b) :
    ∃ ε C T : ℝ, 0 < ε ∧ 0 < C ∧ 0 < T ∧
      ∀ (τ : ℂ), ‖τ - (τ₀ : ℂ)‖ ≤ ε →
      ∀ (α β : ℂ), ‖α‖ ≤ M → ‖β‖ ≤ M →
      ∀ (s : ℝ), s ∈ Set.Icc 0 r → ∀ x : ℝ, T ≤ |x| →
        ‖complexComparisonKernel τ 1 a b α β
          ((x : ℂ) + (s : ℂ) * I)‖ ≤ C * Real.exp (-d * |x|) := by
  obtain ⟨pτ, p1, pa, pb, hpτ, hpττ, hp1, hp11, hpsum,
    hpa, hpaa, hpasum, hpb, hpbb, hpbsum⟩ :=
    exists_complex_period_comparison_decay_rates hτ₀ hd hdτ hda hdb
  exact exists_norm_kernel_tail_le_of_rates hM hr
    hpτ hpττ hp1 hp11 hpsum hpa hpaa hpasum hpb hpbb hpbsum

end SIC
