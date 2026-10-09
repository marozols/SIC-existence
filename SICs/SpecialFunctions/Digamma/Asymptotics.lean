/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Digamma.EulerLimit
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Digamma estimates on slit-plane rays

Quadratic bounds for both Barnes normalization corrections on the slit plane.

This file proves absolute convergence of the two series defining Shintani's Barnes double-gamma
normalization coefficients in [95, Shintani (1977), Section 1.1]:

```text
sum_n (psi'(n tau) - (n tau)^-1),
sum_n (psi(n tau) - log(n tau) + (2 n tau)^-1).
```

The Euler limits from `SICs.SpecialFunctions.Digamma.EulerLimit` hold on the slit plane
`ℂ \ (-∞,0]`, the period-ratio domain of [95, Shintani (1977), paragraph 1.6
on p. 181]. Subtracting a telescoping reciprocal series from the trigamma expansion leaves a
cubic reciprocal remainder. A principal-logarithm telescoping identity and its cubic Taylor
remainder give the corresponding corrected-digamma estimate. An integral-test bound for the
cubic tail makes both errors `O(n^-2)`. The ray constant
`C(τ)=1+(1+‖τ‖)/max(Re τ, |Im τ|)` is continuous on the slit plane, including the
positive real axis. Its compact-set bounds give the locally
uniform convergence proved in `SICs.SpecialFunctions.Digamma.Series`.

## Main declarations

- `norm_deriv_digamma_mul_sub_inv_le`: an explicit bound for the trigamma correction.
- `deriv_digamma_mul_sub_inv_isBigO`: the `O(n^-2)` trigamma estimate.
- `summable_deriv_digamma_mul_sub_inv`: convergence of the trigamma normalization series.
- `norm_digamma_mul_sub_log_add_half_inv_le`: an explicit bound for the corrected digamma.
- `digamma_mul_sub_log_add_half_inv_isBigO`: the `O(n^-2)` corrected-digamma estimate.
- `summable_digamma_mul_sub_log_add_half_inv`: convergence of the second normalization series.

## References

- [95] T. Shintani, "On a Kronecker limit formula for real quadratic fields," J. Fac. Sci.
  Univ. Tokyo Sect. IA Math. 24 (1977), proof of Lemma 1 on p. 170, immediately before
  equation (1.3), and the analytic continuation in paragraph 1.6 on p. 181
-/

noncomputable section

open Complex Real MeasureTheory Set Filter Asymptotics

namespace SIC

/-! ### Quantitative trigamma estimate on slit-plane rays

For the trigamma coefficient in [95, Shintani (1977), equation (1.2)], set `z = N tau` and
subtract the telescoping series

```text
sum_j ((z+j)^-1 - (z+j+1)^-1) = z^-1
```

from the reciprocal-square expansion writes `psi'(z) - z^-1` as a sum whose `j`-th term is
`(z+j)^-2 (z+j+1)^-1`.  On a fixed ray in the slit plane, all three reciprocal factors are
bounded by a ray-dependent constant times `(N+j)^-1`.  The integral test for the resulting cubic
tail gives the explicit `O(N^-2)` estimate below.
-/

/-- The elementary improper integral used to bound the cubic reciprocal tail. -/
private lemma integral_Ioi_rpow_neg_three (N : ℕ) (hN : 0 < N) :
    ∫ x in Ioi (N : ℝ), x ^ (-3 : ℝ) = 1 / (2 * (N : ℝ) ^ 2) := by
  have hNR : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hNR]
  rw [show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg hNR.le]
  field_simp [hNR.ne']
  exact (Real.rpow_natCast (N : ℝ) 2).symm

/-- Translating the convergent cubic `p`-series preserves its summability. -/
private lemma summable_rpow_nat_add_neg_three (N : ℕ) :
    Summable (fun j : ℕ => ((j : ℝ) + N) ^ (-3 : ℝ)) := by
  have hall : Summable (fun j : ℕ => (j : ℝ) ^ (-3 : ℝ)) := by
    rw [Real.summable_nat_rpow]
    norm_num
  simpa only [Nat.cast_add] using (summable_nat_add_iff N).mpr hall

/-- The complete cubic reciprocal tail starting at a positive natural number is bounded by its
first term plus the corresponding improper integral. -/
private lemma tsum_rpow_nat_add_neg_three_le (N : ℕ) (hN : 0 < N) :
    ∑' j : ℕ, ((j : ℝ) + N) ^ (-3 : ℝ) ≤ 3 / (2 * (N : ℝ) ^ 2) := by
  let f : ℝ → ℝ := fun x => x ^ (-3 : ℝ)
  have hNR : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hanti : AntitoneOn f (Ici (N : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num : (-3 : ℝ) ≤ 0)).mono
      fun x hx => hNR.trans_le hx
  have hint : IntegrableOn f (Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hNR
  have hnonneg : ∀ x ∈ Ioi (N : ℝ), 0 ≤ f x :=
    fun x hx => Real.rpow_nonneg (le_of_lt <| hNR.trans hx) _
  have htail := hanti.tsum_comp_add_le_integral N hint hnonneg
  rw [integral_Ioi_rpow_neg_three N hN] at htail
  have hsum : Summable (fun j : ℕ => f ((j : ℝ) + N)) :=
    summable_rpow_nat_add_neg_three N
  have htail' : ∑' j : ℕ, f (((j + 1 : ℕ) : ℝ) + N) ≤
      1 / (2 * (N : ℝ) ^ 2) := by
    convert htail using 1
    congr 1
    funext j
    congr 1
    push_cast
    ring
  rw [hsum.tsum_eq_zero_add]
  have hfN : f N = 1 / (N : ℝ) ^ 3 := by
    dsimp [f]
    rw [Real.rpow_neg hNR.le, one_div]
    exact congrArg Inv.inv (Real.rpow_natCast (N : ℝ) 3)
  simp only [Nat.cast_zero, zero_add]
  rw [hfN]
  have hNge : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc
    1 / (N : ℝ) ^ 3 + ∑' j : ℕ, f (((j + 1 : ℕ) : ℝ) + N) ≤
        1 / (N : ℝ) ^ 3 + 1 / (2 * (N : ℝ) ^ 2) := by
      exact add_le_add_right htail' _
    _ ≤ 3 / (2 * (N : ℝ) ^ 2) := by
      rw [div_eq_mul_inv]
      field_simp
      nlinarith

/-- Every finite initial segment of the cubic reciprocal tail has the same integral-test bound. -/
private lemma sum_range_inv_nat_add_cube_le (N M : ℕ) (hN : 0 < N) :
    ∑ j ∈ Finset.range M, (((N + j : ℕ) : ℝ) ^ 3)⁻¹ ≤
      3 / (2 * (N : ℝ) ^ 2) := by
  have hsum := summable_rpow_nat_add_neg_three N
  calc
    (∑ j ∈ Finset.range M, (((N + j : ℕ) : ℝ) ^ 3)⁻¹) =
        ∑ j ∈ Finset.range M, ((j : ℝ) + N) ^ (-3 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Real.rpow_neg]
          · have hpow : ((((N + j : ℕ) : ℝ)) ^ 3) =
                ((j : ℝ) + N) ^ 3 := by
              push_cast
              ring
            exact (congrArg Inv.inv hpow).trans
              (congrArg Inv.inv (Real.rpow_natCast ((j : ℝ) + N) 3).symm)
          · positivity
    _ ≤ ∑' j : ℕ, ((j : ℝ) + N) ^ (-3 : ℝ) := by
      apply hsum.sum_le_tsum
      intro j hj
      exact Real.rpow_nonneg (by positivity) _
    _ ≤ _ := tsum_rpow_nat_add_neg_three_le N hN

/-- Positive dilation and nonnegative translation preserve the slit plane.
This supplies the nonvanishing needed by `norm_slitRay_inv_le`. -/
private lemma slitPlane_nat_mul_add (tau : ℂ) (htau : tau ∈ Complex.slitPlane)
    (N : ℕ) (hN : 0 < N) (j : ℕ) : (N : ℂ) * tau + j ∈ Complex.slitPlane := by
  rcases htau with h | h
  · left
    simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero]
    positivity
  · right
    simpa using mul_ne_zero (Nat.cast_ne_zero.mpr hN.ne' : (N : ℝ) ≠ 0) h

/-- The denominator `max(Re τ, |Im τ|)` is positive exactly where the ray
estimates are used, including the positive real axis. This supplies
`digammaRayConstant_pos` and `continuousOn_digammaRayConstant`. -/
private lemma ray_denominator_pos (tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    0 < max tau.re |tau.im| := by
  rcases htau with h | h
  · exact lt_max_of_lt_left h
  · exact lt_max_of_lt_right (abs_pos.mpr h)

/-- The ray constant `C(τ)=1+(1+‖τ‖)/max(Re τ, |Im τ|)` controls the
reciprocals of `Nτ+j`. It is finite and locally bounded on `ℂ \ (-∞,0]`,
as needed for the continuation of Shintani's coefficient series in
[95, Shintani (1977), paragraph 1.6, p. 181]. -/
noncomputable def digammaRayConstant (tau : ℂ) : ℝ :=
  1 + (1 + ‖tau‖) / max tau.re |tau.im|

/-- The ray constant `C(τ)` is positive on the slit plane. -/
lemma digammaRayConstant_pos (tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    0 < digammaRayConstant tau := by
  have := ray_denominator_pos tau htau
  unfold digammaRayConstant
  positivity

/-- The ray constant `C(τ)` is continuous on the slit plane, so compact sets
have a single bound for both digamma remainders. -/
lemma continuousOn_digammaRayConstant :
    ContinuousOn digammaRayConstant Complex.slitPlane := by
  intro tau htau
  exact (continuousAt_const.add ((continuousAt_const.add continuous_norm.continuousAt).div
    (Complex.continuous_re.continuousAt.max Complex.continuous_im.continuousAt.abs)
    (ray_denominator_pos tau htau).ne')).continuousWithinAt

/-- On a slit-plane ray, `N+j ≤ C(τ) ‖Nτ+j‖`. This is the geometric
comparison used in `norm_slitRay_inv_le` and in the Barnes cone product estimates. -/
lemma nat_add_le_digammaRayConstant_mul_norm (tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) (N j : ℕ) :
    ((N + j : ℕ) : ℝ) ≤ digammaRayConstant tau * ‖(N : ℂ) * tau + j‖ := by
  let a : ℂ := (N : ℂ) * tau + j
  have hreal : (N : ℝ) * tau.re ≤ ‖a‖ := by
    have h := Complex.re_le_norm a
    simp only [a, Complex.add_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero] at h
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have him : (N : ℝ) * |tau.im| ≤ ‖a‖ := by
    simpa [a, abs_mul, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      using Complex.abs_im_le_norm a
  have hN : (N : ℝ) ≤ ‖a‖ / max tau.re |tau.im| := by
    apply (le_div_iff₀ (ray_denominator_pos tau htau)).2
    rw [mul_max_of_nonneg _ _ (Nat.cast_nonneg N)]
    exact max_le hreal him
  have hj : (j : ℝ) ≤ ‖a‖ + (N : ℝ) * ‖tau‖ := by
    calc
      (j : ℝ) = ‖a - (N : ℂ) * tau‖ := by simp [a]
      _ ≤ ‖a‖ + ‖(N : ℂ) * tau‖ := norm_sub_le _ _
      _ = ‖a‖ + (N : ℝ) * ‖tau‖ := by simp
  have hNnorm := mul_le_mul_of_nonneg_right hN (norm_nonneg tau)
  rw [Nat.cast_add]
  calc
    (N : ℝ) + j ≤ ‖a‖ / max tau.re |tau.im| +
        (‖a‖ + (‖a‖ / max tau.re |tau.im|) * ‖tau‖) := by linarith
    _ = digammaRayConstant tau * ‖a‖ := by unfold digammaRayConstant; ring

/-- Reciprocals along a slit-plane ray satisfy `‖(Nτ+j)⁻¹‖ ≤ C(τ)/(N+j)`. -/
private lemma norm_slitRay_inv_le (tau : ℂ) (htau : tau ∈ Complex.slitPlane)
    (N : ℕ) (hN : 0 < N) (j : ℕ) :
    ‖(((N : ℂ) * tau + j)⁻¹)‖ ≤ digammaRayConstant tau / ((N + j : ℕ) : ℝ) := by
  have ha := Complex.slitPlane_ne_zero (slitPlane_nat_mul_add tau htau N hN j)
  rw [norm_inv]
  apply (le_div_iff₀ (Nat.cast_pos.mpr (Nat.add_pos_left hN j))).2
  have h := nat_add_le_digammaRayConstant_mul_norm tau htau N j
  calc
    _ ≤ ‖(N : ℂ) * tau + j‖⁻¹ *
        (digammaRayConstant tau * ‖(N : ℂ) * tau + j‖) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (norm_nonneg _))
    _ = digammaRayConstant tau := by field_simp [norm_ne_zero_iff.mpr ha]

/-- Each term of the telescoped trigamma remainder is dominated by the corresponding cubic
reciprocal term. -/
private lemma norm_trigamma_remainder_le (tau : ℂ) (htau : tau ∈ Complex.slitPlane)
    (N : ℕ) (hN : 0 < N) (j : ℕ) :
    ‖(((N : ℂ) * tau + j)⁻¹ ^ 2 * ((N : ℂ) * tau + j + 1)⁻¹)‖ ≤
      digammaRayConstant tau ^ 3 * ((((N + j : ℕ) : ℝ) ^ 3)⁻¹) := by
  have hC := (digammaRayConstant_pos tau htau).le
  have hj := norm_slitRay_inv_le tau htau N hN j
  have hj1 := norm_slitRay_inv_le tau htau N hN (j + 1)
  have hj1' : ‖((N : ℂ) * tau + j + 1)⁻¹‖ ≤
      digammaRayConstant tau / (((N + (j + 1) : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hj1
  have hfrac : digammaRayConstant tau / (((N + (j + 1) : ℕ) : ℝ)) ≤
      digammaRayConstant tau / (((N + j : ℕ) : ℝ)) := by
    gcongr
    omega
  rw [norm_mul, norm_pow]
  calc
    ‖((N : ℂ) * tau + j)⁻¹‖ ^ 2 * ‖((N : ℂ) * tau + j + 1)⁻¹‖ ≤
        (digammaRayConstant tau / ((N + j : ℕ) : ℝ)) ^ 2 *
          (digammaRayConstant tau / ((N + (j + 1) : ℕ) : ℝ)) := by
      gcongr
    _ ≤ (digammaRayConstant tau / ((N + j : ℕ) : ℝ)) ^ 3 := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left hfrac (sq_nonneg _)
    _ = digammaRayConstant tau ^ 3 * ((((N + j : ℕ) : ℝ) ^ 3)⁻¹) := by
      field_simp

/-- Subtracting the finite telescoping reciprocal sum expresses the finite trigamma error as a
sum of cubic-order remainder terms. -/
private lemma gammaSeqTrigamma_sub_inv_add_endpoint (z : ℂ) (n : ℕ)
    (hz : ∀ j ∈ Finset.range (n + 2), z + j ≠ 0) :
    gammaSeqTrigamma z n - z⁻¹ + (z + (n + 1 : ℕ))⁻¹ =
      ∑ j ∈ Finset.range (n + 1), (z + j)⁻¹ ^ 2 * (z + j + 1)⁻¹ := by
  have htel : (∑ j ∈ Finset.range (n + 1),
      ((z + j)⁻¹ - (z + (j + 1 : ℕ))⁻¹)) =
      z⁻¹ - (z + (n + 1 : ℕ))⁻¹ := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] using
      (Finset.sum_range_sub' (fun j : ℕ => (z + j)⁻¹) (n + 1))
  rw [gammaSeqTrigamma]
  calc
    (∑ j ∈ Finset.range (n + 1), (z + j)⁻¹ ^ 2) - z⁻¹ +
        (z + (n + 1 : ℕ))⁻¹ =
        (∑ j ∈ Finset.range (n + 1), (z + j)⁻¹ ^ 2) -
          (z⁻¹ - (z + (n + 1 : ℕ))⁻¹) := by ring
    _ = (∑ j ∈ Finset.range (n + 1), (z + j)⁻¹ ^ 2) -
          ∑ j ∈ Finset.range (n + 1),
            ((z + j)⁻¹ - (z + (j + 1 : ℕ))⁻¹) := by rw [htel]
    _ = ∑ j ∈ Finset.range (n + 1),
          ((z + j)⁻¹ ^ 2 - ((z + j)⁻¹ - (z + (j + 1 : ℕ))⁻¹)) := by
        symm
        exact Finset.sum_sub_distrib
          (s := Finset.range (n + 1))
          (f := fun j : ℕ => (z + j)⁻¹ ^ 2)
          (g := fun j : ℕ => (z + j)⁻¹ - (z + (j + 1 : ℕ))⁻¹)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < n + 1 := Finset.mem_range.mp hj
      have hzero : z + j ≠ 0 := hz j (Finset.mem_range.mpr (by omega))
      have hzero1 : z + j + 1 ≠ 0 := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
          hz (j + 1) (Finset.mem_range.mpr (by omega))
      rw [show z + (j + 1 : ℕ) = z + j + 1 by push_cast; ring]
      field_simp [hzero, hzero1]
      ring

/-- The finite telescoped trigamma remainders satisfy the ray-wise quadratic bound uniformly in
the Euler cutoff. -/
private lemma gammaSeqTrigamma_remainder_norm_le (tau : ℂ) (htau : tau ∈ Complex.slitPlane)
    (N : ℕ) (hN : 0 < N) (n : ℕ) :
    ‖gammaSeqTrigamma ((N : ℂ) * tau) n - ((N : ℂ) * tau)⁻¹ +
        ((N : ℂ) * tau + (n + 1 : ℕ))⁻¹‖ ≤
      3 * digammaRayConstant tau ^ 3 / (2 * (N : ℝ) ^ 2) := by
  have hz : ∀ j ∈ Finset.range (n + 2), (N : ℂ) * tau + j ≠ 0 :=
    fun j _ => Complex.slitPlane_ne_zero (slitPlane_nat_mul_add tau htau N hN j)
  rw [gammaSeqTrigamma_sub_inv_add_endpoint ((N : ℂ) * tau) n hz]
  calc
    ‖∑ j ∈ Finset.range (n + 1),
        (((N : ℂ) * tau + j)⁻¹ ^ 2 * ((N : ℂ) * tau + j + 1)⁻¹)‖ ≤
        ∑ j ∈ Finset.range (n + 1),
          ‖(((N : ℂ) * tau + j)⁻¹ ^ 2 * ((N : ℂ) * tau + j + 1)⁻¹)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1),
          digammaRayConstant tau ^ 3 * ((((N + j : ℕ) : ℝ) ^ 3)⁻¹) := by
      gcongr with j hj
      exact norm_trigamma_remainder_le tau htau N hN j
    _ = digammaRayConstant tau ^ 3 *
          ∑ j ∈ Finset.range (n + 1), ((((N + j : ℕ) : ℝ) ^ 3)⁻¹) := by
      simp only [Finset.mul_sum]
    _ ≤ digammaRayConstant tau ^ 3 * (3 / (2 * (N : ℝ) ^ 2)) := by
      gcongr
      · exact pow_nonneg (digammaRayConstant_pos tau htau).le _
      · exact sum_range_inv_nat_add_cube_le N (n + 1) hN
    _ = 3 * digammaRayConstant tau ^ 3 / (2 * (N : ℝ) ^ 2) := by ring

/-- Along any slit-plane ray, the trigamma correction satisfies the explicit bound

```text
‖psi'(N tau) - (N tau)^-1‖
  ≤ 3 (1 + (1 + ‖tau‖) / max(Re(tau), |Im(tau)|))^3 / (2 N^2).
```

This is a quantitative complex-ray form of the decay used to define `γ₂₁` in
[95, Shintani (1977), equation (1.2) and proof of Lemma 1 on pp. 170–171], with the extension to
slit-plane period ratios described in [95, Shintani (1977), paragraph 1.6 on p. 181]. -/
theorem norm_deriv_digamma_mul_sub_inv_le (tau : ℂ) (htau : tau ∈ Complex.slitPlane)
    (N : ℕ) (hN : 0 < N) :
    ‖deriv Complex.digamma ((N : ℂ) * tau) - ((N : ℂ) * tau)⁻¹‖ ≤
      3 * (1 + (1 + ‖tau‖) / max tau.re |tau.im|) ^ 3 / (2 * (N : ℝ) ^ 2) := by
  let z : ℂ := (N : ℂ) * tau
  have hz : z ∈ Complex.slitPlane := by
    simpa [z] using slitPlane_nat_mul_add tau htau N hN 0
  have htri := tendsto_gammaSeqTrigamma_of_mem_slitPlane z hz
  have hend : Tendsto (fun n : ℕ => (z + ((n + 2 : ℕ) : ℂ))⁻¹) atTop (nhds 0) := by
    apply tendsto_inv₀_cobounded.comp
    exact (tendsto_const_add_cobounded z).comp
      (tendsto_natCast_atTop_cobounded.comp (tendsto_add_atTop_nat 2))
  have hlim : Tendsto (fun n : ℕ =>
      gammaSeqTrigamma z (n + 1) - z⁻¹ + (z + (n + 2 : ℕ))⁻¹) atTop
      (nhds (deriv Complex.digamma z - z⁻¹)) := by
    simpa only [add_zero] using (htri.sub_const z⁻¹).add hend
  apply le_of_tendsto hlim.norm
  apply Filter.Eventually.of_forall
  intro n
  simpa only [digammaRayConstant] using
    gammaSeqTrigamma_remainder_norm_le tau htau N hN (n + 1)

/-- The trigamma correction on every slit-plane ray is `O(N⁻²)`.  This is the asymptotic
form of `norm_deriv_digamma_mul_sub_inv_le`. -/
theorem deriv_digamma_mul_sub_inv_isBigO (tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    (fun n : ℕ => deriv Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) -
      (((n + 1 : ℕ) : ℂ) * tau)⁻¹) =O[atTop]
      (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
  apply IsBigO.of_bound (3 * digammaRayConstant tau ^ 3 / 2)
  apply Filter.Eventually.of_forall
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  calc
    ‖deriv Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) -
        (((n + 1 : ℕ) : ℂ) * tau)⁻¹‖ ≤
        3 * digammaRayConstant tau ^ 3 / (2 * (((n + 1 : ℕ) : ℝ) ^ 2)) :=
      norm_deriv_digamma_mul_sub_inv_le tau htau (n + 1) (Nat.zero_lt_succ n)
    _ = 3 * digammaRayConstant tau ^ 3 / 2 *
          ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by ring

/-- The trigamma correction series on every slit-plane ray is absolutely summable:

```text
sum_{n=1}^∞ (psi'(n tau) - (n tau)^-1).
```

This is the convergence required for Shintani's coefficient `γ₂₁` in
[95, Shintani (1977), equation (1.2) on p. 170]; it follows from
`deriv_digamma_mul_sub_inv_isBigO`. -/
theorem summable_deriv_digamma_mul_sub_inv (tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    Summable (fun n : ℕ =>
      deriv Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) -
        (((n + 1 : ℕ) : ℂ) * tau)⁻¹) := by
  have hs : Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by decide))
  exact summable_of_isBigO_nat hs (deriv_digamma_mul_sub_inv_isBigO tau htau)

/-! ### Quantitative corrected-digamma estimate

For the second coefficient in [95, Shintani (1977), equation (1.1)], the logarithmic-derivative
correction is treated by telescoping the principal logarithm along the horizontal translates
`z + j`. After adding half of the reciprocal telescoping difference, the
individual remainder is cubic in `(z+j)⁻¹`.  A third-order complex-log Taylor bound therefore
reduces the estimate to the same cubic tail used above.
-/

/-- For `a ∈ ℂ \ (-∞,0]` and `‖a⁻¹‖<1`,
`log(1+a⁻¹)=log(a+1)-log(a)`. The arguments of the two factors have
opposite signs, so their sum stays in the principal branch. This supplies
`gammaSeqLogDeriv_corrected_eq`. -/
private lemma log_one_add_inv_eq_sub {a : ℂ} (ha : a ∈ Complex.slitPlane)
    (hinv : ‖a⁻¹‖ < 1) :
    Complex.log (1 + a⁻¹) = Complex.log (a + 1) - Complex.log a := by
  have ha0 := Complex.slitPlane_ne_zero ha
  have hw := Complex.mem_slitPlane_of_norm_lt_one hinv
  have him : (1 + a⁻¹).im = -a.im / Complex.normSq a := by simp [Complex.inv_im]
  have harg : a.arg + (1 + a⁻¹).arg ∈ Ioc (-π) π := by
    rcases lt_trichotomy a.im 0 with h | h | h
    · have haarg := Complex.arg_neg_iff.mpr h
      have hwarg := Complex.arg_nonneg_iff.mpr (show 0 ≤ (1 + a⁻¹).im by
        rw [him]; exact div_nonneg (neg_nonneg.mpr h.le) (normSq_nonneg a))
      constructor <;> linarith [Complex.neg_pi_lt_arg a, Complex.arg_le_pi (1 + a⁻¹)]
    · have hare : 0 < a.re := ha.resolve_right (not_ne_iff.mpr h)
      have hwre : 0 < (1 + a⁻¹).re := hw.resolve_right (by simp [him, h])
      simp [Complex.arg_eq_zero_iff.mpr ⟨hare.le, h⟩,
        Complex.arg_eq_zero_iff.mpr ⟨hwre.le, by simp [him, h]⟩, Real.pi_pos.le,
        Real.pi_pos]
    · have haarg := Complex.arg_nonneg_iff.mpr h.le
      have hwarg := Complex.arg_neg_iff.mpr (show (1 + a⁻¹).im < 0 by
        rw [him]; exact div_neg_of_neg_of_pos (neg_neg_of_pos h) (normSq_pos.mpr ha0))
      constructor <;> linarith [Complex.neg_pi_lt_arg (1 + a⁻¹), Complex.arg_le_pi a]
  have hlog := Complex.log_mul ha0 (Complex.slitPlane_ne_zero hw) harg
  rw [show a * (1 + a⁻¹) = a + 1 by field_simp] at hlog
  rw [hlog]
  ring

/-- The cubic-order term obtained after telescoping both the logarithms and half of the
reciprocals in the finite digamma approximant. -/
private noncomputable def correctedDigammaTerm (a : ℂ) : ℂ :=
  Complex.log (1 + a⁻¹) - a⁻¹ + (a⁻¹ - (a + 1)⁻¹) / 2

/-- When `a≠0` and `‖a⁻¹‖ ≤ 1/2`, the corrected-digamma remainder term
is bounded by `(5/3) ‖a⁻¹‖³`. -/
private lemma norm_correctedDigammaTerm_le {a : ℂ} (ha : a ≠ 0)
    (hinv : ‖a⁻¹‖ ≤ 1 / 2) :
    ‖correctedDigammaTerm a‖ ≤ (5 / 3 : ℝ) * ‖a⁻¹‖ ^ 3 := by
  let w : ℂ := a⁻¹
  have hw : ‖w‖ < 1 := lt_of_le_of_lt hinv (by norm_num)
  have hone : 1 + w ≠ 0 := by
    intro h
    have hneg : w = -1 := by linear_combination h
    rw [hneg, norm_neg, norm_one] at hw
    exact lt_irrefl 1 hw
  have hlog :
      ‖Complex.log (1 + w) - (w - w ^ 2 / 2)‖ ≤
        ‖w‖ ^ 3 * (1 - ‖w‖)⁻¹ / 3 := by
    have htaylor : Complex.logTaylor 3 w = w - w ^ 2 / 2 := by
      norm_num [Complex.logTaylor, Finset.sum_range_succ]
      ring
    have h := Complex.norm_log_sub_logTaylor_le 2 hw
    rw [htaylor] at h
    norm_num at h
    exact h
  have hden : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (sub_pos_of_lt hw) (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hlog' :
      ‖Complex.log (1 + w) - (w - w ^ 2 / 2)‖ ≤ (2 / 3 : ℝ) * ‖w‖ ^ 3 := by
    calc
      _ ≤ ‖w‖ ^ 3 * (1 - ‖w‖)⁻¹ / 3 := hlog
      _ ≤ ‖w‖ ^ 3 * 2 / 3 := by gcongr
      _ = (2 / 3 : ℝ) * ‖w‖ ^ 3 := by ring
  have haone : (a + 1)⁻¹ = w / (1 + w) := by
    dsimp [w]
    field_simp [ha, hone]
  have hrewrite : correctedDigammaTerm a =
      (Complex.log (1 + w) - (w - w ^ 2 / 2)) - w ^ 3 / (2 * (1 + w)) := by
    unfold correctedDigammaTerm
    change Complex.log (1 + w) - w + (w - (a + 1)⁻¹) / 2 = _
    rw [haone]
    field_simp [hone]
    ring
  have honeNorm : (1 / 2 : ℝ) ≤ ‖1 + w‖ := by
    calc
      (1 / 2 : ℝ) ≤ 1 - ‖w‖ := by linarith
      _ ≤ ‖1 + w‖ := by
        simpa only [norm_one, norm_neg, sub_neg_eq_add] using norm_sub_norm_le 1 (-w)
  have hsecond : ‖w ^ 3 / (2 * (1 + w))‖ ≤ ‖w‖ ^ 3 := by
    rw [norm_div, norm_mul, Complex.norm_ofNat, norm_pow]
    apply (div_le_iff₀ (mul_pos (by norm_num) (norm_pos_iff.mpr hone))).2
    have hfactor : (1 : ℝ) ≤ 2 * ‖1 + w‖ := by linarith
    calc
      ‖w‖ ^ 3 = ‖w‖ ^ 3 * 1 := by ring
      _ ≤ ‖w‖ ^ 3 * (2 * ‖1 + w‖) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
  rw [hrewrite]
  exact (norm_sub_le _ _).trans <| by linarith

/-- The corrected finite logarithmic derivative splits into a vanishing endpoint term and the
partial sum of `correctedDigammaTerm`. -/
private lemma gammaSeqLogDeriv_corrected_eq (z : ℂ) (hz : z ∈ Complex.slitPlane) (n : ℕ)
    (hinv : ∀ j ∈ Finset.range (n + 1), ‖(z + j)⁻¹‖ < 1) :
    gammaSeqLogDeriv z n - Complex.log z + z⁻¹ / 2 =
      Complex.log n - Complex.log (z + (n + 1 : ℕ)) +
        (z + (n + 1 : ℕ))⁻¹ / 2 +
        ∑ j ∈ Finset.range (n + 1), correctedDigammaTerm (z + j) := by
  have hlogtel : (∑ j ∈ Finset.range (n + 1), Complex.log (1 + (z + j)⁻¹)) =
      Complex.log (z + (n + 1 : ℕ)) - Complex.log z := by
    calc
      (∑ j ∈ Finset.range (n + 1), Complex.log (1 + (z + j)⁻¹)) =
          ∑ j ∈ Finset.range (n + 1),
            (Complex.log (z + (j + 1 : ℕ)) - Complex.log (z + j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [log_one_add_inv_eq_sub
          (by simpa using slitPlane_nat_mul_add z hz 1 (by decide) j) (hinv j hj)]
        congr 2
        push_cast
        ring
      _ = -(∑ j ∈ Finset.range (n + 1),
            (Complex.log (z + j) - Complex.log (z + (j + 1 : ℕ)))) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = -(Complex.log z - Complex.log (z + (n + 1 : ℕ))) := by
        rw [Finset.sum_range_sub']
        simp only [Nat.cast_zero, add_zero]
      _ = _ := by ring
  have hinvtel : (∑ j ∈ Finset.range (n + 1),
      ((z + j)⁻¹ - (z + (j + 1 : ℕ))⁻¹)) =
      z⁻¹ - (z + (n + 1 : ℕ))⁻¹ := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] using
      (Finset.sum_range_sub' (fun j : ℕ => (z + j)⁻¹) (n + 1))
  have hsumterm : (∑ j ∈ Finset.range (n + 1), correctedDigammaTerm (z + j)) =
      (Complex.log (z + (n + 1 : ℕ)) - Complex.log z) -
        ∑ j ∈ Finset.range (n + 1), (z + j)⁻¹ +
        (z⁻¹ - (z + (n + 1 : ℕ))⁻¹) / 2 := by
    calc
      (∑ j ∈ Finset.range (n + 1), correctedDigammaTerm (z + j)) =
          ∑ j ∈ Finset.range (n + 1),
            ((Complex.log (1 + (z + j)⁻¹) - (z + j)⁻¹) +
              ((z + j)⁻¹ - (z + j + 1)⁻¹) / 2) := by
        apply Finset.sum_congr rfl
        intro j hj
        unfold correctedDigammaTerm
        rfl
      _ = (∑ j ∈ Finset.range (n + 1), Complex.log (1 + (z + j)⁻¹)) -
            (∑ j ∈ Finset.range (n + 1), (z + j)⁻¹) +
            (∑ j ∈ Finset.range (n + 1),
              ((z + j)⁻¹ - (z + (j + 1 : ℕ))⁻¹)) / 2 := by
        simp_rw [show ∀ j : ℕ, z + j + 1 = z + (j + 1 : ℕ) by
          intro j; push_cast; ring]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div]
      _ = _ := by rw [hlogtel, hinvtel]
  unfold gammaSeqLogDeriv
  rw [hsumterm]
  ring

/-- The logarithmic endpoint left by the finite corrected-digamma identity tends to zero. -/
private lemma tendsto_correctedDigamma_endpoint (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    Tendsto (fun n : ℕ =>
      Complex.log (n + 1) - Complex.log (z + (n + 2 : ℕ)) +
        (z + (n + 2 : ℕ))⁻¹ / 2) atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ => ((((n + 1 : ℕ) : ℂ))⁻¹)) atTop (nhds 0) := by
    apply tendsto_inv₀_cobounded.comp
    exact tendsto_natCast_atTop_cobounded.comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto (fun n : ℕ => 1 + (z + 1) * (((n + 1 : ℕ) : ℂ))⁻¹)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  have hlog : Tendsto (fun n : ℕ =>
      Complex.log (1 + (z + 1) * (((n + 1 : ℕ) : ℂ))⁻¹)) atTop (nhds 0) := by
    simpa using hratio.clog Complex.one_mem_slitPlane
  have hlogdiff : Tendsto (fun n : ℕ =>
      Complex.log (n + 1) - Complex.log (z + (n + 2 : ℕ))) atTop (nhds 0) := by
    have heq : (fun n : ℕ =>
        -Complex.log (1 + (z + 1) * (((n + 1 : ℕ) : ℂ))⁻¹)) =ᶠ[atTop]
        (fun n : ℕ => Complex.log (n + 1) - Complex.log (z + (n + 2 : ℕ))) := by
      filter_upwards with n
      have hnR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hfactor : z + (n + 2 : ℕ) =
          ((n + 1 : ℕ) : ℝ) * (1 + (z + 1) * (((n + 1 : ℕ) : ℂ))⁻¹) := by
        field_simp
        push_cast
        ring
      rw [hfactor, Complex.log_ofReal_mul (r := ((n + 1 : ℕ) : ℝ)) hnR]
      · rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring]
        simp only [Complex.natCast_log]
        ring
      · intro hzero
        have hendzero : z + (n + 2 : ℕ) = 0 := by rw [hfactor, hzero, mul_zero]
        exact Complex.slitPlane_ne_zero
          (by simpa using slitPlane_nat_mul_add z hz 1 (by decide) (n + 2)) hendzero
    simpa only [neg_zero] using hlog.neg.congr' heq
  have hend : Tendsto (fun n : ℕ => (z + ((n + 2 : ℕ) : ℂ))⁻¹ / 2) atTop
      (nhds 0) := by
    have hinvEnd : Tendsto (fun n : ℕ => (z + ((n + 2 : ℕ) : ℂ))⁻¹) atTop
        (nhds 0) := by
      apply tendsto_inv₀_cobounded.comp
      exact (tendsto_const_add_cobounded z).comp
        (tendsto_natCast_atTop_cobounded.comp (tendsto_add_atTop_nat 2))
    simpa using hinvEnd.div_const 2
  simpa using hlogdiff.add hend

/-- The cubic reciprocal series translated by any natural number is summable. -/
private lemma summable_inv_nat_add_cube (N : ℕ) :
    Summable (fun j : ℕ => ((((N + j : ℕ) : ℝ) ^ 3)⁻¹)) := by
  simpa only [Nat.add_comm] using
    (summable_nat_add_iff N).mpr (Real.summable_nat_pow_inv.mpr (by decide : 1 < 3))

/-- Once `N` is at least twice the ray constant, every reciprocal `‖(N τ+j)⁻¹‖` is at most
one half. -/
private lemma norm_slitRay_inv_le_half (tau : ℂ) (htau : tau ∈ Complex.slitPlane)
    (N : ℕ) (hN : 0 < N) (hlarge : 2 * digammaRayConstant tau ≤ (N : ℝ)) (j : ℕ) :
    ‖(((N : ℂ) * tau + j)⁻¹)‖ ≤ 1 / 2 := by
  have hC := (digammaRayConstant_pos tau htau).le
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hCN : digammaRayConstant tau / (N : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hNR).2
    nlinarith
  have hfrac : digammaRayConstant tau / (((N + j : ℕ) : ℝ)) ≤
      digammaRayConstant tau / (N : ℝ) := by
    gcongr
    exact_mod_cast Nat.le_add_right N j
  exact (norm_slitRay_inv_le tau htau N hN j).trans (hfrac.trans hCN)

/-- On a sufficiently far part of a slit-plane ray, the `j`-th corrected-digamma term is
bounded by the corresponding cubic reciprocal majorant. -/
private lemma norm_correctedDigammaTerm_slitRay_le (tau : ℂ) (htau : tau ∈ Complex.slitPlane)
    (N : ℕ) (hN : 0 < N) (hlarge : 2 * digammaRayConstant tau ≤ (N : ℝ)) (j : ℕ) :
    ‖correctedDigammaTerm ((N : ℂ) * tau + j)‖ ≤
      (5 / 3 : ℝ) * digammaRayConstant tau ^ 3 * ((((N + j : ℕ) : ℝ) ^ 3)⁻¹) := by
  have hC := (digammaRayConstant_pos tau htau).le
  have hj0 := Complex.slitPlane_ne_zero (slitPlane_nat_mul_add tau htau N hN j)
  calc
    ‖correctedDigammaTerm ((N : ℂ) * tau + j)‖ ≤
        (5 / 3 : ℝ) * ‖((N : ℂ) * tau + j)⁻¹‖ ^ 3 :=
      norm_correctedDigammaTerm_le hj0
        (norm_slitRay_inv_le_half tau htau N hN hlarge j)
    _ ≤ (5 / 3 : ℝ) *
        (digammaRayConstant tau / (((N + j : ℕ) : ℝ))) ^ 3 := by
      gcongr
      exact norm_slitRay_inv_le tau htau N hN j
    _ = (5 / 3 : ℝ) * digammaRayConstant tau ^ 3 *
        ((((N + j : ℕ) : ℝ) ^ 3)⁻¹) := by field_simp

/-- The corrected-digamma expression on a sufficiently far point of a slit-plane ray is
the sum of its cubic-order horizontal-translation remainders. -/
private lemma hasSum_correctedDigammaTerm_slitRay (tau : ℂ) (htau : tau ∈ Complex.slitPlane)
    (N : ℕ) (hN : 0 < N) (hlarge : 2 * digammaRayConstant tau ≤ (N : ℝ)) :
    HasSum (fun j : ℕ => correctedDigammaTerm ((N : ℂ) * tau + j))
      (Complex.digamma ((N : ℂ) * tau) - Complex.log ((N : ℂ) * tau) +
        ((N : ℂ) * tau)⁻¹ / 2) := by
  let z : ℂ := (N : ℂ) * tau
  have hz : z ∈ Complex.slitPlane := by
    simpa [z] using slitPlane_nat_mul_add tau htau N hN 0
  have hnorm : Summable (fun j : ℕ => ‖correctedDigammaTerm (z + j)‖) := by
    apply Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => by simpa only [z] using
        norm_correctedDigammaTerm_slitRay_le tau htau N hN hlarge j)
    exact (summable_inv_nat_add_cube N).mul_left
      ((5 / 3 : ℝ) * digammaRayConstant tau ^ 3)
  apply (hasSum_iff_tendsto_nat_of_summable_norm hnorm).mpr
  have hleft : Tendsto (fun n : ℕ =>
      gammaSeqLogDeriv z (n + 1) - Complex.log z + z⁻¹ / 2) atTop
      (nhds (Complex.digamma z - Complex.log z + z⁻¹ / 2)) :=
    ((tendsto_gammaSeqLogDeriv_of_mem_slitPlane z hz).sub_const _).add_const _
  have hend := tendsto_correctedDigamma_endpoint z hz
  have hsum : Tendsto (fun n : ℕ =>
      ∑ j ∈ Finset.range (n + 2), correctedDigammaTerm (z + j)) atTop
      (nhds (Complex.digamma z - Complex.log z + z⁻¹ / 2)) := by
    have hdiff := hleft.sub hend
    simpa only [sub_zero] using hdiff.congr' (Filter.Eventually.of_forall fun n => by
      have hid := gammaSeqLogDeriv_corrected_eq z hz (n + 1)
        (fun j hj => lt_of_le_of_lt
          (by simpa only [z] using norm_slitRay_inv_le_half tau htau N hN hlarge j)
          (by norm_num))
      rw [show z + (n + 2 : ℕ) = z + (n : ℂ) + 2 by push_cast; ring]
      rw [hid]
      push_cast
      ring_nf)
  apply (tendsto_add_atTop_iff_nat 2).mp
  simpa only [Function.comp_apply, z, Nat.add_comm] using hsum

/-- Along a sufficiently far part of any slit-plane ray, the corrected digamma satisfies
the explicit quadratic bound

```text
‖psi(N tau) - log(N tau) + (N tau)^-1/2‖
  ≤ 5 (1 + (1 + ‖tau‖) / max(Re(tau), |Im(tau)|))^3 / (2 N^2).
```

This is a quantitative complex-ray form of the decay used to define `γ₂₂` in
[95, Shintani (1977), equation (1.1) and proof of Lemma 1 on pp. 170–172], with the extension to
slit-plane period ratios described in [95, Shintani (1977), paragraph 1.6 on p. 181]. -/
theorem norm_digamma_mul_sub_log_add_half_inv_le (tau : ℂ) (htau : tau ∈ Complex.slitPlane)
    (N : ℕ) (hN : 0 < N)
    (hlarge : 2 * (1 + (1 + ‖tau‖) / max tau.re |tau.im|) ≤ (N : ℝ)) :
    ‖Complex.digamma ((N : ℂ) * tau) - Complex.log ((N : ℂ) * tau) +
        ((N : ℂ) * tau)⁻¹ / 2‖ ≤
      5 * (1 + (1 + ‖tau‖) / max tau.re |tau.im|) ^ 3 / (2 * (N : ℝ) ^ 2) := by
  have hsum := hasSum_correctedDigammaTerm_slitRay tau htau N hN
    (by simpa only [digammaRayConstant] using hlarge)
  apply le_of_tendsto hsum.tendsto_sum_nat.norm
  apply Filter.Eventually.of_forall
  intro M
  calc
    ‖∑ j ∈ Finset.range M, correctedDigammaTerm ((N : ℂ) * tau + j)‖ ≤
        ∑ j ∈ Finset.range M,
          ‖correctedDigammaTerm ((N : ℂ) * tau + j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range M,
          (5 / 3 : ℝ) * digammaRayConstant tau ^ 3 *
            ((((N + j : ℕ) : ℝ) ^ 3)⁻¹) := by
      gcongr with j hj
      exact norm_correctedDigammaTerm_slitRay_le tau htau N hN
        (by simpa only [digammaRayConstant] using hlarge) j
    _ = (5 / 3 : ℝ) * digammaRayConstant tau ^ 3 *
          ∑ j ∈ Finset.range M, ((((N + j : ℕ) : ℝ) ^ 3)⁻¹) := by
      simp only [Finset.mul_sum]
    _ ≤ (5 / 3 : ℝ) * digammaRayConstant tau ^ 3 *
          (3 / (2 * (N : ℝ) ^ 2)) := by
      gcongr
      · exact mul_nonneg (by norm_num) (pow_nonneg (digammaRayConstant_pos tau htau).le _)
      · exact sum_range_inv_nat_add_cube_le N M hN
    _ = 5 * (1 + (1 + ‖tau‖) / max tau.re |tau.im|) ^ 3 / (2 * (N : ℝ) ^ 2) := by
      unfold digammaRayConstant
      ring

/-- The corrected digamma on every slit-plane ray is `O(N⁻²)`.  This is the asymptotic form
of `norm_digamma_mul_sub_log_add_half_inv_le`. -/
theorem digamma_mul_sub_log_add_half_inv_isBigO (tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    (fun n : ℕ => Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) -
      Complex.log (((n + 1 : ℕ) : ℂ) * tau) +
      ((((n + 1 : ℕ) : ℂ) * tau)⁻¹) / 2) =O[atTop]
      (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
  apply IsBigO.of_bound (5 * digammaRayConstant tau ^ 3 / 2)
  have hlarge : ∀ᶠ n : ℕ in atTop,
      2 * digammaRayConstant tau ≤ (((n + 1 : ℕ) : ℝ)) :=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
      (eventually_ge_atTop (2 * digammaRayConstant tau))
  filter_upwards [hlarge] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  calc
    ‖Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) -
        Complex.log (((n + 1 : ℕ) : ℂ) * tau) +
        ((((n + 1 : ℕ) : ℂ) * tau)⁻¹) / 2‖ ≤
        5 * digammaRayConstant tau ^ 3 /
          (2 * (((n + 1 : ℕ) : ℝ) ^ 2)) := by
      simpa only [digammaRayConstant] using
        norm_digamma_mul_sub_log_add_half_inv_le tau htau (n + 1)
          (Nat.zero_lt_succ n) (by simpa only [digammaRayConstant] using hn)
    _ = 5 * digammaRayConstant tau ^ 3 / 2 *
          ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by ring

/-- The corrected-digamma series on every slit-plane ray is absolutely summable:

```text
sum_{n=1}^∞ (psi(n tau) - log(n tau) + (n tau)^-1/2).
```

This is the convergence required for Shintani's coefficient `γ₂₂` in
[95, Shintani (1977), equation (1.1) on p. 170]; it follows from
`digamma_mul_sub_log_add_half_inv_isBigO`. -/
theorem summable_digamma_mul_sub_log_add_half_inv (tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    Summable (fun n : ℕ =>
      Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) -
        Complex.log (((n + 1 : ℕ) : ℂ) * tau) +
        ((((n + 1 : ℕ) : ℂ) * tau)⁻¹) / 2) := by
  have hs : Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by decide))
  exact summable_of_isBigO_nat hs (digamma_mul_sub_log_add_half_inv_isBigO tau htau)

end SIC

end
