/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.RealPowerBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries

/-!
# Euler limits for the complex digamma function

Euler gamma approximants and locally uniform digamma and reciprocal-square limits.

The convergence argument for the Barnes double-gamma normalization coefficients in
[95, Shintani (1977), Section 1.1] uses the partial-fraction expansions of `psi` and `psi'`.
This file derives those expansions from Euler's finite gamma approximants
`Complex.GammaSeq`, then continues them away from the real axis as required by
[95, Shintani (1977), paragraph 1.6 on p. 181].

The truncated Euler kernels have an integrable majorant uniform on each vertical strip in the
right half-plane. Dominated convergence therefore upgrades Euler's pointwise gamma limit to a
uniform strip limit. Passing the finite logarithmic derivative to the limit locally uniformly,
and differentiating once more, gives the digamma and reciprocal-square trigamma expansions.
Exact translation formulas then continue both pointwise limits to every point off the real axis.
These limits supply the ordinary-gamma row evaluation and the quantitative ray estimates used by
the Barnes coefficients.

## Main declarations

- `gammaSeqLogDeriv`, `gammaSeqTrigamma`: the finite logarithmic derivative and its derivative.
- `hasDerivAt_gammaSeq`: the exact derivative of Euler's gamma approximant.
- `gammaSeq_tendstoUniformlyOn_strip`: uniform convergence on vertical strips.
- `gammaSeqLogDeriv_tendstoLocallyUniformlyOn_strip`: locally uniform convergence to `digamma`.
- `gammaSeqTrigamma_tendstoLocallyUniformlyOn_strip`: the differentiated locally uniform limit.
- `tendsto_gammaSeqLogDeriv`, `tendsto_gammaSeqTrigamma`: the pointwise limits.
- `tendsto_gammaSeqLogDeriv_of_im_ne_zero`, `tendsto_gammaSeqTrigamma_of_im_ne_zero`: continuation
  of those pointwise limits off the real axis.

## References

- [95] T. Shintani, "On a Kronecker limit formula for real quadratic fields," J. Fac. Sci.
  Univ. Tokyo Sect. IA Math. 24 (1977), proof of Lemma 1 on p. 170, immediately before
  equation (1.3), and the analytic continuation in paragraph 1.6 on p. 181
-/

noncomputable section

open Complex Real MeasureTheory Set Filter Asymptotics

namespace SIC

/-! ### Euler's integral kernels

The dominated-convergence argument for Euler's gamma limit is made uniform on vertical strips.
This prepares the partial-fraction expansions used in [95, Shintani (1977), Section 1.1].
-/

/-- The compactly supported kernel in Euler's integral approximation to `Gamma`:

```text
E_n(x) = max (1 - x/n) 0 ^ n.
```

For `n > 0` this is `(1-x/n)^n` on `[0,n]` and zero to its right. -/
private noncomputable def gammaSeqKernel (n : ℕ) (x : ℝ) : ℝ :=
  max (1 - x / n) 0 ^ n

/-- On Euler's integration interval, the truncated kernel is the usual polynomial kernel. -/
private lemma gammaSeqKernel_eq_of_mem_Icc {n : ℕ} {x : ℝ}
    (hx : x ∈ Icc 0 (n : ℝ)) :
    gammaSeqKernel n x = (1 - x / n) ^ n := by
  unfold gammaSeqKernel
  rw [max_eq_left]
  exact sub_nonneg.mpr (div_le_one_of_le₀ hx.2 (Nat.cast_nonneg n))

/-- To the right of its integration interval, Euler's kernel vanishes. -/
private lemma gammaSeqKernel_eq_zero_of_natCast_le {n : ℕ} (hn : n ≠ 0) {x : ℝ}
    (hx : (n : ℝ) ≤ x) :
    gammaSeqKernel n x = 0 := by
  unfold gammaSeqKernel
  rw [max_eq_right, zero_pow]
  · exact hn
  · exact sub_nonpos.mpr
      ((one_le_div₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr hx)

/-- Euler's kernel is bounded by the limiting exponential on the positive half-line. -/
private lemma gammaSeqKernel_le_exp_neg {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    gammaSeqKernel n x ≤ Real.exp (-x) := by
  by_cases hxn : x ≤ n
  · rw [gammaSeqKernel_eq_of_mem_Icc ⟨hx, hxn⟩]
    exact one_sub_div_pow_le_exp_neg hxn
  · rw [gammaSeqKernel_eq_zero_of_natCast_le hn (le_of_lt (lt_of_not_ge hxn))]
    exact Real.exp_pos (-x) |>.le

/-- Euler's kernel is nonnegative. -/
private lemma gammaSeqKernel_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ gammaSeqKernel n x := by
  unfold gammaSeqKernel
  exact pow_nonneg (le_max_right (1 - x / n) (0 : ℝ)) n

/-- Euler's truncated kernels converge pointwise to `exp(-x)` on the positive half-line. -/
private lemma tendsto_gammaSeqKernel (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => gammaSeqKernel (n + 1) x) atTop (nhds (Real.exp (-x))) := by
  apply Tendsto.congr'
  · filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
    have hxn : x ≤ (n + 1 : ℕ) := by
      rw [Nat.ceil_le] at hn
      exact hn.trans (by exact_mod_cast Nat.le_add_right n 1)
    rw [gammaSeqKernel_eq_of_mem_Icc ⟨hx, hxn⟩]
  · convert (Real.tendsto_one_add_div_pow_exp (-x)).comp (tendsto_add_atTop_nat 1) using 1
    ext n
    simp only [Function.comp_apply, neg_div, sub_eq_add_neg]

/-- The two endpoint powers used to dominate Euler's kernels uniformly on a vertical strip. -/
private noncomputable def gammaSeqStripWeight (a b x : ℝ) : ℝ :=
  x ^ (a - 1) + x ^ (b - 1)

/-- If `a ≤ re(z) ≤ b`, the norm of `x^(z-1)` is bounded by the sum of the two endpoint
powers. -/
private lemma norm_cpow_le_gammaSeqStripWeight {a b x : ℝ} {z : ℂ}
    (hx : 0 < x) (ha : a ≤ z.re) (hb : z.re ≤ b) :
    ‖(x : ℂ) ^ (z - 1)‖ ≤ gammaSeqStripWeight a b x := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.sub_re, Complex.one_re]
  unfold gammaSeqStripWeight
  exact rpow_le_add_of_le hx (by linarith) (by linarith)

/-- The scalar error majorant for Euler's gamma kernels on a vertical strip. -/
private noncomputable def gammaSeqStripError (a b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  |gammaSeqKernel (n + 1) x - Real.exp (-x)| * gammaSeqStripWeight a b x

/-- An integrable majorant for every weighted Euler-kernel error on a fixed vertical strip. -/
private noncomputable def gammaSeqStripBound (a b : ℝ) (x : ℝ) : ℝ :=
  2 * Real.exp (-x) * gammaSeqStripWeight a b x

/-- The strip majorant is integrable when both endpoint exponents are positive. -/
private lemma integrableOn_gammaSeqStripBound (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (gammaSeqStripBound a b) (Ioi (0 : ℝ)) := by
  have haInt := Real.GammaIntegral_convergent ha
  have hbInt := Real.GammaIntegral_convergent hb
  unfold gammaSeqStripBound gammaSeqStripWeight
  simp only [mul_add]
  change Integrable _ (volume.restrict (Ioi (0 : ℝ)))
  apply ((haInt.const_mul 2).add (hbInt.const_mul 2)).congr
  filter_upwards with x
  simp only [Pi.add_apply]
  ring

/-- The weighted Euler-kernel error is measurable on the positive half-line. -/
private lemma gammaSeqStripError_aestronglyMeasurable (a b : ℝ) (n : ℕ) :
    AEStronglyMeasurable (gammaSeqStripError a b n)
      (volume.restrict (Ioi (0 : ℝ))) := by
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
  apply ContinuousOn.mul
  · apply Continuous.continuousOn
    unfold gammaSeqKernel
    fun_prop
  · apply ContinuousOn.add
    · exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)
    · exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)

/-- Every weighted Euler-kernel error is bounded by the strip majorant almost everywhere. -/
private lemma gammaSeqStripError_norm_le_bound (a b : ℝ) (n : ℕ) :
    ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      ‖gammaSeqStripError a b n x‖ ≤ gammaSeqStripBound a b x := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hk0 := gammaSeqKernel_nonneg (n + 1) x
  have hke := gammaSeqKernel_le_exp_neg (Nat.add_one_ne_zero n) hx.le
  have hw0 : 0 ≤ gammaSeqStripWeight a b x := by
    unfold gammaSeqStripWeight
    exact add_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hx.le _)
  unfold gammaSeqStripError gammaSeqStripBound
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hw0)]
  rw [abs_of_nonpos (sub_nonpos.mpr hke)]
  nlinarith [Real.exp_pos (-x)]

/-- The weighted scalar error of Euler's kernels tends to zero in `L¹(0,∞)`. -/
private lemma tendsto_integral_gammaSeqStripError (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n : ℕ => ∫ x in Ioi (0 : ℝ), gammaSeqStripError a b n x)
      atTop (nhds 0) := by
  have hlim : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun n : ℕ => gammaSeqStripError a b n x) atTop (nhds 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    unfold gammaSeqStripError
    convert (((tendsto_gammaSeqKernel x hx.le).sub tendsto_const_nhds).abs.mul_const
      (gammaSeqStripWeight a b x)) using 1
    simp
  have h := tendsto_integral_of_dominated_convergence (gammaSeqStripBound a b)
    (gammaSeqStripError_aestronglyMeasurable a b)
    (integrableOn_gammaSeqStripBound a b ha hb)
    (gammaSeqStripError_norm_le_bound a b) hlim
  simpa using h

/-- Euler's finite gamma approximant is the Mellin integral of `gammaSeqKernel`. -/
private lemma gammaSeq_eq_integral_kernel (z : ℂ) (hz : 0 < z.re) (n : ℕ) (hn : n ≠ 0) :
    Complex.GammaSeq z n =
      ∫ x in Ioi (0 : ℝ), (gammaSeqKernel n x : ℂ) * (x : ℂ) ^ (z - 1) := by
  rw [Complex.GammaSeq_eq_approx_Gamma_integral hz hn,
    intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
  calc
    (∫ x in Ioc (0 : ℝ) n,
        (((1 - x / n) ^ n : ℝ) : ℂ) * (x : ℂ) ^ (z - 1)) =
        ∫ x in Ioc (0 : ℝ) n,
          (gammaSeqKernel n x : ℂ) * (x : ℂ) ^ (z - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      change ((((1 - x / n) ^ n : ℝ) : ℂ) * (x : ℂ) ^ (z - 1)) =
        (gammaSeqKernel n x : ℂ) * (x : ℂ) ^ (z - 1)
      rw [gammaSeqKernel_eq_of_mem_Icc ⟨hx.1.le, hx.2⟩]
    _ = ∫ x in Ioi (0 : ℝ),
          (gammaSeqKernel n x : ℂ) * (x : ℂ) ^ (z - 1) := by
      symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        Ioc_subset_Ioi_self
      intro x hx
      have hnx : ¬x ≤ (n : ℝ) := fun h => hx.2 ⟨hx.1, h⟩
      rw [gammaSeqKernel_eq_zero_of_natCast_le hn (le_of_not_ge hnx)]
      simp

/-- Euler's gamma approximants converge uniformly on every closed vertical strip contained in
the right half-plane.  This upgrades Mathlib's pointwise Euler limit to the locally uniform input
needed for differentiating the limit. -/
lemma gammaSeq_tendstoUniformlyOn_strip (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    TendstoUniformlyOn (fun n z => Complex.GammaSeq z (n + 1)) Complex.Gamma atTop
      {z : ℂ | a ≤ z.re ∧ z.re ≤ b} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have herror : ∀ᶠ n : ℕ in atTop,
      ∫ x in Ioi (0 : ℝ), gammaSeqStripError a b n x < ε :=
    (tendsto_order.1 (tendsto_integral_gammaSeqStripError a b ha hb)).2 ε hε
  filter_upwards [herror] with n hn
  intro z hz
  have hzpos : 0 < z.re := ha.trans_le hz.1
  let f : ℝ → ℂ := fun x =>
    (gammaSeqKernel (n + 1) x : ℂ) * (x : ℂ) ^ (z - 1)
  let g : ℝ → ℂ := fun x =>
    (Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)
  have hg : IntegrableOn g (Ioi (0 : ℝ)) := by
    simpa [g] using Complex.GammaIntegral_convergent hzpos
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.mul
    · apply Continuous.continuousOn
      unfold gammaSeqKernel
      fun_prop
    · apply continuousOn_of_forall_continuousAt
      intro x hx
      have hpow : ContinuousAt (fun w : ℂ => w ^ (z - 1)) (x : ℂ) :=
        continuousAt_cpow_const <| ofReal_mem_slitPlane.2 hx
      exact hpow.comp continuous_ofReal.continuousAt
  have hf : IntegrableOn f (Ioi (0 : ℝ)) := by
    change Integrable g (volume.restrict (Ioi (0 : ℝ))) at hg
    change Integrable f (volume.restrict (Ioi (0 : ℝ)))
    apply hg.norm.mono' hfmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hk0 := gammaSeqKernel_nonneg (n + 1) x
    have hke := gammaSeqKernel_le_exp_neg (Nat.add_one_ne_zero n) hx.le
    dsimp [f, g]
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hk0,
      abs_of_pos (Real.exp_pos (-x))]
    exact mul_le_mul_of_nonneg_right hke (norm_nonneg _)
  have herr : IntegrableOn (gammaSeqStripError a b n) (Ioi (0 : ℝ)) :=
    (integrableOn_gammaSeqStripBound a b ha hb).mono'
      (gammaSeqStripError_aestronglyMeasurable a b n)
      (gammaSeqStripError_norm_le_bound a b n)
  rw [dist_eq_norm, Complex.Gamma_eq_integral hzpos,
    gammaSeq_eq_integral_kernel z hzpos (n + 1) (Nat.add_one_ne_zero n)]
  unfold Complex.GammaIntegral
  change ‖(∫ x in Ioi (0 : ℝ), g x) - ∫ x in Ioi (0 : ℝ), f x‖ < ε
  rw [← integral_sub hg hf]
  refine (norm_integral_le_of_norm_le herr ?_).trans_lt hn
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  unfold f g
  rw [← sub_mul, norm_mul, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_sub_comm]
  exact mul_le_mul_of_nonneg_left
    (norm_cpow_le_gammaSeqStripWeight hx hz.1 hz.2) (abs_nonneg _)

/-! ### Euler's finite logarithmic derivative

The logarithmic derivative of the finite Euler product and its reciprocal-square derivative
provide the finite forms of the expansions used in [95, Shintani (1977), proof of Lemma 1
on p. 170].
-/

/-- Adding a natural number cannot move a point of the right half-plane to zero. -/
private lemma add_nat_ne_zero_of_re_pos (z : ℂ) (hz : 0 < z.re) (j : ℕ) :
    z + j ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hre
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

/-- Every nondegenerate Euler gamma approximant is nonzero on the right half-plane. -/
private lemma gammaSeq_ne_zero_of_re_pos (z : ℂ) (n : ℕ) (hn : n ≠ 0)
    (hz : 0 < z.re) :
    Complex.GammaSeq z n ≠ 0 := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  unfold Complex.GammaSeq
  exact div_ne_zero
    (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))
      (by exact_mod_cast Nat.factorial_ne_zero n))
    (Finset.prod_ne_zero_iff.mpr fun j _ => add_nat_ne_zero_of_re_pos z hz j)

/-- The logarithmic derivative of Euler's `n`-th gamma approximant:

```text
log(n) - sum_{j=0}^n (z+j)^-1.
```

This is the finite expression whose limit is `psi(z)`. -/
noncomputable def gammaSeqLogDeriv (z : ℂ) (n : ℕ) : ℂ :=
  Complex.log n - ∑ j ∈ Finset.range (n + 1), (z + j)⁻¹

/-- The finite reciprocal-square approximant obtained by differentiating
`gammaSeqLogDeriv`:

```text
sum_{j=0}^n (z+j)^-2.
``` -/
def gammaSeqTrigamma (z : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), (z + j)⁻¹ ^ 2

/-- Translating the argument of the finite logarithmic derivative by one removes its first
reciprocal term and introduces one endpoint term. -/
lemma gammaSeqLogDeriv_add_one (z : ℂ) (n : ℕ) :
    gammaSeqLogDeriv (z + 1) n =
      gammaSeqLogDeriv z n + z⁻¹ - (z + (n + 1 : ℕ))⁻¹ := by
  have hsum :
      (∑ j ∈ Finset.range (n + 1), ((z + 1) + j)⁻¹) =
        (∑ j ∈ Finset.range (n + 1), (z + j)⁻¹) - z⁻¹ +
          (z + (n + 1 : ℕ))⁻¹ := by
    calc
      (∑ j ∈ Finset.range (n + 1), ((z + 1) + j)⁻¹) =
          (∑ j ∈ Finset.range n, ((z + 1) + j)⁻¹) +
            ((z + 1) + n)⁻¹ := Finset.sum_range_succ _ n
      _ = (∑ j ∈ Finset.range n, (z + (j + 1 : ℕ))⁻¹) +
            (z + (n + 1 : ℕ))⁻¹ := by
          congr 1
          · apply Finset.sum_congr rfl
            intro j hj
            apply congrArg Inv.inv
            push_cast
            ring
          · apply congrArg Inv.inv
            push_cast
            ring
      _ = (z⁻¹ + ∑ j ∈ Finset.range n, (z + (j + 1 : ℕ))⁻¹) - z⁻¹ +
            (z + (n + 1 : ℕ))⁻¹ := by ring
      _ = (∑ j ∈ Finset.range (n + 1), (z + j)⁻¹) - z⁻¹ +
            (z + (n + 1 : ℕ))⁻¹ := by
          rw [Finset.sum_range_succ']
          simp
  unfold gammaSeqLogDeriv
  rw [hsum]
  ring

/-- Translating the finite reciprocal-square sum by one removes its first term and introduces
one endpoint term. -/
lemma gammaSeqTrigamma_add_one (z : ℂ) (n : ℕ) :
    gammaSeqTrigamma (z + 1) n =
      gammaSeqTrigamma z n - z⁻¹ ^ 2 + (z + (n + 1 : ℕ))⁻¹ ^ 2 := by
  have hsum :
      (∑ j ∈ Finset.range (n + 1), (((z + 1) + j)⁻¹ ^ 2)) =
        (∑ j ∈ Finset.range (n + 1), ((z + j)⁻¹ ^ 2)) - z⁻¹ ^ 2 +
          (z + (n + 1 : ℕ))⁻¹ ^ 2 := by
    calc
      (∑ j ∈ Finset.range (n + 1), (((z + 1) + j)⁻¹ ^ 2)) =
          (∑ j ∈ Finset.range n, (((z + 1) + j)⁻¹ ^ 2)) +
            ((z + 1) + n)⁻¹ ^ 2 := Finset.sum_range_succ _ n
      _ = (∑ j ∈ Finset.range n, ((z + (j + 1 : ℕ))⁻¹ ^ 2)) +
            (z + (n + 1 : ℕ))⁻¹ ^ 2 := by
          congr 1
          · apply Finset.sum_congr rfl
            intro j hj
            apply congrArg (fun w : ℂ => w⁻¹ ^ 2)
            push_cast
            ring
          · apply congrArg (fun w : ℂ => w⁻¹ ^ 2)
            push_cast
            ring
      _ = (z⁻¹ ^ 2 + ∑ j ∈ Finset.range n, ((z + (j + 1 : ℕ))⁻¹ ^ 2)) -
            z⁻¹ ^ 2 + (z + (n + 1 : ℕ))⁻¹ ^ 2 := by ring
      _ = (∑ j ∈ Finset.range (n + 1), ((z + j)⁻¹ ^ 2)) - z⁻¹ ^ 2 +
            (z + (n + 1 : ℕ))⁻¹ ^ 2 := by
          rw [Finset.sum_range_succ']
          simp
  unfold gammaSeqTrigamma
  exact hsum

/-- Euler's gamma approximant has logarithmic derivative `gammaSeqLogDeriv`.  The assumptions
exclude the degenerate zeroth approximant and its denominator zeros. -/
lemma hasDerivAt_gammaSeq (z : ℂ) (n : ℕ) (hn : n ≠ 0)
    (hz : ∀ j ∈ Finset.range (n + 1), z + j ≠ 0) :
    HasDerivAt (fun w => Complex.GammaSeq w n)
      (Complex.GammaSeq z n * gammaSeqLogDeriv z n) z := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hpow : (n : ℂ) ^ z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hden : ∏ j ∈ Finset.range (n + 1), (z + j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hz
  have hdiffPow : DifferentiableAt ℂ (fun w : ℂ => (n : ℂ) ^ w) z :=
    differentiableAt_id.const_cpow (Or.inl hnC)
  have hdiffDen : DifferentiableAt ℂ
      (fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + j)) z := by
    fun_prop
  have hdiff : DifferentiableAt ℂ (fun w => Complex.GammaSeq w n) z := by
    unfold Complex.GammaSeq
    exact (hdiffPow.mul_const (n.factorial : ℂ)).div hdiffDen hden
  have hnonzero : Complex.GammaSeq z n ≠ 0 := by
    unfold Complex.GammaSeq
    exact div_ne_zero (mul_ne_zero hpow hfac) hden
  have hlogPow : logDeriv (fun w : ℂ => (n : ℂ) ^ w) z = Complex.log n := by
    rw [logDeriv_apply, (hasStrictDerivAt_const_cpow (x := (n : ℂ))
      (y := z) (Or.inl hnC)).hasDerivAt.deriv]
    exact mul_div_cancel_left₀ _ hpow
  have hlogDen : logDeriv
      (fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + j)) z =
        ∑ j ∈ Finset.range (n + 1), (z + j)⁻¹ := by
    have hprod := logDeriv_prod (s := Finset.range (n + 1))
      (f := fun (j : ℕ) (w : ℂ) => w + j) (x := z) hz (by
        intro j hj
        fun_prop)
    have hfun : (fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + j)) =
        ∏ j ∈ Finset.range (n + 1), fun w : ℂ => w + j := by
      funext w
      simp
    rw [hfun, hprod]
    apply Finset.sum_congr rfl
    intro j hj
    rw [logDeriv_apply]
    simp only [deriv_add_const, deriv_id'', one_div]
  have hlog : logDeriv (fun w => Complex.GammaSeq w n) z =
      gammaSeqLogDeriv z n := by
    unfold Complex.GammaSeq gammaSeqLogDeriv
    change logDeriv
      ((fun w : ℂ => (n : ℂ) ^ w * (n.factorial : ℂ)) /
        (fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + j))) z = _
    rw [logDeriv_div (f := fun w : ℂ => (n : ℂ) ^ w * (n.factorial : ℂ))
      (g := fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + j)) z
      (mul_ne_zero hpow hfac) hden
      (hdiffPow.mul_const (n.factorial : ℂ)) hdiffDen,
      logDeriv_mul_const (f := fun w : ℂ => (n : ℂ) ^ w) z
        (n.factorial : ℂ) hfac,
      hlogPow, hlogDen]
  refine hdiff.hasDerivAt.congr_deriv ?_
  rw [← hlog, logDeriv_apply]
  field_simp

/-- The logarithmic derivative of Euler's gamma approximant is exactly
`gammaSeqLogDeriv` on the right half-plane. -/
lemma logDeriv_gammaSeq (z : ℂ) (n : ℕ) (hn : n ≠ 0) (hz : 0 < z.re) :
    logDeriv (fun w => Complex.GammaSeq w n) z = gammaSeqLogDeriv z n := by
  rw [logDeriv_apply,
    (hasDerivAt_gammaSeq z n hn fun j _ => add_nat_ne_zero_of_re_pos z hz j).deriv]
  exact mul_div_cancel_left₀ _ (gammaSeq_ne_zero_of_re_pos z n hn hz)

/-- Differentiating the finite logarithmic derivative gives the corresponding finite sum of
reciprocal squares. -/
lemma hasDerivAt_gammaSeqLogDeriv (z : ℂ) (n : ℕ)
    (hz : ∀ j ∈ Finset.range (n + 1), z + j ≠ 0) :
    HasDerivAt (fun w => gammaSeqLogDeriv w n)
      (gammaSeqTrigamma z n) z := by
  unfold gammaSeqLogDeriv gammaSeqTrigamma
  have hsum : HasDerivAt (fun w : ℂ =>
      ∑ j ∈ Finset.range (n + 1), (w + j)⁻¹)
      (∑ j ∈ Finset.range (n + 1), -((z + j)⁻¹ ^ 2)) z := by
    apply HasDerivAt.fun_sum
    intro j hj
    have hadd : HasDerivAt (fun w : ℂ => w + (j : ℂ)) 1 z :=
      (hasDerivAt_id z).add_const (j : ℂ)
    simpa only [Function.comp_def, inv_pow, mul_one] using
      (hasDerivAt_inv (hz j hj)).comp z hadd
  refine ((hasDerivAt_const z (Complex.log n)).sub hsum).congr_deriv ?_
  simp only [zero_sub, Finset.sum_neg_distrib, neg_neg]

/-! ### Euler's limit formula for `digamma`

Locally uniform convergence permits two differentiations of Euler's gamma limit on the right
half-plane, yielding the digamma expansions used in [95, Shintani (1977), Section 1.1].
-/

/-- Euler's finite logarithmic derivatives converge locally uniformly to `digamma` on every
open vertical strip in the right half-plane.  This is the differentiated, locally uniform form
of Euler's gamma limit. -/
theorem gammaSeqLogDeriv_tendstoLocallyUniformlyOn_strip
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    TendstoLocallyUniformlyOn (fun n z => gammaSeqLogDeriv z (n + 1))
      Complex.digamma atTop {z : ℂ | a < z.re ∧ z.re < b} := by
  let s : Set ℂ := {z | a < z.re ∧ z.re < b}
  have hs : IsOpen s := by
    change IsOpen ({z : ℂ | a < z.re} ∩ {z : ℂ | z.re < b})
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hGammaUniform :
      TendstoUniformlyOn (fun n z => Complex.GammaSeq z (n + 1)) Complex.Gamma atTop s :=
    (gammaSeq_tendstoUniformlyOn_strip a b ha hb).mono fun _ hz => ⟨hz.1.le, hz.2.le⟩
  have hGammaLocal := hGammaUniform.tendstoLocallyUniformlyOn
  have hGammaSeqDiff : ∀ n : ℕ,
      DifferentiableOn ℂ (fun z => Complex.GammaSeq z (n + 1)) s := by
    intro n z hz
    have hzpos : 0 < z.re := ha.trans hz.1
    exact (hasDerivAt_gammaSeq z (n + 1) (Nat.add_one_ne_zero n)
      fun j _ => add_nat_ne_zero_of_re_pos z hzpos j).differentiableAt.differentiableWithinAt
  have hGammaDerivLocal := hGammaLocal.deriv
    (Filter.Eventually.of_forall hGammaSeqDiff) hs
  have hGammaCont : ContinuousOn Complex.Gamma s :=
    hGammaLocal.continuousOn <| Filter.Frequently.of_forall fun n =>
      (hGammaSeqDiff n).continuousOn
  have hGammaSeqDerivCont : ∀ n : ℕ,
      ContinuousOn (deriv (fun z => Complex.GammaSeq z (n + 1))) s := by
    intro n
    have hprodDiff : DifferentiableOn ℂ (fun z =>
        Complex.GammaSeq z (n + 1) * gammaSeqLogDeriv z (n + 1)) s := by
      intro z hz
      have hzpos : 0 < z.re := ha.trans hz.1
      exact ((hasDerivAt_gammaSeq z (n + 1) (Nat.add_one_ne_zero n)
        fun j _ => add_nat_ne_zero_of_re_pos z hzpos j).mul
          (hasDerivAt_gammaSeqLogDeriv z (n + 1)
            fun j _ => add_nat_ne_zero_of_re_pos z hzpos j)).differentiableAt.differentiableWithinAt
    refine hprodDiff.continuousOn.congr fun z hz => ?_
    have hzpos : 0 < z.re := ha.trans hz.1
    exact (hasDerivAt_gammaSeq z (n + 1) (Nat.add_one_ne_zero n)
      fun j _ => add_nat_ne_zero_of_re_pos z hzpos j).deriv
  have hGammaDerivCont : ContinuousOn (deriv Complex.Gamma) s :=
    hGammaDerivLocal.continuousOn <| Filter.Frequently.of_forall fun n => by
      simpa only [Function.comp_apply] using hGammaSeqDerivCont n
  have hquot := hGammaDerivLocal.div₀ hGammaLocal hGammaDerivCont hGammaCont
    (fun z hz => Complex.Gamma_ne_zero_of_re_pos (ha.trans hz.1))
  have hfinite : TendstoLocallyUniformlyOn
      (fun n z => gammaSeqLogDeriv z (n + 1))
      (deriv Complex.Gamma / Complex.Gamma) atTop s := by
    apply hquot.congr
    intro n z hz
    change deriv (fun w => Complex.GammaSeq w (n + 1)) z /
        Complex.GammaSeq z (n + 1) = gammaSeqLogDeriv z (n + 1)
    rw [← logDeriv_apply,
      logDeriv_gammaSeq z (n + 1) (Nat.add_one_ne_zero n) (ha.trans hz.1)]
  exact hfinite.congr_right fun z _ => by
    rw [Pi.div_apply, Complex.digamma_def, logDeriv_apply]

/-- The finite reciprocal-square approximants converge locally uniformly to
`deriv Complex.digamma` on every open vertical strip in the right half-plane.  This is the
complex trigamma partial-fraction limit used in Shintani's equation (1.2). -/
theorem gammaSeqTrigamma_tendstoLocallyUniformlyOn_strip
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    TendstoLocallyUniformlyOn (fun n z => gammaSeqTrigamma z (n + 1))
      (deriv Complex.digamma) atTop {z : ℂ | a < z.re ∧ z.re < b} := by
  let s : Set ℂ := {z | a < z.re ∧ z.re < b}
  have hs : IsOpen s := by
    change IsOpen ({z : ℂ | a < z.re} ∩ {z : ℂ | z.re < b})
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hdiff : ∀ᶠ n : ℕ in atTop,
      DifferentiableOn ℂ (fun z => gammaSeqLogDeriv z (n + 1)) s := by
    apply Filter.Eventually.of_forall
    intro n z hz
    have h := hasDerivAt_gammaSeqLogDeriv z (n + 1)
      fun j _ => add_nat_ne_zero_of_re_pos z (ha.trans hz.1) j
    exact h.differentiableAt.differentiableWithinAt
  have hderiv :=
    (gammaSeqLogDeriv_tendstoLocallyUniformlyOn_strip a b ha hb).deriv hdiff hs
  apply hderiv.congr
  intro n z hz
  simp only [Function.comp_apply]
  exact (hasDerivAt_gammaSeqLogDeriv z (n + 1)
    fun j _ => add_nat_ne_zero_of_re_pos z (ha.trans hz.1) j).deriv

/-- Euler's finite logarithmic derivatives converge to the complex digamma function on the
right half-plane:

```text
psi(z) = lim_{n → ∞} (log(n+1) - sum_{j=0}^{n+1} (z+j)^-1).
```

The locally uniform argument supplies the analytic justification for the partial-fraction
expansion in [95, Shintani (1977), proof of Lemma 1 on p. 170, immediately before equation
(1.3)]. -/
theorem tendsto_gammaSeqLogDeriv (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => gammaSeqLogDeriv z (n + 1)) atTop
      (nhds (Complex.digamma z)) := by
  let a : ℝ := z.re / 2
  let b : ℝ := z.re + 1
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hb : 0 < b := by
    dsimp [b]
    linarith
  have hzs : z ∈ {w : ℂ | a < w.re ∧ w.re < b} := by
    change a < z.re ∧ z.re < b
    dsimp [a, b]
    constructor <;> linarith
  exact (gammaSeqLogDeriv_tendstoLocallyUniformlyOn_strip a b ha hb).tendsto_at hzs

/-- The finite reciprocal-square sums converge to the derivative of `digamma` throughout the
right half-plane:

```text
psi'(z) = lim_{n → ∞} sum_{j=0}^{n+1} (z+j)^-2.
```

This is the trigamma expansion in [95, Shintani (1977), proof of Lemma 1 on p. 170, immediately
before equation (1.3)]. -/
theorem tendsto_gammaSeqTrigamma (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => gammaSeqTrigamma z (n + 1)) atTop
      (nhds (deriv Complex.digamma z)) := by
  let a : ℝ := z.re / 2
  let b : ℝ := z.re + 1
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hb : 0 < b := by
    dsimp [b]
    linarith
  have hzs : z ∈ {w : ℂ | a < w.re ∧ w.re < b} := by
    change a < z.re ∧ z.re < b
    dsimp [a, b]
    constructor <;> linarith
  exact (gammaSeqTrigamma_tendstoLocallyUniformlyOn_strip a b ha hb).tendsto_at hzs

/-- The reciprocal-square expansion `psi'(z) = ∑_{n≥0} (z+n)⁻²` is absolutely
convergent when `Re(z)>0`. This is the series form of `tendsto_gammaSeqTrigamma`,
used to integrate the trigamma tail term by term. -/
theorem hasSum_trigamma_series (z : ℂ) (hz : 0 < z.re) :
    HasSum (fun n : ℕ => (z + n)⁻¹ ^ 2) (deriv Complex.digamma z) := by
  have hbound := (Real.summable_one_div_nat_add_rpow z.re 2).mpr (by norm_num)
  have hsum : Summable (fun n : ℕ => (z + n)⁻¹ ^ 2) := by
    apply hbound.of_norm_bounded
    intro n
    have hn : 0 < (n : ℝ) + z.re := by positivity
    rw [norm_pow, norm_inv, Real.rpow_two, abs_of_pos hn, one_div, ← inv_pow]
    gcongr
    simpa [add_comm] using Complex.re_le_norm (z + n)
  rw [hsum.hasSum_iff_tendsto_nat]
  apply (tendsto_add_atTop_iff_nat 2).mp
  simpa only [gammaSeqTrigamma, Nat.add_assoc] using tendsto_gammaSeqTrigamma z hz

/-- For `Re(z)>0`, the trigamma recurrence is `psi'(z+1)=psi'(z)-z⁻²`.
This is the first-term decomposition of `hasSum_trigamma_series`. -/
theorem deriv_digamma_add_one_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    deriv Complex.digamma (z + 1) = deriv Complex.digamma z - z⁻¹ ^ 2 := by
  have ht := (hasSum_nat_add_iff' 1).mpr (hasSum_trigamma_series z hz)
  have hs := hasSum_trigamma_series (z + 1) (by simp; linarith)
  apply hs.unique
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using ht

/-! ### Continuation away from the real axis

The exact unit-translation formulas move the pointwise limits to nonreal arguments, covering
the complex period ratios considered in [95, Shintani (1977), paragraph 1.6 on p. 181].
-/

/-- Reciprocals of a fixed complex translate of the natural numbers tend to zero.  This supplies
the endpoint limit in both translation recurrences below. -/
private lemma tendsto_inv_add_nat (z : ℂ) :
    Tendsto (fun n : ℕ => (z + (n : ℂ))⁻¹) atTop (nhds 0) := by
  apply tendsto_inv₀_cobounded.comp
  exact (tendsto_const_add_cobounded z).comp tendsto_natCast_atTop_cobounded

/-- If the finite logarithmic derivatives converge at `z + 1`, their exact translation formula
and the digamma recurrence give convergence at `z`. -/
private lemma tendsto_gammaSeqLogDeriv_of_add_one (z : ℂ)
    (hz : ∀ m : ℕ, z ≠ -m)
    (h : Tendsto (fun n : ℕ => gammaSeqLogDeriv (z + 1) (n + 1)) atTop
      (nhds (Complex.digamma (z + 1)))) :
    Tendsto (fun n : ℕ => gammaSeqLogDeriv z (n + 1)) atTop
      (nhds (Complex.digamma z)) := by
  have hend : Tendsto (fun n : ℕ => (z + ((n + 2 : ℕ) : ℂ))⁻¹) atTop (nhds 0) := by
    simpa [Function.comp_def, Nat.cast_add] using
      (tendsto_inv_add_nat z).comp (tendsto_add_atTop_nat 2)
  have hrec := h.sub_const z⁻¹ |>.add hend
  convert hrec using 1
  · ext n
    rw [gammaSeqLogDeriv_add_one z (n + 1)]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  · rw [Complex.digamma_apply_add_one z hz]
    ring_nf

/-- Euler's finite logarithmic derivatives converge to `digamma` at every point off the real
axis.  Translation by a sufficiently large natural number reaches the right half-plane, while
the exact finite recurrence has a vanishing endpoint term.  This supplies the continuation to
the upper-half-plane rays required in [95, Shintani (1977), paragraph 1.6 on p. 181]. -/
theorem tendsto_gammaSeqLogDeriv_of_im_ne_zero (z : ℂ) (hz : z.im ≠ 0) :
    Tendsto (fun n : ℕ => gammaSeqLogDeriv z (n + 1)) atTop
      (nhds (Complex.digamma z)) := by
  obtain ⟨k : ℕ, hk⟩ := exists_nat_gt (-z.re)
  have hbase : Tendsto
      (fun n : ℕ => gammaSeqLogDeriv (z + k) (n + 1)) atTop
      (nhds (Complex.digamma (z + k))) := by
    apply tendsto_gammaSeqLogDeriv
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  have hshift : ∀ k : ℕ,
      Tendsto (fun n : ℕ => gammaSeqLogDeriv (z + k) (n + 1)) atTop
          (nhds (Complex.digamma (z + k))) →
        Tendsto (fun n : ℕ => gammaSeqLogDeriv z (n + 1)) atTop
          (nhds (Complex.digamma z)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        intro hj
        apply ih
        apply tendsto_gammaSeqLogDeriv_of_add_one (z + j)
        · intro m hm
          have him := congrArg Complex.im hm
          simp only [Complex.add_im, Complex.natCast_im, add_zero, neg_im, Complex.natCast_im,
            neg_zero] at him
          exact hz him
        · convert hj using 1 <;> push_cast <;> ring_nf
  exact hshift k hbase

/-- Mathlib's `Complex.digamma_apply_add_nat` specialized to nonreal arguments, for
`continuousAt_digamma_of_im_ne_zero`. -/
private lemma digamma_add_nat_of_im_ne_zero (z : ℂ) (hz : z.im ≠ 0) (k : ℕ) :
    Complex.digamma (z + k) = Complex.digamma z +
      ∑ j ∈ Finset.range k, (z + j)⁻¹ := by
  apply Complex.digamma_apply_add_nat
  intro m hm
  exact hz (by simpa using congrArg Complex.im hm)

/-- On the right half-plane, locally uniform convergence of the finite logarithmic derivatives
makes `digamma` continuous. -/
private lemma continuousAt_digamma_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    ContinuousAt Complex.digamma z := by
  let a : ℝ := z.re / 2
  let b : ℝ := z.re + 1
  let s : Set ℂ := {w | a < w.re ∧ w.re < b}
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hs : IsOpen s := by
    change IsOpen ({w : ℂ | a < w.re} ∩ {w : ℂ | w.re < b})
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hzs : z ∈ s := by
    change a < z.re ∧ z.re < b
    dsimp [a, b]
    constructor <;> linarith
  have hcont : ContinuousOn Complex.digamma s :=
    (gammaSeqLogDeriv_tendstoLocallyUniformlyOn_strip a b ha hb).continuousOn <|
      Filter.Frequently.of_forall fun n => by
        intro w hw
        have hwpos : 0 < w.re := ha.trans hw.1
        exact (hasDerivAt_gammaSeqLogDeriv w (n + 1) fun j _ hzero => by
          have hre := congrArg Complex.re hzero
          simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hre
          have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
          linarith).continuousAt.continuousWithinAt
  exact hcont.continuousAt (hs.mem_nhds hzs)

/-- The digamma function is analytic for `Re(z)>0`. This extracts regularity from
Euler's locally uniform limit and Mathlib's meromorphy, for integration and
differentiation of the digamma expansions. -/
theorem analyticAt_digamma_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.digamma z :=
  (Complex.meromorphic_digamma z).analyticAt (continuousAt_digamma_of_re_pos z hz)

/-- Translating locally to the right half-plane makes `digamma` continuous at every point off the
real axis. -/
private lemma continuousAt_digamma_of_im_ne_zero (z : ℂ) (hz : z.im ≠ 0) :
    ContinuousAt Complex.digamma z := by
  obtain ⟨k : ℕ, hk⟩ := exists_nat_gt (-z.re)
  have hzk : 0 < (z + k).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  have hcomp : ContinuousAt (fun w : ℂ => Complex.digamma (w + k)) z := by
    have h := ContinuousAt.comp (f := fun w : ℂ => w + (k : ℂ))
      (g := Complex.digamma) (continuousAt_digamma_of_re_pos (z + k) hzk)
      (continuousAt_id.add_const (k : ℂ))
    change ContinuousAt (fun w : ℂ => Complex.digamma (w + k)) z at h
    exact h
  have hsum : ContinuousAt (fun w : ℂ => ∑ j ∈ Finset.range k, (w + j)⁻¹) z := by
    have hdiff : DifferentiableAt ℂ
        (fun w : ℂ => ∑ j ∈ Finset.range k, (w + j)⁻¹) z := by
      apply DifferentiableAt.fun_sum
      intro j hj
      apply HasDerivAt.differentiableAt
      exact (hasDerivAt_inv fun hzero => by
        change z + (j : ℂ) = 0 at hzero
        have him := congrArg Complex.im hzero
        simp only [Complex.add_im, Complex.natCast_im, add_zero, Complex.zero_im] at him
        exact hz him).comp z ((hasDerivAt_id z).add_const (j : ℂ))
    exact hdiff.continuousAt
  apply (hcomp.sub hsum).congr_of_eventuallyEq
  filter_upwards [(isOpen_ne_fun Complex.continuous_im continuous_const).mem_nhds hz] with w hw
  change Complex.digamma w = Complex.digamma (w + k) -
    ∑ j ∈ Finset.range k, (w + j)⁻¹
  rw [digamma_add_nat_of_im_ne_zero w hw k]
  ring

/-- Meromorphy and the continued local recurrence make `digamma` differentiable away from the
real axis. -/
private lemma differentiableAt_digamma_of_im_ne_zero (z : ℂ) (hz : z.im ≠ 0) :
    DifferentiableAt ℂ Complex.digamma z :=
  (Complex.meromorphic_digamma z).analyticAt
    (continuousAt_digamma_of_im_ne_zero z hz) |>.differentiableAt

/-- Differentiating the digamma recurrence away from its poles gives the one-step recurrence for
its derivative. -/
private lemma deriv_digamma_add_one_of_im_ne_zero (z : ℂ) (hz : z.im ≠ 0) :
    deriv Complex.digamma (z + 1) = deriv Complex.digamma z - z⁻¹ ^ 2 := by
  have hne : z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.zero_im] at him
    exact hz him
  have hleft := (differentiableAt_digamma_of_im_ne_zero (z + 1)
    (by simpa using hz)).hasDerivAt.comp z ((hasDerivAt_id z).add_const 1)
  have hright := (differentiableAt_digamma_of_im_ne_zero z hz).hasDerivAt.add
    (hasDerivAt_inv hne)
  have heq : (Complex.digamma ∘ fun w : ℂ => id w + 1) =ᶠ[nhds z]
      Complex.digamma + fun w : ℂ => w⁻¹ := by
    filter_upwards [(isOpen_ne_fun Complex.continuous_im continuous_const).mem_nhds hz] with w hw
    change Complex.digamma (w + 1) = Complex.digamma w + w⁻¹
    apply Complex.digamma_apply_add_one
    intro m hm
    have him := congrArg Complex.im hm
    simp only [neg_im, Complex.natCast_im, neg_zero] at him
    exact hw him
  have hder := hleft.unique (hright.congr_of_eventuallyEq heq)
  simpa only [mul_one, inv_pow, sub_eq_add_neg] using hder

/-- If the finite reciprocal-square sums converge at `z + 1`, their exact translation formula
and the differentiated digamma recurrence give convergence at `z`. -/
private lemma tendsto_gammaSeqTrigamma_of_add_one (z : ℂ) (hz : z.im ≠ 0)
    (h : Tendsto (fun n : ℕ => gammaSeqTrigamma (z + 1) (n + 1)) atTop
      (nhds (deriv Complex.digamma (z + 1)))) :
    Tendsto (fun n : ℕ => gammaSeqTrigamma z (n + 1)) atTop
      (nhds (deriv Complex.digamma z)) := by
  have hend : Tendsto (fun n : ℕ => (z + ((n + 2 : ℕ) : ℂ))⁻¹ ^ 2) atTop (nhds 0) := by
    simpa using (show Tendsto (fun n : ℕ => (z + ((n + 2 : ℕ) : ℂ))⁻¹) atTop
        (nhds 0) by
      simpa [Function.comp_def, Nat.cast_add] using
        (tendsto_inv_add_nat z).comp (tendsto_add_atTop_nat 2)).pow 2
  have hrec := h.add_const (z⁻¹ ^ 2) |>.sub hend
  convert hrec using 1
  · ext n
    rw [gammaSeqTrigamma_add_one z (n + 1)]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  · rw [deriv_digamma_add_one_of_im_ne_zero z hz]
    ring_nf

/-- The finite reciprocal-square sums converge to `deriv digamma` at every point off the real
axis.  The exact finite recurrence continues the right-half-plane result and therefore covers the
upper-half-plane rays in [95, Shintani (1977), paragraph 1.6 on p. 181]. -/
theorem tendsto_gammaSeqTrigamma_of_im_ne_zero (z : ℂ) (hz : z.im ≠ 0) :
    Tendsto (fun n : ℕ => gammaSeqTrigamma z (n + 1)) atTop
      (nhds (deriv Complex.digamma z)) := by
  obtain ⟨k : ℕ, hk⟩ := exists_nat_gt (-z.re)
  have hbase : Tendsto
      (fun n : ℕ => gammaSeqTrigamma (z + k) (n + 1)) atTop
      (nhds (deriv Complex.digamma (z + k))) := by
    apply tendsto_gammaSeqTrigamma
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  have hshift : ∀ k : ℕ,
      Tendsto (fun n : ℕ => gammaSeqTrigamma (z + k) (n + 1)) atTop
          (nhds (deriv Complex.digamma (z + k))) →
        Tendsto (fun n : ℕ => gammaSeqTrigamma z (n + 1)) atTop
          (nhds (deriv Complex.digamma z)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        intro hj
        apply ih
        apply tendsto_gammaSeqTrigamma_of_add_one (z + j)
        · simpa using hz
        · convert hj using 1 <;> push_cast <;> ring_nf
  exact hshift k hbase

/-! ### Euler limits and regularity on the slit plane

The union of the right half-plane and the nonreal points is precisely
`ℂ \ (-∞,0]`. The preceding continuations therefore give the limits and
holomorphy needed for Shintani's period continuation in paragraph 1.6.
-/

/-- Euler's logarithmic derivatives converge on `ℂ \ (-∞,0]`, combining
`tendsto_gammaSeqLogDeriv` and `tendsto_gammaSeqLogDeriv_of_im_ne_zero`. -/
theorem tendsto_gammaSeqLogDeriv_of_mem_slitPlane (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    Tendsto (fun n : ℕ => gammaSeqLogDeriv z (n + 1)) atTop
      (nhds (Complex.digamma z)) := by
  rcases hz with hz | hz
  · exact tendsto_gammaSeqLogDeriv z hz
  · exact tendsto_gammaSeqLogDeriv_of_im_ne_zero z hz

/-- Euler's reciprocal-square sums converge to `ψ'(z)` on `ℂ \ (-∞,0]`,
combining `tendsto_gammaSeqTrigamma` and `tendsto_gammaSeqTrigamma_of_im_ne_zero`. -/
theorem tendsto_gammaSeqTrigamma_of_mem_slitPlane (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    Tendsto (fun n : ℕ => gammaSeqTrigamma z (n + 1)) atTop
      (nhds (deriv Complex.digamma z)) := by
  rcases hz with hz | hz
  · exact tendsto_gammaSeqTrigamma z hz
  · exact tendsto_gammaSeqTrigamma_of_im_ne_zero z hz

/-- The digamma function is holomorphic on `ℂ \ (-∞,0]`. This combines
`analyticAt_digamma_of_re_pos` with the same continued recurrence used in
`tendsto_gammaSeqLogDeriv_of_im_ne_zero`, supplying regularity for Shintani's
coefficient series in [95, Shintani (1977), paragraph 1.6, p. 181]. -/
theorem analyticAt_digamma_of_mem_slitPlane (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    AnalyticAt ℂ Complex.digamma z := by
  rcases hz with hz | hz
  · exact analyticAt_digamma_of_re_pos z hz
  · exact (Complex.meromorphic_digamma z).analyticAt
      (continuousAt_digamma_of_im_ne_zero z hz)

end SIC

end
