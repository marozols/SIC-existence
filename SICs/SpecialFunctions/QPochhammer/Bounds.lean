/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.NearOne
import SICs.SpecialFunctions.QPochhammer.Infinite

/-!
# Quantitative bounds for q-Pochhammer products

Explicit bounds and uniform convergence to one for q-products high in the upper half plane,
and for finite products with complex periods.

This module supplies elementary product estimates for the upper-half-plane calculation of
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. The infinite-product estimates
require the imaginary part of the modulus to be bounded below by a positive constant, so they
do not assert uniformity as the modulus approaches the real axis. The finite-product estimates
instead bound the imaginary parts of the individual phases and allow complex periods near it.

## The argument

For a finite product, `‖∏(1+uⱼ)-1‖ ≤ exp(∑‖uⱼ‖)-1`. Apply this to
`uⱼ=-e(z+jτ)` and pass to the convergent infinite product. The sum of norms is the
geometric series `exp(-2π Im z)/(1-exp(-2π Im τ))`. A positive lower bound for
`Im τ` gives a bound independent of the real parts of both parameters. As `Im z`
tends to infinity, the majorant tends to zero, so the product tends to one.
Subtracting the integer part of `Re z` puts points in a compact real interval without changing
the q-product. Compactness gives a positive lower bound on a closed strip above the real axis;
convergence to one extends it to the upper half plane above that strip.

For complex periods, if each phase `z + jτ` of the finite symbol `ϖ_n(z,τ)` has
`Im(z + jτ) ≥ η > 0`, each exponential factor has norm at most `δ = exp(-2π η)`.
A direct factor differs from one by at most `δ`, and an inverse factor by at most
`δ/(1-δ)`. Thus `‖ϖ_n(z,τ) - 1‖ ≤ exp(|n| δ/(1-δ)) - 1` for either sign of `n`. When the
phase bound `η` tends to infinity with `|n| exp(-2πη) → 0`, the finite symbols tend to one; this
is the limit used for Faddeev shifts in `SICs.SpecialFunctions.Faddeev.Asymptotics`. If `|n|`
grows at most linearly with a height `y` and every phase stays above `cy`, half of the
exponential decay absorbs that linear growth. The resulting uniform bound also becomes smaller
than `1/2`, so reverse triangle gives nonvanishing and the same bound, up to a factor of two,
for the inverse finite symbol.
-/

noncomputable section

open Complex Real Filter
open scoped Topology

namespace SIC

/-! ### Geometric majorants and limits

The finite-product estimate passes to the limit by absolute convergence; bounding
the geometric ratio gives uniformity in the modulus. Integer reduction and compactness
then give a positive lower bound away from the zeros.
-/

/-- The norm of an exponential factor is a geometric term. This is used by
`qPochhammer_tsum_norm_eq_bound`. -/
private lemma qPochhammer_norm_exp_factor (z τ : ℂ) (j : ℕ) :
    ‖Complex.exp (2 * π * I * (z + j * τ))‖ =
      Real.exp (-2 * π * z.im) * Real.exp (-2 * π * τ.im) ^ j := by
  rw [Complex.norm_exp]
  have hre : (2 * (π : ℂ) * I * (z + j * τ)).re =
      -2 * π * z.im + (j : ℝ) * (-2 * π * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im, Complex.add_im]
    ring
  rw [hre, Real.exp_add, Real.exp_nat_mul]

/-- The geometric sum of factor norms used in `norm_qPochhammer_sub_one_le`. -/
private lemma qPochhammer_tsum_norm_eq_bound (z τ : ℂ) (hτ : 0 < τ.im) :
    (∑' j : ℕ, ‖Complex.exp (2 * π * I * (z + j * τ))‖) =
      Real.exp (-2 * π * z.im) / (1 - Real.exp (-2 * π * τ.im)) := by
  have hr : Real.exp (-2 * π * τ.im) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  simp_rw [qPochhammer_norm_exp_factor]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (le_of_lt (Real.exp_pos _)) hr]
  ring

/-- The geometric product bound
`|ϖ(z,τ)-1| ≤ exp(exp(-2π Im z)/(1-exp(-2π Im τ)))-1` for `Im τ > 0`.
This is the finite-product norm estimate applied to the definition of `qPochhammer`,
and supplies its upper-half-plane asymptotics. -/
theorem norm_qPochhammer_sub_one_le (z τ : ℂ) (hτ : 0 < τ.im) :
    ‖qPochhammer z τ - 1‖ ≤
      Real.exp (Real.exp (-2 * π * z.im) / (1 - Real.exp (-2 * π * τ.im))) - 1 := by
  have hprod := (qPochhammer_multipliable z τ hτ).tendsto_prod_tprod_nat
  have hsum := (qPochhammer_summable_norm z τ hτ).tendsto_sum_tsum_nat
  have hfinite (n : ℕ) :
      ‖(∏ j ∈ Finset.range n, (1 - Complex.exp (2 * π * I * (z + j * τ)))) - 1‖ ≤
        Real.exp (∑ j ∈ Finset.range n,
          ‖Complex.exp (2 * π * I * (z + j * τ))‖) - 1 := by
    simpa only [sub_eq_add_neg, norm_neg] using
      (Finset.range n).norm_prod_one_add_sub_one_le
        (fun j : ℕ => -Complex.exp (2 * π * I * (z + j * τ)))
  have hle := le_of_tendsto_of_tendsto (hprod.sub tendsto_const_nhds).norm
    ((Real.continuous_exp.tendsto _).comp hsum |>.sub tendsto_const_nhds)
    (Filter.Eventually.of_forall hfinite)
  simpa only [qPochhammer, qPochhammer_tsum_norm_eq_bound z τ hτ] using hle

/-- If `Im τ ≥ δ > 0`, the q-product error is bounded by the same geometric
majorant with `δ` in the denominator, uniformly in both real parts.
This is the uniform-modulus consequence of `norm_qPochhammer_sub_one_le`. -/
theorem norm_qPochhammer_sub_one_le_of_le_im (z τ : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hτ : δ ≤ τ.im) :
    ‖qPochhammer z τ - 1‖ ≤
      Real.exp (Real.exp (-2 * π * z.im) / (1 - Real.exp (-2 * π * δ))) - 1 := by
  have hden : 0 < 1 - Real.exp (-2 * π * δ) := by
    have := Real.exp_lt_one_iff.mpr (show -2 * π * δ < 0 by
      nlinarith [Real.pi_pos])
    linarith
  have hden_le : 1 - Real.exp (-2 * π * δ) ≤
      1 - Real.exp (-2 * π * τ.im) := by
    have := Real.exp_le_exp.mpr (show -2 * π * τ.im ≤ -2 * π * δ by
      nlinarith [Real.pi_pos])
    linarith
  calc
    ‖qPochhammer z τ - 1‖ ≤
        Real.exp (Real.exp (-2 * π * z.im) /
          (1 - Real.exp (-2 * π * τ.im))) - 1 :=
      norm_qPochhammer_sub_one_le z τ (lt_of_lt_of_le hδ hτ)
    _ ≤ Real.exp (Real.exp (-2 * π * z.im) /
          (1 - Real.exp (-2 * π * δ))) - 1 := by
      gcongr

/-- Q-products tend to one as `Im z → +∞`, uniformly for periods satisfying
`Im τ ≥ δ > 0`. This is the varying-parameter consequence of
`norm_qPochhammer_sub_one_le_of_le_im`; it applies to arbitrary real translates. -/
theorem tendsto_qPochhammer_of_im_tendsto_atTop {α : Type*} {l : Filter α}
    (z τ : α → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hτ : ∀ᶠ a in l, δ ≤ (τ a).im)
    (hz : Tendsto (fun a => (z a).im) l atTop) :
    Tendsto (fun a => qPochhammer (z a) (τ a)) l (𝓝 1) := by
  have hbot : Tendsto (fun a => -2 * π * (z a).im) l atBot :=
    hz.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos])
  have hexp : Tendsto (fun a => Real.exp (-2 * π * (z a).im)) l (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hbot
  have hmajor : Tendsto
      (fun a => Real.exp (Real.exp (-2 * π * (z a).im) /
        (1 - Real.exp (-2 * π * δ))) - 1) l (𝓝 0) := by
    have hdiv : Tendsto
        (fun a => Real.exp (-2 * π * (z a).im) /
          (1 - Real.exp (-2 * π * δ))) l (𝓝 0) := by
      simpa using hexp.div_const (1 - Real.exp (-2 * π * δ))
    simpa using ((Real.continuous_exp.tendsto 0).comp hdiv).sub
      (tendsto_const_nhds (x := (1 : ℝ)))
  have hnorm : Tendsto (fun a => ‖qPochhammer (z a) (τ a) - 1‖) l (𝓝 0) :=
    Filter.Tendsto.squeeze' tendsto_const_nhds hmajor
      (Filter.Eventually.of_forall fun a => norm_nonneg _)
      (hτ.mono fun a ha => norm_qPochhammer_sub_one_le_of_le_im (z a) (τ a) δ hδ ha)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

/-- For a fixed period `τ ∈ ℍ` and `η > 0`, `‖ϖ(x,τ) - 1‖ ≤ η` whenever
`Im x ≥ X`; the fixed-period form of `tendsto_qPochhammer_of_im_tendsto_atTop`. -/
theorem exists_norm_qPochhammer_sub_one_le (τ : ℂ) (hτ : 0 < τ.im) (η : ℝ) (hη : 0 < η) :
    ∃ X : ℝ, ∀ x : ℂ, X ≤ x.im → ‖qPochhammer x τ - 1‖ ≤ η := by
  have hlim : Tendsto (fun x : ℂ => qPochhammer x τ)
      (Filter.comap Complex.im Filter.atTop) (𝓝 1) :=
    tendsto_qPochhammer_of_im_tendsto_atTop id (fun _ => τ) τ.im hτ
      (Filter.Eventually.of_forall fun _ => le_rfl) Filter.tendsto_comap
  have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp hlim
  have hnear := hnorm.eventually (eventually_lt_nhds hη)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp (Filter.eventually_comap.mp hnear)
  exact ⟨X, fun x hx => (hX x.im hx x rfl).le⟩

/-- Subtracting `⌊Re v⌋` places the real part in `[0,1]` and preserves the imaginary part. -/
theorem exists_intCast_sub_re_mem_Icc (v : ℂ) :
    ∃ k : ℤ, 0 ≤ (v - k).re ∧ (v - k).re ≤ 1 ∧ (v - k).im = v.im := by
  refine ⟨⌊v.re⌋, ?_, ?_, ?_⟩
  · simp [Complex.sub_re]
  · rw [Complex.sub_re, Complex.intCast_re]
    have h := Int.lt_floor_add_one v.re
    linarith
  · simp

/-- A positive minimum for `ϖ` on a closed strip above the real axis, used by
`exists_pos_le_norm_qPochhammer_of_le_im`. -/
private lemma exists_pos_le_norm_qPochhammer_on_strip (τ : ℂ) (hτ : 0 < τ.im)
    (η B : ℝ) (hη : 0 < η) (hB : η ≤ B) :
    ∃ c > 0, ∀ v : ℂ, η ≤ v.im → v.im ≤ B → c ≤ ‖qPochhammer v τ‖ := by
  let K : Set ℂ := Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc η B
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hKne : K.Nonempty := by
    refine ⟨⟨0, η⟩, ?_⟩
    change (0 : ℝ) ∈ Set.Icc 0 1 ∧ η ∈ Set.Icc η B
    exact ⟨by simp, ⟨le_rfl, hB⟩⟩
  obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn hKne
    (qPochhammer_continuous τ hτ).norm.continuousOn
  have hwne : qPochhammer w τ ≠ 0 := by
    intro hz
    have him := im_nonpos_of_qPochhammer_eq_zero hτ hz
    have hηw : η ≤ w.im := hw.2.1
    linarith
  refine ⟨‖qPochhammer w τ‖, norm_pos_iff.mpr hwne, ?_⟩
  intro v hηv hBv
  obtain ⟨k, hre0, hre1, him⟩ := exists_intCast_sub_re_mem_Icc v
  have hϖ : qPochhammer (v - k) τ = qPochhammer v τ := by
    simpa [sub_eq_add_neg] using qPochhammer_add_intCast v τ (-k)
  have hmem : v - (k : ℂ) ∈ K := by
    change (v - (k : ℂ)).re ∈ Set.Icc (0 : ℝ) 1 ∧
      (v - (k : ℂ)).im ∈ Set.Icc η B
    exact ⟨⟨hre0, hre1⟩, by rw [him]; exact ⟨hηv, hBv⟩⟩
  rw [← hϖ]
  exact hmin hmem

/-- For `Im τ > 0` and `η > 0`, `‖ϖ(v,τ)‖` is bounded below by a positive constant on the half
plane `Im v ≥ η`. -/
theorem exists_pos_le_norm_qPochhammer_of_le_im (τ : ℂ) (hτ : 0 < τ.im) (η : ℝ) (hη : 0 < η) :
    ∃ c > 0, ∀ v : ℂ, η ≤ v.im → c ≤ ‖qPochhammer v τ‖ := by
  obtain ⟨X, hX⟩ := exists_norm_qPochhammer_sub_one_le τ hτ (1 / 2) (by norm_num)
  obtain ⟨c, hc, hstrip⟩ :=
    exists_pos_le_norm_qPochhammer_on_strip τ hτ η (max η X) hη (le_max_left _ _)
  refine ⟨min c (1 / 2), lt_min hc (by norm_num), ?_⟩
  intro v hηv
  by_cases hv : X ≤ v.im
  · have herror := hX v hv
    have hone : (1 : ℝ) ≤ ‖qPochhammer v τ‖ + ‖qPochhammer v τ - 1‖ := by
      calc
        (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
        _ = ‖qPochhammer v τ - (qPochhammer v τ - 1)‖ := by
          congr 1
          abel
        _ ≤ _ := norm_sub_le _ _
    exact le_trans (min_le_right _ _) (by linarith)
  · have hvB : v.im ≤ max η X := le_max_of_le_right (le_of_lt (lt_of_not_ge hv))
    exact le_trans (min_le_left _ _) (hstrip v hηv hvB)

/-! ### Finite products with complex periods

For either sign of the index, a lower bound `η > 0` on the imaginary parts of all
phases makes each exponential factor at most `δ = exp(-2π η)` in norm. Direct
factors differ from one by at most `δ`; inverse factors differ by at most
`δ/(1-δ)`. The finite-product inequality then gives a bound depending only on
`|n|` and `η`, even when the period varies in `ℂ`. The preceding infinite-product
bounds still require a positive lower bound on `Im τ`.
-/

/-- A phase above `η` has exponential norm at most `exp(-2π η)`; used by
`norm_qPochhammerFin_sub_one_le_of_le_im`. -/
private lemma qPochhammer_norm_exp_le_of_le_im (w : ℂ) (η : ℝ) (hw : η ≤ w.im) :
    ‖Complex.exp (2 * π * I * w)‖ ≤ Real.exp (-2 * π * η) := by
  rw [Complex.norm_exp]
  have hre : (2 * (π : ℂ) * I * w).re = -2 * π * w.im := by
    simp [Complex.mul_re]
  rw [hre]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])

/-- An inverse factor whose exponential has norm at most `δ < 1` differs from
one by at most `δ/(1-δ)`; used by `norm_qPochhammerFin_sub_one_le_of_le_im`. -/
private lemma qPochhammer_norm_inv_one_sub_sub_one_le (e : ℂ) (δ : ℝ)
    (hδ : ‖e‖ ≤ δ) (hδlt : δ < 1) :
    ‖(1 - e)⁻¹ - 1‖ ≤ δ / (1 - δ) := by
  have hden : 1 - δ ≤ ‖(1 : ℂ) - e‖ := by
    have h := norm_sub_norm_le (1 : ℂ) e
    simp only [norm_one] at h
    linarith
  have hpos : 0 < 1 - δ := by linarith
  have hne : (1 : ℂ) - e ≠ 0 := norm_pos_iff.mp (by linarith)
  have hid : (1 - e)⁻¹ - 1 = e / (1 - e) := by
    field_simp
    ring
  rw [hid, norm_div]
  calc
    ‖e‖ / ‖(1 : ℂ) - e‖ ≤ δ / ‖(1 : ℂ) - e‖ := by gcongr
    _ ≤ δ / (1 - δ) :=
      div_le_div_of_nonneg_left (le_trans (norm_nonneg _) hδ) hpos hden

/-- A uniform bound on factor errors gives the finite-product error used in
`norm_qPochhammerFin_sub_one_le_of_le_im`. -/
private lemma qPochhammer_norm_prod_one_add_sub_one_le_of_bound {ι : Type*}
    (s : Finset ι) (f : ι → ℂ) (B : ℝ)
    (hf : ∀ j ∈ s, ‖f j‖ ≤ B) :
    ‖∏ j ∈ s, (1 + f j) - 1‖ ≤ Real.exp (s.card * B) - 1 := by
  calc
    _ ≤ Real.exp (∑ j ∈ s, ‖f j‖) - 1 := s.norm_prod_one_add_sub_one_le f
    _ ≤ Real.exp (∑ _j ∈ s, B) - 1 := by
      gcongr with j hj
      exact hf j hj
    _ = Real.exp (s.card * B) - 1 := by simp

/-- The nonnegative-index case of `norm_qPochhammerFin_sub_one_le_of_le_im`. -/
private lemma norm_qPochhammerFin_sub_one_le_of_nonneg (n : ℤ) (z τ : ℂ) (η : ℝ)
    (hη : 0 < η) (hn : 0 ≤ n)
    (hphase : ∀ j ∈ Set.Ico (min n 0) (max n 0), η ≤ (z + (j : ℂ) * τ).im) :
    ‖qPochhammerFin n z τ - 1‖ ≤
      Real.exp (|(n : ℝ)| * (Real.exp (-2 * π * η) /
        (1 - Real.exp (-2 * π * η)))) - 1 := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  let δ := Real.exp (-2 * π * η)
  have hδlt : δ < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hδle : δ ≤ δ / (1 - δ) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - δ)).2
    nlinarith [Real.exp_pos (-2 * π * η), sq_nonneg δ]
  have hfactor (j : ℕ) (hj : j ∈ Finset.range k) :
      ‖-Complex.exp (2 * π * I * (z + j * τ))‖ ≤ δ / (1 - δ) := by
    have hidx : (j : ℤ) ∈ Set.Ico (min (k : ℤ) 0) (max (k : ℤ) 0) := by
      refine Set.mem_Ico.mpr ⟨(min_le_right _ _).trans (Int.natCast_nonneg _), ?_⟩
      exact lt_of_lt_of_le (by exact_mod_cast Finset.mem_range.mp hj) (le_max_left _ _)
    have hjphase : η ≤ (z + (j : ℂ) * τ).im := by
      simpa only [Int.cast_natCast] using hphase (j : ℤ) hidx
    simpa only [norm_neg] using
      (qPochhammer_norm_exp_le_of_le_im _ η hjphase).trans hδle
  rw [qPochhammerFin_natCast]
  have hfin := qPochhammer_norm_prod_one_add_sub_one_le_of_bound
    (Finset.range k) (fun j : ℕ => -Complex.exp (2 * π * I * (z + j * τ)))
    (δ / (1 - δ)) hfactor
  simpa [δ, sub_eq_add_neg,
    abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k)] using hfin

/-- The error of one negative-index inverse factor; used by
`norm_qPochhammerFin_sub_one_le_of_neg`. -/
private lemma qPochhammerFin_inverse_factor_bound (n : ℤ) (k : ℕ) (z τ : ℂ) (η : ℝ)
    (hk : (k : ℤ) = -n) (hη : 0 < η)
    (hphase : ∀ j ∈ Set.Ico (min n 0) (max n 0), η ≤ (z + (j : ℂ) * τ).im)
    (j : ℕ) (hj : j ∈ Finset.range k) :
    ‖(1 - Complex.exp (2 * π * I *
      (z + (n + (j : ℤ) : ℂ) * τ)))⁻¹ - 1‖ ≤
      Real.exp (-2 * π * η) / (1 - Real.exp (-2 * π * η)) := by
  have hjk : (j : ℤ) < -n := by
    rw [← hk]
    exact_mod_cast Finset.mem_range.mp hj
  have hidx : n + (j : ℤ) ∈ Set.Ico (min n 0) (max n 0) := by
    refine Set.mem_Ico.mpr ⟨(min_le_left _ _).trans (by omega), ?_⟩
    exact lt_of_lt_of_le (by omega : n + (j : ℤ) < 0) (le_max_right _ _)
  have hjphase : η ≤ (z + (n + (j : ℤ) : ℂ) * τ).im := by
    simpa only [Int.cast_add, Int.cast_natCast] using hphase (n + (j : ℤ)) hidx
  exact qPochhammer_norm_inv_one_sub_sub_one_le _ _
    (qPochhammer_norm_exp_le_of_le_im _ η hjphase)
    (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos]))

/-- The negative-index case of `norm_qPochhammerFin_sub_one_le_of_le_im`. -/
private lemma norm_qPochhammerFin_sub_one_le_of_neg (n : ℤ) (z τ : ℂ) (η : ℝ)
    (hη : 0 < η) (hn : n < 0)
    (hphase : ∀ j ∈ Set.Ico (min n 0) (max n 0), η ≤ (z + (j : ℂ) * τ).im) :
    ‖qPochhammerFin n z τ - 1‖ ≤
      Real.exp (|(n : ℝ)| * (Real.exp (-2 * π * η) /
        (1 - Real.exp (-2 * π * η)))) - 1 := by
  let δ := Real.exp (-2 * π * η)
  let k := (-n).toNat
  have hk : (k : ℤ) = -n := Int.toNat_of_nonneg (by omega : 0 ≤ -n)
  have hfactor (j : ℕ) (hj : j ∈ Finset.range k) :
      ‖(1 - Complex.exp (2 * π * I *
        (z + (n + (j : ℤ) : ℂ) * τ)))⁻¹ - 1‖ ≤ δ / (1 - δ) := by
    exact qPochhammerFin_inverse_factor_bound n k z τ η hk hη hphase j hj
  have hfin := qPochhammer_norm_prod_one_add_sub_one_le_of_bound
    (Finset.range k)
    (fun j : ℕ => (1 - Complex.exp (2 * π * I *
      (z + (n + (j : ℤ) : ℂ) * τ)))⁻¹ - 1) (δ / (1 - δ)) hfactor
  have hcancel (j : ℕ) : (1 : ℂ) +
      ((1 - Complex.exp (2 * π * I * (z + (n + (j : ℤ) : ℂ) * τ)))⁻¹ - 1) =
      (1 - Complex.exp (2 * π * I * (z + (n + (j : ℤ) : ℂ) * τ)))⁻¹ := by ring
  simp_rw [hcancel] at hfin
  have hprod : qPochhammerFin n z τ =
      ∏ j ∈ Finset.range k, (1 - Complex.exp (2 * π * I *
        (z + (n + (j : ℤ) : ℂ) * τ)))⁻¹ := by
    rw [qPochhammerFin, ite_eq_right hn.ne, ite_eq_right (not_lt.mpr hn.le)]
    exact (Finset.prod_inv_distrib _).symm
  have hkre : (k : ℝ) = |(n : ℝ)| := by
    exact_mod_cast (show (k : ℤ) = |n| by simpa only [abs_of_neg hn] using hk)
  rw [hprod]
  simpa only [Finset.card_range, hkre] using hfin

/-- If every phase of the finite symbol has imaginary part at least `η > 0`, then
`‖ϖ_n(z,τ) - 1‖ ≤ exp(|n| δ/(1-δ)) - 1`, where `δ = exp(-2π η)`.
This is the elementary finite-product estimate for `qPochhammerFin`, the finite symbol of
[AFK25, Definition 1.14, `dfn:variantqPochhammer`], with inverse factors for negative indices.
It supplies the finite-shift estimate needed when the Faddeev period varies near a real one. -/
theorem norm_qPochhammerFin_sub_one_le_of_le_im (n : ℤ) (z τ : ℂ) (η : ℝ)
    (hη : 0 < η)
    (hphase : ∀ j ∈ Set.Ico (min n 0) (max n 0), η ≤ (z + (j : ℂ) * τ).im) :
    ‖qPochhammerFin n z τ - 1‖ ≤
      Real.exp (|(n : ℝ)| * (Real.exp (-2 * π * η) /
        (1 - Real.exp (-2 * π * η)))) - 1 := by
  by_cases hn : 0 ≤ n
  · exact norm_qPochhammerFin_sub_one_le_of_nonneg n z τ η hη hn hphase
  · exact norm_qPochhammerFin_sub_one_le_of_neg n z τ η hη (lt_of_not_ge hn) hphase

/-- A linear factor times `exp (-κy)` is bounded independently of `y ≥ 0`; used by
`exists_norm_qPochhammerFin_sub_one_le`. -/
private lemma linear_mul_exp_neg_le (A B κ y : ℝ) (hκ : 0 < κ) (hy : 0 ≤ y) :
    (|A| * y + |B|) * Real.exp (-κ * y) ≤ |A| / κ + |B| := by
  have hexp_le_one : Real.exp (-κ * y) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hκ.le hy])
  have hyexp : y * Real.exp (-κ * y) ≤ 1 / κ := by
    calc
      y * Real.exp (-κ * y) = κ⁻¹ * ((κ * y) * Real.exp (-(κ * y))) := by
        field_simp
      _ ≤ κ⁻¹ * 1 := by
        gcongr
        exact (Real.mul_exp_neg_le_exp_neg_one (κ * y)).trans
          (Real.exp_le_one_iff.mpr (by norm_num))
      _ = 1 / κ := by simp [div_eq_mul_inv]
  calc
    (|A| * y + |B|) * Real.exp (-κ * y) =
        |A| * (y * Real.exp (-κ * y)) + |B| * Real.exp (-κ * y) := by ring
    _ ≤ |A| * (1 / κ) + |B| * 1 := by gcongr
    _ = |A| / κ + |B| := by ring

/-- A linearly bounded integer index inherits the uniform linear-exponential bound; used by
`exists_norm_qPochhammerFin_sub_one_le`. -/
private lemma intCast_abs_mul_exp_neg_le_of_linear (A B κ y : ℝ) (n : ℤ)
    (hκ : 0 < κ) (hy : 0 ≤ y) (hn : |(n : ℝ)| ≤ A * y + B) :
    |(n : ℝ)| * Real.exp (-κ * y) ≤ 1 + |A| / κ + |B| := by
  have hn' : |(n : ℝ)| ≤ |A| * y + |B| :=
    hn.trans (add_le_add (mul_le_mul_of_nonneg_right (le_abs_self A) hy) (le_abs_self B))
  calc
    _ ≤ (|A| * y + |B|) * Real.exp (-κ * y) := by gcongr
    _ ≤ |A| / κ + |B| := linear_mul_exp_neg_le A B κ y hκ hy
    _ ≤ 1 + |A| / κ + |B| := by linarith

/-- On `[0,1]`, the exponential error `exp u - 1` is at most `2u`; used by
`exists_norm_qPochhammerFin_sub_one_le`. -/
private lemma exp_sub_one_le_two_mul {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp u - 1 ≤ 2 * u := by
  have habs := Real.abs_exp_sub_one_le (show |u| ≤ 1 by simpa [abs_of_nonneg hu0])
  simpa [abs_of_nonneg hu0,
    abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hu0))] using habs

/-- Once `2K ≤ κy` and `m exp(-κy) ≤ K`, the exponent in the finite-product majorant is
at most both `1` and `2K exp(-κy)`; used by
`exists_norm_qPochhammerFin_sub_one_le`. -/
private lemma qPochhammerFin_exponent_bounds (m κ K y : ℝ)
    (hm : 0 ≤ m) (hK : 1 ≤ K) (hy : 2 * K ≤ κ * y)
    (hmK : m * Real.exp (-κ * y) ≤ K) :
    let u := m * (Real.exp (-2 * κ * y) / (1 - Real.exp (-2 * κ * y)))
    0 ≤ u ∧ u ≤ 1 ∧ u ≤ 2 * K * Real.exp (-κ * y) := by
  let e := Real.exp (-κ * y)
  let δ := Real.exp (-2 * κ * y)
  have hKe : 2 * K * e ≤ 1 := by simpa [e] using two_mul_mul_exp_neg_le_one κ K y hy
  have hehalf : e ≤ 1 / 2 := by nlinarith [Real.exp_pos (-κ * y)]
  have hδeq : δ = e ^ 2 := by
    dsimp [δ, e]
    rw [show -2 * κ * y = (-κ * y) + (-κ * y) by ring, Real.exp_add]
    ring
  have hδhalf : δ ≤ 1 / 2 := by
    rw [hδeq]
    nlinarith [Real.exp_pos (-κ * y), sq_nonneg (e - 1 / 2)]
  have hden : 1 / 2 ≤ 1 - δ := by linarith
  have hratio : δ / (1 - δ) ≤ 2 * δ := by
    calc
      δ / (1 - δ) ≤ δ / (1 / 2) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hden
      _ = 2 * δ := by ring
  have hu : m * (δ / (1 - δ)) ≤ 2 * K * e := by
    calc
      m * (δ / (1 - δ)) ≤ m * (2 * δ) := by gcongr
      _ = 2 * (m * e) * e := by rw [hδeq]; ring
      _ ≤ 2 * K * e := by gcongr
  refine ⟨by positivity, hu.trans hKe, ?_⟩
  simpa [δ, e] using hu

/-- If the number of finite factors grows at most linearly with `y` and every phase has
imaginary part at least `cy`, then the finite symbol differs from one by at most a constant
times `exp(-πcy)`, uniformly in the index, argument, and complex period. This is the
half-rate quantitative consequence of `norm_qPochhammerFin_sub_one_le_of_le_im` for the
finite symbol of [AFK25, Definition 1.14, `dfn:variantqPochhammer`]. -/
theorem exists_norm_qPochhammerFin_sub_one_le
    (A B c : ℝ) (hc : 0 < c) :
    ∃ C > 0, ∃ R > 0, ∀ (y : ℝ) (n : ℤ) (z τ : ℂ),
      R ≤ y → |(n : ℝ)| ≤ A * y + B →
      (∀ j ∈ Set.Ico (min n 0) (max n 0), c * y ≤ (z + (j : ℂ) * τ).im) →
      ‖qPochhammerFin n z τ - 1‖ ≤ C * Real.exp (-(Real.pi * c) * y) := by
  let κ := Real.pi * c
  have hκ : 0 < κ := mul_pos Real.pi_pos hc
  let K := 1 + |A| / κ + |B|
  have hK : 1 ≤ K := by
    dsimp [K]
    have hA : 0 ≤ |A| / κ := div_nonneg (abs_nonneg A) hκ.le
    linarith [abs_nonneg B]
  refine ⟨4 * K, by positivity, 2 * K / κ, by positivity, ?_⟩
  intro y n z τ hy hn hphase
  have hypos : 0 < y := lt_of_lt_of_le (by positivity : 0 < 2 * K / κ) hy
  have hκy : 2 * K ≤ κ * y := by
    have := (div_le_iff₀ hκ).mp hy
    nlinarith
  have hmK : |(n : ℝ)| * Real.exp (-κ * y) ≤ K := by
    simpa [K] using intCast_abs_mul_exp_neg_le_of_linear A B κ y n hκ hypos.le hn
  obtain ⟨hu0, hu1, hu⟩ := qPochhammerFin_exponent_bounds
    |(n : ℝ)| κ K y (abs_nonneg _) hK hκy hmK
  have hbase := norm_qPochhammerFin_sub_one_le_of_le_im n z τ (c * y)
    (mul_pos hc hypos) hphase
  calc
    ‖qPochhammerFin n z τ - 1‖ ≤ Real.exp
        (|(n : ℝ)| * (Real.exp (-2 * κ * y) / (1 - Real.exp (-2 * κ * y)))) - 1 := by
      simpa [κ, mul_assoc] using hbase
    _ ≤ 2 * (|(n : ℝ)| * (Real.exp (-2 * κ * y) /
        (1 - Real.exp (-2 * κ * y)))) := exp_sub_one_le_two_mul hu0 hu1
    _ ≤ 4 * K * Real.exp (-κ * y) := by linarith
    _ = (4 * K) * Real.exp (-(Real.pi * c) * y) := by rfl

/-- Under the linear-height hypotheses, the finite symbol is nonzero for all sufficiently
large `y`, and its inverse differs from one by at most twice the corresponding near-one
bound. The constants are uniform in the index, argument, and complex period. -/
theorem exists_norm_qPochhammerFin_inv_sub_one_le
    (A B c : ℝ) (hc : 0 < c) :
    ∃ C > 0, ∃ R > 0, ∀ (y : ℝ) (n : ℤ) (z τ : ℂ),
      R ≤ y → |(n : ℝ)| ≤ A * y + B →
      (∀ j ∈ Set.Ico (min n 0) (max n 0), c * y ≤ (z + (j : ℂ) * τ).im) →
      qPochhammerFin n z τ ≠ 0 ∧
        ‖(qPochhammerFin n z τ)⁻¹ - 1‖ ≤
          2 * C * Real.exp (-(Real.pi * c) * y) := by
  obtain ⟨C, hC, R, hR, hbound⟩ :=
    exists_norm_qPochhammerFin_sub_one_le A B c hc
  let κ := Real.pi * c
  have hκ : 0 < κ := mul_pos Real.pi_pos hc
  let R' := max R (2 * C / κ)
  refine ⟨C, hC, R', lt_of_lt_of_le hR (le_max_left _ _), ?_⟩
  intro y n z τ hy hn hphase
  have hRy : R ≤ y := (le_max_left R (2 * C / κ)).trans hy
  have hκy : 2 * C ≤ κ * y := by
    have hCy : 2 * C / κ ≤ y := (le_max_right R (2 * C / κ)).trans hy
    have := (div_le_iff₀ hκ).mp hCy
    nlinarith
  have hCe : C * Real.exp (-κ * y) ≤ 1 / 2 := by
    nlinarith [two_mul_mul_exp_neg_le_one κ C y hκy]
  have hnear := hbound y n z τ hRy hn hphase
  obtain ⟨hne, hinv⟩ := norm_inv_sub_one_le_two_mul_norm_sub_one
    (qPochhammerFin n z τ) (hnear.trans (by simpa [κ] using hCe))
  refine ⟨hne, hinv.trans ?_⟩
  calc
    2 * ‖qPochhammerFin n z τ - 1‖ ≤
        2 * (C * Real.exp (-(Real.pi * c) * y)) := by gcongr
    _ = 2 * C * Real.exp (-(Real.pi * c) * y) := by ring

/-- Finite symbols tend to one for varying complex periods when their phase lower
bound tends to infinity and the product length times the exponential error tends to zero.
This is the varying-parameter form of `norm_qPochhammerFin_sub_one_le_of_le_im`. -/
theorem tendsto_qPochhammerFin_of_im_tendsto_atTop {α : Type*} {l : Filter α}
    (n : α → ℤ) (z τ : α → ℂ) (η : α → ℝ)
    (hη : Tendsto η l atTop)
    (hphase : ∀ᶠ a in l, ∀ j ∈ Set.Ico (min (n a) 0) (max (n a) 0),
      η a ≤ (z a + (j : ℂ) * τ a).im)
    (hcount : Tendsto (fun a => |(n a : ℝ)| * Real.exp (-2 * π * η a)) l (𝓝 0)) :
    Tendsto (fun a => qPochhammerFin (n a) (z a) (τ a)) l (𝓝 1) := by
  have hbot : Tendsto (fun a => -2 * π * η a) l atBot :=
    hη.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos])
  have hexp : Tendsto (fun a => Real.exp (-2 * π * η a)) l (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hbot
  have hden : Tendsto (fun a => 1 - Real.exp (-2 * π * η a)) l (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hexp
  have hratio : Tendsto (fun a => |(n a : ℝ)| * Real.exp (-2 * π * η a) /
      (1 - Real.exp (-2 * π * η a))) l (𝓝 0) := by
    convert hcount.div hden (by norm_num : (1 : ℝ) ≠ 0) using 1; simp
  have hmajor : Tendsto (fun a =>
      Real.exp (|(n a : ℝ)| * (Real.exp (-2 * π * η a) /
        (1 - Real.exp (-2 * π * η a)))) - 1) l (𝓝 0) := by
    simpa only [Function.comp_def, Real.exp_zero, sub_self, mul_div_assoc] using
      ((Real.continuous_exp.tendsto 0).comp hratio).sub
        (tendsto_const_nhds (x := (1 : ℝ)))
  have hnorm : Tendsto (fun a => ‖qPochhammerFin (n a) (z a) (τ a) - 1‖) l (𝓝 0) :=
    Filter.Tendsto.squeeze' tendsto_const_nhds hmajor
      (Filter.Eventually.of_forall fun a => norm_nonneg _)
      ((hη.eventually_gt_atTop 0).and hphase |>.mono fun a ha =>
        norm_qPochhammerFin_sub_one_le_of_le_im (n a) (z a) (τ a) (η a) ha.1 ha.2)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

end SIC
