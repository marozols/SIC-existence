/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Pseudolattice.Conjugation
import SICs.Dilogarithm.Pseudolattice.FiveTerm

/-!
# A value off the unit circle

When `N = |G_{I,ε}| ≥ 25`, the finite quantum dilogarithm of a pseudolattice has a nonzero
argument `x` with `|E_{I,ε}(x)| ≠ 1`, using the norm-one Gauss sum of
`SICs.Dilogarithm.MetricGroup`.

This module follows [RW26b, Radchenko, Wheeler (2026b), Section 7.1, Lemma 7]. It is stated first
for an abstract `FiniteQuantumDilog` over `ℂ` with the conjugation law `conj E(x) = ⟨x⟩E(x)` and a
positive value at zero, then for pseudolattices, where the conjugation law is
[RW26b, Radchenko, Wheeler (2026b), Proposition 2, (7)] (`pseudolatticeDilog_conj`) and `E(0) = √ε`.

## The argument

*The Gauss sum.* `MetricGroup.norm_gaussSum` gives absolute value one for
`s⁻¹ ∑_x ⟨x⟩⁻¹ = λ³`, and hence for `λ`.

*Lemma 7.* Suppose `|E(x)| = 1` for all `x ≠ 0`. The conjugation law gives `E(x)⁻¹ = ⟨x⟩E(x)`,
that is `E(x)² = ⟨x⟩⁻¹`. The Fourier law at zero, `Ê(0) = λE(0)`, gives
`S₁ = ∑_{x ≠ 0} E(x) = E(0)(λ√N - 1)`, and `S₂ = ∑_{x ≠ 0} E(x)² = λ³√N - 1`. From
`E(0)² = √N E(0) + 1` and `E(0) > 0`, `E(0) = (√N + √(N + 4))/2 > √N`, so
`|S₁| > √N(√N - 1)`, while `|S₂| ≤ √N + 1`. Rotating by a unit `u` with `uS₁ = |S₁|` and applying
Cauchy–Schwarz to the real parts, with `(Re w)² = (1 + Re(w²))/2` for `|w| = 1`,
`|S₁|² ≤ ((N - 1)/2)(N - 1 + |S₂|) ≤ (N - 1)(N + √N)/2`. With `t = √N ≥ 5`,
`(t² - 1)(t² + t)/2 < t²(t - 1)²` because `t² - 4t - 1 > 0`, a contradiction.
-/

noncomputable section

open scoped MatrixGroups ComplexConjugate

namespace SIC

/-! ### The off-unit-circle argument -/

section MetricGroup

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- A unit scalar rotates a complex number onto the nonnegative real axis, for
`norm_sum_sq_le_card_add_norm_sq`. -/
private theorem exists_rotate_to_norm (S : ℂ) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ u * S = (‖S‖ : ℂ) := by
  by_cases hS : S = 0
  · exact ⟨1, by simp, by simp [hS]⟩
  have hSn : ‖S‖ ≠ 0 := by simpa using hS
  refine ⟨(starRingEnd ℂ) S / (‖S‖ : ℂ), ?_, ?_⟩
  · rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg S), div_self hSn]
  · calc
      _ = ((starRingEnd ℂ) S * S) / (‖S‖ : ℂ) := by ring
      _ = (‖S‖ : ℂ) := by rw [Complex.conj_mul']; field_simp [hSn]

/-- The real part of a unit complex number satisfies the identity used by
`sum_re_sq_eq`. -/
private theorem unit_re_sq (w : ℂ) (hw : ‖w‖ = 1) :
    2 * w.re ^ 2 = 1 + (w ^ 2).re := by
  have hnormsq : w.re ^ 2 + w.im ^ 2 = 1 := by
    have hh := Complex.normSq_eq_norm_sq w
    rw [Complex.normSq_apply, hw] at hh
    nlinarith
  have hpow : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by
    rw [pow_two, Complex.mul_re]
    ring
  rw [hpow]
  nlinarith

/-- The second moment of the rotated real parts, for
`norm_sum_sq_le_card_add_norm_sq`. -/
private theorem sum_re_sq_eq {α : Type*} (s : Finset α) (z : α → ℂ) (u : ℂ)
    (hu : ‖u‖ = 1) (hz : ∀ x ∈ s, ‖z x‖ = 1) :
    2 * (∑ x ∈ s, (u * z x).re ^ 2) =
      (s.card : ℝ) + (u ^ 2 * ∑ x ∈ s, z x ^ 2).re := by
  have hsumSquare : (∑ x ∈ s, ((u * z x) ^ 2).re) =
      (u ^ 2 * ∑ x ∈ s, z x ^ 2).re := by
    rw [← Complex.re_sum]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  calc
    _ = ∑ x ∈ s, 2 * (u * z x).re ^ 2 := by rw [Finset.mul_sum]
    _ = ∑ x ∈ s, ((1 : ℝ) + ((u * z x) ^ 2).re) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply unit_re_sq
      rw [norm_mul, hu, hz x hx, one_mul]
    _ = _ := by rw [Finset.sum_add_distrib, hsumSquare]; simp

/-- A Cauchy–Schwarz bound for sums of unit complex numbers, used in
`FiniteQuantumDilog.exists_norm_ne_one`. -/
private theorem norm_sum_sq_le_card_add_norm_sq {α : Type*} (s : Finset α) (z : α → ℂ)
    (hz : ∀ x ∈ s, ‖z x‖ = 1) :
    2 * ‖∑ x ∈ s, z x‖ ^ 2 ≤
      (s.card : ℝ) * ((s.card : ℝ) + ‖∑ x ∈ s, z x ^ 2‖) := by
  obtain ⟨u, hu, hrot⟩ := exists_rotate_to_norm (∑ x ∈ s, z x)
  have hRe : (∑ x ∈ s, (u * z x).re) = ‖∑ x ∈ s, z x‖ := by
    calc
      _ = (∑ x ∈ s, u * z x).re := (Complex.re_sum s _).symm
      _ = (u * ∑ x ∈ s, z x).re := by rw [← Finset.mul_sum]
      _ = _ := by rw [hrot]; simp
  have hcs : (∑ x ∈ s, (u * z x).re) ^ 2 ≤
      (∑ x ∈ s, (u * z x).re ^ 2) * (s.card : ℝ) := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun x => (u * z x).re)
      (fun _ => (1 : ℝ))
  have hS2 : (u ^ 2 * ∑ x ∈ s, z x ^ 2).re ≤ ‖∑ x ∈ s, z x ^ 2‖ := by
    calc
      _ ≤ ‖u ^ 2 * ∑ x ∈ s, z x ^ 2‖ := Complex.re_le_norm _
      _ = _ := by rw [norm_mul, norm_pow, hu]; norm_num
  have hupper : 2 * (∑ x ∈ s, (u * z x).re ^ 2) * (s.card : ℝ) ≤
      (s.card : ℝ) * ((s.card : ℝ) + ‖∑ x ∈ s, z x ^ 2‖) := by
    rw [sum_re_sq_eq s z u hu hz]
    calc
      _ = (s.card : ℝ) * ((s.card : ℝ) +
          (u ^ 2 * ∑ x ∈ s, z x ^ 2).re) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hS2]) (Nat.cast_nonneg _)
  rw [hRe] at hcs
  nlinarith

/-- The strict real inequality at `N ≥ 25` used by `exists_norm_ne_one`. -/
private theorem final_real_inequality (N : ℕ) (hN : 25 ≤ N) :
    ((N : ℝ) - 1) * ((N : ℝ) + Real.sqrt N) / 2 <
      (N : ℝ) * (Real.sqrt N - 1) ^ 2 := by
  let t : ℝ := Real.sqrt N
  have ht : 5 ≤ t := by
    apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr
    exact_mod_cast hN
  have hsq : t ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hq : 0 < t ^ 2 - 4 * t - 1 := by
    have hh : 0 ≤ (t - 5) * (t + 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hdiff : 0 < t * (t - 1) * (t ^ 2 - 4 * t - 1) := by
    exact mul_pos (mul_pos (by linarith) (by linarith)) hq
  have heq : 2 * (t ^ 2 * (t - 1) ^ 2 -
      (t ^ 2 - 1) * (t ^ 2 + t) / 2) =
      t * (t - 1) * (t ^ 2 - 4 * t - 1) := by ring
  have hbound : (t ^ 2 - 1) * (t ^ 2 + t) / 2 <
      t ^ 2 * (t - 1) ^ 2 := by linarith
  simpa only [t, hsq] using hbound

variable [DecidableEq G]

namespace FiniteQuantumDilog
variable {M : MetricGroup G ℂ} (E : FiniteQuantumDilog M)

/-- The Fourier law gives the sum of `E` away from zero, for `exists_norm_ne_one`. -/
private theorem sum_erase_zero :
    (∑ x ∈ (Finset.univ.erase (0 : G)), E x) =
      E 0 * (E.multiplier * M.sqrtCard - 1) := by
  classical
  have hf := E.fourier_eq (0 : G)
  simp only [MetricGroup.fourier, neg_zero, M.bichar_zero_right, mul_one,
    M.gaussian_zero] at hf
  have hsum : (∑ x, E x) = M.sqrtCard * E.multiplier * E 0 := by
    calc
      _ = M.sqrtCard * (M.sqrtCard⁻¹ * ∑ x, E x) := by
        field_simp [M.sqrtCard_ne_zero]
      _ = _ := by rw [hf]; ring
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : G)), hsum]
  ring

/-- The conjugation law gives the sum of the squares away from zero, for
`exists_norm_ne_one`. -/
private theorem sum_sq_erase_zero
    (hconj : ∀ x, (starRingEnd ℂ) (E x) = M.gaussian x * E x)
    (hunit : ∀ x : G, x ≠ 0 → ‖E x‖ = 1) :
    (∑ x ∈ (Finset.univ.erase (0 : G)), E x ^ 2) =
      E.multiplier ^ 3 * M.sqrtCard - 1 := by
  classical
  have heq (x : G) (hx : x ≠ 0) : E x ^ 2 = (M.gaussian x)⁻¹ := by
    have hm : E x * (starRingEnd ℂ) (E x) = 1 := by
      rw [Complex.mul_conj', hunit x hx]
      norm_num
    rw [hconj x] at hm
    apply eq_inv_of_mul_eq_one_right
    convert hm using 1; ring
  calc
    _ = ∑ x ∈ (Finset.univ.erase (0 : G)), (M.gaussian x)⁻¹ := by
      apply Finset.sum_congr rfl
      intro x hx
      exact heq x (Finset.ne_of_mem_erase hx)
    _ = (∑ x, (M.gaussian x)⁻¹) - 1 := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : G)), M.gaussian_zero, inv_one]
    _ = _ := by
      rw [E.multiplier_pow_three]
      simp only [MetricGroup.gaussSum]
      field_simp [M.sqrtCard_ne_zero]

/-- The conjugation law makes the zero value real, for `exists_norm_ne_one`. -/
private theorem zero_eq_re
    (hconj : ∀ x, (starRingEnd ℂ) (E x) = M.gaussian x * E x) :
    E 0 = ((E 0).re : ℂ) := by
  have hi : (E 0).im = 0 := by
    have hc := congrArg Complex.im (hconj (0 : G))
    simp only [M.gaussian_zero, one_mul, Complex.conj_im] at hc
    linarith
  apply Complex.ext
  · simp
  · simpa only [Complex.ofReal_im] using hi

/-- Positivity and the reflection law imply `E(0) > √N`, for `exists_norm_ne_one`. -/
private theorem zero_re_gt_sqrtCard
    (hs : M.sqrtCard = (Real.sqrt (Fintype.card G) : ℂ))
    (hconj : ∀ x, (starRingEnd ℂ) (E x) = M.gaussian x * E x)
    (h0 : 0 < (E 0).re) : Real.sqrt (Fintype.card G) < (E 0).re := by
  have hr := E.zero_eq_re hconj
  have hz : (E 0).re ^ 2 = Real.sqrt (Fintype.card G) * (E 0).re + 1 := by
    have he := E.zero_sq
    rw [hr, hs] at he
    exact_mod_cast he
  by_contra hn
  have hle : (E 0).re ≤ Real.sqrt (Fintype.card G) := le_of_not_gt hn
  have hm := mul_nonpos_of_nonneg_of_nonpos h0.le (sub_nonpos.mpr hle)
  nlinarith


/-- The Fourier multiplier has norm one, for `exists_norm_ne_one`. -/
private theorem norm_multiplier
    (hs : M.sqrtCard = (Real.sqrt (Fintype.card G) : ℂ)) :
    ‖E.multiplier‖ = 1 := by
  have hcube : ‖E.multiplier ^ 3‖ = 1 := by
    rw [E.multiplier_pow_three]
    exact M.norm_gaussSum hs
  apply (pow_left_inj₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : 3 ≠ 0)).mp
  simpa only [norm_pow, one_pow] using hcube

/-- The first sum in Lemma 7 has norm greater than `√N(√N - 1)`, for
`exists_norm_ne_one`. -/
private theorem norm_sum_erase_zero_gt
    (hs : M.sqrtCard = (Real.sqrt (Fintype.card G) : ℂ))
    (hconj : ∀ x, (starRingEnd ℂ) (E x) = M.gaussian x * E x)
    (h0 : 0 < (E 0).re) (hN : 25 ≤ Fintype.card G) :
    Real.sqrt (Fintype.card G) * (Real.sqrt (Fintype.card G) - 1) <
      ‖∑ x ∈ (Finset.univ.erase (0 : G)), E x‖ := by
  let t : ℝ := Real.sqrt (Fintype.card G)
  have ht : 5 ≤ t := by
    apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr
    exact_mod_cast hN
  have hzeroNorm : ‖E 0‖ = (E 0).re := by
    rw [E.zero_eq_re hconj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]
    simp
  have hdiff : t - 1 ≤ ‖E.multiplier * M.sqrtCard - 1‖ := by
    have hh := norm_sub_norm_le (E.multiplier * M.sqrtCard) (1 : ℂ)
    simpa only [norm_mul, E.norm_multiplier hs, one_mul, hs, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), norm_one, t] using hh
  calc
    _ < (E 0).re * (t - 1) := by
      exact mul_lt_mul_of_pos_right (E.zero_re_gt_sqrtCard hs hconj h0)
        (by linarith)
    _ ≤ (E 0).re * ‖E.multiplier * M.sqrtCard - 1‖ :=
      mul_le_mul_of_nonneg_left hdiff h0.le
    _ = _ := by rw [E.sum_erase_zero, norm_mul, hzeroNorm]

/-- The second sum in Lemma 7 has norm at most `√N + 1`, for
`exists_norm_ne_one`. -/
private theorem norm_sum_sq_erase_zero_le
    (hs : M.sqrtCard = (Real.sqrt (Fintype.card G) : ℂ))
    (hconj : ∀ x, (starRingEnd ℂ) (E x) = M.gaussian x * E x)
    (hunit : ∀ x : G, x ≠ 0 → ‖E x‖ = 1) :
    ‖∑ x ∈ (Finset.univ.erase (0 : G)), E x ^ 2‖ ≤
      Real.sqrt (Fintype.card G) + 1 := by
  rw [E.sum_sq_erase_zero hconj hunit]
  have hcube : ‖E.multiplier ^ 3‖ = 1 := by
    rw [E.multiplier_pow_three]
    exact M.norm_gaussSum hs
  have hh := norm_sub_le (E.multiplier ^ 3 * M.sqrtCard) (1 : ℂ)
  simpa only [norm_mul, hcube, one_mul, hs, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), norm_one] using hh

/-- Cauchy–Schwarz and the second sum give the upper bound in Lemma 7, for
`exists_norm_ne_one`. -/
private theorem norm_sum_erase_zero_cs
    (hs : M.sqrtCard = (Real.sqrt (Fintype.card G) : ℂ))
    (hconj : ∀ x, (starRingEnd ℂ) (E x) = M.gaussian x * E x)
    (hunit : ∀ x : G, x ≠ 0 → ‖E x‖ = 1) :
    2 * ‖∑ x ∈ (Finset.univ.erase (0 : G)), E x‖ ^ 2 ≤
      ((Fintype.card G : ℝ) - 1) *
        ((Fintype.card G : ℝ) + Real.sqrt (Fintype.card G)) := by
  let s := Finset.univ.erase (0 : G)
  have hcard : (s.card : ℝ) = (Fintype.card G : ℝ) - 1 := by
    dsimp [s]
    rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : G)), Finset.card_univ,
      Nat.cast_sub (Fintype.card_pos : 1 ≤ Fintype.card G)]
    norm_num
  calc
    _ ≤ (s.card : ℝ) * ((s.card : ℝ) + ‖∑ x ∈ s, E x ^ 2‖) :=
      norm_sum_sq_le_card_add_norm_sq s E
        (fun x hx => hunit x (Finset.ne_of_mem_erase hx))
    _ ≤ (s.card : ℝ) * ((s.card : ℝ) +
        (Real.sqrt (Fintype.card G) + 1)) := by
      gcongr
      exact E.norm_sum_sq_erase_zero_le hs hconj hunit
    _ = _ := by rw [hcard]; ring

end FiniteQuantumDilog

/-- **[RW26b, Radchenko, Wheeler (2026b), Section 7.1, Lemma 7], abstract form**: a finite quantum
dilogarithm over `ℂ` with the conjugation law `conj E(x) = ⟨x⟩E(x)`, `s = √N`, a positive value
at zero, and `N ≥ 25` has a nonzero argument with `|E(x)| ≠ 1`. -/
theorem FiniteQuantumDilog.exists_norm_ne_one {M : MetricGroup G ℂ}
    (E : FiniteQuantumDilog M) (hs : M.sqrtCard = (Real.sqrt (Fintype.card G) : ℂ))
    (hconj : ∀ x, conj (E x) = M.gaussian x * E x) (h0 : 0 < (E 0).re)
    (hN : 25 ≤ Fintype.card G) : ∃ x, x ≠ 0 ∧ ‖E x‖ ≠ 1 := by
  classical
  by_contra hn
  push Not at hn
  have hunit (x : G) (hx : x ≠ 0) : ‖E x‖ = 1 := hn x hx
  let N := Fintype.card G
  let t : ℝ := Real.sqrt N
  let s := Finset.univ.erase (0 : G)
  have ht : 5 ≤ t := by
    apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr
    exact_mod_cast hN
  have hS1 := E.norm_sum_erase_zero_gt hs hconj h0 hN
  have hcs := E.norm_sum_erase_zero_cs hs hconj hunit
  have hsq : t ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hlow : (N : ℝ) * (t - 1) ^ 2 < ‖∑ x ∈ s, E x‖ ^ 2 := by
    rw [← hsq]
    have hp : 0 < (‖∑ x ∈ s, E x‖ - t * (t - 1)) *
        (‖∑ x ∈ s, E x‖ + t * (t - 1)) := by
      have htp : 0 < t * (t - 1) := mul_pos (by linarith) (by linarith)
      exact mul_pos (by linarith)
        (add_pos_of_pos_of_nonneg (lt_trans htp hS1) htp.le)
    nlinarith
  have hfinal := final_real_inequality N hN
  change ((N : ℝ) - 1) * ((N : ℝ) + t) / 2 <
    (N : ℝ) * (t - 1) ^ 2 at hfinal
  nlinarith

end MetricGroup

/-! ### Pseudolattices -/

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K} {B : PseudolatticeBasis F} {ε : K}

/-- **[RW26b, Radchenko, Wheeler (2026b), Section 7.1, Lemma 7]**: if `N = |G_{I,ε}| ≥ 25`, some
`x ∈ G_{I,ε}` with `x ∉ I` has `|E_{I,ε}(x)| ≠ 1`. -/
@[source "RW26b, Lemma 7, p. 13"]
theorem pseudolatticeDilog_exists_norm_ne_one (h : B.IsPeriod ε)
    (hN : 25 ≤ finiteDilogOrder h.matrix) :
    ∃ x : K, (ε - 1) * x ∈ B.submodule ∧ x ∉ B.submodule ∧ ‖pseudolatticeDilog h x‖ ≠ 1 := by
  let _ : NeZero (finiteDilogOrder h.matrix) :=
    finiteDilogOrder_neZero h.isAttractiveFixedPoint
  let hdet := det_sub_one_eq_neg_finiteDilogOrder h.isAttractiveFixedPoint
  let M := fixedMetricGroup h.matrix (finiteDilogOrder h.matrix) hdet
  let E := h.finiteQuantumDilog
  have hc : Fintype.card (finiteDilogGroup h.matrix) = finiteDilogOrder h.matrix :=
    card_fixedCharacteristics h.matrix (finiteDilogOrder h.matrix) hdet
  have hs : M.sqrtCard = (Real.sqrt (Fintype.card (finiteDilogGroup h.matrix)) : ℂ) := by
    rw [hc]
    exact fixedMetricGroup_sqrtCard h.matrix (finiteDilogOrder h.matrix) hdet
  have hconj (y : finiteDilogGroup h.matrix) :
      (starRingEnd ℂ) (E y) = M.gaussian y * E y := by
    obtain ⟨x, hx, hr⟩ := h.exists_residue_eq y.property
    have he : pseudolatticeDilog h x = E y := by
      rw [pseudolatticeDilog_eq_finiteDilogE h hx, hr]
      exact (h.finiteQuantumDilog_apply y).symm
    have hg : pseudolatticeGaussian h x = M.gaussian y := by
      rw [pseudolatticeGaussian_eq_fixedGaussian h hx, hr]
      rfl
    simpa only [he, hg] using pseudolatticeDilog_conj h hx
  have h0 : 0 < (E 0).re := by
    have he0 : E 0 = ((Real.sqrt (realEmbeddingAt K F.place ε) : ℝ) : ℂ) := by
      rw [h.finiteQuantumDilog_apply]
      have hx : (ε - 1) * (0 : K) ∈ B.submodule := by simp
      have he := pseudolatticeDilog_eq_finiteDilogE h hx
      rw [h.residue_zero, pseudolatticeDilog_of_mem h B.submodule.zero_mem] at he
      exact he.symm
    rw [he0, Complex.ofReal_re]
    exact Real.sqrt_pos.mpr (lt_trans zero_lt_one h.one_lt)
  have hNgroup : 25 ≤ Fintype.card (finiteDilogGroup h.matrix) := by
    rw [hc]
    exact hN
  obtain ⟨y, hy, hynorm⟩ := E.exists_norm_ne_one hs hconj h0 hNgroup
  obtain ⟨x, hx, hr⟩ := h.exists_residue_eq y.property
  refine ⟨x, hx, ?_, ?_⟩
  · intro hxi
    apply hy
    apply Subtype.ext
    exact hr.symm.trans ((h.residue_eq_zero_iff hx).mpr hxi)
  · rw [pseudolatticeDilog_eq_finiteDilogE h hx, hr]
    exact hynorm

end SIC

end
