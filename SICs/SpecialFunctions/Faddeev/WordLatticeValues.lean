/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.NearOne
import SICs.SpecialFunctions.Faddeev.WordContinuation
import SICs.SpecialFunctions.Faddeev.WordShift

/-!
# Continued Faddeev word products at lattice arguments

At a fixed point `γ·τ = τ`, the continued word product at an integral characteristic is
`Φ_{γ,0,0}(0;τ)` or `ε⁻¹Φ_{γ,0,0}(0;τ)`, `ε = j_γ(τ)`, according to the sign of its diagonal
index.

This module follows the zero-class values `F^±_γ(u) = ε^{±1/2}` of
[RW26, Radchenko, Wheeler (2026), Section 1, equation (2), `eq:fgam.def`] and the residue
bookkeeping of Section 3.2, the proof of Theorem 2, `thm:fg.equs`, for an arbitrary letter word
`γ = ∏_j T^{b_j}S` at a real irrational fixed point.

## The argument

For `r = (-ℓ, k) ∈ ℤ²`, the characteristic is the lattice point `⟨⟨r,τ⟩⟩ = kτ + ℓ`, and the
lattice shift law `faddeevWord_add_lattice_eventuallyEq` gives
`Φ_{m,n}(kτ + ℓ + w) = Φ_{m+k, n+γ₁₁k-γ₁₀ℓ}(w)` as germs at `w = 0`. With
`m = -nQPInt r γ + j`, `n = j`, and `nQPInt r γ = γ₁₀ℓ + (1-γ₁₁)k`, the two indices coincide:
the shifted product is the diagonal product `Φ_{J,J}` with `J = k - nQPInt r γ + j`.

At a fixed point, the index shift laws give
`Φ_{J,J}(w) = Φ_{0,0}(w) ∏_{i<J} (1 - q^i e(w/ε))/(1 - q^i e(w))` for `J ≥ 0`, with
`q = e(τ)`, and the inverse product for `J < 0`. As `w → 0` the factor `i = 0` tends to `1/ε`;
every other factor tends to `1`, since `e(iτ) ≠ 1` for `i ≠ 0` at irrational `τ`. Since
`Φ_{0,0}` is regular at the origin (`faddeevWordContinued_zero`), the continued value at
`kτ + ℓ` is `ε⁻¹Φ_{0,0}(0)` when `J ≥ 1` and `Φ_{0,0}(0)` otherwise. With
`Φ_{0,0}(0) = ε^{1/2}/μ_γ` these are the source's `F⁻(0)/μ_γ` and `F⁺(0)/μ_γ`.
-/

noncomputable section

open Complex Filter Topology
open scoped MatrixGroups

namespace SIC

/-! ### The diagonal product

At a fixed point the two index shift laws move along the diagonal `Φ_{j,j}` by a finite ratio of
`q`-factors, whose punctured limit at the origin is `ε⁻¹` for `j ≥ 1` and `1` otherwise. -/

/-- The finite `q`-factor ratio relating `Φ_{γ,j,j}` to `Φ_{γ,0,0}` at a fixed point with
`ε = j_γ(τ)`: `∏_{i<j} (1 - e(w/ε + iτ))/(1 - e(w + iτ))` for `j ≥ 0` and
`∏_{i<-j} (1 - e(w - (i+1)τ))/(1 - e(w/ε - (i+1)τ))` for `j < 0`. -/
def faddeevWordDiagonalRatio (ε τ : ℂ) (j : ℤ) (w : ℂ) : ℂ :=
  if 0 ≤ j then
    ∏ i ∈ Finset.range j.toNat,
      (1 - Complex.exp (2 * Real.pi * I * (w / ε + i * τ))) /
        (1 - Complex.exp (2 * Real.pi * I * (w + i * τ)))
  else
    ∏ i ∈ Finset.range (-j).toNat,
      (1 - Complex.exp (2 * Real.pi * I * (w - ((i : ℂ) + 1) * τ))) /
        (1 - Complex.exp (2 * Real.pi * I * (w / ε - ((i : ℂ) + 1) * τ)))

/-- The numerator factor in the diagonal step of `faddeevWord_diag_eventuallyEq`. -/
private def wordDiagonalNumerator (ε τ : ℂ) (i : ℤ) (w : ℂ) : ℂ :=
  1 - Complex.exp (2 * Real.pi * I * (w / ε + i * τ))

/-- The denominator factor in the diagonal step of `faddeevWord_diag_eventuallyEq`. -/
private def wordDiagonalDenominator (τ : ℂ) (i : ℤ) (w : ℂ) : ℂ :=
  1 - Complex.exp (2 * Real.pi * I * (w + i * τ))

/-- At an admissible nonzero fixed point, the word's Jacobi denominator is nonzero; this
supplies the nonzero slope in `wordDiagonalNumerator_eventually_ne_zero`. -/
private lemma wordJacobi_ne_zero (bs : List ℤ) {τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ)
    (hfix : flt (letterWord bs : Mat(2, ℤ)) τ = τ) :
    fltDenominator (letterWord bs : Mat(2, ℤ)) τ ≠ 0 := by
  have hslit : τ ∈ Complex.slitPlane := by
    have hnil : [] ∈ bs.tail.tails := by simp [List.mem_tails]
    simpa [letterWord_nil, flt_one] using (hτ [] hnil).2
  intro h
  have hz : τ = 0 := by
    change _ / fltDenominator (letterWord bs : Mat(2, ℤ)) τ = τ at hfix
    rw [h, div_zero] at hfix
    exact hfix.symm
  exact (Complex.slitPlane_ne_zero hslit) hz

/-- One simultaneous index shift multiplies a word product by its diagonal factor. -/
private lemma faddeevWord_diag_step_eventuallyEq (bs : List ℤ) (hne : bs ≠ [])
    (i : ℤ) {τ : ℂ} (hτ : FaddeevWordPeriodsSlitPlane bs τ)
    (hfix : flt (letterWord bs : Mat(2, ℤ)) τ = τ) (z : ℂ) :
    (fun w => faddeevWord bs (i + 1) (i + 1) w τ) =ᶠ[𝓝[≠] z]
      (fun w => faddeevWord bs i i w τ *
        (wordDiagonalNumerator (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) τ i w /
          wordDiagonalDenominator τ i w)) := by
  have hleft := faddeevWord_index_add_one_left_eventuallyEq bs hne i (i + 1) hτ z
  have hright := faddeevWord_index_add_one_right_eventuallyEq bs hne i i hτ z
  have hden : ∀ᶠ w in 𝓝[≠] z, wordDiagonalDenominator τ i w ≠ 0 := by
    filter_upwards [eventually_exp_affine_ne_nhdsNE (2 * Real.pi * I)
      ((2 * Real.pi * I) * (i * τ)) 1 z Complex.two_pi_I_ne_zero] with w hw
    exact sub_ne_zero.mpr (by simpa only [wordDiagonalDenominator, mul_add] using hw.symm)
  filter_upwards [hleft, hright, hden] with w hl hr hne'
  have hl' : faddeevWord bs (i + 1) (i + 1) w τ *
      wordDiagonalDenominator τ i w = faddeevWord bs i (i + 1) w τ := hl
  have hr' : faddeevWord bs i (i + 1) w τ =
      wordDiagonalNumerator (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) τ i w *
        faddeevWord bs i i w τ := by
    simpa only [wordDiagonalNumerator, hfix] using hr
  apply mul_right_cancel₀ hne'
  calc
    _ = wordDiagonalNumerator
        (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) τ i w *
          faddeevWord bs i i w τ := hl'.trans hr'
    _ = _ := by field_simp [hne']

/-- Appending a nonnegative diagonal factor extends the finite word ratio. -/
private lemma wordDiagonalRatio_succ_nat (ε τ : ℂ) (i : ℕ) (w : ℂ) :
    faddeevWordDiagonalRatio ε τ ((i : ℤ) + 1) w =
      faddeevWordDiagonalRatio ε τ i w *
        (wordDiagonalNumerator ε τ i w / wordDiagonalDenominator τ i w) := by
  simp only [faddeevWordDiagonalRatio, Int.toNat_natCast_add_one,
    Finset.prod_range_succ, neg_add_rev, Int.reduceNeg, Nat.cast_nonneg, ↓reduceIte,
    Int.toNat_natCast, wordDiagonalNumerator, Int.cast_natCast,
    wordDiagonalDenominator, ite_eq_left_iff, not_le]
  intro h
  omega

/-- Appending a negative diagonal factor extends the inverse word ratio. -/
private lemma wordDiagonalRatio_pred_nat (ε τ : ℂ) (i : ℕ) (w : ℂ) :
    faddeevWordDiagonalRatio ε τ (-((i : ℤ) + 1)) w =
      faddeevWordDiagonalRatio ε τ (-(i : ℤ)) w *
        (wordDiagonalDenominator τ (-((i : ℤ) + 1)) w /
          wordDiagonalNumerator ε τ (-((i : ℤ) + 1)) w) := by
  by_cases hi : i = 0
  · subst i
    simp [faddeevWordDiagonalRatio, wordDiagonalNumerator,
      wordDiagonalDenominator, sub_eq_add_neg]
  · have hpos : 0 < i := Nat.pos_of_ne_zero hi
    simp [faddeevWordDiagonalRatio, wordDiagonalNumerator,
      wordDiagonalDenominator, Finset.prod_range_succ, hi,
      sub_eq_add_neg, -Finset.prod_div_distrib]
    split_ifs with hguard
    · omega
    · congr 2 <;> congr 2 <;> ring_nf

/-- The word numerator has isolated zeros when its Jacobi denominator is nonzero. -/
private lemma wordDiagonalNumerator_eventually_ne_zero (ε τ : ℂ) (hε : ε ≠ 0)
    (i : ℤ) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, wordDiagonalNumerator ε τ i w ≠ 0 := by
  filter_upwards [eventually_exp_two_pi_I_affine_ne_one_nhdsNE
    ε⁻¹ (i * τ) z (inv_ne_zero hε)] with w hw
  exact sub_ne_zero.mpr (by
    simpa only [wordDiagonalNumerator, div_eq_mul_inv, mul_comm] using hw.symm)

/-- Reverse the simultaneous index shift as a punctured germ. -/
private lemma faddeevWord_diag_step_rev_eventuallyEq (bs : List ℤ) (hne : bs ≠ [])
    (i : ℤ) {τ : ℂ} (hτ : FaddeevWordPeriodsSlitPlane bs τ)
    (hfix : flt (letterWord bs : Mat(2, ℤ)) τ = τ) (z : ℂ) :
    (fun w => faddeevWord bs i i w τ) =ᶠ[𝓝[≠] z]
      (fun w => faddeevWord bs (i + 1) (i + 1) w τ *
        (wordDiagonalDenominator τ i w /
          wordDiagonalNumerator (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) τ i w)) := by
  have hden : ∀ᶠ w in 𝓝[≠] z, wordDiagonalDenominator τ i w ≠ 0 := by
    filter_upwards [eventually_exp_affine_ne_nhdsNE (2 * Real.pi * I)
      ((2 * Real.pi * I) * (i * τ)) 1 z Complex.two_pi_I_ne_zero] with w hw
    exact sub_ne_zero.mpr (by simpa only [wordDiagonalDenominator, mul_add] using hw.symm)
  filter_upwards [faddeevWord_diag_step_eventuallyEq bs hne i hτ hfix z,
    wordDiagonalNumerator_eventually_ne_zero _ _ (wordJacobi_ne_zero bs hτ hfix) i z,
    hden] with w hs hne' hd'
  rw [hs]
  field_simp [hne', hd']

/-- At a fixed point `γ·τ = τ`, `Φ_{γ,j,j}(w;τ) = Φ_{γ,0,0}(w;τ) R_j(w)` near every point, with
`R_j = faddeevWordDiagonalRatio` at `ε = j_γ(τ)`. This iterates the index shift laws of
[RW26, Radchenko, Wheeler (2026), Section 2.2] along the diagonal. -/
theorem faddeevWord_diag_eventuallyEq (bs : List ℤ) (hne : bs ≠ []) (j : ℤ) {τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (hfix : flt (letterWord bs : Mat(2, ℤ)) τ = τ)
    (z : ℂ) :
    (fun w => faddeevWord bs j j w τ) =ᶠ[𝓝[≠] z]
      fun w => faddeevWord bs 0 0 w τ *
        faddeevWordDiagonalRatio (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) τ j w := by
  induction j using Int.induction_on with
  | zero => simp [faddeevWordDiagonalRatio]
  | succ i hi =>
    filter_upwards [faddeevWord_diag_step_eventuallyEq bs hne i hτ hfix z, hi]
      with w hs hiw
    rw [hs, hiw, wordDiagonalRatio_succ_nat]
    ring
  | pred i hi =>
    have hrev := faddeevWord_diag_step_rev_eventuallyEq bs hne
      (-((i : ℤ) + 1)) hτ hfix z
    filter_upwards [hrev, hi] with w hr hiw
    have hindex : -((i : ℤ) + 1) + 1 = -(i : ℤ) := by omega
    rw [hindex, hiw] at hr
    have hr' : faddeevWord bs (-((i : ℤ) + 1)) (-((i : ℤ) + 1)) w τ =
        faddeevWord bs 0 0 w τ *
          faddeevWordDiagonalRatio (fltDenominator (letterWord bs : Mat(2, ℤ)) τ)
            τ (-((i : ℤ) + 1)) w := by
      rw [hr, wordDiagonalRatio_pred_nat]
      ring
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hr'

/-- A nonzero power of `e(τ)` is not one when `τ` is real and irrational; used by
`tendsto_faddeevWordDiagonalRatio_zero`. -/
private lemma wordDiagonalDenominator_zero_ne {τ : ℝ} (hτ : Irrational τ)
    (i : ℤ) (hi : i ≠ 0) :
    wordDiagonalDenominator τ i 0 ≠ 0 := by
  have hreal : ∀ n : ℤ, (i : ℝ) * τ ≠ n := by
    intro n hn
    have hrel : (((i : ℤ) : ℚ) : ℝ) * τ = (((n : ℤ) : ℚ) : ℝ) := by
      simpa using hn
    exact hi (by exact_mod_cast (ratCast_eq_zero_of_irrational_mul hτ hrel).1)
  simpa [wordDiagonalDenominator] using
    one_sub_exp_two_pi_I_ne_zero_of_forall_ne_int ((i : ℝ) * τ) hreal

/-- Every nonzero-index diagonal quotient tends to one. -/
private lemma tendsto_wordDiagonalQuotient_of_ne_zero {ε τ : ℝ} (hτ : Irrational τ)
    (i : ℤ) (hi : i ≠ 0) :
    Tendsto (fun w => wordDiagonalNumerator ε τ i w / wordDiagonalDenominator τ i w)
      (𝓝[≠] 0) (𝓝 1) := by
  have hA : ContinuousAt (wordDiagonalNumerator ε τ i) 0 := by
    unfold wordDiagonalNumerator
    fun_prop
  have hB : ContinuousAt (wordDiagonalDenominator τ i) 0 := by
    unfold wordDiagonalDenominator
    fun_prop
  have heq : wordDiagonalNumerator ε τ i 0 = wordDiagonalDenominator τ i 0 := by
    simp [wordDiagonalNumerator, wordDiagonalDenominator]
  have hne := wordDiagonalDenominator_zero_ne hτ i hi
  convert (hA.tendsto.mono_left nhdsWithin_le_nhds).div
    (hB.tendsto.mono_left nhdsWithin_le_nhds) hne using 1
  simp [heq, hne]

/-- The inverse of a nonzero-index diagonal quotient also tends to one. -/
private lemma tendsto_wordDiagonalQuotient_inv_of_ne_zero {ε τ : ℝ} (hτ : Irrational τ)
    (i : ℤ) (hi : i ≠ 0) :
    Tendsto (fun w => wordDiagonalDenominator τ i w / wordDiagonalNumerator ε τ i w)
      (𝓝[≠] 0) (𝓝 1) := by
  simpa only [inv_div, inv_one] using
    (tendsto_wordDiagonalQuotient_of_ne_zero (ε := ε) hτ i hi).inv₀ one_ne_zero

/-- The exceptional diagonal quotient at index zero tends to `ε⁻¹`. -/
private lemma tendsto_wordDiagonalQuotient_zero {ε τ : ℝ} (hε : ε ≠ 0) :
    Tendsto (fun w => wordDiagonalNumerator ε τ 0 w /
      wordDiagonalDenominator τ 0 w) (𝓝[≠] 0)
      (𝓝 ((ε : ℂ)⁻¹)) := by
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  have hlim := tendsto_one_sub_exp_mul_div ((2 * Real.pi * I) / (ε : ℂ))
    (2 * Real.pi * I) Complex.two_pi_I_ne_zero
  convert hlim using 1
  · funext w
    simp only [wordDiagonalNumerator, wordDiagonalDenominator,
      Int.cast_zero, zero_mul, add_zero]
    congr 2
    field_simp
  · field_simp [Complex.two_pi_I_ne_zero, hε']

/-- Positive induction step for the diagonal ratio's punctured limit. -/
private lemma tendsto_wordDiagonalRatio_succ_nat {ε τ : ℝ} (hτ : Irrational τ)
    (hε : ε ≠ 0) (i : ℕ)
    (hi : Tendsto (faddeevWordDiagonalRatio ε τ i) (𝓝[≠] 0)
      (𝓝 (if 1 ≤ (i : ℤ) then (ε : ℂ)⁻¹ else 1))) :
    Tendsto (faddeevWordDiagonalRatio ε τ ((i : ℤ) + 1)) (𝓝[≠] 0)
      (𝓝 (if 1 ≤ (i : ℤ) + 1 then (ε : ℂ)⁻¹ else 1)) := by
  have hfun : faddeevWordDiagonalRatio ε τ ((i : ℤ) + 1) =
      fun w => faddeevWordDiagonalRatio ε τ i w *
        (wordDiagonalNumerator ε τ i w / wordDiagonalDenominator τ i w) :=
    funext (wordDiagonalRatio_succ_nat ε τ i)
  rw [hfun]
  by_cases hi0 : i = 0
  · subst i
    have h := hi.mul (tendsto_wordDiagonalQuotient_zero (τ := τ) hε)
    simpa using h
  · have hfactor := tendsto_wordDiagonalQuotient_of_ne_zero
      (ε := ε) hτ i (by exact_mod_cast hi0)
    have h := hi.mul hfactor
    have hipos : (1 : ℤ) ≤ i := by omega
    have hjpos : (1 : ℤ) ≤ (i : ℤ) + 1 := by omega
    simpa [hipos, hjpos] using h

/-- Negative induction step for the diagonal ratio's punctured limit. -/
private lemma tendsto_wordDiagonalRatio_pred_nat {ε τ : ℝ} (hτ : Irrational τ)
    (i : ℕ)
    (hi : Tendsto (faddeevWordDiagonalRatio ε τ (-(i : ℤ))) (𝓝[≠] 0)
      (𝓝 (if 1 ≤ -(i : ℤ) then (ε : ℂ)⁻¹ else 1))) :
    Tendsto (faddeevWordDiagonalRatio ε τ (-(i : ℤ) - 1)) (𝓝[≠] 0)
      (𝓝 (if 1 ≤ -(i : ℤ) - 1 then (ε : ℂ)⁻¹ else 1)) := by
  have hfun : faddeevWordDiagonalRatio ε τ (-((i : ℤ) + 1)) =
      fun w => faddeevWordDiagonalRatio ε τ (-(i : ℤ)) w *
        (wordDiagonalDenominator τ (-((i : ℤ) + 1)) w /
          wordDiagonalNumerator ε τ (-((i : ℤ) + 1)) w) :=
    funext (wordDiagonalRatio_pred_nat ε τ i)
  have hindex : -((i : ℤ) + 1) ≠ 0 := by omega
  have hfactor := tendsto_wordDiagonalQuotient_inv_of_ne_zero
    (ε := ε) hτ (-((i : ℤ) + 1)) hindex
  have h := hi.mul hfactor
  have hneg : ¬(1 : ℤ) ≤ -((i : ℤ) + 1) := by omega
  have hineg : ¬(1 : ℤ) ≤ -(i : ℤ) := by omega
  have heq : -(i : ℤ) - 1 = -((i : ℤ) + 1) := by omega
  rw [heq, hfun]
  simpa only [ite_eq_right hneg, ite_eq_right hineg, one_mul] using h

/-- At a real irrational `τ` and real `ε ≠ 0`, the diagonal ratio tends to `ε⁻¹` for `j ≥ 1`
and to `1` otherwise through the punctured neighborhood of the origin. -/
theorem tendsto_faddeevWordDiagonalRatio_zero {ε τ : ℝ} (hτ : Irrational τ) (hε : ε ≠ 0)
    (j : ℤ) :
    Tendsto (faddeevWordDiagonalRatio ε τ j) (𝓝[≠] 0)
      (𝓝 (if 1 ≤ j then (ε : ℂ)⁻¹ else 1)) := by
  induction j using Int.induction_on with
  | zero =>
    change Tendsto (fun _ : ℂ => (1 : ℂ)) (𝓝[≠] 0) (𝓝 1)
    exact tendsto_const_nhds
  | succ i hi => exact tendsto_wordDiagonalRatio_succ_nat hτ hε i hi
  | pred i hi => exact tendsto_wordDiagonalRatio_pred_nat hτ i hi

/-- At a real irrational fixed point with positive word periods, the continued diagonal product
at the origin is `Φ^cont_{γ,j,j}(0) = ε⁻¹Φ_{γ,0,0}(0)` for `j ≥ 1` and `Φ_{γ,0,0}(0)` otherwise,
`ε = j_γ(τ)`. -/
theorem faddeevWordContinued_diag_zero (bs : List ℤ) (hne : bs ≠ []) {τ : ℝ}
    (hirr : Irrational τ)
    (hpos : ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ)
    (hfix : flt (letterWord bs : Mat(2, ℤ)) τ = τ) (j : ℤ) :
    faddeevWordContinued bs j j 0 τ =
      (if 1 ≤ j then ((fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℝ) : ℂ)⁻¹ else 1) *
        faddeevWord bs 0 0 0 τ := by
  have hτ := faddeevWordPeriodsSlitPlane_of_irrational bs hirr hpos
  have hfixC : flt (letterWord bs : Mat(2, ℤ)) (τ : ℂ) = (τ : ℂ) := by
    exact_mod_cast hfix
  have hε : fltDenominator (letterWord bs : Mat(2, ℤ)) τ ≠ 0 :=
    fltDenominator_ne_zero_of_irrational hirr (letterWord bs)
  have hbase : Tendsto (fun w => faddeevWord bs 0 0 w τ) (𝓝[≠] 0)
      (𝓝 (faddeevWord bs 0 0 0 τ)) := by
    simpa [nQPInt, nQP, fracSymplecticFormRat, faddeevWordContinued_zero bs hpos]
      using tendsto_faddeevWord_continued_characteristic bs hne hirr hpos
        (0 : Fin 2 → ℚ) 0
  have hraw : Tendsto (fun w => faddeevWord bs j j w τ) (𝓝[≠] 0)
      (𝓝 ((if 1 ≤ j then
        ((fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℝ) : ℂ)⁻¹ else 1) *
        faddeevWord bs 0 0 0 τ)) := by
    have hdiag : (fun w => faddeevWord bs j j w τ) =ᶠ[𝓝[≠] 0]
        (fun w => faddeevWord bs 0 0 w τ *
          faddeevWordDiagonalRatio
            ((fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℝ) : ℂ) τ j w) := by
      simpa only [← ofReal_fltDenominator] using
        faddeevWord_diag_eventuallyEq bs hne j hτ hfixC 0
    convert (hbase.mul (tendsto_faddeevWordDiagonalRatio_zero hirr hε j)).congr'
      hdiag.symm using 1
    ring_nf
  have hcont : Tendsto (fun w => faddeevWord bs j j w τ) (𝓝[≠] 0)
      (𝓝 (faddeevWordContinued bs j j 0 τ)) := by
    simpa [nQPInt, nQP, fracSymplecticFormRat]
      using tendsto_faddeevWord_continued_characteristic bs hne hirr hpos
        (0 : Fin 2 → ℚ) j
  exact tendsto_nhds_unique hcont hraw

/-! ### The zero class

At an integral characteristic the lattice shift law turns the indices `(-nQPInt r γ + j, j)` into
the diagonal pair `(J, J)` at the origin. -/

/-- Integral-characteristic lattice translation makes the two shifted word indices equal;
used by `faddeevWordContinued_zeroClass`. -/
private lemma faddeevWord_zeroClass_shift_eventuallyEq (bs : List ℤ) (hne : bs ≠ [])
    {τ : ℝ} (hτ : FaddeevWordPeriodsSlitPlane bs τ)
    {r : Fin 2 → ℚ} (hr : IsIntegralIndex r) (j : ℤ) :
    (fun w => faddeevWord bs (-nQPInt r (letterWord bs : Mat(2, ℤ)) + j) j
      (w + (fracSymplecticFormRat r τ : ℂ)) τ) =ᶠ[𝓝[≠] 0]
      (fun w => faddeevWord bs
        ((r 1).num - nQPInt r (letterWord bs : Mat(2, ℤ)) + j)
        ((r 1).num - nQPInt r (letterWord bs : Mat(2, ℤ)) + j) w τ) := by
  have hz := fracSymplecticFormRat_of_isIntegralIndex hr (τ : ℂ)
  have hN := nQPInt_of_isIntegralIndex hr (letterWord bs : Mat(2, ℤ))
  let N := nQPInt r (letterWord bs : Mat(2, ℤ))
  let J := (r 1).num - N + j
  have hleft : (-N + j) + (r 1).num = J := by dsimp [J]; ring
  have hright : j + (r 1).num * letterWord bs 1 1 -
      (-(r 0).num) * letterWord bs 1 0 = J := by
    dsimp [J, N]
    rw [hN]
    ring
  have hshift := faddeevWord_add_lattice_eventuallyEq
    bs hne (-N + j) j (r 1).num (-(r 0).num) hτ 0
  rw [hleft, hright] at hshift
  simpa only [hz, sub_eq_add_neg, Int.cast_neg, add_assoc, J, N] using hshift

/-- A translated word-product germ equality identifies continued values at analytic points;
used by `faddeevWordContinued_zeroClass`. -/
private lemma wordContinued_eq_of_shift_eventuallyEq
    (bs : List ℤ) (m n m' n' : ℤ) {τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (z : ℂ)
    (hshift : (fun w => faddeevWord bs m n (w + z) τ) =ᶠ[𝓝[≠] 0]
      fun w => faddeevWord bs m' n' w τ)
    (ha : AnalyticAt ℂ (fun w => faddeevWordContinued bs m n w τ) z)
    (hb : AnalyticAt ℂ (fun w => faddeevWordContinued bs m' n' w τ) 0) :
    faddeevWordContinued bs m n z τ =
      faddeevWordContinued bs m' n' 0 τ := by
  have ht : Tendsto (fun w : ℂ => w + z) (𝓝[≠] 0) (𝓝 z) := by
    convert ((tendsto_id.add_const z).mono_left nhdsWithin_le_nhds) using 1 <;> simp
  have hleft : Tendsto (fun w => faddeevWord bs m n (w + z) τ)
      (𝓝[≠] 0) (𝓝 (faddeevWordContinued bs m n z τ)) := by
    have hc := ha.continuousAt.tendsto.comp ht
    have heq := eventuallyEq_comp_add_const_nhdsNE (z := 0) (c := z)
      (show (fun w => faddeevWord bs m n w τ) =ᶠ[𝓝[≠] (0 + z)]
        (fun w => faddeevWordContinued bs m n w τ) by
          simpa only [zero_add] using faddeevWord_eventuallyEq_continued bs m n hτ z)
    exact hc.congr' heq.symm
  have hright : Tendsto (fun w => faddeevWord bs m' n' w τ) (𝓝[≠] 0)
      (𝓝 (faddeevWordContinued bs m' n' 0 τ)) := by
    exact (hb.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (faddeevWord_eventuallyEq_continued bs m' n' hτ 0).symm
  exact tendsto_nhds_unique (hright.congr' hshift.symm) hleft |>.symm

/-- **The type rule at the zero class.** At a real irrational fixed point `γ·τ = τ` with
positive word periods and `r ∈ ℤ²`, the continued product
`Φ^cont_{γ,-n_QP+j,j}(⟨⟨r,τ⟩⟩)` is `ε⁻¹Φ_{γ,0,0}(0)` when `J = r₁ - n_QP(r,γ) + j ≥ 1` and
`Φ_{γ,0,0}(0)` otherwise, `ε = j_γ(τ)`. These are the zero-class values that the residue
computation of [RW26, Radchenko, Wheeler (2026), Section 3.2] meets at lattice arguments. -/
theorem faddeevWordContinued_zeroClass (bs : List ℤ) (hne : bs ≠ []) {τ : ℝ}
    (hirr : Irrational τ)
    (hpos : ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ)
    (hfix : flt (letterWord bs : Mat(2, ℤ)) τ = τ)
    {r : Fin 2 → ℚ} (hr : IsIntegralIndex r) (j : ℤ) :
    faddeevWordContinued bs (-nQPInt r (letterWord bs : Mat(2, ℤ)) + j) j
        (fracSymplecticFormRat r τ : ℂ) τ =
      (if 1 ≤ (r 1).num - nQPInt r (letterWord bs : Mat(2, ℤ)) + j then
          ((fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℝ) : ℂ)⁻¹ else 1) *
        faddeevWord bs 0 0 0 τ := by
  have hτ := faddeevWordPeriodsSlitPlane_of_irrational bs hirr hpos
  let J : ℤ := (r 1).num - nQPInt r (letterWord bs : Mat(2, ℤ)) + j
  have hshift := faddeevWord_zeroClass_shift_eventuallyEq bs hne hτ hr j
  have hanalytic : AnalyticAt ℂ
      (fun w => faddeevWordContinued bs
        (-nQPInt r (letterWord bs : Mat(2, ℤ)) + j) j w τ)
      (fracSymplecticFormRat r τ : ℂ) := by
    simpa only [← ofReal_fracSymplecticFormRat] using
      analyticAt_faddeevWordContinued_characteristic bs hne hirr hpos r j
  have hdiagAnalytic : AnalyticAt ℂ
      (fun w => faddeevWordContinued bs J J w τ) 0 := by
    simpa [nQPInt, nQP, fracSymplecticFormRat] using
      analyticAt_faddeevWordContinued_characteristic bs hne hirr hpos
        (0 : Fin 2 → ℚ) J
  have hval := wordContinued_eq_of_shift_eventuallyEq bs
    (-nQPInt r (letterWord bs : Mat(2, ℤ)) + j) j J J hτ
    (fracSymplecticFormRat r τ : ℂ) hshift hanalytic hdiagAnalytic
  rw [hval, faddeevWordContinued_diag_zero bs hne hirr hpos hfix J]

end SIC

end
