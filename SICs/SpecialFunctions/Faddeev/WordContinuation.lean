/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.WordDivisor

/-!
# Continued Faddeev word products

The meromorphic normal form of the Faddeev word product in its argument, and its regular nonzero
value at every characteristic of a real irrational period.

This module follows the special values of [RW26, Radchenko, Wheeler (2026), equation (2),
`eq:fgam.def`], the zero and pole support in Section 2.2, and the product expression of
Proposition 2(ii), equation (20), `eq:modulartofaddeevCF`, for an arbitrary letter word
`γ = ∏_j T^{b_j}S`.

## The argument

At slit-plane word periods the word product `Φ_{γ,m,n}(·;τ)` is meromorphic on the whole
argument plane. Its Mathlib normal form changes only the point value at each singularity, so the
pointwise definition below agrees with the single global normal form; it has the raw product's
punctured germs and meromorphic orders, and it equals the raw product off the period lattice,
where the product is analytic. At the origin every factor `Φ_{S,0,0}` of `Φ_{γ,0,0}` is regular,
so the continued value there is the raw value.

At `z = ⟨⟨r,τ⟩⟩` with real irrational `τ` and positive word periods, the order of the product
with indices `(-nQPInt r γ + j, j)` is zero. For `r ∉ ℤ²`, `z` is off the lattice. For
`r = (-ℓ, k) ∈ ℤ²`, `z = kτ + ℓ` and `nQPInt r γ = γ₁₀ℓ + (1-γ₁₁)k`, so both indicators in
the exact lattice-order formula `meromorphicOrderAt_faddeevWord_real_lattice` have the argument
`γ₁₁k - γ₁₀ℓ + j`. Thus the continued value is analytic and nonzero there, and the raw product
tends to it through the punctured neighborhood.

At a genuine pole the normal form assigns the total value zero; it does not turn the pole into a
finite value. The construction varies only `z` at a fixed period.
-/

noncomputable section

open Filter Topology
open scoped MatrixGroups

namespace SIC

/-! ### Global normal form in the argument

The pointwise definition is identified with Mathlib's global normal form, which supplies its
meromorphic API and its comparison with the raw punctured germs. -/

/-- The continued value of the word product `Φ_{γ,m,n}(z;τ)` in its argument `z`, the period
`τ` fixed: the value at `z` of the meromorphic normal form of `w ↦ Φ_{γ,m,n}(w;τ)`. At nonzero
meromorphic order this totalized value is zero. -/
def faddeevWordContinued (bs : List ℤ) (m n : ℤ) (z τ : ℂ) : ℂ :=
  toMeromorphicNFAt (fun w => faddeevWord bs m n w τ) z z

/-- The raw word product is meromorphic on the whole argument plane; used by
`faddeevWordContinued_eq_toMeromorphicNFOn`. -/
private lemma meromorphicOn_faddeevWord (bs : List ℤ) (m n : ℤ) {τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) :
    MeromorphicOn (fun w => faddeevWord bs m n w τ) Set.univ :=
  fun z _ => meromorphicAt_faddeevWord bs m n hτ z

/-- At slit-plane word periods the continued word product is the global meromorphic normal form
of the raw product on the whole argument plane. -/
theorem faddeevWordContinued_eq_toMeromorphicNFOn (bs : List ℤ) (m n : ℤ) {τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) :
    (fun z => faddeevWordContinued bs m n z τ) =
      toMeromorphicNFOn (fun w => faddeevWord bs m n w τ) Set.univ := by
  funext z
  rw [faddeevWordContinued,
    toMeromorphicNFOn_eq_toMeromorphicNFAt
      (meromorphicOn_faddeevWord bs m n hτ) (Set.mem_univ z)]

/-- The continued word product is in meromorphic normal form at every point. -/
theorem meromorphicNFAt_faddeevWordContinued (bs : List ℤ) (m n : ℤ) {τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (z : ℂ) :
    MeromorphicNFAt (fun w => faddeevWordContinued bs m n w τ) z := by
  rw [faddeevWordContinued_eq_toMeromorphicNFOn bs m n hτ]
  exact meromorphicNFOn_toMeromorphicNFOn _ _ (Set.mem_univ z)

/-- The raw and continued word products have the same punctured germ at every point. -/
theorem faddeevWord_eventuallyEq_continued (bs : List ℤ) (m n : ℤ) {τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (z : ℂ) :
    (fun w => faddeevWord bs m n w τ) =ᶠ[𝓝[≠] z]
      fun w => faddeevWordContinued bs m n w τ := by
  rw [faddeevWordContinued_eq_toMeromorphicNFOn bs m n hτ]
  exact (meromorphicOn_faddeevWord bs m n hτ
    |>.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)).symm

/-- The raw and continued word products have the same meromorphic order at every point. -/
theorem meromorphicOrderAt_faddeevWordContinued (bs : List ℤ) (m n : ℤ) {τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (z : ℂ) :
    meromorphicOrderAt (fun w => faddeevWordContinued bs m n w τ) z =
      meromorphicOrderAt (fun w => faddeevWord bs m n w τ) z := by
  rw [faddeevWordContinued_eq_toMeromorphicNFOn bs m n hτ,
    meromorphicOrderAt_toMeromorphicNFOn
      (meromorphicOn_faddeevWord bs m n hτ) (Set.mem_univ z)]

/-- Off the period lattice the continued word product is the raw product. -/
theorem faddeevWordContinued_eq_of_notMem (bs : List ℤ) (m n : ℤ) {z τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (hz : ¬ IsPeriodLatticePoint τ z) :
    faddeevWordContinued bs m n z τ = faddeevWord bs m n z τ := by
  unfold faddeevWordContinued
  rw [toMeromorphicNFAt_eq_self.mpr
    (analyticAt_faddeevWord bs m n hτ
      (faddeevWordGammaRegular_of_notMem bs m n hτ hz)).meromorphicNFAt]

/-- A Faddeev generator at the origin is analytic for a period in the right half-plane;
used by `analyticAt_faddeevWord_zero`. -/
private lemma analyticAt_faddeevS_zero_of_re_pos {σ : ℂ} (hσ : 0 < σ.re) :
    AnalyticAt ℂ (fun z => faddeevS z σ) 0 := by
  have hslit : σ ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hσ)
  exact analyticAt_faddeevS 0 σ hslit
    (by simpa using barnesDoubleGammaInv_ne_zero_of_re_pos σ σ hslit hσ.le hσ)

/-- Every factor of the unshifted word product is analytic at the origin when its real
period is positive; used by `faddeevWordContinued_zero`. -/
private lemma analyticAt_faddeevWord_zero (bs : List ℤ) {τ : ℝ}
    (hpos : ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ) :
    AnalyticAt ℂ (fun z => faddeevWord bs 0 0 z τ) 0 := by
  induction bs with
  | nil => exact analyticAt_const
  | cons a bs ih =>
      cases bs with
      | nil =>
          have hτ : 0 < τ := by
            simpa [letterWord_nil, flt_one] using hpos [] (by simp)
          simpa [faddeevWord_singleton] using
            (analyticAt_faddeevS_zero_of_re_pos
              (σ := (τ : ℂ)) (by simpa using hτ))
      | cons b bs =>
          have hheadpos : 0 < flt (letterWord (b :: bs) : Mat(2, ℤ)) τ :=
            hpos (b :: bs) (by simp)
          have htailpos : ∀ w ∈ (b :: bs).tail.tails,
              0 < flt (letterWord w : Mat(2, ℤ)) τ :=
            forall_tail_tails_of_cons a (b :: bs) hpos
          have hfirst : AnalyticAt ℂ (fun z : ℂ => faddeevS
              (z / fltDenominator (letterWord (b :: bs) : Mat(2, ℤ)) (τ : ℂ) - 0)
              (flt (letterWord (b :: bs) : Mat(2, ℤ)) (τ : ℂ))) 0 := by
            have hσ : 0 < (flt (letterWord (b :: bs) : Mat(2, ℤ)) (τ : ℂ)).re := by
              simpa only [← ofReal_flt, Complex.ofReal_re] using hheadpos
            have hfactor : AnalyticAt ℂ
                (fun z => faddeevS z
                  (flt (letterWord (b :: bs) : Mat(2, ℤ)) (τ : ℂ)))
                ((fun z : ℂ => z /
                  fltDenominator (letterWord (b :: bs) : Mat(2, ℤ)) (τ : ℂ)) 0) := by
              simpa using analyticAt_faddeevS_zero_of_re_pos hσ
            simpa only [Int.cast_zero, sub_zero, Function.comp_def] using
              hfactor.comp
                (f := fun z : ℂ => z /
                  fltDenominator (letterWord (b :: bs) : Mat(2, ℤ)) (τ : ℂ))
                (analyticAt_id.div_const)
          have hrest := ih htailpos
          convert hfirst.mul hrest using 1
          funext z
          simpa only [Pi.mul_apply, Int.cast_zero] using
            faddeevWord_cons_cons a b bs 0 0 z τ

/-- At the origin and positive real word periods, the continued product with indices `(0,0)` is
the raw product: every factor `Φ_{S,0,0}` is regular at its argument `0`. -/
theorem faddeevWordContinued_zero (bs : List ℤ) {τ : ℝ}
    (hpos : ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ) :
    faddeevWordContinued bs 0 0 0 τ = faddeevWord bs 0 0 0 τ := by
  unfold faddeevWordContinued
  rw [toMeromorphicNFAt_eq_self.mpr (analyticAt_faddeevWord_zero bs hpos).meromorphicNFAt]

/-! ### Characteristics

At `z = ⟨⟨r,τ⟩⟩` the indices `(-nQPInt r γ + j, j)` make the order zero: off `ℤ²` because `z` is
off the lattice, on `ℤ²` because the two indicators of the lattice-order formula agree. -/

/-- At a real irrational period with positive word periods, the word product with indices
`(-nQPInt r γ + j, j)` has meromorphic order zero at `z = ⟨⟨r,τ⟩⟩`, for every rational `r`
and integer `j`. This is the regularity of the values `F^±_γ` of
[RW26, Radchenko, Wheeler (2026), equation (2), `eq:fgam.def`] at their characteristics. -/
theorem meromorphicOrderAt_faddeevWord_characteristic (bs : List ℤ) (hne : bs ≠ [])
    {τ : ℝ} (hirr : Irrational τ)
    (hpos : ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ)
    (r : Fin 2 → ℚ) (j : ℤ) :
    meromorphicOrderAt
        (fun w => faddeevWord bs (-nQPInt r (letterWord bs : Mat(2, ℤ)) + j) j w τ)
        (fracSymplecticFormRat r τ : ℂ) = 0 := by
  by_cases hr : IsIntegralIndex r
  · obtain ⟨r₀, hr₀⟩ := hr 0
    obtain ⟨r₁, hr₁⟩ := hr 1
    let k : ℤ := r₁
    let l : ℤ := -r₀
    have hz : (fracSymplecticFormRat r τ : ℂ) =
        (k : ℂ) * (τ : ℂ) + l := by
      rw [fracSymplecticFormRat_of_isIntegralIndex hr (τ : ℂ), hr₀, hr₁]
      simp only [k, l, Rat.num_intCast, Int.cast_neg]
      ring
    have hN : nQPInt r (letterWord bs : Mat(2, ℤ)) =
        letterWord bs 1 0 * l + (1 - letterWord bs 1 1) * k := by
      rw [nQPInt_of_isIntegralIndex hr, hr₀, hr₁]
      simp only [k, l, Rat.num_intCast]
      ring
    have hthreshold : k + (-nQPInt r (letterWord bs : Mat(2, ℤ)) + j) =
        letterWord bs 1 1 * k - letterWord bs 1 0 * l + j := by
      rw [hN]
      ring
    rw [hz, meromorphicOrderAt_faddeevWord_real_lattice bs hne _ _ k l hirr hpos,
      hthreshold]
    simp
  · have hoff : ¬ IsPeriodLatticePoint (τ : ℂ) (fracSymplecticFormRat r τ : ℂ) := by
      simpa only [ofReal_fracSymplecticFormRat] using
        (isPeriodLatticePoint_fracSymplecticFormRat_iff hirr r).not.mpr hr
    exact meromorphicOrderAt_faddeevWord_eq_zero bs _ _
      (faddeevWordPeriodsSlitPlane_of_irrational bs hirr hpos) hoff

/-- The continued word product is nonzero at a characteristic; see
`meromorphicOrderAt_faddeevWord_characteristic`. -/
theorem faddeevWordContinued_characteristic_ne_zero (bs : List ℤ) (hne : bs ≠ [])
    {τ : ℝ} (hirr : Irrational τ)
    (hpos : ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ)
    (r : Fin 2 → ℚ) (j : ℤ) :
    faddeevWordContinued bs (-nQPInt r (letterWord bs : Mat(2, ℤ)) + j) j
      (fracSymplecticFormRat r τ : ℂ) τ ≠ 0 := by
  have hτ := faddeevWordPeriodsSlitPlane_of_irrational bs hirr hpos
  apply (meromorphicNFAt_faddeevWordContinued bs _ _ hτ _
    |>.meromorphicOrderAt_eq_zero_iff).mp
  rw [meromorphicOrderAt_faddeevWordContinued bs _ _ hτ,
    meromorphicOrderAt_faddeevWord_characteristic bs hne hirr hpos r j]

/-- The continued word product is analytic at a characteristic; see
`meromorphicOrderAt_faddeevWord_characteristic`. -/
theorem analyticAt_faddeevWordContinued_characteristic (bs : List ℤ) (hne : bs ≠ [])
    {τ : ℝ} (hirr : Irrational τ)
    (hpos : ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ)
    (r : Fin 2 → ℚ) (j : ℤ) :
    AnalyticAt ℂ
      (fun w => faddeevWordContinued bs (-nQPInt r (letterWord bs : Mat(2, ℤ)) + j) j w τ)
      (fracSymplecticFormRat r τ : ℂ) := by
  have hτ := faddeevWordPeriodsSlitPlane_of_irrational bs hirr hpos
  have hnf := meromorphicNFAt_faddeevWordContinued bs
    (-nQPInt r (letterWord bs : Mat(2, ℤ)) + j) j hτ
    (fracSymplecticFormRat r τ : ℂ)
  have horder := hnf.meromorphicOrderAt_eq_zero_iff.mpr
    (faddeevWordContinued_characteristic_ne_zero bs hne hirr hpos r j)
  exact hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp (by rw [horder])

/-- The raw word product tends to its continued value at a characteristic through the punctured
neighborhood; see `meromorphicOrderAt_faddeevWord_characteristic`. -/
theorem tendsto_faddeevWord_continued_characteristic (bs : List ℤ) (hne : bs ≠ [])
    {τ : ℝ} (hirr : Irrational τ)
    (hpos : ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ)
    (r : Fin 2 → ℚ) (j : ℤ) :
    Tendsto (fun w => faddeevWord bs (-nQPInt r (letterWord bs : Mat(2, ℤ)) + j) j w τ)
      (𝓝[≠] (fracSymplecticFormRat r τ : ℂ))
      (𝓝 (faddeevWordContinued bs (-nQPInt r (letterWord bs : Mat(2, ℤ)) + j) j
        (fracSymplecticFormRat r τ : ℂ) τ)) := by
  exact (analyticAt_faddeevWordContinued_characteristic bs hne hirr hpos r j)
    |>.continuousAt.tendsto |>.mono_left nhdsWithin_le_nhds |>.congr'
      (faddeevWord_eventuallyEq_continued bs _ _
        (faddeevWordPeriodsSlitPlane_of_irrational bs hirr hpos) _).symm

end SIC

end
