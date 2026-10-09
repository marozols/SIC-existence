/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.Word.Faddeev
import SICs.Dilogarithm.Values
import SICs.SpecialFunctions.Faddeev.WordLatticeValues

/-!
# Finite dilogarithm values as Faddeev word products

At an attractive fixed point of a letter word `γ`, the finite quantum dilogarithm is
`μ_γ Φ_{γ,-n_QP,0}(⟨⟨r,τ⟩⟩;τ)` off `ℤ²` and `ε^{±1/2}` on `ℤ²`, and the continued word product
recovers both values.

This module identifies the definition of `F^±_γ` in
[RW26, Radchenko, Wheeler (2026), equation (2), `eq:fgam.def`] with `finiteDilogValue`,
which is built from the real cocycle of [AFK25, Definition 1.18, `def:shin`, equation (1.26),
`eq:shindf`], for every letter word `γ = ∏_j T^{b_j}S` whose letters after the first are at
least `2`. The principal case `γ = A_d` is proved directly in
`SICs.Principal.Dilogarithm.Faddeev.Cocycle`.

## The argument

For `r ∉ ℤ²` and `γ ∈ Γ_r` with `j_γ(τ) > 0`, the word arguments `⟨⟨r,τ⟩⟩/j_{γ_j}(τ)` avoid the
lattices `ℤγ_j·τ + ℤ` (`sigmaSLatticeFree_fracSymplecticFormRat_div`) and the word periods are
positive (`flt_letterWord_pos_of_mem_tails`), so `faddeevWord_ofReal_eq_inv_wordSigmaS` at
`n = n_QP(r,γ)` gives the reciprocal of the word quotient defining `ש^r_γ(τ)`. Hence
`F(r) = μ_γ/ש^r_γ(τ) = μ_γ Φ_{γ,0,n_QP}(⟨⟨r,τ⟩⟩;τ)`. At a fixed point, `γ ∈ Γ_r` makes the two
outer multipliers of the simultaneous index shift (16) agree at `⟨⟨r,τ⟩⟩`, so the indices
`(0,n_QP)` may be replaced by `(-n_QP+j,j)` for every `j`; at `j = 0` this is the form of the
source's definition.

At the origin, `Φ_{γ,0,0}(0;τ) = σ_γ(0,τ)⁻¹ = ש^0_γ(τ)⁻¹`, and the zero-characteristic value
`ש^0_γ(τ) = μ_γ/√ε` at a fixed point gives `Φ_{γ,0,0}(0;τ) = √ε/μ_γ`, `ε = j_γ(τ)`.

For the continued product, off `ℤ²` the characteristic is off the lattice, where the continued
product is the raw one; on `ℤ²` the type rule `faddeevWordContinued_zeroClass` gives
`ε^{-1}√ε/μ_γ` or `√ε/μ_γ`, that is `F⁻(r)/μ_γ` or `F(r)/μ_γ`.
-/

noncomputable section

open Filter Topology
open scoped MatrixGroups

namespace SIC

variable {bs : List ℤ} {τ : ℝ}

/-! ### Nonintegral characteristics

The word product with indices `(0,n_QP)` is the reciprocal real cocycle, and at a fixed
point the indices can be moved to `(-n_QP+j,j)`. -/

/-- For `r ∉ ℤ²`, `γ = ∏_j T^{b_j}S ∈ Γ_r` with letters after the first at least `2`, and
`j_γ(τ) > 0` at an irrational `τ`, the word product at `z = ⟨⟨r,τ⟩⟩` with indices
`(0,n_QP(r,γ))` is `ש^r_γ(τ)⁻¹`. This bridges [RW26, Radchenko, Wheeler (2026), equation (20),
`eq:modulartofaddeevCF`] and [AFK25, Definition 1.18, `def:shin`, equation (1.26),
`eq:shindf`]. -/
theorem faddeevWord_fracSymplecticForm (hne : bs ≠ []) (hbs : ∀ b ∈ bs.tail, 2 ≤ b)
    (hτ : Irrational τ) (hjac : 0 < fltDenominator (letterWord bs : Mat(2, ℤ)) τ)
    {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r) (hA : letterWord bs ∈ gammaSubgroup r) :
    faddeevWord bs 0 (nQPInt r (letterWord bs : Mat(2, ℤ)))
        (fracSymplecticFormRat r τ : ℂ) τ =
      (sfModularCocycleReal' r (letterWord bs) τ)⁻¹ := by
  let M := letterWord bs
  let z := fracSymplecticFormRat r τ
  let n := nQPInt r (M : Mat(2, ℤ))
  have h0 := letterWord_lowerLeft_nonneg hbs
  have hpos := flt_letterWord_pos_of_mem_tails hne hbs hτ hjac
  have hlat : ∀ w ∈ bs.tail.tails,
      SigmaSLatticeFree (flt (letterWord w : Mat(2, ℤ)) τ)
        (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ) := by
    intro w _
    exact sigmaSLatticeFree_fracSymplecticFormRat_div hτ hr _
      (fltDenominator_ne_zero_of_irrational hτ (letterWord w))
  have hmod : sfModularCocycleReal' r M τ =
      wordSigmaS z τ M h0 /
        qPochhammerFin n ((z : ℂ) / (fltDenominator (M : Mat(2, ℤ)) τ : ℂ))
          (flt (M : Mat(2, ℤ)) τ : ℂ) := by
    rw [sfModularCocycleReal'_of_mem hA,
      sfModularCocycleRealTotal_of_nonneg hA h0,
      sfModularCocycleReal_eq_of_not_isIntegralIndex hr hA h0]
    simp only [M, z, n, ofReal_fltDenominator, ofReal_flt]
  have hprod := faddeevWord_ofReal_eq_inv_wordSigmaS bs hne hbs n hpos hlat h0
  simpa only [M, z, n, ofReal_fracSymplecticFormRat] using
    hprod.trans (congrArg Inv.inv hmod.symm)

/-- `F(r) = μ_γ Φ_{γ,0,n_QP}(⟨⟨r,τ⟩⟩;τ)` for `r ∉ ℤ²` and `γ ∈ Γ_r`; this rewrites
`faddeevWord_fracSymplecticForm` through `finiteDilogValue_of_not_isIntegralIndex`. -/
theorem finiteDilogValue_eq_etaMultiplier_mul_nQPInt (hne : bs ≠ [])
    (hbs : ∀ b ∈ bs.tail, 2 ≤ b) (hτ : Irrational τ)
    (hjac : 0 < fltDenominator (letterWord bs : Mat(2, ℤ)) τ)
    {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r) (hA : letterWord bs ∈ gammaSubgroup r) :
    finiteDilogValue (letterWord bs) τ r = etaMultiplier (letterWord bs) *
      faddeevWord bs 0 (nQPInt r (letterWord bs : Mat(2, ℤ)))
        (fracSymplecticFormRat r τ : ℂ) τ := by
  rw [finiteDilogValue_of_not_isIntegralIndex _ _ hr,
    faddeevWord_fracSymplecticForm hne hbs hτ hjac hr hA]
  ring

/-- The phase equality at a word fixed point used by the index shift in
`faddeevWord_characteristic_indices`. -/
private lemma faddeevWord_characteristic_phase {bs : List ℤ} {τ : ℝ}
    (hfix : flt (letterWord bs : Mat(2, ℤ)) τ = τ)
    (hJ : fltDenominator (letterWord bs : Mat(2, ℤ)) τ ≠ 0)
    {r : Fin 2 → ℚ} (hA : letterWord bs ∈ gammaSubgroup r) :
    Complex.exp (2 * Real.pi * Complex.I * (fracSymplecticFormRat r τ : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((fracSymplecticFormRat r τ : ℂ) /
          (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) +
          nQPInt r (letterWord bs : Mat(2, ℤ)) * (τ : ℂ))) := by
  obtain ⟨c, hc⟩ := div_fltDenominator_add_nQPInt_mul hA hfix hJ
  apply exp_two_pi_I_eq_of_sub_intCast _ _ (-c)
  have hc' : (fracSymplecticFormRat r τ : ℂ) /
        (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) +
        nQPInt r (letterWord bs : Mat(2, ℤ)) * (τ : ℂ) =
      (fracSymplecticFormRat r τ : ℂ) + c := by
    exact_mod_cast hc
  simp only [Int.cast_neg]
  linear_combination -hc'

/-- At a word fixed point, the index shift identifies every diagonal translate with the
`(0,n_QP)` product; used by `etaMultiplier_mul_faddeevWordContinued`. -/
private lemma faddeevWord_characteristic_indices (hne : bs ≠ [])
    (hbs : ∀ b ∈ bs.tail, 2 ≤ b)
    (h : IsAttractiveFixedPoint (letterWord bs) τ)
    {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r)
    (hA : letterWord bs ∈ gammaSubgroup r) (j : ℤ) :
    faddeevWord bs (-nQPInt r (letterWord bs : Mat(2, ℤ)) + j) j
        (fracSymplecticFormRat r τ : ℂ) τ =
      faddeevWord bs 0 (nQPInt r (letterWord bs : Mat(2, ℤ)))
        (fracSymplecticFormRat r τ : ℂ) τ := by
  let N := nQPInt r (letterWord bs : Mat(2, ℤ))
  have hpos := flt_letterWord_pos_of_mem_tails hne hbs h.irrational
    h.fltDenominator_pos
  have hperiod := faddeevWordPeriodsSlitPlane_of_irrational bs h.irrational hpos
  have hfix : flt (letterWord bs : Mat(2, ℤ)) (τ : ℂ) = τ := by
    exact_mod_cast h.flt_eq
  have hoff : ¬ IsPeriodLatticePoint (τ : ℂ)
      (fracSymplecticFormRat r τ : ℂ) := by
    simpa only [ofReal_fracSymplecticFormRat] using
      ((isPeriodLatticePoint_fracSymplecticFormRat_iff h.irrational r).not.mpr hr)
  have hphase := faddeevWord_characteristic_phase h.flt_eq
    h.fltDenominator_pos.ne' hA
  have hshift := faddeevWord_indices_add bs hne 0 N (-N + j) hperiod hfix hoff (by
    simpa only [Int.cast_zero, zero_mul, add_zero, ofReal_fltDenominator] using hphase)
  have hindices : N + (-N + j) = j := by omega
  rw [hindices] at hshift
  simpa only [N, zero_add] using hshift

/-! ### The origin

At the origin the word product is `ש^0_γ(τ)⁻¹ = √ε/μ_γ`, the prefactor of the integral
five-term relation. -/

/-- At an attractive fixed point of `γ = ∏_j T^{b_j}S` with letters after the first at least
`2`, `Φ_{γ,0,0}(0;τ) = √ε/μ_γ` with `ε = j_γ(τ)`: the prefactor of
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`, equation (23),
`eq:5term.int`]. This uses the zero-characteristic cocycle formula
[72, Kopp (2024), Theorem 4.38, `thm:trivrmval`]. -/
theorem faddeevWord_zero_eq_etaMultiplier (hne : bs ≠ []) (hbs : ∀ b ∈ bs.tail, 2 ≤ b)
    (h : IsAttractiveFixedPoint (letterWord bs) τ) :
    faddeevWord bs 0 0 0 τ =
      (Real.sqrt (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) : ℂ) /
        etaMultiplier (letterWord bs) := by
  have hA : letterWord bs ∈ gammaSubgroup 0 := fun _ => ⟨0, by simp⟩
  have h0 := letterWord_lowerLeft_nonneg hbs
  have hpos := flt_letterWord_pos_of_mem_tails hne hbs h.irrational
    h.fltDenominator_pos
  have hword : faddeevWord bs 0 0 0 τ =
      (sfModularCocycleReal' 0 (letterWord bs) τ)⁻¹ := by
    rw [sfModularCocycleReal'_of_mem hA,
      sfModularCocycleRealTotal_of_nonneg hA h0,
      sfModularCocycleReal_zero]
    exact faddeevWord_zero_eq_inv_wordSigmaS bs hne hbs hpos h0
  have hvalue : sfModularCocycleRealTotal 0 (letterWord bs) hA τ =
      etaMultiplier (letterWord bs) /
        (Real.sqrt (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) : ℂ) := by
    simpa only [etaMultiplier] using
      (sfModularCocycleRealTotal_zero_of_flt_eq_self h.irrational hA
        h.fltDenominator_pos h.flt_eq)
  rw [hword, sfModularCocycleReal'_of_mem hA, hvalue, inv_div]

/-! ### Continued values

The continued word product at a characteristic, multiplied by `μ_γ`, is `F(r)`, or `F⁻(r)` at the
zero class when the diagonal index is positive. -/

/-- Off `ℤ²` the continued word product recovers the finite dilogarithm for every diagonal shift
`j`: `μ_γ Φ^cont_{γ,-n_QP+j,j}(⟨⟨r,τ⟩⟩) = F(r)`. -/
theorem etaMultiplier_mul_faddeevWordContinued (hne : bs ≠ [])
    (hbs : ∀ b ∈ bs.tail, 2 ≤ b) (h : IsAttractiveFixedPoint (letterWord bs) τ)
    {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r) (hA : letterWord bs ∈ gammaSubgroup r)
    (j : ℤ) :
    etaMultiplier (letterWord bs) *
        faddeevWordContinued bs (-nQPInt r (letterWord bs : Mat(2, ℤ)) + j) j
          (fracSymplecticFormRat r τ : ℂ) τ =
      finiteDilogValue (letterWord bs) τ r := by
  have hpos := flt_letterWord_pos_of_mem_tails hne hbs h.irrational
    h.fltDenominator_pos
  have hperiod := faddeevWordPeriodsSlitPlane_of_irrational bs h.irrational hpos
  have hoff : ¬ IsPeriodLatticePoint (τ : ℂ)
      (fracSymplecticFormRat r τ : ℂ) := by
    simpa only [ofReal_fracSymplecticFormRat] using
      ((isPeriodLatticePoint_fracSymplecticFormRat_iff h.irrational r).not.mpr hr)
  rw [faddeevWordContinued_eq_of_notMem bs _ _ hperiod hoff,
    faddeevWord_characteristic_indices hne hbs h hr hA j]
  exact (finiteDilogValue_eq_etaMultiplier_mul_nQPInt hne hbs h.irrational
    h.fltDenominator_pos hr hA).symm

/-- **The type rule in the values of the finite dilogarithm.** For `r ∈ ℤ²`,
`μ_γ Φ^cont_{γ,-n_QP+j,j}(⟨⟨r,τ⟩⟩)` is `F⁻(r) = ε^{-1/2}` when
`r₁ - n_QP(r,γ) + j ≥ 1` and `F(r) = ε^{1/2}` otherwise
([RW26, Radchenko, Wheeler (2026), Section 3.2, the proof of Theorem 2, `thm:fg.equs`]). -/
theorem etaMultiplier_mul_faddeevWordContinued_zeroClass (hne : bs ≠ [])
    (hbs : ∀ b ∈ bs.tail, 2 ≤ b) (h : IsAttractiveFixedPoint (letterWord bs) τ)
    {r : Fin 2 → ℚ} (hr : IsIntegralIndex r) (j : ℤ) :
    etaMultiplier (letterWord bs) *
        faddeevWordContinued bs (-nQPInt r (letterWord bs : Mat(2, ℤ)) + j) j
          (fracSymplecticFormRat r τ : ℂ) τ =
      if 1 ≤ (r 1).num - nQPInt r (letterWord bs : Mat(2, ℤ)) + j then
        finiteDilogValueMinus (letterWord bs) τ r
      else finiteDilogValue (letterWord bs) τ r := by
  let ε := fltDenominator (letterWord bs : Mat(2, ℤ)) τ
  let μ := etaMultiplier (letterWord bs)
  let s : ℂ := Real.sqrt ε
  have hε : 0 < ε := h.fltDenominator_pos
  have hμ : μ ≠ 0 := etaMultiplier_ne_zero _
  have hs : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast Real.sqrt_ne_zero'.mpr hε
  have hs_sq : s ^ 2 = (ε : ℂ) := by
    dsimp [s]
    exact_mod_cast Real.sq_sqrt hε.le
  have hkey : (ε : ℂ)⁻¹ * s = s⁻¹ := by
    rw [← hs_sq]
    field_simp
  have hpos := flt_letterWord_pos_of_mem_tails hne hbs h.irrational hε
  rw [faddeevWordContinued_zeroClass bs hne h.irrational hpos h.flt_eq hr j,
    faddeevWord_zero_eq_etaMultiplier hne hbs h]
  split_ifs with hi
  · rw [finiteDilogValueMinus_of_isIntegralIndex _ _ hr]
    rw [Complex.ofReal_inv]
    change μ * ((ε : ℂ)⁻¹ * (s / μ)) = s⁻¹
    calc
      μ * ((ε : ℂ)⁻¹ * (s / μ)) = (ε : ℂ)⁻¹ * s := by
        field_simp
      _ = s⁻¹ := hkey
  · rw [finiteDilogValue_of_isIntegralIndex _ _ hr]
    change μ * (1 * (s / μ)) = s
    field_simp

end SIC

end
