/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Cocycle.SFReduction

/-!
# Pole Avoidance for the Principal SF Reduction

Nonvanishing of the finite q-Pochhammer products; the unconditional identification.

This file discharges the two finite `q`-Pochhammer nonvanishing hypotheses left in
`principal_sf_reduction2_eq_one`. Every exponent occurring in the `k`- and `ℓ`-products is a
rational affine expression in the irrational principal root `ρ_d`. If its irrational coefficient
vanishes, the remaining rational number lies strictly between consecutive integers; the excluded
origin is exactly what rules out the endpoint.

## Main results

- `principal_qPoch_k_ne_zero`: the finite product indexed by the `k`-shift has no zero factor.
- `principal_qPoch_ell_ne_zero`: the finite product indexed by the `ℓ`-shift has no zero factor.
- `principal_sf_reduction2_eq_one_unconditional`: the reduced principal cocycle equals the
  three-double-sine overlap without additional pole hypotheses.

## References

- [AFK25, Section 8, especially equation (8.9)]
-/

noncomputable section

open Real Complex

namespace SIC

/-! ### Irrational affine exponents

Every possible factor exponent is rewritten as `(aρ_d+b)/d`. If `a ≠ 0`, irrationality of
`ρ_d` excludes an integral exponent. The only remaining case is controlled by canonical residue
bounds.
-/

/-- A nonconstant integral affine expression in `ρ_d`, divided by the positive integer `d`, is
irrational and hence cannot be an integer. -/
private lemma principal_affine_div_ne_int (d : ℕ) (hd : 3 < d) (a b m : ℤ) (ha : a ≠ 0) :
    ((a : ℝ) * principalRoot d + b) / d ≠ m := by
  have hirr : Irrational (((a : ℝ) * principalRoot d + b) / d) := by
    exact (((principalRoot_irrational d hd).intCast_mul ha).add_intCast b).div_natCast
      (by omega)
  exact hirr.ne_int m

/-- For a nonzero canonical pair, the third index `r` cannot vanish together with `q`. -/
private lemma principalThirdIndex_ne_zero_of_q_eq_zero (d : ℕ) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hne : ¬(p = 0 ∧ q = 0)) (hq : q = 0) :
    principalThirdIndex d p q ≠ 0 := by
  intro hr
  have hdvdnegp : (d : ℤ) ∣ -p := by
    rw [Int.dvd_iff_emod_eq_zero]
    simpa [principalThirdIndex, hq] using hr
  obtain ⟨c, hc⟩ := hdvdnegp
  have hdvdp : (d : ℤ) ∣ p := by
    refine ⟨-c, ?_⟩
    linear_combination -hc
  have hp : p = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt hp0 hp1 hdvdp
  exact hne ⟨hp, hq⟩

/-- The exponent in a factor of the `k`-product, rewritten as an integral affine expression in
`ρ_d` divided by `d`. -/
private lemma principal_k_exponent_eq (d : ℕ) (hd : 3 < d) (p q k : ℤ) :
    principalDoubleSineArg d (principalThirdIndex d p q) q - 1 +
        k * principalRoot d =
      (((principalThirdIndex d p q + d * k : ℤ) : ℝ) * principalRoot d - q) / d := by
  rw [principalDoubleSineArg]
  push_cast
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  field_simp
  ring

/-- The exponent in a factor of the `ℓ`-product, rewritten as an integral affine expression in
`ρ_d` divided by `d`. The rewrite uses `ρ_d² - (d-1)ρ_d + 1 = 0`. -/
private lemma principal_ell_exponent_eq (d : ℕ) (hd : 3 < d) (p q k : ℤ) :
    (principalDoubleSineArg d (principalThirdIndex d p q) q - 1) / principalRoot d +
        k * principalRoot d =
      (((q + d * k : ℤ) : ℝ) * principalRoot d +
          (principalThirdIndex d p q - q * ((d : ℤ) - 1) : ℤ)) / d := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hρ0 : principalRoot d ≠ 0 := (principalRoot_irrational d hd).ne_zero
  have hquad := principalRoot_satisfies_quadratic d hd
  rw [principalDoubleSineArg]
  push_cast
  field_simp
  linear_combination (-(q : ℝ)) * hquad

/-! ### Nonvanishing of the two finite products

Applying the affine-exponent criterion factor by factor proves that both finite
`qPochhammerFin` products in the reduction are nonzero for a nonzero canonical pair.
-/

/-- The finite `k`-product is nonzero for every nonzero canonical residue pair.
Thus `principal_qPoch_k_pair_eq_one`'s nonvanishing premise is automatic. -/
theorem principal_qPoch_k_ne_zero (d : ℕ) (hd : 3 < d) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ))
    (hne : ¬(p = 0 ∧ q = 0)) :
    qPochhammerFin (principalReductionK d p q)
      (principalDoubleSineArg d (principalThirdIndex d p q) q - 1) (principalRoot d) ≠ 0 := by
  have hz : (principalDoubleSineArg d (principalThirdIndex d p q) q : ℂ) - 1 =
      ((principalDoubleSineArg d (principalThirdIndex d p q) q - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [hz]
  let n := principalReductionK d p q
  let z := principalDoubleSineArg d (principalThirdIndex d p q) q - 1
  change qPochhammerFin n z (principalRoot d) ≠ 0
  refine qPochhammerFin_ne_zero_of_forall_ne_int n z (principalRoot d) ?_
  intro k _ m
  dsimp only [z]
  rw [principal_k_exponent_eq d hd]
  by_cases ha : principalThirdIndex d p q + d * k = 0
  · have hq : q ≠ 0 := fun hq => principalThirdIndex_ne_zero_of_q_eq_zero
        d p q hp0 hp1 hne hq (Int.eq_zero_of_dvd_of_nonneg_of_lt
          (Int.emod_nonneg _ (by exact_mod_cast (by omega : d ≠ 0)))
          (Int.emod_lt_of_pos _ (by exact_mod_cast (by omega : 0 < d)))
          ⟨-k, by linear_combination ha⟩)
    rw [ha]
    norm_num only [Int.cast_zero, zero_mul, zero_sub]
    exact neg_intCast_div_natCast_ne_int d q m (lt_of_le_of_ne hq0 hq.symm) hq1
  · simpa only [Int.cast_neg, sub_eq_add_neg] using
      principal_affine_div_ne_int d hd _ (-q) m ha

/-- The finite `ℓ`-product is nonzero for every nonzero canonical residue pair.
Thus `principal_qPoch_ell_pair_eq_one`'s nonvanishing premise is automatic. -/
theorem principal_qPoch_ell_ne_zero (d : ℕ) (hd : 3 < d) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ))
    (hne : ¬(p = 0 ∧ q = 0)) :
    qPochhammerFin (principalReductionL d p q)
      ((principalDoubleSineArg d (principalThirdIndex d p q) q - 1) / principalRoot d)
      (principalRoot d) ≠ 0 := by
  have hz : ((principalDoubleSineArg d (principalThirdIndex d p q) q : ℂ) - 1) /
        (principalRoot d : ℂ) =
      (((principalDoubleSineArg d (principalThirdIndex d p q) q - 1) / principalRoot d : ℝ) :
        ℂ) := by push_cast; rfl
  rw [hz]
  let n := principalReductionL d p q
  let z := (principalDoubleSineArg d (principalThirdIndex d p q) q - 1) / principalRoot d
  change qPochhammerFin n z (principalRoot d) ≠ 0
  refine qPochhammerFin_ne_zero_of_forall_ne_int n z (principalRoot d) ?_
  intro k _ m
  dsimp only [z]
  rw [principal_ell_exponent_eq d hd]
  by_cases ha : q + d * k = 0
  · have hdvdq : (d : ℤ) ∣ q := ⟨-k, by linear_combination ha⟩
    have hq : q = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt hq0 hq1 hdvdq
    subst q
    have hdZ0 : (d : ℤ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    have hdZpos : (0 : ℤ) < d := by exact_mod_cast (by omega : 0 < d)
    have hr0 := Int.emod_nonneg (-p - 0) hdZ0
    have hr1 := Int.emod_lt_of_pos (-p - 0) hdZpos
    have hrne := principalThirdIndex_ne_zero_of_q_eq_zero d p 0 hp0 hp1 hne rfl
    rw [ha]
    norm_num only [Int.cast_zero, zero_mul, zero_sub, mul_zero, sub_zero]
    intro heq
    norm_num at heq
    have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hr0R : (0 : ℝ) ≤ principalThirdIndex d p 0 := by
      exact_mod_cast (show 0 ≤ principalThirdIndex d p 0 from hr0)
    have hr1R : (principalThirdIndex d p 0 : ℝ) < d := by
      exact_mod_cast (show principalThirdIndex d p 0 < (d : ℤ) from hr1)
    have hlower : (0 : ℝ) < (principalThirdIndex d p 0 : ℝ) / d :=
      div_pos (lt_of_le_of_ne hr0R (Ne.symm (by exact_mod_cast hrne))) hdR
    have hupper : (principalThirdIndex d p 0 : ℝ) / d < 1 := (div_lt_one hdR).2 hr1R
    have hmPos : (0 : ℤ) < m := by exact_mod_cast (heq ▸ hlower)
    have hmLt : m < 1 := by exact_mod_cast (heq ▸ hupper)
    omega
  · exact principal_affine_div_ne_int d hd _
      (principalThirdIndex d p q - q * ((d : ℤ) - 1)) m ha

/-! ### Removing the pole hypotheses

The two preceding nonvanishing theorems discharge the last hypotheses of the finite-algebra
reduction, giving the exact principal cocycle/product identity on every nonzero canonical pair.
-/

/-- **`principal_sf_reduction2_eq_one` without pole hypotheses.** The principal SF value defined
by the word product equals the normalized ghost overlap for every nonzero canonical residue pair.
The nonvanishing premises are supplied by `principal_qPoch_k_ne_zero` and
`principal_qPoch_ell_ne_zero`. -/
theorem principal_sf_reduction2_eq_one_unconditional (d : ℕ) (hd : 3 < d)
    (p q : ℤ) (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ))
    (hne : ¬(p = 0 ∧ q = 0)) :
    (principalRankOneAdmissibleTuple ⟨d, hd⟩).sfPhase (principalA d) ![p, q] *
        (sigmaS (principalZ d p q) (principalRoot d) 0 0 *
          sigmaS (principalDoubleSineArg d p (principalThirdIndex d p q) - 1) (principalRoot d) 0
            (-principalReductionK d p q) *
          sigmaS (principalDoubleSineArg d (principalThirdIndex d p q) q - 1) (principalRoot d)
            (principalReductionK d p q) (-principalReductionL d p q)) /
        qPochhammerFin (-principalReductionL d p q)
          (principalZ d p q / principalJacobiFactor d) (principalRoot d) =
      (principalTripleDoubleSine d p q : ℂ) := by
  exact principal_sf_reduction2_eq_one d hd p q hp0 hp1 hq0 hq1 hne
    (principal_qPoch_k_ne_zero d hd p q hp0 hp1 hq0 hq1 hne)
    (principal_qPoch_ell_ne_zero d hd p q hp0 hp1 hq0 hq1 hne)

end SIC

end
