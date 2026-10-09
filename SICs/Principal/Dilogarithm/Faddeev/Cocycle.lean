/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.SigmaS.Faddeev
import SICs.Principal.Dilogarithm.Faddeev.Basic
import SICs.Principal.Dilogarithm.Values

/-!
# Principal Faddeev products and real cocycle values

The principal Faddeev product at a characteristic is the reciprocal real modular cocycle,
and recovers the finite quantum dilogarithm up to the eta multiplier.

This module compares the principal product of [RW26, Radchenko, Wheeler (2026),
Proposition 2(ii), `prop:prod.id.mod,fad`, equation (20), `eq:modulartofaddeevCF`]
with [AFK25, Definition 1.18, `def:shin`, equation (1.26), `eq:shindf`], and hence with
the finite dilogarithm of [RW26, Radchenko, Wheeler (2026), equation (2), `eq:fgam.def`],
at `A_d` and `τ=ρ_d`.

## The argument

At a nonintegral characteristic, the three word arguments avoid the period lattice.
The general generator comparison identifies each factor with the reciprocal of
`sigmaSHonest`. Moving the integer shift `-n` out of the first factor inserts
`ϖ_n(z/ρ_d³,-1/ρ_d)`. Since `-1/ρ_d = ρ_d-(d-1)`, its period can be replaced by `ρ_d`.
The remaining three factors are the reciprocal principal word, so at `n = n_QP(r,A_d)`
the result is `ש^r_{A_d}(ρ_d)⁻¹`. At the origin all three factors lie in the base chamber.

The finite dilogarithm is the reciprocal cocycle multiplied by `μ_{A_d}`. The simultaneous
index-shift identity also places the finite correction in the left index, giving the
product form with indices `(-n_QP,0)` used in the finite five-term relation.

At the literal origin, the zero-characteristic cocycle formula evaluates the removable value as
`μ_{A_d}^{-1}√(ρ_d³)`, the prefactor in the integral five-term relation.

These are pointwise gamma quotients. A product of their totalized values does not cancel
a zero against a pole. The comparison therefore covers nonintegral characteristics and
the literal origin separately; it asserts no evaluation at other removable singularities.
-/

noncomputable section

open Filter Topology
open scoped MatrixGroups

namespace SIC

/-! ### Comparison at the characteristics of the finite dilogarithm

The nonintegral arguments are lattice-free by irrationality of `ρ_d` and covariance of
the fractional symplectic form. The origin comparison uses the base chamber directly.
-/

/-- The reciprocal of an integer-shifted principal generator carries the finite
`q`-Pochhammer factor with period `ρ_d`. This is the shift used in
`principalFaddeev_fracSymplecticForm`. -/
private lemma principal_sigmaSHonest_sub_int_inv (d : ℕ) (hd : 3 < d) (w : ℝ)
    (n : ℤ) (hlat : SigmaSLatticeFree (principalRoot d) w) :
    (sigmaSHonest (w - n) (principalRoot d))⁻¹ =
      qPochhammerFin n ((w : ℂ) / (principalRoot d : ℂ)) (principalRoot d) *
        (sigmaSHonest w (principalRoot d))⁻¹ := by
  have hpos := principalRoot_pos d hd
  have hshift := sigmaSHonest_lattice_shift w (principalRoot d) 0 (-n) hpos hlat
  have hq : qPochhammerFin n ((w : ℂ) / (principalRoot d : ℂ))
      (-1 / (principalRoot d : ℂ)) ≠ 0 :=
    qPochhammerFin_ne_zero_of_forall_factor_ne_zero _ _ _
      (one_sub_exp_dual_ne_zero hpos hlat)
  have heq : sigmaSHonest (w - n) (principalRoot d) *
      qPochhammerFin n ((w : ℂ) / (principalRoot d : ℂ))
        (-1 / (principalRoot d : ℂ)) = sigmaSHonest w (principalRoot d) := by
    simpa [qPochhammerFin, sub_eq_add_neg] using hshift
  have hperiod' : qPochhammerFin n ((w : ℂ) / (principalRoot d : ℂ))
      (-1 / (principalRoot d : ℂ)) =
        qPochhammerFin n ((w : ℂ) / (principalRoot d : ℂ)) (principalRoot d) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one] using
      qPochhammerFin_principalRoot_neg_inv d hd n
        ((w : ℂ) / (principalRoot d : ℂ))
  calc
    (sigmaSHonest (w - n) (principalRoot d))⁻¹ =
        qPochhammerFin n ((w : ℂ) / (principalRoot d : ℂ))
          (-1 / (principalRoot d : ℂ)) *
          (sigmaSHonest w (principalRoot d))⁻¹ := by
      rw [← heq, mul_inv_rev]
      simp [hq]
    _ = qPochhammerFin n ((w : ℂ) / (principalRoot d : ℂ))
          (principalRoot d) * (sigmaSHonest w (principalRoot d))⁻¹ := by
      rw [hperiod']

/-- The three principal word arguments of a nonintegral characteristic are outside the
period lattice. These are the hypotheses for the three generator comparisons in
`principalFaddeev_fracSymplecticForm`. -/
private lemma principal_faddeev_word_lattice_free (d : ℕ) (hd : 3 < d)
    {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r) :
    SigmaSLatticeFree (principalRoot d)
        (fracSymplecticFormRat r (principalRoot d)) ∧
      SigmaSLatticeFree (principalRoot d)
        (fracSymplecticFormRat r (principalRoot d) / principalRoot d) ∧
      SigmaSLatticeFree (principalRoot d)
        (fracSymplecticFormRat r (principalRoot d) / principalRoot d ^ 2) := by
  have hirr := principalRoot_irrational d hd
  refine ⟨sigmaSLatticeFree_fracSymplecticFormRat hirr hr, ?_, ?_⟩
  · have h := sigmaSLatticeFree_fracSymplecticFormRat_div hirr hr
      (principalU d : Mat(2, ℤ)) (by
        rw [fltDenominator_principalU_principalRoot]
        exact (principalRoot_pos d hd).ne')
    rwa [flt_principalU_principalRoot d hd,
      fltDenominator_principalU_principalRoot] at h
  · have h := sigmaSLatticeFree_fracSymplecticFormRat_div hirr hr
      ((principalU d ^ 2 : SL(2, ℤ)) : Mat(2, ℤ)) (by
        rw [fltDenominator_principalU_sq_principalRoot d hd]
        exact pow_ne_zero _ (principalRoot_pos d hd).ne')
    rwa [flt_principalU_sq_principalRoot d hd,
      fltDenominator_principalU_sq_principalRoot d hd] at h

/-- At a real point where all three word arguments are lattice-free, the fixed Faddeev
product is the reciprocal principal word with its finite correction. This is the
pointwise comparison used by `principalFaddeev_fracSymplecticForm`. -/
private lemma principalFaddeev_real_eq_inv_word_quotient (d : ℕ) (hd : 3 < d)
    (z : ℝ) (n : ℤ)
    (hlat0 : SigmaSLatticeFree (principalRoot d) z)
    (hlat1 : SigmaSLatticeFree (principalRoot d) (z / principalRoot d))
    (hlat2 : SigmaSLatticeFree (principalRoot d) (z / principalRoot d ^ 2)) :
    principalFaddeev d 0 n z =
      (wordSigmaS z (principalRoot d) (principalA d)
        (principalA_lowerLeft_nonneg d hd) /
        qPochhammerFin n ((z : ℂ) / (principalRoot d : ℂ) ^ 3)
          (principalRoot d))⁻¹ := by
  let ρ := principalRoot d
  have hpos : 0 < ρ := principalRoot_pos d hd
  have hlat2' : SigmaSLatticeFree ρ (z / ρ ^ 2 - n) := by
    simpa [sub_eq_add_neg] using hlat2.add 0 (-n)
  have hf2 := faddeevS_eq_inv_sigmaSHonest (z / ρ ^ 2 - n) ρ hpos hlat2'
  have hf1 := faddeevS_eq_inv_sigmaSHonest (z / ρ) ρ hpos hlat1
  have hf0 := faddeevS_eq_inv_sigmaSHonest z ρ hpos hlat0
  have hf2' : faddeevS ((z : ℂ) / (ρ : ℂ) ^ 2 - n) ρ =
      (sigmaSHonest (z / ρ ^ 2 - n) ρ)⁻¹ := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_intCast] using hf2
  have hf1' : faddeevS ((z : ℂ) / (ρ : ℂ)) ρ =
      (sigmaSHonest (z / ρ) ρ)⁻¹ := by
    simpa only [Complex.ofReal_div] using hf1
  have hshift := principal_sigmaSHonest_sub_int_inv d hd (z / ρ ^ 2) n hlat2
  have hquot : (((z / ρ ^ 2 : ℝ) : ℂ) / (ρ : ℂ)) = (z : ℂ) / (ρ : ℂ) ^ 3 := by
    push_cast
    ring
  rw [principalFaddeev]
  simp only [Int.cast_zero, zero_mul, add_zero]
  rw [wordSigmaS_principalA_eq_triple d hd z (principalA_lowerLeft_nonneg d hd)]
  rw [hf2', hf1', hf0, hshift, hquot]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- For `r ∉ ℤ²` with `A_d ∈ Γ_r`, the product at `z = ⟨⟨r,ρ_d⟩⟩` and indices
`(0,n_QP(r,A_d))` equals `ש^r_{A_d}(ρ_d)⁻¹`. This bridges
[RW26, Radchenko, Wheeler (2026), equation (20), `eq:modulartofaddeevCF`] and
[AFK25, Definition 1.18, `def:shin`, equation (1.26), `eq:shindf`].
Specializes `faddeevS_eq_inv_sigmaSHonest` along the principal word. -/
theorem principalFaddeev_fracSymplecticForm (d : ℕ) (hd : 3 < d)
    {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r) (hA : principalA d ∈ gammaSubgroup r) :
    principalFaddeev d 0 (nQPInt r (principalA d))
        (fracSymplecticFormRat r (principalRoot d) : ℂ) =
      (sfModularCocycleReal' r (principalA d) (principalRoot d))⁻¹ := by
  let ρ := principalRoot d
  let z := fracSymplecticFormRat r ρ
  let n := nQPInt r (principalA d)
  have h0 := principalA_lowerLeft_nonneg d hd
  obtain ⟨hlat0, hlat1, hlat2⟩ := principal_faddeev_word_lattice_free d hd hr
  have hmod : sfModularCocycleReal' r (principalA d) ρ =
      wordSigmaS z ρ (principalA d) h0 /
        qPochhammerFin n ((z : ℂ) / (ρ : ℂ) ^ 3) ρ := by
    rw [sfModularCocycleReal'_of_mem hA,
      sfModularCocycleRealTotal_of_nonneg hA h0,
      sfModularCocycleReal_eq_of_not_isIntegralIndex hr hA h0,
      fltDenominator_principalA_principalRoot,
      principalJacobiFactor_eq_principalRoot_pow_three d hd,
      flt_principalA_principalRoot d hd]
    simp only [Complex.ofReal_pow]
    rfl
  have hprod := principalFaddeev_real_eq_inv_word_quotient d hd z n
    hlat0 hlat1 hlat2
  simpa only [z, n, ρ, ofReal_fracSymplecticFormRat] using
    hprod.trans (congrArg Inv.inv hmod.symm)

/-- The principal finite dilogarithm value satisfies
`F(r) = μ_{A_d} Φ_{A_d,0,n_QP}(⟨⟨r,ρ_d⟩⟩;ρ_d)` for `r ∉ ℤ²` and `A_d ∈ Γ_r`.
This connects `principalDilogValue` to `principalFaddeev_fracSymplecticForm`. -/
theorem principalDilogValue_eq_etaMultiplier_mul_nQPInt
    (d : ℕ) (hd : 3 < d) {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r) (hA : principalA d ∈ gammaSubgroup r) :
    principalDilogValue d r = etaMultiplier (principalA d) *
      principalFaddeev d 0 (nQPInt r (principalA d))
        (fracSymplecticFormRat r (principalRoot d)) := by
  rw [principalDilogValue_of_not_isIntegralIndex d hr,
    principalFaddeev_fracSymplecticForm d hd hr hA]
  ring

/-- At `A_d ∈ Γ_r`, the two outer multipliers in equation (16) agree at
`z = ⟨⟨r,ρ_d⟩⟩`; used by the negative-index form of `principalDilogValue`. -/
private lemma principalDilogValue_faddeev_phase (d : ℕ) (hd : 3 < d)
    {r : Fin 2 → ℚ} (hA : principalA d ∈ gammaSubgroup r) :
    Complex.exp (2 * Real.pi * Complex.I *
      ((fracSymplecticFormRat r (principalRoot d) : ℝ) : ℂ)) =
    Complex.exp (2 * Real.pi * Complex.I *
      (((fracSymplecticFormRat r (principalRoot d) : ℝ) : ℂ) /
        (principalJacobiFactor d : ℂ) +
        nQPInt r (principalA d) * (principalRoot d : ℂ))) := by
  let ρ := principalRoot d
  let z := fracSymplecticFormRat r ρ
  let N := nQPInt r (principalA d)
  have hJ : fltDenominator (principalA d : Mat(2, ℤ)) ρ ≠ 0 := by
    rw [fltDenominator_principalA_principalRoot]
    exact (principalJacobiFactor_pos d hd).ne'
  obtain ⟨c, hc⟩ := div_fltDenominator_add_nQPInt_mul hA
    (flt_principalA_principalRoot d hd) hJ
  apply exp_two_pi_I_eq_of_sub_intCast _ _ (-c)
  have hc' : (z : ℂ) / (principalJacobiFactor d : ℂ) + N * (ρ : ℂ) =
      (z : ℂ) + c := by
    exact_mod_cast (by simpa only [fltDenominator_principalA_principalRoot] using hc)
  change (z : ℂ) - ((z : ℂ) / (principalJacobiFactor d : ℂ) +
      N * (ρ : ℂ)) = ((-c : ℤ) : ℂ)
  simp only [Int.cast_neg]
  linear_combination -hc'

/-- The principal instance of [RW26, Radchenko, Wheeler (2026), equation (2),
`eq:fgam.def`] is `F(r) = μ_{A_d} Φ_{A_d,-n_QP,0}(⟨⟨r,ρ_d⟩⟩;ρ_d)` for
`r ∉ ℤ²` and `A_d ∈ Γ_r`. This is the index-shift form of
`principalDilogValue_eq_etaMultiplier_mul_nQPInt`. -/
theorem principalDilogValue_eq_etaMultiplier_mul
    (d : ℕ) (hd : 3 < d) {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r) (hA : principalA d ∈ gammaSubgroup r) :
    principalDilogValue d r = etaMultiplier (principalA d) *
      principalFaddeev d (-nQPInt r (principalA d)) 0
        (fracSymplecticFormRat r (principalRoot d)) := by
  let ρ := principalRoot d
  let z := fracSymplecticFormRat r ρ
  let N := nQPInt r (principalA d)
  obtain ⟨hlat0, _, hlat2⟩ := principal_faddeev_word_lattice_free d hd hr
  have h₀ : barnesDoubleGammaInv
      ((ρ : ℂ) - ((z : ℂ) + (0 + max (-N) 0 : ℤ) * (ρ : ℂ)))
      1 ρ ≠ 0 := by
    simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast,
      Int.cast_zero, add_zero, zero_add] using
      (hlat0.add (max (-N) 0) 0).faddeevS_den_ne_zero (principalRoot_pos d hd)
  have h₂ : barnesDoubleGammaInv
      ((ρ : ℂ) - ((z : ℂ) / (ρ : ℂ) ^ 2 - (N + min (-N) 0 : ℤ)))
      1 ρ ≠ 0 := by
    simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_intCast,
      Complex.ofReal_zero, Complex.ofReal_neg, Int.cast_zero, zero_mul,
      zero_add, add_zero, Int.cast_neg, Int.cast_add, sub_eq_add_neg] using
      (hlat2.add 0 (-(N + min (-N) 0))).faddeevS_den_ne_zero
        (principalRoot_pos d hd)
  have hshift := principalFaddeev_indices_add d hd 0 N (-N) (z : ℂ)
    (by simpa [z, ρ, N, ofReal_fracSymplecticFormRat] using
      principalDilogValue_faddeev_phase d hd hA) h₀ h₂
  have hshift' : principalFaddeev d (-N) 0 (z : ℂ) =
      principalFaddeev d 0 N (z : ℂ) := by
    simpa only [zero_add, add_neg_cancel] using hshift
  rw [principalDilogValue_eq_etaMultiplier_mul_nQPInt d hd hr hA]
  simpa only [z, ρ, N, ofReal_fracSymplecticFormRat] using
    congrArg (etaMultiplier (principalA d) * ·) hshift'.symm

/-- At the literal origin, `Φ_{A_d,0,0}(0;ρ_d) = ש^0_{A_d}(ρ_d)⁻¹`.
Specializes `faddeevS_eq_inv_sigmaSBase` at the three unshifted factors; this is the
origin case of the comparison with [RW26, Radchenko, Wheeler (2026), equation (20),
`eq:modulartofaddeevCF`]. -/
theorem principalFaddeev_zero (d : ℕ) (hd : 3 < d) :
    principalFaddeev d 0 0 0 =
      (sfModularCocycleReal' 0 (principalA d) (principalRoot d))⁻¹ := by
  have hpos := principalRoot_pos d hd
  have hbase := faddeevS_eq_inv_sigmaSBase 0 (principalRoot d) hpos (by norm_num) hpos
  have hA : principalA d ∈ gammaSubgroup 0 := fun _ => ⟨0, by simp⟩
  have h0 := principalA_lowerLeft_nonneg d hd
  rw [sfModularCocycleReal'_of_mem hA,
    sfModularCocycleRealTotal_of_nonneg hA h0,
    sfModularCocycleReal_zero,
    wordSigmaS_principalA_eq_triple d hd 0 h0]
  simp only [Complex.ofReal_zero] at hbase
  simp only [principalFaddeev, zero_div, Int.cast_zero, sub_zero, zero_mul,
    zero_add, sigmaSHonest_zero, hbase, mul_inv_rev]
  ring

/-- The removable principal origin has the prefactor `μ_{A_d}^{-1}√(ρ_d³)` of
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`, equation (23),
`eq:5term.int`] at the principal fixed point. This rewrites `principalFaddeev_zero` using
the zero-characteristic cocycle formula [72, Kopp (2024), Theorem 4.38, `thm:trivrmval`]. -/
theorem principalFaddeev_zero_eq_etaMultiplier (d : ℕ) (hd : 3 < d) :
    principalFaddeev d 0 0 0 =
      (Real.sqrt (principalRoot d ^ 3) : ℂ) / etaMultiplier (principalA d) := by
  have hA : principalA d ∈ gammaSubgroup 0 := fun _ => ⟨0, by simp⟩
  have hvalue : sfModularCocycleRealTotal 0 (principalA d) hA (principalRoot d) =
      etaMultiplier (principalA d) /
        ((Real.sqrt (fltDenominator (principalA d : Mat(2, ℤ))
          (principalRoot d)) : ℝ) : ℂ) := by
    simpa only [etaMultiplier] using
      (sfModularCocycleRealTotal_zero_of_flt_eq_self
        (principalRoot_irrational d hd) hA
        (fltDenominator_principalA_principalRoot_pos d hd)
        (flt_principalA_principalRoot d hd))
  rw [principalFaddeev_zero d hd, sfModularCocycleReal'_of_mem hA,
    hvalue, inv_div, fltDenominator_principalA_principalRoot,
    principalJacobiFactor_eq_principalRoot_pow_three d hd]

end SIC

end
