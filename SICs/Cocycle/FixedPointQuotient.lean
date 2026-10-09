/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.HJReduction
import SICs.Quadratic.CycleUnit
import SICs.Cocycle.HJCycleProduct
import SICs.Cocycle.FixedPointCocycle

/-!
# The reflected quotient at a real quadratic fixed point

At every real quadratic irrational `β` fixed by `A ∈ Γ_r` with `j_A(β) > 0`, `r ∉ ℤ²`, the reflected
quotient `ש^r_A(β)/ש^{-r}_A(β)` is a positive real: `U^{(1)}(r)^{∓2}` at a reduced representative,
where `A` is a power of the cycle matrix, carried to `β` by Katok's reduction and Kopp's Theorem
4.37.

This file proves that the reflected quotient `ש^r_A(β)/ש^{-r}_A(β)` of the real
Shintani--Faddeev cocycle is a positive real number, for every real quadratic irrational `β`,
every `r ∈ ℚ² ∖ ℤ²`, and every `A ∈ Γ_r` fixing `β` with `j_A(β) > 0`. At a reduced `β` and a
cycle matrix `A` the quotient is `U^{(1)}(r)^{-2}`; this is the value side of [72, Kopp (2024),
Theorem 8.2, `thm:mainrestate`], whose other side is `exp(nZ'_{𝔪∞₂}(0,𝒜))`. Here no ray class data
enter and `β` may have any conductor. The positivity is what makes the normalized ghost overlaps
real ([AFK25, Theorem 5.8, `thm:nupnumpeq1`], `SICs.Ghost.RealOverlaps`).

## Mathematical argument

*Reduced `β`.* Let `0 < β' < 1 < β` be the roots of `X² - tX + n`, `t, n ∈ ℚ`. A matrix
`A ∈ SL₂(ℤ)` fixing `β` and `β'` with positive Jacobi denominators is a power `P^m` of the cycle
matrix `P = A_{0,ℓ}` of the purely periodic expansion of `β`
(`BinaryQF.exists_zpow_eq_of_flt_eq_self_of_sq_eq`, [72, Kopp (2024), Proposition 7.7,
`prop:betatogamma`]). For `m = k ≥ 0`, `A = A_{0,kℓ}` is the cycle matrix of a closed cycle
(`hjCycleMatrix_mul_of_hjPeriod_eq`), and Kopp's Proposition 7.20 at `r` and `-r` gives
`ש^r_A(β)/ש^{-r}_A(β) = U^{(1)}(r)^{-2}` (`sfModularCocycleReal_div_neg_hjCycleMatrix`). For
`m < 0` the inverse `A⁻¹` is such a cycle matrix, and `ש^r_A(β) = ש^r_{A⁻¹}(β)⁻¹` at a fixed
point (`sfModularCocycleRealTotal_inv_of_irrational`) inverts the
quotient.

*Arbitrary `β`.* Some `R ∈ SL₂(ℤ)` with `j_R(β) > 0` carries the pair `(β, β')` to a reduced pair
(`exists_flt_reduced_of_sq_eq`, Katok's eventual reducedness), which is again the pair of roots
of a rational quadratic (`exists_sq_eq_flt_of_sq_eq`). The matrix `A` fixes `β'` too, with
`j_A(β)j_A(β') = 1` (`flt_eq_self_of_flt_eq_self_of_sq_eq`,
`fltDenominator_mul_fltDenominator_eq_one_of_sq_eq`), so its conjugate `A₁ = RAR⁻¹ ∈ Γ_{Rr}`
fixes both reduced roots with positive Jacobi denominators
(`mem_gammaSubgroup_ratVecAction_of_mul_eq`, `flt_of_mul_eq_of_flt_eq_self`,
`fltDenominator_of_mul_eq_of_flt_eq_self`). Kopp's Theorem 4.37
(`sfModularCocycleRealTotal_conj_of_det_one`) at `r` and at `-r`, with `R(-r) = -Rr`
(`ratVecAction_neg`), transports the quotient from the reduced pair back to `β`.

## References

- [72, Kopp (2024), Theorem 8.2, `thm:mainrestate`; Proposition 7.20, `prop:almost`;
  Proposition 7.22, `prop:lambdaminus`; Theorem 4.37, `thm:shinconj`; Proposition 7.7,
  `prop:betatogamma`; Proposition 3.17, `prop:reduced`].
- [68, Katok (2003), Theorem 1.3].
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The reduced case

A matrix fixing a reduced pair of roots is a power of the cycle matrix, and at a cycle matrix the
quotient is `U^{(1)}(r)^{-2}`. -/

/-- A closed HJ cycle has positive reflected quotient; this is the cycle-matrix step used in the
reduced fixed-point argument. -/
private theorem exists_pos_eq_mul_neg_hjCycleMatrix {x : ℝ}
    (hirr : Irrational x) (hx1 : 1 < x) {N : ℕ} (hN : hjPeriod x N = x)
    {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r)
    (hA : (hjCycleMatrix x N : SL(2, ℤ)) ∈ gammaSubgroup r) :
    ∃ c : ℝ, 0 < c ∧
      sfModularCocycleRealTotal r (hjCycleMatrix x N) hA x =
        (c : ℂ) * sfModularCocycleRealTotal (-r) (hjCycleMatrix x N)
          (neg_mem_gammaSubgroup hA) x := by
  let U := starkTangedalYamamoto r x N
  have h0 := lowerLeft_hjCycleMatrix_nonneg hirr N
  have hprod := sfModularCocycleReal_mul_neg_hjCycleMatrix hirr hx1 hN hr hA h0
  have hneg : sfModularCocycleReal (-r) (hjCycleMatrix x N)
      (neg_mem_gammaSubgroup hA) h0 x ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hprod
    exact Complex.exp_ne_zero _ hprod.symm
  refine ⟨U⁻¹ ^ 2, sq_pos_of_pos (inv_pos.mpr (starkTangedalYamamoto_pos r x N)), ?_⟩
  rw [sfModularCocycleRealTotal_of_nonneg hA h0,
    sfModularCocycleRealTotal_of_nonneg (neg_mem_gammaSubgroup hA) h0]
  have hdiv := sfModularCocycleReal_div_neg_hjCycleMatrix hirr hx1 hN hr hA h0
  rw [div_eq_iff hneg] at hdiv
  simpa only [U, inv_pow, Complex.ofReal_inv, Complex.ofReal_pow] using hdiv

/-- **The reflected quotient at a reduced real quadratic fixed point is a positive real**: for
`0 < y < 1 < x` the roots of `X² - tX + n` with `x` irrational, `r ∉ ℤ²`, and `A ∈ Γ_r` fixing `x`
and `y` with positive Jacobi denominators at both, `ש^r_A(x) = c·ש^{-r}_A(x)` for some `c > 0`.
`A = P^m` (`BinaryQF.exists_zpow_eq_of_flt_eq_self_of_sq_eq`); for `m ≥ 0` the constant is
`U^{(1)}(r)^{-2}` at the closed cycle of length `mℓ`
(`sfModularCocycleReal_div_neg_hjCycleMatrix`), for `m < 0` its inverse at `A⁻¹`. -/
theorem exists_pos_eq_mul_neg_of_reduced {x y : ℝ} {t n : ℚ}
    (hx : x ^ 2 = t * x - n) (hy : y ^ 2 = t * y - n) (hirr : Irrational x) (hx1 : 1 < x)
    (hy01 : y ∈ Set.Ioo 0 1) {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r) {A : SL(2, ℤ)}
    (hA : A ∈ gammaSubgroup r)
    (hfix : flt (A : Mat(2, ℤ)) x = x)
    (hfix' : flt (A : Mat(2, ℤ)) y = y)
    (hj : 0 < fltDenominator (A : Mat(2, ℤ)) x)
    (hj' : 0 < fltDenominator (A : Mat(2, ℤ)) y) :
    ∃ c : ℝ, 0 < c ∧ sfModularCocycleRealTotal r A hA x =
      (c : ℂ) * sfModularCocycleRealTotal (-r) A (neg_mem_gammaSubgroup hA) x := by
  obtain ⟨m, hm⟩ := BinaryQF.exists_zpow_eq_of_flt_eq_self_of_sq_eq
    hx hy hirr hx1 hy01 hfix hfix' hj hj'
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg m
  · rw [hk, zpow_natCast, ← hjCycleMatrix_mul_of_hjPeriod_eq
      (hjPeriod_minimalPeriod x)] at hm
    subst A
    exact exists_pos_eq_mul_neg_hjCycleMatrix hirr hx1
      (hjPeriod_mul_of_hjPeriod_eq (hjPeriod_minimalPeriod x) k) hr hA
  · let B := hjCycleMatrix x (Function.minimalPeriod hjRotate x * k)
    rw [hk, zpow_neg, zpow_natCast, ← hjCycleMatrix_mul_of_hjPeriod_eq
      (hjPeriod_minimalPeriod x)] at hm
    change A = B⁻¹ at hm
    subst A
    have hB : B ∈ gammaSubgroup r := by
      simpa only [inv_inv] using inv_mem_gammaSubgroup hA
    have hBN : hjPeriod x (Function.minimalPeriod hjRotate x * k) = x :=
      hjPeriod_mul_of_hjPeriod_eq (hjPeriod_minimalPeriod x) k
    obtain ⟨c, hc, heq⟩ :=
      exists_pos_eq_mul_neg_hjCycleMatrix hirr hx1 hBN hr hB
    have hfixB := flt_hjCycleMatrix_of_hjPeriod_eq hirr hBN
    have hjB := fltDenominator_hjCycleMatrix_pos_of_hjPeriod_eq hirr hBN
    have hinv := sfModularCocycleRealTotal_inv_of_irrational
      hB hirr hr hfixB hjB
    have hrneg : ¬ IsIntegralIndex (-r) := (isIntegralIndex_neg_iff r).not.mpr hr
    have hinvneg := sfModularCocycleRealTotal_inv_of_irrational
      (neg_mem_gammaSubgroup hB) hirr hrneg hfixB hjB
    refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
    rw [hinv, hinvneg, heq, mul_inv]
    simp only [B, Complex.ofReal_inv]

/-! ### An arbitrary real quadratic irrational

Katok's reduction and Kopp's Theorem 4.37 carry the reduced case to every real quadratic
irrational. -/

/-- **The reflected quotient at a real quadratic fixed point is a positive real**: for `x ≠ y` the
roots of `X² - tX + n` with `t, n ∈ ℚ` and `x` irrational, `r ∉ ℤ²`, and `A ∈ Γ_r` fixing `x` with
`j_A(x) > 0`, `ש^r_A(x) = c·ש^{-r}_A(x)` for some `c > 0`. Reduce the pair by
`exists_flt_reduced_of_sq_eq`, conjugate `A`, apply
`exists_pos_eq_mul_neg_of_reduced`, and transport back by
`sfModularCocycleRealTotal_conj_of_det_one` at `r` and `-r`. -/
theorem exists_pos_sfModularCocycleRealTotal_eq_mul_neg {x y : ℝ} {t n : ℚ}
    (hx : x ^ 2 = t * x - n) (hy : y ^ 2 = t * y - n) (hxy : x ≠ y) (hirr : Irrational x)
    {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r) {A : SL(2, ℤ)}
    (hA : A ∈ gammaSubgroup r)
    (hfix : flt (A : Mat(2, ℤ)) x = x)
    (hj : 0 < fltDenominator (A : Mat(2, ℤ)) x) :
    ∃ c : ℝ, 0 < c ∧ sfModularCocycleRealTotal r A hA x =
      (c : ℂ) * sfModularCocycleRealTotal (-r) A (neg_mem_gammaSubgroup hA) x := by
  have hfix' := flt_eq_self_of_flt_eq_self_of_sq_eq hx hy hxy hirr hfix
  have hj' : 0 < fltDenominator (A : Mat(2, ℤ)) y := by
    nlinarith [fltDenominator_mul_fltDenominator_eq_one_of_sq_eq hx hy hxy hirr hfix]
  have hirr' : Irrational y := by
    rw [show y = (t : ℝ) - x by linarith [(BinaryQF.add_eq_and_mul_eq_of_sq_eq hxy hx hy).1]]
    exact hirr.ratCast_sub t
  obtain ⟨R, hRx, hRy, hjR⟩ := exists_flt_reduced_of_sq_eq hx hy hxy hirr
  have hjRy := fltDenominator_ne_zero_of_irrational hirr' R
  obtain ⟨t', n', hx', hy'⟩ := exists_sq_eq_flt_of_sq_eq hx hy hxy R hjR.ne' hjRy
  have hA' := mul_mul_inv_mem_gammaSubgroup_ratVecAction hA R
  obtain ⟨c, hc, heq⟩ := exists_pos_eq_mul_neg_of_reduced hx' hy'
    (Irrational.flt hirr R) hRx hRy ((isIntegralIndex_ratVecAction_iff R).not.mpr hr) hA'
    (flt_mul_mul_inv_of_flt_eq_self R hjR.ne' hj.ne' hfix)
    (flt_mul_mul_inv_of_flt_eq_self R hjRy hj'.ne' hfix')
    (by rwa [fltDenominator_mul_mul_inv_of_flt_eq_self R hjR.ne' hj.ne' hfix])
    (by rwa [fltDenominator_mul_mul_inv_of_flt_eq_self R hjRy hj'.ne' hfix'])
  have hneg := sfModularCocycleRealTotal_mul_mul_inv (neg_mem_gammaSubgroup hA) R hirr
    ((isIntegralIndex_neg_iff r).not.mpr hr) hfix hj hjR
  rw [sfModularCocycleRealTotal_congr_index (ratVecAction_neg _ r) _
    (neg_mem_gammaSubgroup hA')] at hneg
  refine ⟨c, hc, ?_⟩
  rw [← sfModularCocycleRealTotal_mul_mul_inv hA R hirr hr hfix hj hjR, heq, hneg]

/-- **The reflected quotient at the root `ρ_{Q,+}` of an admissible form is a positive real**:
`exists_pos_sfModularCocycleRealTotal_eq_mul_neg` at `x = ρ_{Q,+}`, `y = ρ_{Q,-}`, the roots of
`X² + (b/a)X + c/a` (`BinaryQF.rootPlus_satisfies_quadratic`,
`BinaryQF.rootMinus_satisfies_quadratic`), distinct since `Δ > 0`. -/
theorem BinaryQF.IsAdmissible.exists_pos_sfModularCocycleRealTotal_eq_mul_neg {Q : BinaryQF}
    (hQ : Q.IsAdmissible) {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r) {A : SL(2, ℤ)}
    (hA : A ∈ gammaSubgroup r)
    (hfix : flt (A : Mat(2, ℤ)) Q.rootPlus = Q.rootPlus)
    (hj : 0 < fltDenominator (A : Mat(2, ℤ)) Q.rootPlus) :
    ∃ c : ℝ, 0 < c ∧ sfModularCocycleRealTotal r A hA Q.rootPlus =
      (c : ℂ) * sfModularCocycleRealTotal (-r) A (neg_mem_gammaSubgroup hA) Q.rootPlus := by
  have ha : (Q.a : ℝ) ≠ 0 := by exact_mod_cast hQ.a_ne_zero
  have hx : Q.rootPlus ^ 2 = ((-Q.b / Q.a : ℚ) : ℝ) * Q.rootPlus -
      ((Q.c / Q.a : ℚ) : ℝ) := by
    push_cast
    field_simp
    nlinarith [BinaryQF.rootPlus_satisfies_quadratic Q hQ]
  have hy : Q.rootMinus ^ 2 = ((-Q.b / Q.a : ℚ) : ℝ) * Q.rootMinus -
      ((Q.c / Q.a : ℚ) : ℝ) := by
    push_cast
    field_simp
    nlinarith [BinaryQF.rootMinus_satisfies_quadratic Q hQ]
  have hxy : Q.rootPlus ≠ Q.rootMinus := by
    intro heq
    have hplus := BinaryQF.two_mul_a_mul_rootPlus Q hQ.a_ne_zero
    have hminus := BinaryQF.two_mul_a_mul_rootMinus Q hQ.a_ne_zero
    have hsqrt : 0 < Real.sqrt (Q.disc : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hQ.disc_pos)
    rw [heq] at hplus
    nlinarith
  exact SIC.exists_pos_sfModularCocycleRealTotal_eq_mul_neg hx hy hxy
    hQ.rootPlus_irrational hr hA hfix hj

end SIC

end
