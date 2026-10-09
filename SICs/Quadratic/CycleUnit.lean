/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.HJStabilizer
import SICs.Quadratic.ElementForms

/-!
# The stabilizer of a Hirzebruch--Jung cycle

Kopp's Proposition 7.7, positive half: every matrix fixing both roots of a reduced quadratic
irrational, or a reduced pair of real roots, with positive Jacobi denominators is a power `P^m` of
the cycle matrix.

This file proves the positive half of [72, Kopp (2024), Proposition 7.7, `prop:betatogamma`] in
its purely periodic case, for Kopp's cycle data [72, Kopp (2024), Definition 7.4,
`defn:cycledata`] of a reduced quadratic irrational `β = ρ_{Q,+}`, `0 < β' < 1 < β`, with `Q`
irreducible but not necessarily primitive: every `M ∈ SL₂(ℤ)` fixing `β` and `β'` with positive
Jacobi denominators at both is a power of `P = A_{0,ℓ}`, the cycle matrix of the minimal period
`ℓ`. The same statement holds for a reduced pair `0 < y < 1 < x` of real roots of a rational
quadratic.

## Mathematical argument

The conjugates `β'_n` along the rotation orbit form a companion sequence of the expansion with
values in `(0,1)`, periodic with the period of `β` (`SICs.Quadratic.ReducedForms`). So the general
stabilizer theorem of `SICs.SL2Z.HJStabilizer`, proved by the relative-minima argument, applies
and gives `M = P^m`. A reduced pair `0 < y < 1 < x` of roots of `X² - tX + n` is the pair of roots
of the reduced irreducible form `ofTraceNorm t n`, so the pair statement is the form statement
there.

## References

- [72, Kopp (2024), Definition 7.4, `defn:cycledata`] and [72, Kopp (2024), Proposition 7.7,
  `prop:betatogamma`].
-/

open MatrixGroups

namespace SIC.BinaryQF

/-! ### The minimal period

Kopp's `ℓ` is the period of the purely periodic expansion, `Function.minimalPeriod hjRotate β`;
the rotation orbit of a reduced irreducible form closes up, so `β` is a periodic point. -/

/-- **`β` is a periodic point of the rotation**, by `exists_hjPeriod_rootPlus_eq`. -/
theorem IsHJReduced.rootPlus_mem_periodicPts {Q : BinaryQF} (h : Q.IsHJReduced)
    (hirr : Q.IsIrreducible) : Q.rootPlus ∈ Function.periodicPts hjRotate := by
  obtain ⟨ℓ, hℓpos, hℓ⟩ := exists_hjPeriod_rootPlus_eq h hirr
  exact Function.mk_mem_periodicPts hℓpos hℓ

/-! ### The stabilizer of `β`

[72, Kopp (2024), Proposition 7.7, `prop:betatogamma`], purely periodic case, for matrices with
positive Jacobi denominators at both roots. -/

/-- **Every matrix fixing both roots with positive Jacobi denominators is `P^m`**,
[72, Kopp (2024), Proposition 7.7, `prop:betatogamma`] in its purely periodic case, positive half,
for a reduced irreducible form that need not be primitive. The conjugates `β'_n` along the rotation
orbit are a companion sequence with values in `(0,1)` closing up with the period of `β`, so
`exists_zpow_eq_of_flt_eq_self_of_isHJCompanion` applies. -/
theorem exists_zpow_eq_of_flt_rootPlus_rootMinus_eq {Q : BinaryQF}
    (hirr : Q.IsIrreducible) (h : Q.IsHJReduced) {M : SL(2, ℤ)}
    (hM : flt (M : Mat(2, ℤ)) Q.rootPlus = Q.rootPlus)
    (hM' : flt (M : Mat(2, ℤ)) Q.rootMinus = Q.rootMinus)
    (hj : 0 < fltDenominator (M : Mat(2, ℤ)) Q.rootPlus)
    (hj' : 0 < fltDenominator (M : Mat(2, ℤ)) Q.rootMinus) :
    ∃ m : ℤ, M = hjCycleMatrix Q.rootPlus (Function.minimalPeriod hjRotate Q.rootPlus) ^ m := by
  apply exists_zpow_eq_of_flt_eq_self_of_isHJCompanion (h.irrational_rootPlus hirr)
    h.one_lt_rootPlus (isHJCompanion_rootMinus_hjRotateForm_iterate h hirr)
    (rootMinus_hjRotateForm_iterate_mem_Ioo h hirr) (h.rootPlus_mem_periodicPts hirr)
  · rw [rootMinus_hjRotateForm_iterate_of_hjPeriod_eq h hirr
      (hjPeriod_minimalPeriod Q.rootPlus)]
    rfl
  · exact hM
  · exact hM'
  · exact hj
  · exact hj'

/-- **The stabilizer of a reduced pair of real roots**: if `0 < y < 1 < x` are the roots of
`X² - tX + n` with `t, n ∈ ℚ` and `x` irrational, every `M ∈ SL₂(ℤ)` fixing `x` and `y` with
positive Jacobi denominators at both is a power of the cycle matrix `P = A_{0,ℓ}` of `x`. This is
`exists_zpow_eq_of_flt_rootPlus_rootMinus_eq` at the form `ofTraceNorm t n`, which is
reduced and irreducible with roots `x` and `y` (`isHJReduced_ofTraceNorm`,
`isIrreducible_ofTraceNorm`, `rootPlus_ofTraceNorm`, `rootMinus_ofTraceNorm`). -/
theorem exists_zpow_eq_of_flt_eq_self_of_sq_eq {x y : ℝ} {t n : ℚ} (hx : x ^ 2 = t * x - n)
    (hy : y ^ 2 = t * y - n) (hirr : Irrational x) (hx1 : 1 < x) (hy01 : y ∈ Set.Ioo 0 1)
    {M : SL(2, ℤ)} (hM : flt (M : Mat(2, ℤ)) x = x)
    (hM' : flt (M : Mat(2, ℤ)) y = y)
    (hj : 0 < fltDenominator (M : Mat(2, ℤ)) x)
    (hj' : 0 < fltDenominator (M : Mat(2, ℤ)) y) :
    ∃ m : ℤ, M = hjCycleMatrix x (Function.minimalPeriod hjRotate x) ^ m := by
  have hxy : y < x := hy01.2.trans hx1
  have hplus := rootPlus_ofTraceNorm hxy hx hy
  have hminus := rootMinus_ofTraceNorm hxy hx hy
  have h := exists_zpow_eq_of_flt_rootPlus_rootMinus_eq
    (isIrreducible_ofTraceNorm hirr hx) (isHJReduced_ofTraceNorm hx1 hy01 hx hy)
    (M := M) (by rw [hplus]; exact hM) (by rw [hminus]; exact hM')
    (by rw [hplus]; exact hj) (by rw [hminus]; exact hj')
  rwa [hplus] at h

end SIC.BinaryQF
