/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Local.PrincipalUnitPowers
import SICs.PowerIndex
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.GroupTheory.IndexNSmul

/-!
# Power indices in finite completions

The exact indices of nth powers in local multiplicative groups and their integral units.

This follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, Proposition 6.8,
at the finite completions of number fields. Its small-neighborhood linearization is implemented
by the polynomial contraction argument of Serre, *Local Fields* (1979), Chapter XIV, §4,
Proposition 9, through `exists_unitSubgroup_powerIndex`.

## The argument

On a sufficiently small subgroup of principal units, nth powering has the same index
as multiplication by n on an integral additive lattice. The power map scales distances by
$|n|_v$ on a sufficiently small ball; its quotient is identified with $\mathcal O_v/n\mathcal O_v$.
Finite quotients preserve the ratio of the cokernel and kernel cardinalities. The kernel consists
of nth roots
of unity, and the valuation sequence supplies one further factor of n for the full
multiplicative group. The norm is normalized by the size of the residue field.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped SIC.FinitePlace

namespace SIC.FinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-! ### The integral unit index

Finite-index invariance carries the calculation on a small principal-unit group to all
integral units; the remaining kernel is the group of roots of unity. -/

/-- Local roots of unity are integral units; supplies `powKerEquivRootsOfUnity` with its
hypothesis in `card_units_powerQuotient`. -/
private theorem rootsOfUnity_le_unitGroup (v : HeightOneSpectrum (𝓞 K))
    {n : ℕ} (hn : n ≠ 0) : rootsOfUnity n (v.adicCompletion K) ≤ unitGroup v := by
  intro x hx
  apply (unitsValuation_eq_one_iff v).mp
  have hpow : unitsValuation v x ^ n = 1 := by
    rw [← map_pow, (mem_rootsOfUnity n x).mp hx, map_one]
  exact (pow_eq_one_iff_left hn).mp hpow

/-- Integral local units satisfy $[U_v:U_v^n]=|\mu_n(K_v)|/|n|_v$.
Milne, *Class Field Theory*, Chapter VII, Proposition 6.8, finite-place unit clause. -/
theorem card_unitGroup_powerQuotient (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : 0 < n) :
    (Nat.card (unitGroup v ⧸
      (powMonoidHom n : unitGroup v →* unitGroup v).range) : ℝ) =
      Nat.card (rootsOfUnity n (v.adicCompletion K)) / ‖(n : v.adicCompletion K)‖ := by
  obtain ⟨H, hH, hinj, hindex⟩ := exists_unitSubgroup_powerIndex v hn
  have : H.FiniteIndex := hH
  have hker : Nat.card (powMonoidHom n : H →* H).ker = 1 := by
    rw [MonoidHom.ker_eq_bot _ hinj]
    simp
  have h := SIC.index_pow_mul_card_ker_of_finiteIndex H n
  rw [hker, mul_one, Nat.card_congr
    (powKerEquivRootsOfUnity n (unitGroup v) (rootsOfUnity_le_unitGroup v hn.ne'))] at h
  change ((powMonoidHom (α := unitGroup v) n).range.index : ℝ) = _
  rw [h, Nat.cast_mul, hindex]
  ring

/-! ### The full multiplicative index

The valuation splits the multiplicative group as the product of integral units and $\mathbb Z$,
so the power index gains the factor $n$. -/

/-- The valuation splitting contributes a factor of $n$ to the index of $n$th powers.
Milne, *Class Field Theory*, Chapter VII, Proposition 6.8, proof. -/
theorem index_units_pow (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (powMonoidHom (α := (v.adicCompletion K)ˣ) n).range.index =
      (powMonoidHom (α := unitGroup v) n).range.index * n := by
  have hprod : (powMonoidHom (α := unitGroup v × Multiplicative ℤ) n).range =
      (powMonoidHom (α := unitGroup v) n).range.prod
        (powMonoidHom (α := Multiplicative ℤ) n).range := by
    exact MonoidHom.range_prodMap (powMonoidHom (α := unitGroup v) n)
      (powMonoidHom (α := Multiplicative ℤ) n)
  rw [← MulEquiv.map_range_powMonoidHom (unitsEquivUnitGroupProd v).symm n,
    Subgroup.index_map_equiv, hprod, Subgroup.index_prod]
  congr 1
  change (nsmulAddMonoidHom (α := ℤ) n).range.index = n
  simpa using AddSubgroup.index_range_nsmul ℤ n

/-- The full local multiplicative group satisfies
$[K_v^\times:K_v^{\times n}]=n|\mu_n(K_v)|/|n|_v$.
Milne, *Class Field Theory*, Chapter VII, Proposition 6.8, finite-place clause. -/
theorem card_units_powerQuotient (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : 0 < n) :
    (Nat.card ((v.adicCompletion K)ˣ ⧸
      (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) : ℝ) =
      n * Nat.card (rootsOfUnity n (v.adicCompletion K)) / ‖(n : v.adicCompletion K)‖ := by
  change ((powMonoidHom (α := (v.adicCompletion K)ˣ) n).range.index : ℝ) = _
  rw [index_units_pow, Nat.cast_mul]
  change (Nat.card (unitGroup v ⧸ (powMonoidHom n).range) : ℝ) * n = _
  rw [card_unitGroup_powerQuotient v hn]
  ring

end SIC.FinitePlace
