/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.SUnits.Basic
import SICs.PowerIndex
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Finite valuations of S-units

The valuations of S-units at the finite places above S form a lattice of finite index in the
integer functions on those places. Together with ordinary units as the kernel, this is the
finite-place part of the S-unit theorem.

This follows Milne, *Algebraic Number Theory*, version 3.08, Theorem 5.11. The arithmetic
valuation sequence is the finite-place part of the lattices in Milne, *Class Field Theory*,
version 4.03, Chapter VII, Proposition 3.1.

## The argument

A finitely supported integer vector specifies a product of powers of prime fractional ideals.
The class number kills its ideal class, so a positive power has a generator in $L^\times$.
That generator is an S-unit, and its valuation vector is the prescribed vector multiplied by the
class number. Our valuation map uses $-\operatorname{ord}_w$, the opposite of Milne's exponent
convention. Rank additivity in the valuation sequence gives the S-unit rank: the number of
finite places above S plus the ordinary unit rank. The root-of-unity torsion and the free rank
give the order of the S-unit power-class quotient.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField nonZeroDivisors WithZero SIC.FinitePlace

namespace SIC.IdeleGroup

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-! ### The class-number argument

The fractional ideal attached to a valuation vector has the chosen exponents at the places
above S and exponent zero elsewhere. Its class-number power is principal. -/

/-- The arithmetic S-unit valuation is the logarithm of the corresponding prime valuation.
This component formula is used by `sUnitsValuationLinear_eq_neg_count` and the equivariant
valuation map. -/
theorem sUnitsValuationLinear_eq_log (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : sUnits (L := L) S) (w : FinitePlace.placesAbove (L := L) S) :
    sUnitsValuationLinear (L := L) S (Additive.ofMul x) w =
      WithZero.log (w.1.valuation L (x.1 : L)) := by
  rw [sUnitsValuationLinear_apply, sUnitsValuation_apply]
  have hv := FinitePlace.coe_unitsValuation w.1
    (finiteComponent L w.1 (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L x.1))
  rw [finiteComponent_unitEmbedding] at hv
  change ((FinitePlace.unitsValuation w.1 _) : ℤᵐ⁰) =
    Valued.v ((x.1 : L) : w.1.adicCompletion L) at hv
  rw [w.1.valuedAdicCompletion_eq_valuation'] at hv
  exact congrArg WithZero.log hv

/-- The arithmetic S-unit valuation is the negative count of the principal fractional ideal:
$\log v_w(x)=-\operatorname{ord}_w((x))$. This sign follows the `unitsValuation`
convention, which sends a uniformizer to $-1$ rather than its ideal exponent $+1$. -/
theorem sUnitsValuationLinear_eq_neg_count (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : sUnits (L := L) S) (w : FinitePlace.placesAbove (L := L) S) :
    sUnitsValuationLinear (L := L) S (Additive.ofMul x) w =
      -FractionalIdeal.count L w.1 (FractionalIdeal.spanSingleton (𝓞 L)⁰ (x.1 : L)) := by
  rw [sUnitsValuationLinear_eq_log,
    FractionalIdeal.count_spanSingleton w.1 (x.1 : L) x.1.ne_zero]
  simp

/-- A principal fractional ideal has order zero at $w$ exactly when its generator has
trivial $w$-valuation. Used by `finite_sUnitsValuation_cokernel`. -/
private theorem valuation_eq_one_of_count_zero (w : HeightOneSpectrum (𝓞 L))
    (x : Lˣ) (h : FractionalIdeal.count L w
      (FractionalIdeal.spanSingleton (𝓞 L)⁰ (x : L)) = 0) :
    w.valuation L (x : L) = 1 := by
  rw [FractionalIdeal.count_spanSingleton w (x : L) x.ne_zero] at h
  have hlog : WithZero.log (w.valuation L (x : L)) = 0 := by omega
  have hv : w.valuation L (x : L) ≠ 0 := by
    exact (Valuation.ne_zero_iff (w.valuation L)).2 x.ne_zero
  calc
    w.valuation L (x : L) = WithZero.exp (WithZero.log (w.valuation L (x : L))) :=
      (WithZero.exp_log hv).symm
    _ = 1 := by rw [hlog, WithZero.exp_zero]

/-- Extend a vector on the finite places above S by zero, with the opposite sign needed for
the valuation convention. Used by `finite_sUnitsValuation_cokernel`. -/
private def supportedExponents (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : FinitePlace.placesAbove (L := L) S → ℤ) :
    HeightOneSpectrum (𝓞 L) →₀ ℤ := by
  classical
  exact Finsupp.onFinset (FinitePlace.placesAbove (L := L) S)
    (fun w => if hw : w ∈ FinitePlace.placesAbove (L := L) S then -f ⟨w, hw⟩ else 0)
    (by
      intro w hw
      by_cases h : w ∈ FinitePlace.placesAbove (L := L) S
      · exact h
      · simp only [dite_eq_right h] at hw
        exact (hw rfl).elim)

/-- The supported exponent at a place above S is the negative target coordinate. -/
@[simp] private theorem supportedExponents_inside
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : FinitePlace.placesAbove (L := L) S → ℤ)
    (w : FinitePlace.placesAbove (L := L) S) :
    supportedExponents (L := L) S f w.1 = -f w := by
  classical
  simp only [supportedExponents, Finsupp.onFinset_apply, dite_eq_left w.2]

/-- The supported exponent vanishes outside S. -/
@[simp] private theorem supportedExponents_outside
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : FinitePlace.placesAbove (L := L) S → ℤ)
    (w : HeightOneSpectrum (𝓞 L))
    (hw : w ∉ FinitePlace.placesAbove (L := L) S) :
    supportedExponents (L := L) S f w = 0 := by
  classical
  simp only [supportedExponents, Finsupp.onFinset_apply, dite_eq_right hw]

/-- The class number times any finite-place valuation vector is attained by an S-unit.
Milne, *Algebraic Number Theory*, version 3.08, Theorem 5.11, proof. -/
private theorem classNumber_smul_mem_valuation_range
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : FinitePlace.placesAbove (L := L) S → ℤ) :
    (NumberField.classNumber L : ℤ) • f ∈
      (sUnitsValuationLinear (L := L) S).range := by
  classical
  let e := supportedExponents (L := L) S f
  let J₀ : FractionalIdeal (𝓞 L)⁰ L := e.prod (fun w n => (w.asIdeal :
    FractionalIdeal (𝓞 L)⁰ L) ^ n)
  have hJ₀ : J₀ ≠ 0 := by
    classical
    dsimp [J₀, Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro w hw
      exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot))
  obtain ⟨x, hx0, hx⟩ :=
    FractionalIdeal.exists_classGroupCard_power_generator J₀ hJ₀
  let xUnit : Lˣ := Units.mk0 x hx0
  have hcount (w : HeightOneSpectrum (𝓞 L)) :
      FractionalIdeal.count L w (FractionalIdeal.spanSingleton (𝓞 L)⁰ x) =
        (NumberField.classNumber L : ℤ) * e w := by
    rw [← hx, FractionalIdeal.count_pow]
    rw [Nat.card_eq_fintype_card]
    change (NumberField.classNumber L : ℤ) *
      FractionalIdeal.count L w J₀ = _
    rw [show J₀ = e.prod (fun w n => (w.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ n) from rfl,
      FractionalIdeal.count_finsuppProd]
  have hxS : xUnit ∈ sUnits (L := L) S := by
    apply mem_sUnits_of_valuation S
    intro w hw
    apply valuation_eq_one_of_count_zero w xUnit
    change FractionalIdeal.count L w (FractionalIdeal.spanSingleton (𝓞 L)⁰ x) = 0
    rw [hcount, supportedExponents_outside S f w]
    · simp
    · simpa only [FinitePlace.mem_placesAbove] using hw
  refine ⟨Additive.ofMul (⟨xUnit, hxS⟩ : sUnits (L := L) S), ?_⟩
  funext w
  rw [sUnitsValuationLinear_eq_neg_count, show (xUnit : L) = x from rfl,
    hcount, supportedExponents_inside]
  simp

/-- The finite-place valuation image has finite index in the integer permutation lattice.
This is the finite-valuation step of Milne, *Algebraic Number Theory*, version 3.08,
Theorem 5.11. -/
theorem finite_sUnitsValuation_cokernel (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finite ((FinitePlace.placesAbove (L := L) S → ℤ) ⧸
      (sUnitsValuationLinear (L := L) S).range) := by
  classical
  apply Module.finite_of_fg_torsion
  intro q
  induction q using Quotient.inductionOn' with
  | _ f =>
    refine ⟨⟨(NumberField.classNumber L : ℤ), ?_⟩, ?_⟩
    · apply mem_nonZeroDivisors_iff_ne_zero.mpr
      exact_mod_cast NumberField.classNumber_ne_zero L
    change Submodule.Quotient.mk ((NumberField.classNumber L : ℤ) • f) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2
      (classNumber_smul_mem_valuation_range S f)

/-! ### Rank and power classes

The exact valuation sequence gives the S-unit rank. Its torsion is the roots of unity, so
the structure theorem for finitely generated abelian groups counts the power classes. -/

/-- The S-unit rank is $|T|+r_1(L)+r_2(L)-1$, where $T$ is the finite places of $L$
above S. Milne, *Algebraic Number Theory*, version 3.08, Theorem 5.11. -/
theorem finrank_sUnits (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Module.finrank ℤ (Additive (sUnits (L := L) S)) =
      (FinitePlace.placesAbove (L := L) S).card + Units.rank L := by
  let V := sUnitsValuationLinear (L := L) S
  have : V.range.toAddSubgroup.FiniteIndex :=
    AddSubgroup.finiteIndex_iff_finite_quotient.mpr
      (finite_sUnitsValuation_cokernel (L := L) S)
  have hrange : Module.finrank ℤ V.range = (FinitePlace.placesAbove (L := L) S).card := by
    have h := AddSubgroup.finrank_eq_of_finiteIndex V.range.toAddSubgroup
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using! h
  let U := Additive (sUnits (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K))))
  let eU : U ≃ₗ[ℤ] Additive (𝓞 L)ˣ :=
    (sUnitsEmptyEquiv (K := K) (L := L)).toAdditive.toIntLinearEquiv
  have h := V.ker.finrank_quotient_add_finrank
  rw [V.quotKerEquivRange.finrank_eq, hrange,
    (exact_emptySUnitsLinear_sUnitsValuationLinear (L := L) S).linearMap_ker_eq,
    (emptySUnitsLinear (L := L) S).finrank_range_of_inj (emptySUnitsLinear_injective (L := L) S),
    eU.finrank_eq, Units.finrank_eq] at h
  exact h.symm

omit [NumberField K] in
/-- The n-torsion in the S-unit group is the full group $\mu_n(L)$ of nth roots of unity.
This identifies the torsion factor in `card_sUnits_powerQuotient`. -/
def sUnitsPowKerEquivRoots {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (hn : n ≠ 0) :
    (powMonoidHom (α := sUnits (L := L) S) n).ker ≃ rootsOfUnity n L :=
  by
  have hH : rootsOfUnity n L ≤ sUnits (L := L) S := by
    intro x hx
    apply (pow_mem_sUnits_iff S x hn).1
    exact (mem_rootsOfUnity n x).mp hx ▸ (sUnits S).one_mem
  exact powKerEquivRootsOfUnity n (sUnits (L := L) S) hH

/-- The S-unit power classes have order $n^{|S|+r_1+r_2}$ when $\mu_n\subset K$.
Milne, *Class Field Theory*, Chapter VII, §6, construction preceding Lemma 6.2. -/
theorem card_sUnits_powerQuotient {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Nat.card (sUnits (K := K) (L := K) S ⧸
      (powMonoidHom n : sUnits (K := K) (L := K) S →*
        sUnits (K := K) (L := K) S).range) =
      n ^ (S.card + Nat.card (InfinitePlace K)) := by
  have : NeZero n := ⟨hn.ne'⟩
  have hcard : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
  change (powMonoidHom (α := sUnits (K := K) (L := K) S) n).range.index = _
  rw [index_range_pow_eq_card_ker_mul_pow n hn.ne',
    Nat.card_congr (sUnitsPowKerEquivRoots S n hn.ne'),
    hζ.card_rootsOfUnity, finrank_sUnits, FinitePlace.placesAbove_self, ← pow_succ']
  congr 1
  rw [Units.rank, Nat.card_eq_fintype_card]
  omega


end SIC.IdeleGroup
