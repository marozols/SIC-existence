/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.SUnits.LogLattice
import SICs.GroupCohomology.PermutationLattice

/-!
# The Herbrand quotient of ordinary units

For a cyclic extension of number fields, the Herbrand quotient of the ordinary units is the
product of the local degrees at the infinite places, divided by the global degree.

This module follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII,
Proposition 3.1, at the empty set of finite places, using the ordinary-unit logarithmic lattice
in its proof.

## The argument

The infinite places of L form a Galois set whose fibers over the infinite places of K are
transitive. The integer permutation lattice therefore has Herbrand quotient the product of the
infinite local degrees. The augmented logarithm of ordinary units has finite kernel and maps
onto a full stable real lattice in the same permutation representation. Comparing the two
lattices gives the ordinary-unit quotient after removing the trivial integer summand, whose
quotient is [L:K].
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField NumberField.LiesOver SIC.FinitePlace SIC.InfinitePlace

namespace SIC.IdeleGroup

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-! ### The infinite-place permutation lattice

Grouping infinite places by restriction to K turns their integer permutation lattice into the
product over base places. Each fiber is one Galois orbit, with stabilizer order equal to its
local completion degree. -/

/-- A chosen place of L lies in the fiber over its base place; used by
`herbrandQuotient_infinitePermutation`. -/
private def chosenInfinite
    (wi : ∀ v : InfinitePlace K, InfinitePlace.PlaceAbove (L := L) v)
    (v : InfinitePlace K) :
    {w : InfinitePlace L // InfinitePlace.below (K := K) w = v} := by
  refine ⟨(wi v).1, ?_⟩
  exact InfinitePlace.below_eq_of_liesOver v (wi v).1

omit [NumberField K] [NumberField L] in
/-- Every place in a fiber is conjugate to the chosen place; used by
`herbrandQuotient_infinitePermutation`. -/
private theorem chosenInfinite_transitive [IsGalois K L]
    (wi : ∀ v : InfinitePlace K, InfinitePlace.PlaceAbove (L := L) v)
    (v : InfinitePlace K) (y : InfinitePlace L)
    (hy : InfinitePlace.below (K := K) y = v) :
    ∃ σ : L ≃ₐ[K] L, σ • (chosenInfinite (L := L) wi v).1 = y := by
  let : y.LiesOver v := by rw [← hy]; infer_instance
  exact InfinitePlace.exists_smul_eq v (wi v).1 y

/-- The infinite-place integer permutation lattice has quotient
$\prod_{v\mid\infty}[L_{w_v}:K_v]$. This is Milne, *Class Field Theory*, Chapter VII,
Proposition 3.1, infinite-place permutation calculation, with the infinite places separated
from finite S. -/
private theorem herbrandQuotient_infinitePermutation [IsGalois K L]
    (wi : ∀ v : InfinitePlace K, InfinitePlace.PlaceAbove (L := L) v) :
    Representation.herbrandQuotient
      (SIC.Representation.permutation (k := ℤ) (G := L ≃ₐ[K] L) (X := InfinitePlace L)) =
      ∏ v : InfinitePlace K,
        (Module.finrank v.Completion (wi v).1.Completion : ℚ) := by
  classical
  calc
    _ = ∏ v : InfinitePlace K,
        (Nat.card (MulAction.stabilizer (L ≃ₐ[K] L)
          (chosenInfinite (L := L) wi v).1) : ℚ) := by
      exact Representation.herbrandQuotient_permutation_grouped
        (InfinitePlace.below (K := K)) (InfinitePlace.below_smul (L := L))
        (chosenInfinite (L := L) wi) (chosenInfinite_transitive (L := L) wi)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro v _
      exact_mod_cast (InfinitePlace.finrank_eq_card_stabilizer v (wi v).1).symm

/-! ### Ordinary units and the augmented logarithmic lattice

The image of the augmented logarithm is a full real lattice. Its finite kernel and surjection
onto that image transfer the permutation calculation to ordinary units times trivial ℤ. -/

/-- The infinite-place permutation lattice has finite Tate groups, by its local-degree
calculation; used by `herbrandQuotient_augmentedLog_eq_permutation`. -/
private theorem hasHerbrandQuotient_infinitePermutation [IsGalois K L] :
    Representation.HasHerbrandQuotient
      (SIC.Representation.permutation (k := ℤ) (G := L ≃ₐ[K] L)
        (X := InfinitePlace L)) := by
  classical
  let wi : ∀ v : InfinitePlace K, InfinitePlace.PlaceAbove (L := L) v :=
    fun _ => Classical.choice inferInstance
  exact Representation.hasHerbrandQuotient_permutation_grouped
    (InfinitePlace.below (K := K)) (InfinitePlace.below_smul (L := L))
    (chosenInfinite (L := L) wi) (chosenInfinite_transitive (L := L) wi)

/-- The infinite-place part of Milne's lattices has the quotient of the integer permutation lattice.
The finite logarithmic kernel and the full real image give this comparison; used by
`hasHerbrandQuotient_ordinaryUnits` and `herbrandQuotient_ordinaryUnits`. -/
private theorem herbrandQuotient_augmentedLog_eq_permutation [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    Representation.herbrandQuotient
      ((ordinaryUnitsRep (K := K) (L := L)).prod
        (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) =
      Representation.herbrandQuotient
        (SIC.Representation.permutation (k := ℤ) (G := L ≃ₐ[K] L)
          (X := InfinitePlace L)) := by
  classical
  let A := augmentedLog (K := K) (L := L)
  let M := A.range
  have hdisc : DiscreteTopology M.toSubmodule := by
    change DiscreteTopology (LinearMap.range (augmentedLog (K := K) (L := L)).toLinearMap)
    infer_instance
  have hz : IsZLattice ℝ M.toSubmodule := by
    change IsZLattice ℝ (LinearMap.range (augmentedLog (K := K) (L := L)).toLinearMap)
    infer_instance
  let F := Representation.IntertwiningMap.rangeRestrict A
  have hker : Finite (LinearMap.ker F.toLinearMap) := by
    rw [show F.toLinearMap.ker = A.toLinearMap.ker from
      A.toLinearMap.ker_rangeRestrict]
    infer_instance
  have hcoker : Finite (M.toSubmodule ⧸ F.toLinearMap.range) := by
    rw [LinearMap.range_eq_top.mpr (Representation.IntertwiningMap.rangeRestrict_surjective A)]
    infer_instance
  exact (Representation.herbrandQuotient_eq_of_finite_ker_coker F hker hcoker).trans
    (Representation.herbrandQuotient_eq_permutation_of_isZLattice M)

/-- Ordinary units have a defined Herbrand quotient for a cyclic Galois extension. This is the
empty-S step of Milne, *Class Field Theory*, Chapter VII, Proposition 3.1. -/
theorem hasHerbrandQuotient_ordinaryUnits [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    Representation.HasHerbrandQuotient (ordinaryUnitsRep (K := K) (L := L)) := by
  have hn : Representation.herbrandQuotient
      ((ordinaryUnitsRep (K := K) (L := L)).prod
        (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) ≠ 0 := by
    rw [herbrandQuotient_augmentedLog_eq_permutation (L := L),
      ← Representation.hasHerbrandQuotient_iff_ne_zero]
    exact hasHerbrandQuotient_infinitePermutation (L := L)
  rw [Representation.herbrandQuotient_prod, Representation.herbrandQuotient_trivial] at hn
  exact (Representation.hasHerbrandQuotient_iff_ne_zero _).2 (mul_ne_zero_iff.mp hn).1

/-- The ordinary-unit quotient satisfies
$[L:K]h(\mathcal O_L^\times)=\prod_{v\mid\infty}[L_{w_v}:K_v]$.
This is the empty-S step of Milne, *Class Field Theory*, Chapter VII, Proposition 3.1. -/
theorem herbrandQuotient_ordinaryUnits [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (wi : ∀ v : InfinitePlace K, InfinitePlace.PlaceAbove (L := L) v) :
    (Module.finrank K L : ℚ) *
      Representation.herbrandQuotient (ordinaryUnitsRep (K := K) (L := L)) =
      ∏ v : InfinitePlace K,
        (Module.finrank v.Completion (wi v).1.Completion : ℚ) := by
  classical
  calc
    _ = (Fintype.card (L ≃ₐ[K] L) : ℚ) *
        Representation.herbrandQuotient (ordinaryUnitsRep (K := K) (L := L)) := by
      rw [← IsGalois.card_aut_eq_finrank K L, Nat.card_eq_fintype_card]
    _ = Representation.herbrandQuotient
        ((ordinaryUnitsRep (K := K) (L := L)).prod
          (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) := by
      rw [← Representation.herbrandQuotient_trivial (G := L ≃ₐ[K] L),
        mul_comm, ← Representation.herbrandQuotient_prod]
    _ = Representation.herbrandQuotient
        (SIC.Representation.permutation (k := ℤ) (G := L ≃ₐ[K] L)
          (X := InfinitePlace L)) := herbrandQuotient_augmentedLog_eq_permutation (L := L)
    _ = _ := herbrandQuotient_infinitePermutation (L := L) wi

end SIC.IdeleGroup
