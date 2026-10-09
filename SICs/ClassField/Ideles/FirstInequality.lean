/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.SIdeleClasses
import SICs.ClassField.Ideles.NormResidues
import SICs.ClassField.SUnits.Cohomology
import SICs.ClassField.Ideles.SIdeleCohomology

/-!
# The first inequality of global class field theory

For a cyclic extension of number fields, the idèle class group has Herbrand quotient
$[L:K]$, and its norm-residue quotient has at least that many elements.

The argument follows Childress, *Class Field Theory* (2009), Chapter IV, Propositions 3.3,
5.7, 5.10 and Corollary 5.11. The statement is Milne, *Class Field Theory*, version 4.03 (2020),
Chapter VII, Theorem 4.3, whose proof uses $S$-units instead of ordinary units.

## The argument

Let $E_L$ be the idèles that are units at every finite place and $U_L=\mathcal O_L^\times$.
The sequence $0\to U_L\to E_L\to C_L$ is exact and its cokernel is finite, since it
embeds into the ordinary ideal class group. The first two representations have finite Tate
groups, so the third does too. Multiplicativity, with the finite cokernel contributing one,
gives $h(E_L)=h(U_L)h(C_L)$. The ordinary-unit and archimedean formulas give
$[L:K]h(U_L)=h(E_L)$; cancelling nonzero $h(U_L)$ yields $h(C_L)=[L:K]$.
The denominator $|\widehat H^{-1}(G,C_L)|$ is a positive integer, so the numerator
$|\widehat H^0(G,C_L)|$ is at least $[L:K]$. Norm-residue equivalences identify the numerator
with both $C_K/N_{L/K}C_L$ and $I_K/(K^\times N_{L/K}I_L)$, giving Milne's Corollary 4.4.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField

namespace SIC.IdeleClassGroup

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

/-! ### The ordinary-unit sequence

The ordinary units embed in the idèles that are units at every finite place. Their quotient
maps into idèle classes with finite cokernel. The finite-cokernel multiplicativity theorem
therefore transfers the two ordinary-unit formulas to $C_L$. -/

/-- For cyclic $L/K$, the idèle class group has finite Tate groups, using ordinary units and
the finite ordinary ideal class group. Childress, *Class Field Theory* (2009), Chapter IV,
Propositions 3.3, 5.7, 5.10 and Corollary 5.11. -/
theorem hasHerbrandQuotient :
    Representation.HasHerbrandQuotient
      (_root_.Representation.ofMulDistribMulAction (L ≃ₐ[K] L)
        (NumberField.IdeleClassGroup (𝓞 L) L)) := by
  exact Representation.HasHerbrandQuotient.of_exact_of_finite_coker
    (IdeleGroup.sUnitsToSSubrep_injective (K := K) (L := L) ∅)
    (IdeleGroup.exact_sUnitsToSSubrep_sClassMapLinear (K := K) (L := L) ∅)
    (IdeleGroup.finite_sClassMapLinear_cokernel (K := K) (L := L))
    (IdeleGroup.hasHerbrandQuotient_ordinaryUnits (K := K) (L := L))
    (IdeleGroup.hasHerbrandQuotient_sSubrep_empty (K := K) (L := L))

/-- For cyclic $L/K$, $h(C_L)=[L:K]$, computed from ordinary units and ordinary-unit idèles.
Childress, *Class Field Theory* (2009), Chapter IV, Corollary 5.11. -/
theorem herbrandQuotient :
    Representation.herbrandQuotient
      (_root_.Representation.ofMulDistribMulAction (L ≃ₐ[K] L)
        (NumberField.IdeleClassGroup (𝓞 L) L)) = (Module.finrank K L : ℚ) := by
  classical
  let wi : ∀ v : InfinitePlace K, InfinitePlace.PlaceAbove (L := L) v :=
    fun _ => Classical.choice inferInstance
  have hU := IdeleGroup.hasHerbrandQuotient_ordinaryUnits (K := K) (L := L)
  have hmul := Representation.herbrandQuotient_eq_mul_of_finite_coker
    (IdeleGroup.sUnitsToSSubrep_injective (K := K) (L := L) ∅)
    (IdeleGroup.exact_sUnitsToSSubrep_sClassMapLinear (K := K) (L := L) ∅)
    (IdeleGroup.finite_sClassMapLinear_cokernel (K := K) (L := L)) hU
    (hasHerbrandQuotient (K := K) (L := L))
  apply mul_left_cancel₀ ((Representation.hasHerbrandQuotient_iff_ne_zero _).mp hU)
  calc
    _ = Representation.herbrandQuotient
        (IdeleGroup.sSubrep (K := K) (L := L) ∅).toRepresentation := hmul.symm
    _ = (Module.finrank K L : ℚ) * Representation.herbrandQuotient
        (IdeleGroup.ordinaryUnitsRep (K := K) (L := L)) :=
      (IdeleGroup.herbrandQuotient_sSubrep_empty wi).trans
        (IdeleGroup.herbrandQuotient_ordinaryUnits wi).symm
    _ = _ := mul_comm _ _

/-! ### Norm residues and the first inequality

The degree-zero Tate group is the quotient by norms. Its order is the numerator of
$h(C_L)$, while the degree-minus-one Tate group has positive order. -/

/-- The idèle-class form $[L:K]\le |C_K/N_{L/K}C_L|$ of the first inequality, via
`tateZeroEquiv`. Milne, *Class Field Theory*, Chapter VII, Corollary 4.4. -/
theorem firstInequality :
    Module.finrank K L ≤
      Nat.card (NumberField.IdeleClassGroup (𝓞 K) K ⧸
        (norm (K := K) (L := L)).range) := by
  let ρ := _root_.Representation.ofMulDistribMulAction (L ≃ₐ[K] L)
    (NumberField.IdeleClassGroup (𝓞 L) L)
  have hden : (1 : ℚ) ≤ Nat.card (Representation.TateNegOne ρ) := by
    exact_mod_cast (@Nat.card_pos (Representation.TateNegOne ρ) ⟨0⟩
      (hasHerbrandQuotient (K := K) (L := L)).finite_tateNegOne)
  have hnum : 0 ≤ (Nat.card (Representation.TateZero ρ) : ℚ) := Nat.cast_nonneg _
  have hle : (Module.finrank K L : ℚ) ≤ Nat.card (Representation.TateZero ρ) := by
    calc
      _ = (Nat.card (Representation.TateZero ρ) : ℚ) /
            Nat.card (Representation.TateNegOne ρ) := by
          rw [← Representation.herbrandQuotient, herbrandQuotient (K := K) (L := L)]
      _ ≤ _ := div_le_self hnum hden
  have hcard : Nat.card (Representation.TateZero ρ) =
      Nat.card (NumberField.IdeleClassGroup (𝓞 K) K ⧸
        (norm (K := K) (L := L)).range) :=
    Nat.card_congr (tateZeroEquiv (K := K) (L := L)).toEquiv
  rw [hcard] at hle
  exact_mod_cast hle

end SIC.IdeleClassGroup

namespace SIC.IdeleGroup

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

/-! ### The idèle form

The norm-residue equivalence carries the idèle-class bound back to the index appearing in
Milne's statement. -/

/-- The first inequality $[I_K:K^\times N_{L/K}I_L]\ge [L:K]$ for cyclic $L/K$.
Milne, *Class Field Theory*, Chapter VII, Corollary 4.4. -/
theorem firstInequality :
    Module.finrank K L ≤ Nat.card (NumberField.IdeleGroup (𝓞 K) K ⧸
      (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (norm (K := K) (L := L)).range)) := by
  calc
    _ ≤ Nat.card (NumberField.IdeleClassGroup (𝓞 K) K ⧸
        (IdeleClassGroup.norm (K := K) (L := L)).range) :=
      IdeleClassGroup.firstInequality (K := K) (L := L)
    _ = _ := (Nat.card_congr (IdeleClassGroup.normResidueEquiv
      (K := K) (L := L))).symm

end SIC.IdeleGroup
