/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Reciprocity.Cyclic

/-!
# Abelian Artin reciprocity

Every finite abelian extension has a modulus supported on its ramified places for which the
Artin map vanishes on the principal congruent idèles.

This module follows Childress, *Class Field Theory* (2009), Chapter V, proof of Theorem 2.1(ii), p.
114, where Artin reciprocity passes from cyclic to abelian extensions. It supplies the moduli on
which `SICs.ClassField.Reciprocity.GlobalArtinMap` defines the global Artin map. Childress chooses a
modulus divisible by an admissible modulus of every cyclic subextension; here the property the
consumer needs is named `IsReciprocityModulus`, and its existence is proved with support exactly the
ramified places, so that the Artin map can be evaluated at every unramified prime.

## The argument

*Cyclic subextensions separate.* An automorphism trivial on every cyclic subextension is
trivial (`IsAbelianGalois.eq_one_of_forall_isCyclic` in `SICs.FieldTheory.Abelian`).

*Reciprocity moduli.* For each cyclic subextension `E` choose a modulus $\mathfrak m_E$ with
$E^+_{K,\mathfrak m_E}\subseteq N_{E/K}J_E$ supported on the ramified places of `E`
(`IdeleGroup.exists_raySubgroup_le_range_norm`), and let $\mathfrak m$ be their product times the
primes ramified in `L`. Its support is the set of ramified places of `L`, and
$E^+_{K,\mathfrak m}\subseteq E^+_{K,\mathfrak m_E}$ (`IdeleGroup.raySubgroup_mono`), so Artin
reciprocity for the cyclic `E/K` (`IdeleGroup.artinMap_toPrincipalIdeal_eq_one`) gives
$\psi^S_{E/K}((\alpha)) = 1$ for every principal congruent idèle $\alpha$. The Artin symbol
$\psi^S_{L/K}((\alpha))$ restricts to these on every cyclic `E` (`artinMap_restrictNormal`), so it
is trivial by separation.

*Subextensions.* A reciprocity modulus of `L/K` is one of every subextension, by restriction of
Artin symbols.
-/

noncomputable section

open IsDedekindDomain NumberField

namespace SIC

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-! ### Reciprocity moduli -/

variable (L) in
/-- A **reciprocity modulus** of a finite abelian extension `L/K`: a nonzero modulus `m` whose
support `S` contains the primes ramified in `L` and for which $\psi^S_{L/K}((\alpha)) = 1$ for
every principal congruent idèle. By cyclic Artin reciprocity, the admissible cyclic moduli of
Childress, *Class Field Theory*, Chapter V, §2, satisfy this condition
(`IsReciprocityModulus.of_isCyclic`,
`exists_isReciprocityModulus`). -/
structure IsReciprocityModulus [IsAbelianGalois K L] (m : Ideal (𝓞 K)) : Prop where
  /-- The modulus is nonzero. -/
  ne_bot : m ≠ ⊥
  /-- The primes outside the support are unramified in `L`. -/
  unramified : FinitePlace.ramifiedSet K L ⊆ FinitePlace.modulusSupport m
  /-- The Artin map vanishes on the principal congruent idèles. -/
  artinMap_eq_one : ∀ a : Kˣ,
    NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a ∈ IdeleGroup.congruentSubgroup Set.univ m →
      artinMap L (FinitePlace.modulusSupport m) (toPrincipalIdeal (𝓞 K) K a) = 1

/-- **Artin reciprocity for cyclic extensions** gives reciprocity moduli: a nonzero modulus
whose support contains the ramified primes and whose ray subgroup lies in
$K^\times N_{L/K}J_L$. This applies
`IdeleGroup.artinMap_toPrincipalIdeal_eq_one`. -/
theorem IsReciprocityModulus.of_isCyclic [IsAbelianGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    {m : Ideal (𝓞 K)} (hm : m ≠ ⊥)
    (hS : FinitePlace.ramifiedSet K L ⊆ FinitePlace.modulusSupport m)
    (hray : IdeleGroup.raySubgroup Set.univ m ≤
      NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (IdeleGroup.norm (K := K) (L := L)).range) :
    IsReciprocityModulus L m := by
  exact ⟨hm, hS, fun a ha ↦ IdeleGroup.artinMap_toPrincipalIdeal_eq_one m hS hray a ha⟩

/-- A reciprocity modulus of `L/K` is a reciprocity modulus of every abelian subextension `E`,
given as a field in a tower `K ⊆ E ⊆ L`. -/
theorem IsReciprocityModulus.of_tower [IsAbelianGalois K L] (E : Type*) [Field E]
    [NumberField E] [Algebra K E] [Algebra E L] [IsScalarTower K E L] [IsAbelianGalois K E]
    {m : Ideal (𝓞 K)} (h : IsReciprocityModulus L m) : IsReciprocityModulus E m := by
  refine ⟨h.ne_bot, ?_, ?_⟩
  · exact FinitePlace.ramificationIdx_below_eq_one (FinitePlace.modulusSupport m)
      h.unramified
  · intro a ha
    rw [← artinMap_restrictNormal (FinitePlace.modulusSupport m) h.unramified E]
    rw [h.artinMap_eq_one a ha]
    exact map_one (AlgEquiv.restrictNormalHom E)

/-- A common cyclic norm modulus for `exists_isReciprocityModulus`, obtained by multiplying
the cyclic subextension moduli and a modulus supported on the ramified places. -/
private theorem exists_common_cyclic_ray_modulus [IsAbelianGalois K L] :
    ∃ m : Ideal (𝓞 K), m ≠ ⊥ ∧
      FinitePlace.modulusSupport m = FinitePlace.ramifiedSet K L ∧
      ∀ E : IntermediateField K L, IsCyclic (E ≃ₐ[K] E) →
        IdeleGroup.raySubgroup Set.univ m ≤ (IdeleGroup.norm (K := K) (L := E)).range := by
  classical
  let S := FinitePlace.ramifiedSet K L
  have hfinite : Finite (IntermediateField K L) :=
    Finite.of_equiv _ (IsGalois.intermediateFieldEquivSubgroup (F := K) (E := L)).symm.toEquiv
  let C := {E : IntermediateField K L // IsCyclic (E ≃ₐ[K] E)}
  have : Fintype C := Fintype.ofFinite C
  have hcyclic : ∀ E : C, ∃ m : Ideal (𝓞 K), m ≠ ⊥ ∧
      IdeleGroup.raySubgroup Set.univ m ≤ (IdeleGroup.norm (K := K) (L := E.1)).range ∧
      FinitePlace.modulusSupport m ⊆ S := by
    intro E
    have hE : IsCyclic (E.1 ≃ₐ[K] E.1) := E.2
    obtain ⟨m, hm, _, hray, hsupport⟩ :=
      IdeleGroup.exists_raySubgroup_le_range_norm (K := K) (L := E.1) ∅
    have hsupport' : FinitePlace.modulusSupport m ⊆ FinitePlace.ramifiedSet K E.1 := by
      simpa only [Finset.empty_union] using hsupport
    exact ⟨m, hm, hray, hsupport'.trans
      (FinitePlace.ramifiedSet_subset_ramifiedSet K E.1 L)⟩
  choose m hm hray hsupport using hcyclic
  let m₀ : Ideal (𝓞 K) := ∏ v ∈ S, v.asIdeal
  have hm₀ : m₀ ≠ ⊥ := FinitePlace.prod_asIdeal_ne_bot S
  let M : Ideal (𝓞 K) := m₀ * ∏ E : C, m E
  have hprod : (∏ E : C, m E) ≠ ⊥ := by
    change (∏ E : C, m E) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr (fun E _ ↦ hm E)
  have hM : M ≠ ⊥ := mul_ne_zero hm₀ hprod
  have hprodSupport : FinitePlace.modulusSupport (∏ E : C, m E) ⊆ S := by
    rw [FinitePlace.modulusSupport_prod Finset.univ m (fun E _ ↦ hm E)]
    exact Finset.biUnion_subset.mpr (fun E _ ↦ hsupport E)
  have hMS : FinitePlace.modulusSupport M = S := by
    change FinitePlace.modulusSupport (m₀ * ∏ E : C, m E) = S
    rw [mul_comm, show m₀ = ∏ v ∈ S, v.asIdeal from rfl,
      FinitePlace.modulusSupport_mul_prod_asIdeal hprod S]
    exact Finset.union_eq_right.mpr hprodSupport
  refine ⟨M, hM, hMS, ?_⟩
  intro E hE
  let E' : C := ⟨E, hE⟩
  have hle : M ≤ m E' :=
    Ideal.mul_le_right.trans (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ E')))
  exact (IdeleGroup.raySubgroup_mono Set.univ hM hle).trans (hray E')

/-- **Every finite abelian extension has a reciprocity modulus**, with support exactly the
places ramified in `L`. Childress, *Class Field Theory*, Chapter V, proof of Theorem 2.1(ii),
p. 114, with the modulus chosen as described in the module docstring. -/
theorem exists_isReciprocityModulus [IsAbelianGalois K L] :
    ∃ m : Ideal (𝓞 K), IsReciprocityModulus L m ∧
      FinitePlace.modulusSupport m = FinitePlace.ramifiedSet K L := by
  obtain ⟨M, hM, hMS, hray⟩ := exists_common_cyclic_ray_modulus (K := K) (L := L)
  have hUnram : FinitePlace.ramifiedSet K L ⊆ FinitePlace.modulusSupport M := by
    rw [hMS]
  refine ⟨M, ⟨hM, hUnram, ?_⟩, hMS⟩
  intro a ha
  apply IsAbelianGalois.eq_one_of_forall_isCyclic
  intro E hE
  have hEunram : FinitePlace.ramifiedSet K E ⊆ FinitePlace.modulusSupport M := by
    rw [hMS]
    exact FinitePlace.ramifiedSet_subset_ramifiedSet K E L
  have hcyclic : IsCyclic (E ≃ₐ[K] E) := hE
  have hrecE : IsReciprocityModulus E M :=
    IsReciprocityModulus.of_isCyclic hM hEunram ((hray E hE).trans le_sup_right)
  rw [artinMap_restrictNormal (FinitePlace.modulusSupport M) hUnram E]
  exact hrecE.artinMap_eq_one a ha

end SIC
