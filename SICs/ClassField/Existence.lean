/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Existence.Descent
import SICs.ClassField.Existence.Kummer

/-!
# The existence theorem for subgroups with finite support

Every finite-index subgroup `U` of the idèle class group containing the classes of the unit
idèles away from a finite set of primes is the norm group of a finite abelian extension of `K`
inside its algebraic closure.

This module follows Childress, *Class Field Theory* (2009), Chapter VI, Theorem 2.7, with the
reduction to roots of unity of p. 139 and the Kummer case Theorem 2.6. The hypothesis that `U`
contains $U_K^S$ for a finite `S` replaces Childress's openness: it is the only consequence of
openness his proof uses, and the ray subgroups supply it directly. It is the existence input of
the narrow ray class field `exists_narrowRayClassField`.

## The argument

Let $n = [C_K:U]$, so $C_K^n\subseteq U$. Put $K' = K(\zeta_n)$, abelian over `K`. Enlarge `S`
to a finite set $S_1$ containing the primes dividing `n` and the primes below a set of ideal-class
representatives of `K'`, and let $S'$ be the set of primes of `K'` above $S_1$. The Kummer field
$M' = K'(\sqrt[n]{\mathcal O_{K',S'}^\times})$ has norm group $\overline{E'}$
(`range_norm_sUnitKummer`) and is Galois over `K`, since its radicands are the $S_1$-units of
`K'`, which $\operatorname{Gal}(K'/K)$ preserves (`kummerExtension_normal_of_smul_mem`).

The pullback $V' = N_{K'/K}^{-1}(U)$ contains $\overline{E'}$: its nth powers map into
$C_K^n\subseteq U$ (`Subgroup.pow_index_mem`), while norms of unit idèles away from $S'$ lie in
$U_K^{S_1}\subseteq U_K^S$ (`map_norm_awayUnitSubgroup_le`). The fixed field $M''$ of
$\operatorname{Art}_{M'/K'}(V')$ has norm group $V'$ (`range_norm_fixedField`) and is Galois over
`K` because $V'$ is stable under $\operatorname{Gal}(K'/K)$ (`isGalois_fixedField_map_globalArtin`).
Descent along $K'/K$ (`exists_range_norm_eq_of_isAbelianGalois`) gives an abelian `M/K` inside
$M''$ with norm group `U`; its image in the algebraic closure of `K` has the same norm group
(`IdeleClassGroup.range_norm_congr`).
-/

noncomputable section

open IsDedekindDomain NumberField

namespace SIC

variable {K : Type*} [Field K] [NumberField K]

/-! ### Normality of the cyclotomic Kummer field -/

/-- The S-unit radical field for places above `S₁` is Galois over the base when `F/K` is
Galois. This is the normality step in Childress, *Class Field Theory*, Chapter VI,
proof of Theorem 2.7. -/
private theorem isGalois_sUnitKummer_placesAbove {F : Type*} [Field F] [NumberField F]
    [Algebra K F] [IsGalois K F] (n : ℕ) [NeZero n]
    (S₁ : Finset (HeightOneSpectrum (𝓞 K))) :
    IsGalois K (IdeleGroup.sUnitKummer F n (FinitePlace.placesAbove (L := F) S₁)) := by
  have hD : ∀ σ : F ≃ₐ[K] F, ∀ d ∈ IdeleGroup.sUnits (K := F) (L := F)
      (FinitePlace.placesAbove (L := F) S₁),
      σ • d ∈ IdeleGroup.sUnits (K := F) (L := F)
        (FinitePlace.placesAbove (L := F) S₁) := by
    intro σ d hd
    rw [IdeleGroup.sUnits_placesAbove (K := K) (L := F) S₁] at hd ⊢
    exact IdeleGroup.smul_mem_sUnits S₁ σ d hd
  exact isGalois_iff.mpr ⟨inferInstance,
    kummerExtension_normal_of_smul_mem (K := K) (n := n) hD⟩

/-! ### Containment in the pulled-back subgroup -/

/-- The local-power subgroup over `F` maps by the idèle norm into the pullback of `U` when
`n = [C_K : U]` and the classes of unit idèles away from `S` lie in `U`. This is the
containment in Childress, *Class Field Theory*, Chapter VI, proof of Theorem 2.7. -/
private theorem powerSubgroup_map_le_norm_comap {F : Type*} [Field F] [NumberField F]
    [Algebra K F] (U : Subgroup (NumberField.IdeleClassGroup (𝓞 K) K)) [U.FiniteIndex]
    (S S₁ : Finset (HeightOneSpectrum (𝓞 K))) (hSS₁ : S ⊆ S₁)
    (hS : IdeleGroup.awayUnitSubgroup S ≤
      U.comap (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K))) :
    (IdeleGroup.powerSubgroup U.index (FinitePlace.placesAbove (L := F) S₁) ∅).map
      (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)) ≤
      U.comap (IdeleClassGroup.norm (K := K) (L := F)) := by
  apply IdeleGroup.map_powerSubgroup_le (FinitePlace.placesAbove (L := F) S₁)
  · intro x
    change IdeleClassGroup.norm (K := K) (L := F) (x ^ U.index) ∈ U
    rw [map_pow]
    exact U.pow_index_mem _
  · rintro x ⟨d, hd, rfl⟩
    change IdeleClassGroup.norm (K := K) (L := F)
      (d : NumberField.IdeleClassGroup (𝓞 F) F) ∈ U
    rw [IdeleClassGroup.norm_mk]
    apply hS
    exact IdeleGroup.awayUnitSubgroup_anti hSS₁
      (IdeleGroup.map_norm_awayUnitSubgroup_le S₁ ⟨d, hd, rfl⟩)

/-! ### Transport to the algebraic closure -/

/-- Embedding an abelian class field into the algebraic closure preserves its norm group;
used by `exists_intermediateField_range_norm_eq`. -/
private theorem exists_fieldRange_norm (M : Type*) [Field M] [NumberField M] [Algebra K M]
    (hM : IsAbelianGalois K M)
    (U : Subgroup (NumberField.IdeleClassGroup (𝓞 K) K))
    (hU : (IdeleClassGroup.norm (K := K) (L := M)).range = U) :
    ∃ (E : IntermediateField K (AlgebraicClosure K)) (_ : NumberField E),
      IsAbelianGalois K E ∧ (IdeleClassGroup.norm (K := K) (L := E)).range = U := by
  let f : M →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let E := f.fieldRange
  let e : M ≃ₐ[K] E := f.equivFieldRange
  have : FiniteDimensional K E := e.toLinearEquiv.finiteDimensional
  have : NumberField E := NumberField.of_module_finite K E
  have : IsAbelianGalois K E := IsAbelianGalois.of_algHom e.symm.toAlgHom
  exact ⟨E, inferInstance, inferInstance, (IdeleClassGroup.range_norm_congr e).symm.trans hU⟩

/-- **The existence theorem**: a finite-index subgroup `U` of $C_K$ containing the classes of
the unit idèles away from a finite set `S` of primes, $U_K^S$, is the norm group of a finite
abelian extension of `K` in its algebraic closure. Childress, *Class Field Theory*,
Chapter VI, Theorem 2.7, with the finite-support hypothesis in place of openness. -/
theorem exists_intermediateField_range_norm_eq
    (U : Subgroup (NumberField.IdeleClassGroup (𝓞 K) K)) [U.FiniteIndex]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : IdeleGroup.awayUnitSubgroup S ≤
      U.comap (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K))) :
    ∃ (M : IntermediateField K (AlgebraicClosure K)) (_ : NumberField M),
      IsAbelianGalois K M ∧ (IdeleClassGroup.norm (K := K) (L := M)).range = U := by
  let n := U.index
  have : NeZero n := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  let F := CyclotomicField n K
  have : IsAbelianGalois K F := IsCyclotomicExtension.isAbelianGalois {n} K F
  let ζ := IsCyclotomicExtension.zeta n K F
  have hζ : IsPrimitiveRoot ζ n := IsCyclotomicExtension.zeta_spec n K F
  obtain ⟨S₁, hSS₁, hnS, hclass⟩ :=
    IdeleGroup.exists_support_sIdealClass (K := K) (L := F) n S
  let S' := FinitePlace.placesAbove (L := F) S₁
  let M' := IdeleGroup.sUnitKummer F n S'
  have : IsAbelianGalois F M' :=
    IdeleGroup.sUnitKummer_isAbelianGalois hζ (NeZero.pos n) S'
  have : IsGalois K M' := isGalois_sUnitKummer_placesAbove n S₁
  let V := U.comap (IdeleClassGroup.norm (K := K) (L := F))
  have hM' : (IdeleClassGroup.norm (K := F) (L := M')).range ≤ V := by
    rw [IdeleGroup.range_norm_sUnitKummer hζ S' hnS hclass]
    exact powerSubgroup_map_le_norm_comap U S S₁ hSS₁ hS
  let M'' := IntermediateField.fixedField (V.map (globalArtin (K := F) M'))
  have hM'' : (IdeleClassGroup.norm (K := F) (L := M'')).range = V :=
    range_norm_fixedField hM'
  have : IsGalois K M'' := isGalois_fixedField_map_globalArtin
    (fun σ x hx => IdeleClassGroup.smul_mem_comap_norm U σ hx)
  obtain ⟨M, hM, hUM⟩ := exists_range_norm_eq_of_isAbelianGalois (F := F)
    (N := M'') (W := U) hM''
  exact exists_fieldRange_norm M hM U hUM

end SIC
