/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Reciprocity.GlobalArtinMap

/-!
# Norm groups of abelian extensions

The norm groups of the subextensions of a finite abelian extension: inclusion of norm groups
reverses inclusion of fields, and every subgroup of the idèle class group containing a norm
group is the norm group of a subextension.

This module follows Childress, *Class Field Theory* (2009), Chapter VI, Proposition 1.1(i), (iv)
(the Ordering Theorem) and Corollary 1.2, and Milne, *Class Field Theory*, version 4.03 (2020),
Chapter V, Corollary 5.6, for the subfields of a fixed finite abelian extension. It supplies the
upward closure used by the cyclic descent of `SICs.ClassField.Existence.Descent`.

## The argument

Let `L/K` be finite abelian and `E` an intermediate field. Artin symbols restrict
(`globalArtin_restrictNormal`), and the kernel of $\operatorname{Art}_{E/K}$ is $N_{E/K}C_E$
(`ker_globalArtin`), so $\operatorname{Art}_{L/K}(x)$ fixes `E` exactly when
$x\in N_{E/K}C_E$.

*Ordering.* If $N_{E_1}\subseteq N_{E_2}$, every automorphism fixing $E_1$ is
$\operatorname{Art}_{L/K}(x)$ for some $x\in N_{E_1}\subseteq N_{E_2}$ (surjectivity), so it fixes
$E_2$; by the Galois correspondence $E_2\subseteq E_1$. The converse is the tower of norms.

*Upward closure.* If $N_{L/K}C_L\subseteq U$, let `E` be the fixed field of
$\operatorname{Art}_{L/K}(U)$. Then $x\in N_{E/K}C_E$ iff $\operatorname{Art}_{L/K}(x)$ lies in
$\operatorname{Art}_{L/K}(U)$, iff $x\in U\cdot\ker\operatorname{Art}_{L/K} = U$.

*Two abelian extensions.* Abelian extensions `L` and `M` of `K` not given in a common field embed
in an algebraic closure, where their compositum is finite abelian; ordering inside it shows that
$N_{M/K}C_M\subseteq N_{L/K}C_L$ gives a `K`-embedding of `L` into `M`.

*Norms in a tower.* The tower and restriction laws for global Artin symbols identify the
restriction to `L` of $\operatorname{Art}_{M/E}(x)$ with
$\operatorname{Art}_{L/K}(N_{E/K}x)$. If restriction is injective, the norm condition over `K`
therefore implies the norm condition over `E`.
-/

noncomputable section

open IsDedekindDomain NumberField

namespace SIC

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsAbelianGalois K L]

/-- The Artin symbol of `x` fixes an intermediate field `E` exactly when `x` is a norm from `E`:
$\operatorname{Art}_{L/K}(x)\in\operatorname{Gal}(L/E) \iff x\in N_{E/K}C_E$. Childress,
*Class Field Theory*, Chapter VI, proof of Proposition 1.1(iv). -/
theorem globalArtin_mem_fixingSubgroup_iff (E : IntermediateField K L)
    (x : NumberField.IdeleClassGroup (𝓞 K) K) :
    globalArtin L x ∈ E.fixingSubgroup ↔
      x ∈ (IdeleClassGroup.norm (K := K) (L := E)).range := by
  rw [← ker_globalArtin (K := K) (L := E), MonoidHom.mem_ker,
    ← globalArtin_restrictNormal (L := L) E x,
    AlgEquiv.restrictNormal_eq_one_iff, IntermediateField.mem_fixingSubgroup_iff]

/-- **The Ordering Theorem**: for intermediate fields of a finite abelian extension,
$N_{E_1/K}C_{E_1}\subseteq N_{E_2/K}C_{E_2} \iff E_2\subseteq E_1$. Childress, *Class Field
Theory*, Chapter VI, Proposition 1.1(i); Milne, *Class Field Theory*, Chapter V,
Corollary 5.6. -/
theorem range_norm_le_range_norm_iff {E₁ E₂ : IntermediateField K L} :
    (IdeleClassGroup.norm (K := K) (L := E₁)).range ≤
        (IdeleClassGroup.norm (K := K) (L := E₂)).range ↔ E₂ ≤ E₁ := by
  constructor
  · intro hnorm
    have hfix : E₁.fixingSubgroup ≤ E₂.fixingSubgroup := by
      intro σ hσ
      obtain ⟨x, rfl⟩ := globalArtin_surjective (K := K) (L := L) σ
      exact (globalArtin_mem_fixingSubgroup_iff E₂ x).mpr
        (hnorm ((globalArtin_mem_fixingSubgroup_iff E₁ x).mp hσ))
    have hle := (IntermediateField.le_iff_le E₁.fixingSubgroup E₂).mpr hfix
    simpa only [IsGalois.fixedField_fixingSubgroup] using hle
  · intro hE
    exact IdeleClassGroup.range_norm_le_of_algHom (IntermediateField.inclusion hE)

/-- **Upward closure of norm groups**: a subgroup `U` containing $N_{L/K}C_L$ is the norm group
of the fixed field of $\operatorname{Art}_{L/K}(U)$. Childress, *Class Field Theory*,
Chapter VI, Corollary 1.2. -/
theorem range_norm_fixedField {U : Subgroup (NumberField.IdeleClassGroup (𝓞 K) K)}
    (hU : (IdeleClassGroup.norm (K := K) (L := L)).range ≤ U) :
    (IdeleClassGroup.norm (K := K)
      (L := IntermediateField.fixedField (U.map (globalArtin L)))).range = U := by
  have hker : (globalArtin L).ker ≤ U := by
    rw [ker_globalArtin (K := K) (L := L)]
    exact hU
  ext x
  calc
    x ∈ (IdeleClassGroup.norm (K := K)
        (L := IntermediateField.fixedField (U.map (globalArtin L)))).range ↔
        globalArtin L x ∈
          (IntermediateField.fixedField (U.map (globalArtin L))).fixingSubgroup :=
      (globalArtin_mem_fixingSubgroup_iff _ x).symm
    _ ↔ globalArtin L x ∈ U.map (globalArtin L) := by
      rw [IntermediateField.fixingSubgroup_fixedField]
    _ ↔ x ∈ U := by
      change x ∈ (U.map (globalArtin L)).comap (globalArtin L) ↔ x ∈ U
      rw [Subgroup.comap_map_eq_self hker]

/-! ### Norm groups in a tower

The global Artin map translates a norm condition over `K` into one over an intermediate
field whenever restriction to `L` detects automorphisms over that field. -/

/-- If restriction to `L` is injective on $\operatorname{Gal}(M/E)$, then the inverse image
under $N_{E/K}$ of $N_{L/K}C_L$ lies in $N_{M/E}C_M$. This is the Artin-map translation used
in the local splitting arguments. -/
theorem comap_norm_range_norm_le_of_injective {M : Type*} [Field M] [NumberField M]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsAbelianGalois K M]
    (E : IntermediateField K M)
    (hinj : Function.Injective (fun σ : M ≃ₐ[E] M ↦
      (σ.restrictScalars K).restrictNormal L)) :
    (IdeleClassGroup.norm (K := K) (L := L)).range.comap
      (IdeleClassGroup.norm (K := K) (L := E)) ≤
      (IdeleClassGroup.norm (K := E) (L := M)).range := by
  have : IsAbelianGalois E M := IsAbelianGalois.tower_top K E M
  intro x hx
  rw [← ker_globalArtin (K := E) (L := M), MonoidHom.mem_ker]
  apply hinj
  have hone : ((1 : M ≃ₐ[E] M).restrictScalars K).restrictNormal L = 1 := by
    let r : (M ≃ₐ[E] M) →* (M ≃ₐ[K] M) := AlgEquiv.restrictScalarsHom K
    let s : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L) := AlgEquiv.restrictNormalHom L
    change (s.comp r) 1 = 1
    exact map_one _
  change ((globalArtin (K := E) M x).restrictScalars K).restrictNormal L =
    ((1 : M ≃ₐ[E] M).restrictScalars K).restrictNormal L
  rw [hone]
  rw [restrictScalars_globalArtin E, globalArtin_restrictNormal L]
  rw [← ker_globalArtin (K := K) (L := L)] at hx
  exact (MonoidHom.mem_ker).mp hx

/-- Pulling back $N_{L/K}C_L$ along $N_{E/K}$ gives elements of $N_{L/E}C_L$.
This is the same-field case of `comap_norm_range_norm_le_of_injective`. -/
theorem comap_norm_range_norm_le (E : IntermediateField K L) :
    (IdeleClassGroup.norm (K := K) (L := L)).range.comap
      (IdeleClassGroup.norm (K := K) (L := E)) ≤
      (IdeleClassGroup.norm (K := E) (L := L)).range := by
  apply comap_norm_range_norm_le_of_injective E
  intro σ τ h
  apply AlgEquiv.restrictScalars_injective K
  apply AlgEquiv.ext
  intro x
  have hx := congrArg (fun g : L ≃ₐ[K] L => g x) h
  calc
    (σ.restrictScalars K) x = ((σ.restrictScalars K).restrictNormal L) x := by
      simpa only [Algebra.algebraMap_self_apply] using
        (AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) L x).symm
    _ = ((τ.restrictScalars K).restrictNormal L) x := hx
    _ = (τ.restrictScalars K) x := by
      simpa only [Algebra.algebraMap_self_apply] using
        AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) L x

/-- **The Ordering Theorem for two abelian extensions**: if
$N_{M/K}C_M\subseteq N_{L/K}C_L$, then `L` embeds in `M` over `K`. Childress, *Class Field
Theory*, Chapter VI, Proposition 1.1(i), for extensions not given inside a common field: both
lie in their compositum, which is abelian. -/
theorem nonempty_algHom_of_range_norm_le {M : Type*} [Field M] [NumberField M] [Algebra K M]
    [IsAbelianGalois K M]
    (h : (IdeleClassGroup.norm (K := K) (L := M)).range ≤
      (IdeleClassGroup.norm (K := K) (L := L)).range) :
    Nonempty (L →ₐ[K] M) := by
  let fL : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let fM : M →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let L₀ := fL.fieldRange
  let M₀ := fM.fieldRange
  let C := L₀ ⊔ M₀
  let eL : L ≃ₐ[K] L₀ := fL.equivFieldRange
  let eM : M ≃ₐ[K] M₀ := fM.equivFieldRange
  have : FiniteDimensional K L₀ := eL.toLinearEquiv.finiteDimensional
  have : FiniteDimensional K M₀ := eM.toLinearEquiv.finiteDimensional
  have : IsAbelianGalois K L₀ := IsAbelianGalois.of_algHom eL.symm.toAlgHom
  have : IsAbelianGalois K M₀ := IsAbelianGalois.of_algHom eM.symm.toAlgHom
  have : FiniteDimensional K C := IntermediateField.finiteDimensional_sup L₀ M₀
  have : NumberField C := NumberField.of_module_finite K C
  have : IsAbelianGalois K C := IsAbelianGalois.sup L₀ M₀
  let E_L : IntermediateField K C := IntermediateField.restrict (show L₀ ≤ C from le_sup_left)
  let E_M : IntermediateField K C := IntermediateField.restrict (show M₀ ≤ C from le_sup_right)
  let eLC : L ≃ₐ[K] E_L := eL.trans
    (IntermediateField.restrictAlgEquiv (show L₀ ≤ C from le_sup_left))
  let eMC : M ≃ₐ[K] E_M := eM.trans
    (IntermediateField.restrictAlgEquiv (show M₀ ≤ C from le_sup_right))
  have hnorm : (IdeleClassGroup.norm (K := K) (L := E_M)).range ≤
      (IdeleClassGroup.norm (K := K) (L := E_L)).range := by
    calc
      _ = (IdeleClassGroup.norm (K := K) (L := M)).range :=
        (IdeleClassGroup.range_norm_congr eMC).symm
      _ ≤ (IdeleClassGroup.norm (K := K) (L := L)).range := h
      _ = _ := IdeleClassGroup.range_norm_congr eLC
  have hfields : E_L ≤ E_M := (range_norm_le_range_norm_iff
    (E₁ := E_M) (E₂ := E_L)).mp hnorm
  exact ⟨eMC.symm.toAlgHom.comp ((IntermediateField.inclusion hfields).comp eLC.toAlgHom)⟩

end SIC
