/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Reciprocity.Abelian

/-!
# The global Artin map of a finite abelian extension

The global Artin map $C_K\to\operatorname{Gal}(L/K)$ of a finite abelian extension of number
fields: it is surjective with kernel the norm group $N_{L/K}C_L$, it sends the class of a
uniformizer at an unramified prime to Frobenius, and it is compatible with restriction to
subextensions and with norms from intermediate fields.

This module proves Artin reciprocity for finite abelian extensions in idèlic form: Childress,
*Class Field Theory* (2009), Chapter V, Theorem 2.1 for abelian extensions and the passage to
idèles of Chapter V, §§2–3 (Exercises 5.13–5.14), and Milne, *Class Field Theory*, version 4.03
(2020), Chapter V, Theorem 5.3 (the reciprocity law, existence of the Artin map with kernel
$N_{L/K}C_L$). It supplies `globalArtin` for the existence theorem
`exists_intermediateField_range_norm_eq` and the narrow ray class field of
`SICs.ClassField.RayClassField.Narrow`.

## The argument

Fix a reciprocity modulus `m` of `L/K` (`exists_isReciprocityModulus`) with support `S`. Every
idèle class contains a congruent idèle
(`IdeleGroup.exists_mem_congruentSubgroup_mk_eq`), and two congruent representatives
differ by a principal congruent idèle, which the Artin map kills. So $y\mapsto\psi^S_{L/K}((y))$
on $J^+_{K,\mathfrak m}$ descends to a homomorphism $C_K\to\operatorname{Gal}(L/K)$. For another
reciprocity modulus $\mathfrak m'$, choose a representative congruent for the product
$\mathfrak m\mathfrak m'$. It is congruent for each original modulus, and the Artin maps agree
on its ideal (`artinMap_eq_of_mem_primeTo`), so the map is independent of the modulus.

*Surjectivity* is that of the Artin map on congruent idèles
(`IdeleGroup.exists_mem_congruentSubgroup_artinMap_eq`). *Norms* lie in the kernel: every idèle
of `L` has a principal multiple whose norm is congruent
(`IdeleGroup.exists_norm_mul_mem_congruentSubgroup`), and the Artin map kills norms of fractional
ideals (`IdeleGroup.artinMap_toFractionalIdeal_norm`).
*The kernel* is exactly $N_{L/K}C_L$: the quotient by the kernel has order $[L:K]$, while
$[C_K:N_{L/K}C_L]$ divides $[L:K]$ (`IdeleClassGroup.secondInequality_of_isAbelianGalois`).

*Frobenius.* A modulus supported on the ramified places avoids an unramified prime $\mathfrak p$,
so an idèle supported at $\mathfrak p$ whose component has valuation one there is congruent with
fractional ideal $\mathfrak p$, and its Artin symbol is $\operatorname{Frob}_{\mathfrak p}$.
*Restriction.* A reciprocity modulus of `L/K` is one of every subextension `E`
(`IsReciprocityModulus.of_tower`), and Artin symbols restrict (`artinMap_restrictNormal`).

*Tower law.* For an intermediate field `E`, choose reciprocity moduli of `L/K` and of `L/E` and
represent a class of $C_E$ by an idèle `y` that is congruent for the second, with ideal prime to
the primes above the support of the first, and whose norm is congruent for the first (joint norm
approximation, `IdeleGroup.exists_mul_mem_congruentSubgroup_norm_mem`). The ideal of $N_{E/K}y$
is the relative norm of the ideal of `y`, so the ideal-theoretic tower law
$\psi_{L/E}=\psi_{L/K}\circ N_{E/K}$ (`artinMap_restrictScalars`) gives
$\operatorname{Art}_{L/E}=\operatorname{Art}_{L/K}\circ N_{E/K}$.
-/

noncomputable section

open IsDedekindDomain NumberField

namespace SIC

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-! ### The global Artin map -/

/-- Descent of the Artin symbol for one reciprocity modulus; used by `globalArtin`. -/
private def artinOfModulus [IsAbelianGalois K L] (m : Ideal (𝓞 K))
    (hm : IsReciprocityModulus L m) :
    NumberField.IdeleClassGroup (𝓞 K) K →* (L ≃ₐ[K] L) := by
  let H := IdeleGroup.congruentSubgroup Set.univ m
  let π : H →* NumberField.IdeleClassGroup (𝓞 K) K :=
    (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)).comp H.subtype
  let φ : H →* (L ≃ₐ[K] L) :=
    (artinMap L (FinitePlace.modulusSupport m)).comp
      ((IdeleGroup.toFractionalIdeal (K := K)).comp H.subtype)
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨y, hy, hclass⟩ := IdeleGroup.exists_mem_congruentSubgroup_mk_eq Set.univ m x
    exact ⟨⟨y, hy⟩, hclass⟩
  have hker : π.ker ≤ φ.ker := by
    intro y hy
    have hp : (y : NumberField.IdeleGroup (𝓞 K) K) ∈
        NumberField.IdeleGroup.principalSubgroup (𝓞 K) K :=
      (QuotientGroup.eq_one_iff _).mp hy
    obtain ⟨a, ha⟩ := hp
    have haH : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a ∈ H := by
      rw [ha]
      exact y.property
    change artinMap L (FinitePlace.modulusSupport m)
      (IdeleGroup.toFractionalIdeal (y : NumberField.IdeleGroup (𝓞 K) K)) = 1
    rw [← ha, IdeleGroup.toFractionalIdeal_unitEmbedding]
    exact hm.artinMap_eq_one a haH
  exact π.liftOfSurjective hπ ⟨φ, hker⟩

/-- The descent `artinOfModulus` evaluates on a congruent representative. -/
private theorem artinOfModulus_mk [IsAbelianGalois K L] (m : Ideal (𝓞 K))
    (hm : IsReciprocityModulus L m) {y : NumberField.IdeleGroup (𝓞 K) K}
    (hy : y ∈ IdeleGroup.congruentSubgroup Set.univ m) :
    artinOfModulus m hm (y : NumberField.IdeleClassGroup (𝓞 K) K) =
      artinMap L (FinitePlace.modulusSupport m) (IdeleGroup.toFractionalIdeal y) := by
  unfold artinOfModulus
  change (((QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)).comp
      (IdeleGroup.congruentSubgroup Set.univ m).subtype).liftOfSurjective _ ⟨_, _⟩)
      (((QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)).comp
        (IdeleGroup.congruentSubgroup Set.univ m).subtype) ⟨y, hy⟩) = _
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- Descent of the Artin symbol does not depend on the reciprocity modulus; used by
`globalArtin_mk`. -/
private theorem artinOfModulus_eq [IsAbelianGalois K L]
    (m : Ideal (𝓞 K)) (hm : IsReciprocityModulus L m)
    (m' : Ideal (𝓞 K)) (hm' : IsReciprocityModulus L m') :
    artinOfModulus m hm = artinOfModulus m' hm' := by
  let M := m * m'
  have hM : M ≠ ⊥ := by
    change m * m' ≠ ⊥
    rw [ne_eq, Ideal.mul_eq_bot, not_or]
    exact ⟨hm.ne_bot, hm'.ne_bot⟩
  have hMm : M ≤ m := Ideal.mul_le_left
  have hMm' : M ≤ m' := Ideal.mul_le_right
  have hSm : FinitePlace.modulusSupport m ⊆ FinitePlace.modulusSupport M :=
    FinitePlace.modulusSupport_subset_of_le hM hMm
  have hSm' : FinitePlace.modulusSupport m' ⊆ FinitePlace.modulusSupport M :=
    FinitePlace.modulusSupport_subset_of_le hM hMm'
  apply MonoidHom.ext
  intro x
  obtain ⟨z, hz, hclass⟩ := IdeleGroup.exists_mem_congruentSubgroup_mk_eq Set.univ M x
  have hz_m : z ∈ IdeleGroup.congruentSubgroup Set.univ m :=
    IdeleGroup.congruentSubgroup_mono Set.univ hM hMm hz
  have hz_m' : z ∈ IdeleGroup.congruentSubgroup Set.univ m' :=
    IdeleGroup.congruentSubgroup_mono Set.univ hM hMm' hz
  rw [← hclass, artinOfModulus_mk m hm hz_m,
    artinOfModulus_mk m' hm' hz_m']
  have hprime := IdeleGroup.toFractionalIdeal_mem_primeTo Set.univ M hz
  exact (artinMap_eq_of_mem_primeTo (L := L) hSm hprime).trans
    (artinMap_eq_of_mem_primeTo (L := L) hSm' hprime).symm

variable (L) in
/-- **The global Artin map** $C_K\to\operatorname{Gal}(L/K)$ of a finite abelian extension:
the class of a congruent idèle `y` for a reciprocity modulus with support `S` goes to
$\psi^S_{L/K}((y))$ (`globalArtin_mk`). Childress, *Class Field Theory*, Chapter V, Theorem 2.1,
in the idèlic form of Exercises 5.13–5.14; Milne, *Class Field Theory*, Chapter V, Theorem 5.3. -/
def globalArtin [IsAbelianGalois K L] :
    NumberField.IdeleClassGroup (𝓞 K) K →* (L ≃ₐ[K] L) := by
  let m := Classical.choose (exists_isReciprocityModulus (K := K) (L := L))
  exact artinOfModulus m (Classical.choose_spec
    (exists_isReciprocityModulus (K := K) (L := L))).1

/-- The global Artin map evaluates, at the class of a congruent idèle `y` for any reciprocity
modulus with support `S`, to $\psi^S_{L/K}((y))$; in particular it does not depend on the
modulus. Childress, *Class Field Theory*, Chapter V, §2. -/
theorem globalArtin_mk [IsAbelianGalois K L] {m : Ideal (𝓞 K)} (hm : IsReciprocityModulus L m)
    {y : NumberField.IdeleGroup (𝓞 K) K} (hy : y ∈ IdeleGroup.congruentSubgroup Set.univ m) :
    globalArtin L (y : NumberField.IdeleClassGroup (𝓞 K) K) =
      artinMap L (FinitePlace.modulusSupport m) (IdeleGroup.toFractionalIdeal y) := by
  let m₀ := Classical.choose (exists_isReciprocityModulus (K := K) (L := L))
  let hm₀ : IsReciprocityModulus L m₀ := (Classical.choose_spec
    (exists_isReciprocityModulus (K := K) (L := L))).1
  change artinOfModulus m₀ hm₀ (y : NumberField.IdeleClassGroup (𝓞 K) K) = _
  rw [artinOfModulus_eq m₀ hm₀ m hm]
  exact artinOfModulus_mk m hm hy

/-- **The global Artin map is surjective.** Childress, *Class Field Theory*, Chapter V,
Theorem 2.1(i). -/
theorem globalArtin_surjective [IsAbelianGalois K L] :
    Function.Surjective (globalArtin (K := K) L) := by
  obtain ⟨m, hm, _⟩ := exists_isReciprocityModulus (K := K) (L := L)
  intro g
  obtain ⟨y, hy, hgy⟩ := IdeleGroup.exists_mem_congruentSubgroup_artinMap_eq
    m hm.unramified g
  exact ⟨(y : NumberField.IdeleClassGroup (𝓞 K) K),
    (globalArtin_mk hm hy).trans hgy⟩

/-- Norms lie in the kernel of the global Artin map. Childress, *Class Field Theory*,
Chapter V, Corollary 1.4, with norm approximation (Chapter IV, Exercise 4.23). -/
theorem globalArtin_norm [IsAbelianGalois K L] (x : NumberField.IdeleClassGroup (𝓞 L) L) :
    globalArtin L (IdeleClassGroup.norm (K := K) (L := L) x) = 1 := by
  obtain ⟨m, hm, _⟩ := exists_isReciprocityModulus (K := K) (L := L)
  induction x using QuotientGroup.induction_on with
  | _ z =>
    obtain ⟨b, hb⟩ := IdeleGroup.exists_norm_mul_mem_congruentSubgroup
      (K := K) (L := L) m z
    let t := NumberField.IdeleGroup.unitEmbedding (𝓞 L) L b * z
    have ht : (t : NumberField.IdeleClassGroup (𝓞 L) L) =
        (z : NumberField.IdeleClassGroup (𝓞 L) L) :=
      IdeleClassGroup.mk_unitEmbedding_mul b z
    rw [← ht, IdeleClassGroup.norm_mk,
      globalArtin_mk hm hb]
    exact IdeleGroup.artinMap_toFractionalIdeal_norm
      (FinitePlace.modulusSupport m) hm.unramified t

/-- The kernel index calculation used by `ker_globalArtin` and
`IdeleClassGroup.index_range_norm`. -/
private theorem index_ker_globalArtin [IsAbelianGalois K L] :
    (globalArtin (K := K) L).ker.index = Module.finrank K L := by
  rw [Subgroup.index_ker]
  have hrange : (globalArtin (K := K) L).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (globalArtin_surjective (K := K) (L := L))
  rw [hrange, Subgroup.card_top]
  exact IsGalois.card_aut_eq_finrank K L

/-- **Artin reciprocity**: the kernel of the global Artin map is the norm group $N_{L/K}C_L$.
Childress, *Class Field Theory*, Chapter V, Theorem 2.1(ii) in idèlic form; Milne, *Class Field
Theory*, Chapter V, Theorem 5.3. -/
theorem ker_globalArtin [IsAbelianGalois K L] :
    (globalArtin L).ker = (IdeleClassGroup.norm (K := K) (L := L)).range := by
  let A := (globalArtin (K := K) L).ker
  let N := (IdeleClassGroup.norm (K := K) (L := L)).range
  have hNA : N ≤ A := by
    rintro x ⟨z, rfl⟩
    exact globalArtin_norm (K := K) (L := L) z
  have hA : A.index = Module.finrank K L := index_ker_globalArtin
  have hN : N.index ∣ Module.finrank K L := by
    change (IdeleClassGroup.norm (K := K) (L := L)).range.index ∣ _
    rw [Subgroup.index_eq_card]
    exact IdeleClassGroup.secondInequality_of_isAbelianGalois (K := K) (L := L)
  have hindex : N.index = A.index :=
    Nat.dvd_antisymm (hA ▸ hN) (Subgroup.index_dvd_of_le hNA)
  exact (SIC.Subgroup.eq_of_le_of_index_eq N A hNA hindex
    (hA.symm ▸ ne_of_gt Module.finrank_pos)).symm

/-- **The norm index of a finite abelian extension** is its degree:
$[C_K:N_{L/K}C_L]=[L:K]$. Childress, *Class Field Theory*, Chapter V, Theorem 2.1, idèlic form;
Milne, *Class Field Theory*, Chapter V, Theorem 5.3(b). -/
theorem IdeleClassGroup.index_range_norm [IsAbelianGalois K L] :
    (IdeleClassGroup.norm (K := K) (L := L)).range.index = Module.finrank K L := by
  rw [← ker_globalArtin (K := K) (L := L)]
  exact index_ker_globalArtin

/-- If every automorphism of `L/K` satisfies $\sigma^n=1$, every `n`th power of an idèle class is
a norm: $C_K^n\subseteq N_{L/K}C_L$, since the global Artin map kills it. -/
theorem IdeleClassGroup.pow_mem_range_norm [IsAbelianGalois K L] {n : ℕ}
    (h : ∀ σ : L ≃ₐ[K] L, σ ^ n = 1) (x : NumberField.IdeleClassGroup (𝓞 K) K) :
    x ^ n ∈ (IdeleClassGroup.norm (K := K) (L := L)).range := by
  rw [← ker_globalArtin (K := K) (L := L), MonoidHom.mem_ker, map_pow, h]

/-! ### Frobenius and restriction -/

/-- **The global Artin map at an unramified prime is Frobenius**: the class of an idèle supported
at $\mathfrak p$ whose component has normalized valuation one (a uniformizer times a unit) maps
to $\operatorname{Frob}_{\mathfrak p}(L/K)$ when $\mathfrak p$ is unramified in `L`. Childress,
*Class Field Theory*, Chapter V, §2; Milne, *Class Field Theory*, Chapter V, Theorem 5.3. -/
theorem globalArtin_ofAdicCompletion [IsAbelianGalois K L] (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ FinitePlace.ramifiedSet K L) (x : (v.adicCompletion K)ˣ)
    (hx : Valued.v (x : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    globalArtin L (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v x) =
      frobeniusAt L v := by
  obtain ⟨m, hm, hS⟩ := exists_isReciprocityModulus (K := K) (L := L)
  let y := NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v x
  have hy : y ∈ IdeleGroup.congruentSubgroup Set.univ m := by
    apply (IdeleGroup.mem_congruentSubgroup_univ_iff m y).mpr
    constructor
    · intro w hw
      rw [IdeleGroup.infiniteComponent_ofAdicCompletion]
      simp
    · intro w hw
      have hwne : w ≠ v := by
        intro heq
        subst w
        exact hv (hS ▸ (FinitePlace.mem_modulusSupport.mpr hw))
      rw [IdeleGroup.finiteComponent_ofAdicCompletion_of_ne K v w hwne x]
      exact one_mem _
  have hideal : IdeleGroup.toFractionalIdeal y = primeFractionalIdeal K v := by
    apply Units.ext
    exact IdeleGroup.coe_toFractionalIdeal_ofAdicCompletion_uniformizer v x hx
  rw [NumberField.IdeleClassGroup.ofAdicCompletion_apply]
  rw [globalArtin_mk hm hy, hideal]
  exact artinMap_primeFractionalIdeal_of_notMem (L := L) (hS ▸ hv)

/-- **Restriction**: the global Artin map of `L/K` restricts to that of an abelian subextension
`E`: $\operatorname{Art}_{L/K}(x)|_E = \operatorname{Art}_{E/K}(x)$. Childress, *Class Field
Theory*, Chapter V, Corollary 1.2. -/
theorem globalArtin_restrictNormal [IsAbelianGalois K L] (E : Type*) [Field E] [NumberField E]
    [Algebra K E] [Algebra E L] [IsScalarTower K E L] [IsAbelianGalois K E]
    (x : NumberField.IdeleClassGroup (𝓞 K) K) :
    (globalArtin L x).restrictNormal E = globalArtin E x := by
  obtain ⟨m, hm, _⟩ := exists_isReciprocityModulus (K := K) (L := L)
  obtain ⟨z, hz, hclass⟩ := IdeleGroup.exists_mem_congruentSubgroup_mk_eq Set.univ m x
  rw [← hclass, globalArtin_mk hm hz,
    globalArtin_mk (hm.of_tower E) hz]
  exact artinMap_restrictNormal (FinitePlace.modulusSupport m) hm.unramified E
    (IdeleGroup.toFractionalIdeal z)

/-- The comparison of congruent representatives used by `restrictScalars_globalArtin`. -/
private theorem restrictScalars_globalArtin_of_congruent [IsAbelianGalois K L]
    (E : IntermediateField K L) {m : Ideal (𝓞 K)} (hm : IsReciprocityModulus L m)
    {m' M : Ideal (𝓞 E)} (hm' : IsReciprocityModulus L m')
    (hM0 : M ≠ ⊥) (hMm' : M ≤ m')
    (hT : FinitePlace.placesAbove (K := K) (L := E) (FinitePlace.modulusSupport m) ⊆
      FinitePlace.modulusSupport M)
    {y : NumberField.IdeleGroup (𝓞 E) E} (hy : y ∈ IdeleGroup.congruentSubgroup Set.univ M)
    (hynorm : IdeleGroup.norm (K := K) (L := E) y ∈ IdeleGroup.congruentSubgroup Set.univ m) :
    (globalArtin (K := E) L (y : NumberField.IdeleClassGroup (𝓞 E) E)).restrictScalars K =
      globalArtin L (IdeleClassGroup.norm (K := K) (L := E) y) := by
  have hy' := IdeleGroup.congruentSubgroup_mono Set.univ hM0 hMm' hy
  have hJ := IdeleGroup.toFractionalIdeal_mem_primeTo Set.univ M hy
  have hS' := FinitePlace.modulusSupport_subset_of_le hM0 hMm'
  rw [IdeleClassGroup.norm_mk, globalArtin_mk hm' hy', globalArtin_mk hm hynorm]
  calc
    (artinMap L (FinitePlace.modulusSupport m')
        (IdeleGroup.toFractionalIdeal y)).restrictScalars K =
      (artinMap L (FinitePlace.placesAbove (K := K) (L := E)
        (FinitePlace.modulusSupport m)) (IdeleGroup.toFractionalIdeal y)).restrictScalars K := by
        exact congrArg (fun σ : L ≃ₐ[E] L ↦ σ.restrictScalars K) <|
          (artinMap_eq_of_mem_primeTo (L := L) hS' hJ).trans
            (artinMap_eq_of_mem_primeTo (L := L) hT hJ).symm
    _ = artinMap L (FinitePlace.modulusSupport m)
        (FractionalIdeal.relNorm K (IdeleGroup.toFractionalIdeal y)) :=
      artinMap_restrictScalars _ hm.unramified E _
    _ = artinMap L (FinitePlace.modulusSupport m)
        (IdeleGroup.toFractionalIdeal (IdeleGroup.norm (K := K) (L := E) y)) := by
          rw [IdeleGroup.toFractionalIdeal_norm]

/-- **The tower law**: for an intermediate field `E` of a finite abelian extension `L/K`,
$\operatorname{Art}_{L/E}(x)=\operatorname{Art}_{L/K}(N_{E/K}x)$ in
$\operatorname{Gal}(L/E)\subseteq\operatorname{Gal}(L/K)$. Childress, *Class Field Theory*,
Chapter V, Corollary 1.3 (the consistency property) in idèlic form; Milne, *Class Field Theory*,
Chapter V, Proposition 3.3. -/
theorem restrictScalars_globalArtin [IsAbelianGalois K L] (E : IntermediateField K L)
    (x : NumberField.IdeleClassGroup (𝓞 E) E) :
    (globalArtin (K := E) L x).restrictScalars K =
      globalArtin L (IdeleClassGroup.norm (K := K) (L := E) x) := by
  classical
  obtain ⟨m, hm, _⟩ := exists_isReciprocityModulus (K := K) (L := L)
  obtain ⟨m', hm', _⟩ := exists_isReciprocityModulus (K := E) (L := L)
  let S := FinitePlace.modulusSupport m
  let T := FinitePlace.placesAbove (K := K) (L := E) S
  let P : Ideal (𝓞 E) := ∏ w ∈ T, w.asIdeal
  let M := m' * P
  have hP0 : P ≠ ⊥ := FinitePlace.prod_asIdeal_ne_bot T
  have hM0 : M ≠ ⊥ := mul_ne_zero hm'.ne_bot hP0
  have hT : T ⊆ FinitePlace.modulusSupport M := by
    change T ⊆ FinitePlace.modulusSupport (m' * P)
    rw [FinitePlace.modulusSupport_mul_prod_asIdeal hm'.ne_bot T]
    exact Finset.subset_union_right
  induction x using QuotientGroup.induction_on with
  | _ z =>
    obtain ⟨b, hyM, hynorm⟩ :=
      IdeleGroup.exists_mul_mem_congruentSubgroup_norm_mem m M z
    let y := NumberField.IdeleGroup.unitEmbedding (𝓞 E) E b * z
    have hclass : (y : NumberField.IdeleClassGroup (𝓞 E) E) =
        (z : NumberField.IdeleClassGroup (𝓞 E) E) :=
      IdeleClassGroup.mk_unitEmbedding_mul b z
    rw [← hclass]
    exact restrictScalars_globalArtin_of_congruent E hm hm' hM0 Ideal.mul_le_left
      hT hyM hynorm

end SIC
