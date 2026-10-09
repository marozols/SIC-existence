/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Reciprocity.CongruentIdeles
import SICs.ClassField.Reciprocity.Cyclotomic

/-!
# Norms from auxiliary fields

Norms from an auxiliary field `E` with $L\subseteq E(\zeta_M)$ of ideals whose Artin symbol for
`L/K` is trivial are norm residues of `L/K`, and an automorphism fixing finitely many auxiliary
fields is the Artin symbol of an ideal that is a norm from each of them.

This module carries the two steps of Childress, *Class Field Theory* (2009), Chapter V, proof of
Proposition 2.2, pp. 121–123, that use the auxiliary fields of
`SICs.ClassField.Reciprocity.AuxiliaryFields.Construction`: the descent of
$\mathfrak A_{E_i}\in\ker(\mathcal I_{E_i}\to\operatorname{Gal}(KE_i/E_i))$ to
$\mathcal P^+_{F,\mathfrak m}\mathcal N_{K/F}(\mathfrak m)$, and the choice of
$\mathfrak b_F = N_{E/F}\mathfrak B_E$ with Artin symbol $\sigma$. Both are stated inside an
abelian extension $\Omega/K$ containing `L` and the auxiliary fields, with the Artin maps of
$\Omega$ over its intermediate fields; norm residues are idèlic, as in
`SICs.ClassField.Reciprocity.CongruentIdeles`.

## The argument

*Descent.* Let `T` be the compositum of `E` and `L` inside $\Omega$, regarded over `E`, and
$C = E(\zeta)$; then $T\subseteq C$ by hypothesis. Restriction to `L` embeds
$\operatorname{Gal}(T/E)$ in the abelian group $\operatorname{Gal}(L/K)$, so `T/E` is abelian. Let
`A` be an ideal of `E` prime to the primes above `S` with $\psi_{L/K}(N_{E/K}A) = 1$. The Artin
symbol $\psi_{\Omega/E}(A)$ restricts to $\psi_{\Omega/K}(N_{E/K}A)$ over `K`
(`artinMap_restrictScalars`), which fixes `L`; it also fixes `E`, hence `T`, so
$\psi_{T/E}(A) = 1$ (`artinMap_restrictNormal`). Over `E`, the Artin map of `C/E` vanishes on
principal ideals congruent to one modulo a modulus $\mathfrak m_E$ divisible by `M` with support
the primes above `S` (`IsCyclotomicExtension.artinMap_toPrincipalIdeal_eq_one`), and so does
that of `T/E`, by restriction through $\Omega$. The abelian kernel comparison
`IdeleGroup.artinMap_eq_one_iff_of_principal` for `T/E` then puts the uniformizer idèle of `A`
in $E^\times N_{T/E}J_T$. Its norm to `K` lies in
$K^\times N_{T/K}J_T\subseteq K^\times N_{L/K}J_L$ (`IdeleGroup.range_norm_le_of_algHom`).

*A common norm.* Let `g` fix every $E_i$ and let `E` be their compositum, so `g` fixes `E`. The
Artin map of $\Omega/E$ is surjective on ideals prime to the primes above `S`
(`exists_mem_primeTo_artinMap_eq`), so `g` is $\psi_{\Omega/E}(B)$ for such `B`, and
$b = N_{E/K}B$ has $\psi_{\Omega/K}(b) = g$ (`artinMap_restrictScalars`). By transitivity of
norms (`FractionalIdeal.relNorm_relNorm`), $b = N_{E_i/K}(N_{E/E_i}B)$ for each `i`, and these
norms are prime to the primes above `S` (`FractionalIdeal.relNorm_mem_primeTo`).
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors

namespace SIC

variable {K L Ω : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Field Ω] [NumberField Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]

/-! ### Descent through an auxiliary field -/

/-- A nonzero modulus divisible by `M` and supported precisely at the places above `S`; used
by `IdeleGroup.norm_ofFractionalIdeal_mem_of_le_sup_adjoin`. -/
private theorem exists_modulus_support_eq_placesAbove {K Ω : Type*} [Field K] [NumberField K]
    [Field Ω] [NumberField Ω] [Algebra K Ω]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {M : ℕ} [NeZero M]
    (hMS : ∀ v : HeightOneSpectrum (𝓞 K), (M : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (E : IntermediateField K Ω) :
    ∃ m : Ideal (𝓞 E), m ≠ ⊥ ∧
      FinitePlace.modulusSupport m = FinitePlace.placesAbove (K := K) (L := E) S ∧
      m ≤ Ideal.span {(M : 𝓞 E)} := by
  let SE := FinitePlace.placesAbove (K := K) (L := E) S
  let P : Ideal (𝓞 E) := ∏ v ∈ SE, v.asIdeal
  let m := Ideal.span {(M : 𝓞 E)} * P
  have hP0 : P ≠ ⊥ := FinitePlace.prod_asIdeal_ne_bot SE
  have hM0 : (M : 𝓞 E) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hspan0 : Ideal.span {(M : 𝓞 E)} ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hM0
  have hm0 : m ≠ ⊥ := mul_ne_zero hspan0 hP0
  have hMmem (v : HeightOneSpectrum (𝓞 E)) (hv : (M : 𝓞 E) ∈ v.asIdeal) : v ∈ SE := by
    apply (FinitePlace.mem_placesAbove S v).2
    apply hMS
    change (M : 𝓞 K) ∈ v.asIdeal.comap (algebraMap (𝓞 K) (𝓞 E))
    simpa only [Ideal.mem_comap, map_natCast] using hv
  have hsupport : FinitePlace.modulusSupport m = SE := by
    classical
    have hspan : FinitePlace.modulusSupport (Ideal.span {(M : 𝓞 E)}) ⊆ SE := by
      intro w hw
      exact hMmem w ((Ideal.span_singleton_le_iff_mem _).mp
        ((FinitePlace.mem_modulusSupport_iff_le hspan0).mp hw))
    change FinitePlace.modulusSupport (Ideal.span {(M : 𝓞 E)} *
      ∏ v ∈ SE, v.asIdeal) = SE
    rw [FinitePlace.modulusSupport_mul_prod_asIdeal hspan0 SE]
    exact Finset.union_eq_right.mpr hspan
  exact ⟨m, hm0, hsupport, Ideal.mul_le_left⟩

/-- The Artin symbol of `A` over `E` fixes the compositum of `E` and `L` when the symbol of
`N_{E/K}A` in `L/K` is trivial; used by
`IdeleGroup.norm_ofFractionalIdeal_mem_of_le_sup_adjoin`. -/
private theorem artinMap_mem_fixing_compositum {K L Ω : Type*}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Field Ω] [NumberField Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [IsAbelianGalois K L] [IsAbelianGalois K Ω]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hΩ : FinitePlace.ramifiedSet K Ω ⊆ S)
    (E : IntermediateField K Ω) (A : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (hArt : artinMap L S (FractionalIdeal.relNorm K A) = 1) :
    let F := (IsScalarTower.toAlgHom K L Ω).fieldRange
    let T := IntermediateField.extendScalars (le_sup_left : E ≤ E ⊔ F)
    artinMap Ω (FinitePlace.placesAbove (K := K) (L := E) S) A ∈ T.fixingSubgroup := by
  let F := (IsScalarTower.toAlgHom K L Ω).fieldRange
  let T₀ := E ⊔ F
  let T : IntermediateField E Ω := IntermediateField.extendScalars (le_sup_left : E ≤ T₀)
  let SE := FinitePlace.placesAbove (K := K) (L := E) S
  let σ : Ω ≃ₐ[E] Ω := artinMap Ω SE A
  have hσL : (σ.restrictScalars K).restrictNormal L = 1 := by
    change ((artinMap Ω SE A).restrictScalars K).restrictNormal L = 1
    rw [artinMap_restrictScalars S hΩ E A,
      artinMap_restrictNormal S hΩ L (FractionalIdeal.relNorm K A)]
    exact hArt
  have hσF : σ.restrictScalars K ∈ F.fixingSubgroup := by
    change σ.restrictScalars K ∈
      (IsScalarTower.toAlgHom K L Ω).fieldRange.fixingSubgroup
    rw [← AlgEquiv.ker_restrictNormalHom (F := K) (K₁ := Ω) L]
    exact MonoidHom.mem_ker.mpr hσL
  have hσE : σ.restrictScalars K ∈ E.fixingSubgroup := by
    apply (IntermediateField.mem_fixingSubgroup_iff E _).2
    intro x hx
    let y : E := ⟨x, hx⟩
    change σ (y : Ω) = (y : Ω)
    exact σ.commutes y
  have hσT₀ : σ.restrictScalars K ∈ T₀.fixingSubgroup := by
    change σ.restrictScalars K ∈ (E ⊔ F).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hσE, hσF⟩
  apply (IntermediateField.mem_fixingSubgroup_iff T σ).2
  intro x hx
  have hx₀ : x ∈ T₀ := hx
  have hfix := (IntermediateField.mem_fixingSubgroup_iff T₀ (σ.restrictScalars K)).1
    hσT₀ x hx₀
  simpa only [AlgEquiv.restrictScalars_apply] using hfix

/-- Pushing a principal idèle times a norm from `T/E` to `K` gives a principal idèle times a
norm from `L/K` whenever `L` embeds in `T`; used by
`IdeleGroup.norm_ofFractionalIdeal_mem_of_le_sup_adjoin`. -/
private theorem IdeleGroup.norm_mem_principal_sup_range_of_algHom
    {K E L T : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
    [Field L] [NumberField L] [Field T] [NumberField T]
    [Algebra K E] [Algebra K L] [Algebra K T] [Algebra E T] [IsScalarTower K E T]
    (f : L →ₐ[K] T) {y : NumberField.IdeleGroup (𝓞 E) E}
    (hy : y ∈ NumberField.IdeleGroup.principalSubgroup (𝓞 E) E ⊔
      (norm (K := E) (L := T)).range) :
    norm (K := K) (L := E) y ∈ NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
      (norm (K := K) (L := L)).range := by
  obtain ⟨p, hp, n, hn, hpn⟩ := Subgroup.mem_sup.mp hy
  obtain ⟨z, rfl⟩ := hn
  have hpK : norm (K := K) (L := E) p ∈
      NumberField.IdeleGroup.principalSubgroup (𝓞 K) K :=
    principalSubgroup_le_comap_norm hp
  have hnK : norm (K := K) (L := E) (norm (K := E) (L := T) z) ∈
      (norm (K := K) (L := L)).range := by
    rw [norm_norm (K := K) (L := E) (M := T) z]
    exact range_norm_le_of_algHom f ⟨z, rfl⟩
  rw [← hpn, map_mul]
  exact Subgroup.mem_sup.mpr ⟨_, hpK, _, hnK, rfl⟩

/-- If $L\subseteq E(\zeta)$ over `K`, then the compositum of `E` and `L` is contained in
`E(ζ)` over `E`; used by `IdeleGroup.norm_ofFractionalIdeal_mem_of_le_sup_adjoin`. -/
private theorem compositum_le_adjoin {K L Ω : Type*} [Field K] [Field L] [Algebra K L]
    [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    (E : IntermediateField K Ω) {ζ : Ω}
    (hE : (IsScalarTower.toAlgHom K L Ω).fieldRange ≤
      E ⊔ IntermediateField.adjoin K {ζ}) :
    IntermediateField.extendScalars
      (le_sup_left : E ≤ E ⊔ (IsScalarTower.toAlgHom K L Ω).fieldRange) ≤
      IntermediateField.adjoin E {ζ} := by
  change E ⊔ (IsScalarTower.toAlgHom K L Ω).fieldRange ≤
    (IntermediateField.adjoin E {ζ}).restrictScalars K
  rw [IntermediateField.restrictScalars_adjoin_eq_sup K E {ζ}]
  exact sup_le le_sup_left hE

/-- **Norms from an auxiliary field are norm residues**: let `L/K` be abelian inside the abelian
extension $\Omega/K$, unramified outside `S`, let $\zeta\in\Omega$ be a primitive `M`th root of
unity with the primes dividing `M` in `S`, and let `E` be an intermediate field with
$L\subseteq E(\zeta)$. If `A` is an ideal of `E` prime to the primes above `S` with
$\psi^S_{L/K}(N_{E/K}A) = 1$, then the norm of its uniformizer idèle lies in
$K^\times N_{L/K}J_L$. Childress, *Class Field Theory*, Chapter V, proof of Proposition 2.2,
p. 123, in idèlic form. -/
theorem IdeleGroup.norm_ofFractionalIdeal_mem_of_le_sup_adjoin [IsAbelianGalois K L]
    [IsAbelianGalois K Ω] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hΩ : FinitePlace.ramifiedSet K Ω ⊆ S)
    {M : ℕ} [NeZero M] (hMS : ∀ v : HeightOneSpectrum (𝓞 K), (M : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) (E : IntermediateField K Ω)
    (hE : (IsScalarTower.toAlgHom K L Ω).fieldRange ≤ E ⊔ IntermediateField.adjoin K {ζ})
    {A : (FractionalIdeal (𝓞 E)⁰ E)ˣ}
    (hA : A ∈ FractionalIdeal.primeTo E (FinitePlace.placesAbove (K := K) (L := E) S))
    (hArt : artinMap L S (FractionalIdeal.relNorm K A) = 1) :
    IdeleGroup.norm (K := K) (L := E) (IdeleGroup.ofFractionalIdeal A) ∈
      NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (IdeleGroup.norm (K := K) (L := L)).range := by
  let F := (IsScalarTower.toAlgHom K L Ω).fieldRange
  let T₀ := E ⊔ F
  let T : IntermediateField E Ω := IntermediateField.extendScalars (le_sup_left : E ≤ T₀)
  have hTC : T ≤ IntermediateField.adjoin E {ζ} := compositum_le_adjoin E hE
  obtain ⟨m, hm0, hmSupport, hmM⟩ := exists_modulus_support_eq_placesAbove S hMS E
  let SE := FinitePlace.placesAbove (K := K) (L := E) S
  have hramEm : FinitePlace.ramifiedSet E Ω ⊆ FinitePlace.modulusSupport m := by
    rw [hmSupport]
    exact FinitePlace.ramificationIdx_above_eq_one S hΩ
  have hramT := FinitePlace.ramificationIdx_below_eq_one (L := T)
    (FinitePlace.modulusSupport m) hramEm
  have hprin (a : Eˣ)
      (ha : NumberField.IdeleGroup.unitEmbedding (𝓞 E) E a ∈
        IdeleGroup.congruentSubgroup Set.univ m) :
      artinMap T (FinitePlace.modulusSupport m) (toPrincipalIdeal (𝓞 E) E a) = 1 :=
    artinMap_principal_eq_one_of_le_adjoin hζ m hm0 hmM hramEm T hTC a ha
  have hArtT : artinMap T SE A = 1 :=
    (artinMap_eq_one_iff_mem_fixingSubgroup SE
      (FinitePlace.ramificationIdx_above_eq_one S hΩ) T A).mpr
      (artinMap_mem_fixing_compositum S hΩ E A hArt)
  have hy : IdeleGroup.ofFractionalIdeal A ∈
      NumberField.IdeleGroup.principalSubgroup (𝓞 E) E ⊔
        (IdeleGroup.norm (K := E) (L := T)).range := by
    apply (IdeleGroup.artinMap_eq_one_iff_of_principal m hramT hprin
      (IdeleGroup.ofFractionalIdeal_mem_congruentSubgroup Set.univ m (by
        rw [hmSupport]
        exact hA))).mp
    simpa only [IdeleGroup.toFractionalIdeal_ofFractionalIdeal, hmSupport] using hArtT
  let f : L →ₐ[K] T :=
    (IntermediateField.inclusion (le_sup_right : F ≤ T₀)).comp
      (IsScalarTower.toAlgHom K L Ω).rangeRestrict
  exact IdeleGroup.norm_mem_principal_sup_range_of_algHom f hy


/-! ### A common norm with prescribed Artin symbol -/

/-- **A common norm**: if `g` fixes the intermediate fields $E_i$ of the abelian extension
$\Omega/K$, unramified outside `S`, then $g = \psi^S_{\Omega/K}(b)$ for an ideal `b` prime to `S`
which is the norm $N_{E_i/K}B_i$ of an ideal $B_i$ prime to the primes above `S`, for every `i`.
Childress, *Class Field Theory*, Chapter V, proof of Proposition 2.2, p. 122: $\mathfrak b_F =
N_{E/F}\mathfrak B_E$ for the compositum `E` of the $E_i$. -/
theorem exists_relNorm_eq_of_mem_fixingSubgroup [IsAbelianGalois K Ω]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hΩ : FinitePlace.ramifiedSet K Ω ⊆ S)
    {ι : Type*} (T : Finset ι) (E : ι → IntermediateField K Ω) (g : Ω ≃ₐ[K] Ω)
    (hg : ∀ i ∈ T, g ∈ (E i).fixingSubgroup) :
    ∃ b : (FractionalIdeal (𝓞 K)⁰ K)ˣ, b ∈ FractionalIdeal.primeTo K S ∧
      artinMap Ω S b = g ∧ ∀ i ∈ T, ∃ B : (FractionalIdeal (𝓞 (E i))⁰ (E i))ˣ,
        B ∈ FractionalIdeal.primeTo (E i) (FinitePlace.placesAbove (K := K) (L := E i) S) ∧
          FractionalIdeal.relNorm K B = b := by
  let F : IntermediateField K Ω := ⨆ i : T, E i.1
  have hgF : g ∈ F.fixingSubgroup := by
    have hle : F ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
      dsimp [F]
      refine iSup_le fun i => ?_
      exact (IntermediateField.le_iff_le _ _).2 (Subgroup.zpowers_le.mpr (hg i.1 i.2))
    exact ((IntermediateField.le_iff_le _ _).1 hle) (Subgroup.mem_zpowers g)
  let gF : Ω ≃ₐ[F] Ω := F.fixingSubgroupEquiv ⟨g, hgF⟩
  have hramF := FinitePlace.ramificationIdx_above_eq_one (L := F) S hΩ
  obtain ⟨B, hB, hArt⟩ := exists_mem_primeTo_artinMap_eq
    (K := F) (L := Ω) (FinitePlace.placesAbove (K := K) (L := F) S) hramF gF
  refine ⟨FractionalIdeal.relNorm K B, FractionalIdeal.relNorm_mem_primeTo S hB, ?_, ?_⟩
  · rw [← artinMap_restrictScalars (L := Ω) S hΩ F B, hArt]
    rfl
  · intro i hi
    have hiF : E i ≤ F := le_iSup (fun j : T => E j.1) ⟨i, hi⟩
    let _ : Algebra (E i) F := (IntermediateField.inclusion hiF).toAlgebra
    have : IsScalarTower K (E i) F := IsScalarTower.of_algebraMap_eq' rfl
    have hplaces : FinitePlace.placesAbove (K := E i) (L := F)
        (FinitePlace.placesAbove (K := K) (L := E i) S) =
        FinitePlace.placesAbove (K := K) (L := F) S := by
      ext w
      simp only [FinitePlace.mem_placesAbove, FinitePlace.below_below (K := K) (L := E i)]
    have hBF : B ∈ FractionalIdeal.primeTo F
        (FinitePlace.placesAbove (K := E i) (L := F)
          (FinitePlace.placesAbove (K := K) (L := E i) S)) := by
      rw [hplaces]
      exact hB
    exact ⟨FractionalIdeal.relNorm (E i) B,
      FractionalIdeal.relNorm_mem_primeTo _ hBF,
      FractionalIdeal.relNorm_relNorm B⟩

end SIC
