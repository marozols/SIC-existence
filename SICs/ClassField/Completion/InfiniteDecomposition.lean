/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.FieldTheory.PermutedAlgebraFamily
import SICs.ClassField.Completion.InfiniteBaseChange
import SICs.ClassField.Completion.InfiniteConjugation

/-!
# Decomposition groups at infinite places

The decomposition group $D_w \subseteq \operatorname{Gal}(L/K)$ of an infinite place `w` of `L`
above an infinite place `v` of `K` (Mathlib's stabilizer of `w`) acts on the completion $L_w$ by
$K_v$-automorphisms. For Galois `L/K` the action is an isomorphism
$D_w \cong \operatorname{Gal}(L_w/K_v)$, the extension $L_w/K_v$ is Galois of degree $|D_w|$, its
fixed field is $K_v$, and the automorphisms carrying one place `w'` above `v` to `w` multiply to
the local norm at `w'`.

This is the decomposition-group discussion of Milne, *Class Field Theory*, version 4.03 (2020),
Chapter VII, §2, before Lemma 2.1, at an infinite place; the finite places are treated in
`SICs.ClassField.Completion.FiniteDecomposition`.

## The argument

`completionFamily` bundles the $K_v$-algebra transports between completions above `v`, and the
generic `PermutedAlgebraFamily` argument gives the faithful stabilizer action. For any Galois
extension of fields, Mathlib identifies the stabilizer of an infinite place as having order one
or two, precisely its local degree; this proves the public degree theorem without a number-field
hypothesis. In the number-field setting, the degrees also add to $[L:K]$
(`sum_finrank_placeAbove`), and the general family argument gives the same count. The faithful
stabilizer action is then the local Galois group, and descent follows.

The generic coset-product lemma gives the product of the transports from `w'` to `w`; reindexing
the bundled places by their underlying places gives the public completion formula.

The embedding at a place is real on the fixed field of its stabilizer when the base place is
real. Thus the place below it in that fixed field is unramified; over a complex base place,
unramifiedness is automatic.
-/

noncomputable section

open NumberField
open scoped NumberField.LiesOver SIC.InfinitePlace

namespace SIC

namespace InfinitePlace

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L) [w.LiesOver v]

/-! ### The decomposition group acting on the completion -/

/-- The completions above `v`, with transport by Galois automorphisms. -/
def completionFamily : PermutedAlgebraFamily K v.Completion L (PlaceAbove (L := L) v)
    (fun i => i.1.Completion) where
  map σ i j h := completionAlgEquiv σ v i.1 j.1
    (PlaceAbove.mapEquiv_coe_eq_of_smul_eq v σ i j h)
  map_one := by
    intro i
    apply AlgEquiv.ext
    intro x
    change completionEquiv (RingEquiv.refl L) i.1 i.1 (mapEquiv_refl _) x = x
    rw [completionEquiv_refl]
    rfl
  map_mul := by
    intro σ τ i j l hij hjl
    apply AlgEquiv.ext
    intro x
    exact completionEquiv_mul σ τ
      (PlaceAbove.mapEquiv_coe_eq_of_smul_eq v τ i j hij)
      (PlaceAbove.mapEquiv_coe_eq_of_smul_eq v σ j l hjl) x
  map_algebraMap := by
    intro σ i j h x
    exact completionEquiv_algebraMap σ.toRingEquiv i.1 j.1
      (PlaceAbove.mapEquiv_coe_eq_of_smul_eq v σ i j h) x

omit [NumberField K] [NumberField L] in
/-- The stabilizer of a bundled infinite place is that of its underlying place. -/
theorem PlaceAbove.stabilizer_eq (i : PlaceAbove (L := L) v) :
    MulAction.stabilizer (L ≃ₐ[K] L) i = MulAction.stabilizer (L ≃ₐ[K] L) i.1 := by
  ext σ
  change (σ • i = i) ↔ (σ • i.1 = i.1)
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

omit [NumberField K] [NumberField L] in
/-- The stabilizer of the bundled place `w` is its decomposition group. -/
theorem PlaceAbove.stabilizer_mk :
    MulAction.stabilizer (L ≃ₐ[K] L)
      (⟨w, show w.LiesOver v from inferInstance⟩ : PlaceAbove (L := L) v) =
      MulAction.stabilizer (L ≃ₐ[K] L) w :=
  PlaceAbove.stabilizer_eq v ⟨w, show w.LiesOver v from inferInstance⟩

/-- The action of the decomposition group $D_w$ on $L_w$, obtained from the stabilizer action
of `completionFamily`. Milne, *Class Field Theory*, Chapter VII, §2. -/
def decompositionHom :
    MulAction.stabilizer (L ≃ₐ[K] L) w →* (w.Completion ≃ₐ[v.Completion] w.Completion) :=
  ((completionFamily (L := L) v).fiber
    (⟨w, show w.LiesOver v from inferInstance⟩ : PlaceAbove (L := L) v)).comp
    (MulEquiv.subgroupCongr (PlaceAbove.stabilizer_mk v w).symm).toMonoidHom

omit [NumberField K] [NumberField L] in
/-- The extension of `σ ∈ D_w` to $L_w$ is `σ` on `L`. -/
@[simp]
theorem decompositionHom_algebraMap (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) (x : L) :
    decompositionHom v w σ (algebraMap L w.Completion x) =
      algebraMap L w.Completion ((σ : L ≃ₐ[K] L) x) := by
  exact (completionFamily (L := L) v).fiber_algebraMap
    (⟨w, show w.LiesOver v from inferInstance⟩ : PlaceAbove (L := L) v)
    ((MulEquiv.subgroupCongr (PlaceAbove.stabilizer_mk v w).symm) σ) x

omit [NumberField K] [NumberField L] in
/-- The action of $D_w$ on $L_w$ is faithful. -/
theorem decompositionHom_injective : Function.Injective (decompositionHom v w) := by
  exact ((completionFamily (L := L) v).fiber_injective
    (⟨w, show w.LiesOver v from inferInstance⟩ : PlaceAbove (L := L) v)).comp
      (MulEquiv.subgroupCongr (PlaceAbove.stabilizer_mk v w).symm).injective

/-! ### Galois extensions -/

variable [IsGalois K L]

omit [NumberField K] [NumberField L] in
/-- The Galois group acts transitively on the infinite places above `v`. Milne, *Class Field
Theory*, Chapter VII, §2. -/
theorem exists_smul_eq (w' : NumberField.InfinitePlace L) [w'.LiesOver v] :
    ∃ σ : L ≃ₐ[K] L, σ • w = w' := by
  apply NumberField.InfinitePlace.exists_smul_eq_of_comap_eq
  rw [NumberField.InfinitePlace.LiesOver.comap_eq w v,
    NumberField.InfinitePlace.LiesOver.comap_eq w' v]

omit [NumberField K] [NumberField L] in
/-- The Galois group acts transitively on the bundled places above `v`. -/
theorem PlaceAbove.exists_smul_eq (i j : PlaceAbove (L := L) v) :
    ∃ σ : L ≃ₐ[K] L, σ • i = j := by
  obtain ⟨σ, hσ⟩ := SIC.InfinitePlace.exists_smul_eq v i.1 j.1
  exact ⟨σ, Subtype.ext hσ⟩

omit [NumberField K] [NumberField L] in
/-- The local degree is the order of the decomposition group: $[L_w : K_v] = |D_w|$. -/
theorem finrank_eq_card_stabilizer :
    Module.finrank v.Completion w.Completion = Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w) := by
  classical
  rw [NumberField.InfinitePlace.card_stabilizer]
  rcases w.isUnramified_or_isRamified K with hw | hw
  · simp only [hw, ↓reduceIte, hw.finrank_eq_one v]
  · simp only [show ¬w.IsUnramified K from hw, ↓reduceIte, hw.finrank_eq_two v]

/-- The local degree divides the global degree: $[L_w:K_v]\mid[L:K]$ for Galois `L/K`. -/
theorem finrank_dvd_finrank :
    Module.finrank v.Completion w.Completion ∣ Module.finrank K L := by
  have h := (completionFamily (L := L) v).finrank_dvd_finrank
    (PlaceAbove.exists_smul_eq v) (sum_finrank_placeAbove v)
    (⟨w, show w.LiesOver v from inferInstance⟩ : PlaceAbove (L := L) v)
  convert h using 1

omit [NumberField K] [NumberField L] in
/-- For Galois `L/K`, the action of $D_w$ on $L_w$ is bijective. -/
theorem decompositionHom_bijective : Function.Bijective (decompositionHom v w) :=
  bijective_of_injective_of_card_eq_finrank (decompositionHom v w)
    (decompositionHom_injective v w) (finrank_eq_card_stabilizer v w).symm

/-- The completion of a Galois extension at an infinite place is Galois. -/
instance isGalois_completion : IsGalois v.Completion w.Completion :=
  isGalois_of_injective_of_card_eq_finrank (decompositionHom v w)
    (decompositionHom_injective v w) (finrank_eq_card_stabilizer v w).symm

omit [NumberField K] [NumberField L] in
/-- Galois descent for the completion: the elements of $L_w$ fixed by $D_w$ are those of $K_v$. -/
theorem mem_range_completionMap_iff (x : w.Completion) :
    x ∈ (NumberField.LiesOver.completionMap (v := v) (w := w)).range ↔
      ∀ σ : MulAction.stabilizer (L ≃ₐ[K] L) w, decompositionHom v w σ x = x :=
  mem_range_algebraMap_iff_of_surjective (decompositionHom v w)
    (decompositionHom_bijective v w).2 x

/-- For places `w'` and `w` above `v`, the automorphisms carrying `w'` to `w` multiply to the local
norm: $\prod_{\sigma w' = w} \sigma y = N_{L_{w'}/K_v}(y)$ for $y \in L_{w'}$. Milne,
*Class Field Theory*, Chapter VII, §2, "The norm map on idèles". -/
theorem prod_completionEquiv_eq_completionMap_norm (w' : NumberField.InfinitePlace L)
    [w'.LiesOver v] [Fintype {σ : L ≃ₐ[K] L // σ • w' = w}] (y : w'.Completion) :
    ∏ σ : {σ : L ≃ₐ[K] L // σ • w' = w},
        completionEquiv (σ : L ≃ₐ[K] L).toRingEquiv w' w σ.2 y =
      NumberField.LiesOver.completionMap (v := v) (w := w) (Algebra.norm v.Completion y) := by
  let i : PlaceAbove (L := L) v := ⟨w', show w'.LiesOver v from inferInstance⟩
  let j : PlaceAbove (L := L) v := ⟨w, show w.LiesOver v from inferInstance⟩
  let _ : Fintype {σ : L ≃ₐ[K] L // σ • i = j} := Fintype.ofFinite _
  let e : {σ : L ≃ₐ[K] L // σ • w' = w} ≃ {σ : L ≃ₐ[K] L // σ • i = j} :=
    Equiv.subtypeEquivRight (fun σ => by
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)
  have hreindex :
      (∏ σ : {σ : L ≃ₐ[K] L // σ • w' = w},
        completionEquiv (σ : L ≃ₐ[K] L).toRingEquiv w' w σ.2 y) =
      (∏ σ : {σ : L ≃ₐ[K] L // σ • i = j},
        (completionFamily (L := L) v).map σ i j σ.2 y) := by
    apply Fintype.prod_equiv e _ _
    intro σ
    rfl
  have hprod := (completionFamily (L := L) v).prod_map_eq_algebraMap_norm
    (PlaceAbove.exists_smul_eq v) (sum_finrank_placeAbove v) i j y
  exact hreindex.trans hprod

/-! ### Bundled places above a fixed place

The local degree formula and the family's faithful fiber map identify the stabilizer with the
local Galois group without requiring the global extension to be finite. -/

omit [NumberField K] [NumberField L] in
/-- The stabilizer of a place above `v` is its local Galois group:
$D_w \cong \operatorname{Gal}(L_w/K_v)$. -/
def PlaceAbove.decompositionEquiv (w : PlaceAbove (L := L) v) :
    MulAction.stabilizer (L ≃ₐ[K] L) w ≃*
      (w.1.Completion ≃ₐ[v.Completion] w.1.Completion) := by
  have hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w) =
      Module.finrank v.Completion w.1.Completion := by
    rw [PlaceAbove.stabilizer_eq v w]
    exact (finrank_eq_card_stabilizer v w.1).symm
  exact MulEquiv.ofBijective ((completionFamily (L := L) v).fiber w)
    (bijective_of_injective_of_card_eq_finrank _
      ((completionFamily (L := L) v).fiber_injective w) hcard)

end InfinitePlace

/-! ### The decomposition field of a place

A complex embedding `ρ` of `H` whose restriction to `K` is real is real on the fixed field of the
decomposition group `D_w` of its place: either `ρ` is real, or its place is ramified over `K` and
`D_w` contains complex conjugation at `ρ`. The place below `w` is therefore unramified in the
decomposition field: it is real if the base place is real, and every place over a complex base
place is unramified. -/

section DecompositionField

variable {K H : Type*} [Field K] [Field H] [Algebra K H]

/-- **An embedding is real on the decomposition field of its place**: if `H/K` is Galois and
`φ : H → ℂ` is real on `K`, then `φ` is real on the fixed field `E` of the stabilizer `D_w` of
`w = InfinitePlace.mk φ`. If `φ` is not real, `w` is ramified over `K`
(`NumberField.InfinitePlace.isRamified_iff`), so some `σ ∈ D_w` is complex conjugation at `φ`
(`NumberField.InfinitePlace.exists_isConj_of_isRamified`), and `φ(x) = φ(σx) = conj(φ(x))` for
`x ∈ E`. -/
theorem isReal_comp_algebraMap_fixedField_stabilizer [IsGalois K H] (φ : H →+* ℂ)
    (hK : ComplexEmbedding.IsReal (φ.comp (algebraMap K H))) :
    ComplexEmbedding.IsReal (φ.comp (algebraMap
      (IntermediateField.fixedField (MulAction.stabilizer (H ≃ₐ[K] H) (InfinitePlace.mk φ)))
        H)) := by
  by_cases hφ : ComplexEmbedding.IsReal φ
  · exact hφ.comp _
  · have hwComplex : (InfinitePlace.mk φ).IsComplex :=
      InfinitePlace.not_isReal_iff_isComplex.mp fun hwReal ↦
        hφ (InfinitePlace.isReal_mk_iff.mp hwReal)
    have hwBase : ((InfinitePlace.mk φ).comap (algebraMap K H)).IsReal := by
      rw [InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff]
      exact hK
    have hwRam : InfinitePlace.IsRamified K (InfinitePlace.mk φ) :=
      InfinitePlace.isRamified_iff.mpr ⟨hwComplex, hwBase⟩
    obtain ⟨σ, hσ⟩ := InfinitePlace.exists_isConj_of_isRamified hwRam
    have hσmem : σ ∈ MulAction.stabilizer (H ≃ₐ[K] H) (InfinitePlace.mk φ) :=
      (InfinitePlace.mem_stabilizer_mk_iff φ σ).mpr (.inr hσ)
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have hfix : σ (algebraMap _ H x) = algebraMap _ H x :=
      IntermediateField.mem_fixedField_iff _ _ |>.mp x.property σ hσmem
    change star (φ (algebraMap _ H x)) = φ (algebraMap _ H x)
    rw [← hσ.eq, hfix]

/-- The place below `w` in its decomposition field is unramified over the base place. Used by
`globalArtin_ofCompletion_mem_stabilizer`. -/
theorem InfinitePlace.isUnramified_fixedField_stabilizer [IsGalois K H]
    (v : InfinitePlace K) (w : InfinitePlace H) [w.LiesOver v] :
    (InfinitePlace.below
      (K := IntermediateField.fixedField
        (MulAction.stabilizer (H ≃ₐ[K] H) w)) w).IsUnramified K := by
  let S := MulAction.stabilizer (H ≃ₐ[K] H) w
  let E := IntermediateField.fixedField S
  let u := InfinitePlace.below (K := E) w
  have hu : u.LiesOver v := InfinitePlace.liesOver_below_of_liesOver (L := E) v w
  rcases v.isReal_or_isComplex with hv | hv
  · have hwK : ComplexEmbedding.IsReal (w.embedding.comp (algebraMap K H)) := by
      rw [← InfinitePlace.isReal_mk_iff, ← InfinitePlace.comap_mk,
        InfinitePlace.mk_embedding, InfinitePlace.LiesOver.comap_eq w v]
      exact hv
    have huReal : u.IsReal := by
      change (w.comap (algebraMap E H)).IsReal
      rw [← InfinitePlace.mk_embedding w, InfinitePlace.comap_mk,
        InfinitePlace.isReal_mk_iff]
      have hh := isReal_comp_algebraMap_fixedField_stabilizer w.embedding hwK
      rw [InfinitePlace.mk_embedding w] at hh
      exact hh
    exact InfinitePlace.isUnramified_iff.mpr (.inl huReal)
  · apply InfinitePlace.isUnramified_iff.mpr
    right
    rwa [InfinitePlace.LiesOver.comap_eq u v]

end DecompositionField

end SIC
