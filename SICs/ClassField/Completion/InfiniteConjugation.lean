/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Completion.Norm
import SICs.ClassField.Completion.PlacesAbove
import Mathlib.Algebra.Order.Archimedean.Real.Hom

/-!
# Infinite completions under isomorphisms of number fields

An isomorphism of number fields `σ : L ≃ L'` carries each infinite place `w` of `L` to the
infinite place $\sigma(w) = w \circ \sigma^{-1}$ of `L'` and extends to an isometric isomorphism
of completions $L_w \cong L'_{\sigma(w)}$. When `σ` is a `K`-algebra isomorphism, it permutes the
places above each infinite place `v` of `K`, its completion is a $K_v$-algebra isomorphism, and it
preserves local norms.

This is the extension of `σ` to completions in Milne, *Class Field Theory*, version 4.03 (2020),
Chapter VII, §2, before Lemma 2.1, at the infinite places and for an arbitrary isomorphism of
number fields. For automorphisms, $\sigma(w)$ is Mathlib's action `σ • w`.

## The argument

By definition $|\sigma x|_{\sigma(w)} = |x|_w$, so `σ` is an isometric isomorphism
$(L, |\cdot|_w) \cong (L', |\cdot|_{\sigma(w)})$ and extends to the completions. On the dense
subfield `L` the extension is `σ`, which gives the composition, inverse, and identity laws by
density. When `σ` fixes `K`, the place `σ(w)` lies over the same place `v` as `w`, and the
extension agrees with the canonical completion maps from $K_v$ on the dense subfield `K`, hence
everywhere; it is therefore a $K_v$-algebra isomorphism and preserves the algebraic norm.

As at finite places, the second place is an explicit argument `w'` with a proof of
`mapEquiv σ w = w'`.
-/

noncomputable section

open NumberField
open scoped NumberField.LiesOver SIC.InfinitePlace

namespace SIC

namespace InfinitePlace

/-! ### Places under isomorphisms -/

section Places

variable {L L' L'' : Type*} [Field L] [Field L'] [Field L'']

/-- The bijection $w \mapsto w \circ \sigma^{-1}$ between the infinite places of isomorphic
fields. -/
def mapEquiv (σ : L ≃+* L') : NumberField.InfinitePlace L ≃ NumberField.InfinitePlace L' where
  toFun w := w.comap σ.symm.toRingHom
  invFun w' := w'.comap σ.toRingHom
  left_inv w := by
    ext x
    simp [NumberField.InfinitePlace.comap_apply]
  right_inv w' := by
    ext x
    simp [NumberField.InfinitePlace.comap_apply]

/-- The absolute value at `σ(w)` of `σ x` is the absolute value at `w` of `x`. -/
@[simp]
theorem mapEquiv_apply_apply (σ : L ≃+* L') (w : NumberField.InfinitePlace L) (x : L) :
    mapEquiv σ w (σ x) = w x := by
  simp [mapEquiv]

/-- The inverse of $w \mapsto \sigma(w)$ is $w' \mapsto \sigma^{-1}(w')$. -/
@[simp]
theorem mapEquiv_symm (σ : L ≃+* L') : (mapEquiv σ).symm = mapEquiv σ.symm := by
  rfl

/-- The places of a composite isomorphism: $(\tau\sigma)(w) = \tau(\sigma(w))$. -/
theorem mapEquiv_trans (σ : L ≃+* L') (τ : L' ≃+* L'') (w : NumberField.InfinitePlace L) :
    mapEquiv (σ.trans τ) w = mapEquiv τ (mapEquiv σ w) := by
  ext x
  simp [mapEquiv]

/-- The identity isomorphism fixes every infinite place. -/
@[simp]
theorem mapEquiv_refl (w : NumberField.InfinitePlace L) :
    mapEquiv (RingEquiv.refl L) w = w := by
  ext x
  simp [mapEquiv]

/-- For an automorphism over `K`, the map on infinite places is Mathlib's Galois action. -/
theorem mapEquiv_toRingEquiv {K : Type*} [Field K] [Algebra K L] (σ : L ≃ₐ[K] L)
    (w : NumberField.InfinitePlace L) : mapEquiv σ.toRingEquiv w = σ • w :=
  rfl

end Places

/-! ### Completions under isomorphisms -/

section Completion

variable {L L' L'' : Type*} [Field L] [Field L'] [Field L''] (σ : L ≃+* L')
  (w : NumberField.InfinitePlace L) (w' : NumberField.InfinitePlace L')
  (h : mapEquiv σ w = w')

include h in
/-- `σ` is an isometry between `L` with the absolute value of `w` and `L'` with that of `σ(w)`;
used by `completionEquiv`. -/
theorem isometry_withAbsCongr : Isometry (WithAbs.congr w.1 w'.1 σ) := by
  rw [AddMonoidHomClass.isometry_iff_norm]
  intro x
  change w' (σ x.ofAbs) = w x.ofAbs
  rw [← h, mapEquiv_apply_apply]

include h in
/-- `σ⁻¹` is an isometry between `L'` with the absolute value of `σ(w)` and `L` with that of
`w`; used by `completionEquiv`. -/
theorem isometry_withAbsCongr_symm : Isometry (WithAbs.congr w.1 w'.1 σ).symm := by
  have hs : mapEquiv σ.symm w' = w := by
    rw [← h, ← mapEquiv_symm, Equiv.symm_apply_apply]
  rw [WithAbs.congr_symm]
  exact isometry_withAbsCongr σ.symm w' w hs

/-- The isomorphism of completions $L_w \cong L'_{w'}$ extending `σ`, for $w' = \sigma(w)$.
Milne, *Class Field Theory*, Chapter VII, §2. -/
def completionEquiv : w.Completion ≃+* w'.Completion :=
  ((NumberField.InfinitePlace.Completion.equiv w).trans
    (UniformSpace.Completion.mapRingEquiv _ (isometry_withAbsCongr σ w w' h).continuous
      (isometry_withAbsCongr_symm σ w w' h).continuous)).trans
    (NumberField.InfinitePlace.Completion.equiv w').symm

/-- The completion of `σ` is an isometry. -/
theorem isometry_completionEquiv : Isometry (completionEquiv σ w w' h) := by
  exact (NumberField.InfinitePlace.Completion.isometryEquivCompletion w').symm.isometry.comp
    ((UniformSpace.Completion.isometry_mapRingHom (isometry_withAbsCongr σ w w' h)).comp
      (NumberField.InfinitePlace.Completion.isometryEquivCompletion w).isometry)

/-- The completion of `σ` extends `σ`. -/
@[simp]
theorem completionEquiv_algebraMap (x : L) :
    completionEquiv σ w w' h (algebraMap L w.Completion x) =
      algebraMap L' w'.Completion (σ x) := by
  apply NumberField.InfinitePlace.Completion.ext
  change (UniformSpace.Completion.mapRingHom (WithAbs.congr w.1 w'.1 σ).toRingHom
    (isometry_withAbsCongr σ w w' h).continuous)
      (↑(WithAbs.toAbs w.1 x)) = ↑(WithAbs.toAbs w'.1 (σ x))
  exact UniformSpace.Completion.mapRingHom_coe
    (f := (WithAbs.congr w.1 w'.1 σ).toRingHom)
    (isometry_withAbsCongr σ w w' h).continuous (WithAbs.toAbs w.1 x)

/-- The inverse of the completion of `σ` is the completion of `σ⁻¹`. -/
theorem completionEquiv_symm :
    (completionEquiv σ w w' h).symm =
      completionEquiv σ.symm w' w (by rw [← h, ← mapEquiv_symm, Equiv.symm_apply_apply]) := by
  rfl

/-- The completions of `σ` and `τ` compose to the completion of `τ ∘ σ`. -/
theorem completionEquiv_trans (τ : L' ≃+* L'') (w'' : NumberField.InfinitePlace L'')
    (h' : mapEquiv τ w' = w'') :
    (completionEquiv σ w w' h).trans (completionEquiv τ w' w'' h') =
      completionEquiv (σ.trans τ) w w'' (by rw [mapEquiv_trans, h, h']) := by
  apply RingEquiv.ext
  intro y
  have heq := SIC.InfinitePlace.funext_completion w
    ((isometry_completionEquiv τ w' w'' h').continuous.comp
      (isometry_completionEquiv σ w w' h).continuous)
    (isometry_completionEquiv (σ.trans τ) w w''
      (by rw [mapEquiv_trans, h, h'])).continuous
    (by
      intro x
      change completionEquiv τ w' w'' h'
          (completionEquiv σ w w' h (algebraMap L w.Completion x)) =
        completionEquiv (σ.trans τ) w w''
          (by rw [mapEquiv_trans, h, h']) (algebraMap L w.Completion x)
      rw [completionEquiv_algebraMap σ w w' h x,
        completionEquiv_algebraMap τ w' w'' h' (σ x),
        completionEquiv_algebraMap (σ.trans τ) w w'' _ x]
      rfl)
  exact congrFun heq y

/-- The completion of the identity is the identity. -/
@[simp]
theorem completionEquiv_refl :
    completionEquiv (RingEquiv.refl L) w w (mapEquiv_refl w) = RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro y
  have heq := SIC.InfinitePlace.funext_completion w
    (isometry_completionEquiv (RingEquiv.refl L) w w (mapEquiv_refl w)).continuous
    continuous_id (by
      intro x
      change completionEquiv (RingEquiv.refl L) w w (mapEquiv_refl w)
        (algebraMap L w.Completion x) = algebraMap L w.Completion x
      rw [completionEquiv_algebraMap]
      rfl)
  exact congrFun heq y

/-- At real places the completion of `σ` commutes with the real embeddings:
$\iota_{w'}(\sigma x) = \iota_w(x)$ for $x \in L_w$, since a ring isomorphism of $\mathbb R$ is
the identity. Used by `IdeleGroup.congr_mem_congruentSubgroup` to transport positivity. -/
theorem extensionEmbeddingOfIsReal_completionEquiv (hw : w.IsReal) (hw' : w'.IsReal)
    (x : w.Completion) :
    NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw'
        (completionEquiv σ w w' h x) =
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x := by
  let e : ℝ →+* ℝ :=
    (((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.trans
      (completionEquiv σ w w' h)).trans
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw')).toRingHom
  have he : e = RingHom.id ℝ := Subsingleton.elim _ _
  have hx := congrArg (fun f : ℝ →+* ℝ =>
    f ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw) x)) he
  change (((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.trans
      (completionEquiv σ w w' h)).trans
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw'))
      ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw) x) =
    (RingHom.id ℝ) ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw) x) at hx
  simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply, RingHom.id_apply] at hx
  simpa only [NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply] using hx

end Completion

/-! ### Isomorphisms over a base field -/

section Algebra

variable {K L L' : Type*} [Field K] [Field L] [Field L'] [NumberField K] [NumberField L]
  [NumberField L'] [Algebra K L] [Algebra K L'] (σ : L ≃ₐ[K] L')
  (v : NumberField.InfinitePlace K)

omit [NumberField K] [NumberField L] [NumberField L'] in
/-- A `K`-isomorphism carries a place above `v` to a place above `v`. -/
theorem liesOver_mapEquiv (w : NumberField.InfinitePlace L) [w.LiesOver v] :
    (mapEquiv σ.toRingEquiv w).LiesOver v := by
  refine ⟨?_⟩
  apply AbsoluteValue.ext
  intro x
  change w (σ.symm (algebraMap K L' x)) = v x
  rw [show σ.symm (algebraMap K L' x) = algebraMap K L x by simp]
  exact NumberField.InfinitePlace.comp_of_comap_eq
    (NumberField.InfinitePlace.LiesOver.comap_eq w v) x

/-- A `K`-isomorphism permutes the infinite places above `v`: $w \mapsto \sigma(w)$. -/
def PlaceAbove.mapEquiv : PlaceAbove (L := L) v ≃ PlaceAbove (L := L') v where
  toFun w := ⟨InfinitePlace.mapEquiv σ.toRingEquiv w.1, liesOver_mapEquiv σ v w.1⟩
  invFun w' := ⟨InfinitePlace.mapEquiv σ.symm.toRingEquiv w'.1, liesOver_mapEquiv σ.symm v w'.1⟩
  left_inv w := by
    apply Subtype.ext
    change InfinitePlace.mapEquiv σ.symm.toRingEquiv
      (InfinitePlace.mapEquiv σ.toRingEquiv w.1) = w.1
    rw [AlgEquiv.symm_toRingEquiv, ← InfinitePlace.mapEquiv_symm,
      Equiv.symm_apply_apply]
  right_inv w' := by
    apply Subtype.ext
    change InfinitePlace.mapEquiv σ.toRingEquiv
      (InfinitePlace.mapEquiv σ.symm.toRingEquiv w'.1) = w'.1
    rw [AlgEquiv.symm_toRingEquiv, ← InfinitePlace.mapEquiv_symm,
      Equiv.apply_symm_apply]

variable (w : NumberField.InfinitePlace L) (w' : NumberField.InfinitePlace L')
  [w.LiesOver v] [w'.LiesOver v] (h : InfinitePlace.mapEquiv σ.toRingEquiv w = w')

omit [NumberField K] [NumberField L] [NumberField L'] in
/-- The completion of a `K`-isomorphism is compatible with the completion maps from $K_v$. -/
@[simp]
theorem completionEquiv_completionMap (a : v.Completion) :
    completionEquiv σ.toRingEquiv w w' h (NumberField.LiesOver.completionMap (w := w) a) =
      NumberField.LiesOver.completionMap (w := w') a := by
  have heq := SIC.InfinitePlace.funext_completion v
    ((isometry_completionEquiv σ.toRingEquiv w w' h).continuous.comp
      NumberField.LiesOver.continuous_completionMap)
    NumberField.LiesOver.continuous_completionMap
    (by
      intro x
      change completionEquiv σ.toRingEquiv w w' h
          (NumberField.LiesOver.completionMap (w := w) (algebraMap K v.Completion x)) =
        NumberField.LiesOver.completionMap (w := w') (algebraMap K v.Completion x)
      have hw : NumberField.LiesOver.completionMap (w := w)
          (algebraMap K v.Completion x) = algebraMap K w.Completion x := by
        exact (IsScalarTower.algebraMap_apply K v.Completion w.Completion x).symm
      have hw' : NumberField.LiesOver.completionMap (w := w')
          (algebraMap K v.Completion x) = algebraMap K w'.Completion x := by
        exact (IsScalarTower.algebraMap_apply K v.Completion w'.Completion x).symm
      rw [hw, hw']
      have hk : algebraMap K w.Completion x =
          algebraMap L w.Completion (algebraMap K L x) := by
        rfl
      have hk' : algebraMap K w'.Completion x =
          algebraMap L' w'.Completion (algebraMap K L' x) := by
        rfl
      rw [hk, hk', completionEquiv_algebraMap]
      exact congrArg (algebraMap L' w'.Completion) (σ.commutes x))
  exact congrFun heq a

/-- The completion of a `K`-isomorphism as a $K_v$-algebra isomorphism $L_w \cong L'_{w'}$. -/
def completionAlgEquiv : w.Completion ≃ₐ[v.Completion] w'.Completion :=
  AlgEquiv.ofRingEquiv (f := completionEquiv σ.toRingEquiv w w' h)
    (completionEquiv_completionMap σ v w w' h)

omit [NumberField K] [NumberField L] [NumberField L'] in
/-- The completion of a `K`-isomorphism preserves local norms:
$N_{L'_{\sigma(w)}/K_v}(\sigma x) = N_{L_w/K_v}(x)$. -/
@[simp]
theorem localNorm_completionEquiv (x : w.Completionˣ) :
    localNorm v w'
        (Units.map (completionEquiv σ.toRingEquiv w w' h : w.Completion →* w'.Completion) x) =
      localNorm v w x := by
  apply Units.ext
  exact Algebra.norm_eq_of_algEquiv (completionAlgEquiv σ v w w' h) (x : w.Completion)

end Algebra

/-! ### The Galois action on infinite places

Mathlib's action of the automorphisms of `L` over `K` on the infinite places of `L` is
`mapEquiv`; it permutes the places above each infinite place of `K`, and completions of products
compose. -/

section Action

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- An automorphism over `K` carries a place above `v` to a place above `v`. -/
instance liesOver_smul (v : NumberField.InfinitePlace K) (σ : L ≃ₐ[K] L)
    (w : NumberField.InfinitePlace L) [w.LiesOver v] : (σ • w).LiesOver v := by
  simpa only [mapEquiv_toRingEquiv] using liesOver_mapEquiv σ v w

/-- The completion of a product of automorphisms is the composite of the completions:
$(\sigma\tau)_{w \to w''} = \sigma_{w' \to w''} \circ \tau_{w \to w'}$. -/
theorem completionEquiv_mul (σ τ : L ≃ₐ[K] L) {w w' w'' : NumberField.InfinitePlace L}
    (hτ : τ • w = w') (hσ : σ • w' = w'') (y : w.Completion) :
    completionEquiv (σ * τ).toRingEquiv w w''
      (by rw [mapEquiv_toRingEquiv, mul_smul, hτ, hσ]) y =
      completionEquiv σ.toRingEquiv w' w'' hσ (completionEquiv τ.toRingEquiv w w' hτ y) := by
  have heq := completionEquiv_trans τ.toRingEquiv w w' hτ σ.toRingEquiv w'' hσ
  have hmul : (σ * τ).toRingEquiv = τ.toRingEquiv.trans σ.toRingEquiv := by
    ext a
    rfl
  simpa only [hmul, RingEquiv.trans_apply] using
    congrArg (fun e : w.Completion ≃+* w''.Completion ↦ e y) heq.symm

variable [NumberField K] [NumberField L] (v : NumberField.InfinitePlace K)

/-- Galois automorphisms act on the places above `v`. -/
instance PlaceAbove.mulAction : MulAction (L ≃ₐ[K] L) (PlaceAbove (L := L) v) where
  smul σ w := PlaceAbove.mapEquiv σ v w
  one_smul w := by
    apply Subtype.ext
    change SIC.InfinitePlace.mapEquiv (1 : L ≃ₐ[K] L).toRingEquiv w.1 = w.1
    exact SIC.InfinitePlace.mapEquiv_refl w.1
  mul_smul σ τ w := by
    apply Subtype.ext
    change SIC.InfinitePlace.mapEquiv (σ * τ).toRingEquiv w.1 =
      SIC.InfinitePlace.mapEquiv σ.toRingEquiv
        (SIC.InfinitePlace.mapEquiv τ.toRingEquiv w.1)
    exact SIC.InfinitePlace.mapEquiv_trans τ.toRingEquiv σ.toRingEquiv w.1

omit [NumberField K] [NumberField L] in
/-- If an automorphism carries `w` to `w'`, its `mapEquiv` carries the underlying infinite
place to that of `w'`. Used by the infinite idèle fiber transport. -/
theorem PlaceAbove.mapEquiv_coe_eq_of_smul_eq (σ : L ≃ₐ[K] L)
    (w w' : PlaceAbove (L := L) v) (h : σ • w = w') :
    SIC.InfinitePlace.mapEquiv σ.toRingEquiv w.1 = w'.1 := by
  have h' := congrArg Subtype.val h
  change SIC.InfinitePlace.mapEquiv σ.toRingEquiv w.1 = w'.1 at h'
  exact h'

omit [NumberField K] [NumberField L] in
/-- Conjugation fixes the infinite place below `w`. Used by the infinite-place permutation
lattice in the S-unit cohomology argument. -/
theorem below_smul (σ : L ≃ₐ[K] L) (w : NumberField.InfinitePlace L) :
    below (K := K) (σ • w) = below (K := K) w := by
  exact below_eq_of_liesOver (below (K := K) w) (σ • w)

omit [NumberField K] [NumberField L] in
/-- Real or complex multiplicity is invariant under conjugation. Used by the weighted unit
logarithm. -/
theorem mult_smul (σ : L ≃ₐ[K] L) (w : NumberField.InfinitePlace L) :
    (σ • w).mult = w.mult := by
  unfold NumberField.InfinitePlace.mult
  rw [NumberField.InfinitePlace.isReal_smul_iff]

end Action

end InfinitePlace

end SIC
