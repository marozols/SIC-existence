/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Components of number-field idèles

Algebraic component maps, extensionality, principal-component formulas, and homomorphisms
assembled from local parts for Mathlib's idèle group.

## The argument

Units of the product of the infinite and finite adèle rings split as a product.  Infinite adèle
units are the product of the local unit groups, while finite adèle units are the restricted
product of the finite local unit groups.  Evaluation in these two descriptions gives the local
components.  Since both equivalences are injective, equality at every finite and infinite place
determines an idèle.  The principal-component formulas follow from the diagonal adèle embedding.
An idèle inserted from one finite or infinite completion is `1` at every other place and has the
prescribed unit at its supporting place.  The commutativity of the idèle class group is recorded as
an instance so that quotients by its subgroups are found by instance search.  Principal idèles
have trivial idèle class by definition of the quotient. Homomorphisms on the infinite and finite
local parts assemble through the algebraic component equivalence, and composition is partwise.
-/

noncomputable section

open scoped NumberField NumberField.AdeleRing RestrictedProduct
open IsDedekindDomain NumberField

namespace SIC

/-! ### Local component coordinates -/

/-- The infinite local part of the idèle group, in product coordinates. -/
abbrev InfiniteLocalIdele (K : Type*) [Field K] :=
  (v : InfinitePlace K) → v.Completionˣ

/-- The finite local part of the idèle group, in restricted-product coordinates. -/
abbrev FiniteLocalIdele (K : Type*) [Field K] [NumberField K] :=
  Πʳ v : HeightOneSpectrum (NumberField.RingOfIntegers K),
    [(v.adicCompletion K)ˣ,
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units]

/-! ### Commutativity of the idèle class group -/

/-- The idèle class group is commutative.  Stated directly because instance search for the
normality of its subgroups otherwise explores the cyclic-group instances first and fails. -/
instance IdeleClassGroup.instIsMulCommutative (K : Type*) [Field K] [NumberField K] :
    IsMulCommutative (NumberField.IdeleClassGroup (𝓞 K) K) :=
  ⟨⟨fun a b ↦ mul_comm a b⟩⟩

namespace IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

/-- The algebraic decomposition of idèles into their infinite components and restricted finite
components. -/
def componentsEquiv :
    NumberField.IdeleGroup (𝓞 K) K ≃*
      InfiniteLocalIdele K × FiniteLocalIdele K :=
  MulEquiv.prodUnits.trans <|
    MulEquiv.prodCongr MulEquiv.piUnits
      (_root_.RestrictedProduct.unitsEquiv
        (fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K))

/-- The component of an idèle at an infinite place. -/
def infiniteComponent (v : InfinitePlace K) :
    NumberField.IdeleGroup (𝓞 K) K →* v.Completionˣ :=
  (Pi.evalMonoidHom (fun v : InfinitePlace K ↦ v.Completionˣ) v).comp <|
    (MonoidHom.fst _ _).comp (componentsEquiv K).toMonoidHom

/-- The component of an idèle at a finite place. -/
def finiteComponent (v : HeightOneSpectrum (𝓞 K)) :
    NumberField.IdeleGroup (𝓞 K) K →* (v.adicCompletion K)ˣ :=
  (_root_.RestrictedProduct.evalMonoidHom
    (fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ) v).comp <|
      (MonoidHom.snd _ _).comp (componentsEquiv K).toMonoidHom

/-- Evaluation of `infiniteComponent` in the component decomposition. -/
@[simp]
theorem infiniteComponent_apply
    (v : InfinitePlace K) (x : NumberField.IdeleGroup (𝓞 K) K) :
    infiniteComponent K v x = (componentsEquiv K x).1 v := rfl

/-- Evaluation of `finiteComponent` in the component decomposition. -/
@[simp]
theorem finiteComponent_apply
    (v : HeightOneSpectrum (𝓞 K)) (x : NumberField.IdeleGroup (𝓞 K) K) :
    finiteComponent K v x = (componentsEquiv K x).2 v := rfl

/-- Two idèles are equal when all their finite and infinite components are equal. -/
@[ext]
theorem ext {x y : NumberField.IdeleGroup (𝓞 K) K}
    (hinf : ∀ v, infiniteComponent K v x = infiniteComponent K v y)
    (hfin : ∀ v, finiteComponent K v x = finiteComponent K v y) : x = y := by
  apply (componentsEquiv K).injective
  apply Prod.ext
  · funext v
    exact hinf v
  · apply _root_.RestrictedProduct.ext
    intro v
    exact hfin v

/-- The infinite component of a principal idèle is the corresponding completion embedding. -/
@[simp]
theorem infiniteComponent_unitEmbedding (v : InfinitePlace K) (x : Kˣ) :
    infiniteComponent K v (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K x) =
      Units.map (algebraMap K v.Completion) x := rfl

/-- The finite component of a principal idèle is the corresponding completion embedding. -/
@[simp]
theorem finiteComponent_unitEmbedding (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    finiteComponent K v (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K x) =
      Units.map (algebraMap K (v.adicCompletion K)) x := rfl

/-- The principal idèle embedding $K^\times \to I_K$ is injective. -/
theorem unitEmbedding_injective :
    Function.Injective (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K) :=
  Units.map_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 K) K)

end IdeleGroup

/-! ### Principal idèle classes -/

namespace IdeleClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- A principal idèle represents the identity in the idèle class group. -/
@[simp]
theorem coe_unitEmbedding (x : Kˣ) :
    ((NumberField.IdeleGroup.unitEmbedding (𝓞 K) K x :
        NumberField.IdeleGroup (𝓞 K) K) :
      NumberField.IdeleClassGroup (𝓞 K) K) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨x, rfl⟩

/-- Multiplying an idèle by a principal idèle does not change its class: $[a y] = [y]$ in
$C_K$ for $a\in K^\times$. -/
@[simp]
theorem mk_unitEmbedding_mul (a : Kˣ) (y : NumberField.IdeleGroup (𝓞 K) K) :
    ((NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a * y : NumberField.IdeleGroup (𝓞 K) K) :
      NumberField.IdeleClassGroup (𝓞 K) K) = y := by
  rw [QuotientGroup.mk_mul, coe_unitEmbedding]
  change (1 : NumberField.IdeleClassGroup (𝓞 K) K) * (y : NumberField.IdeleClassGroup (𝓞 K) K) = y
  exact one_mul (y : NumberField.IdeleClassGroup (𝓞 K) K)

end IdeleClassGroup

namespace IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

/-! ### Idèles supported at one finite place -/

/-- Every infinite component of an idèle supported at one finite place is `1`. -/
@[simp]
theorem infiniteComponent_ofAdicCompletion
    (w : InfinitePlace K) (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    infiniteComponent K w
      (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v x) = 1 := by
  rfl

/-- The component at `v` of the idèle supported at `v` is its original local unit. -/
@[simp]
theorem finiteComponent_ofAdicCompletion_self
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    finiteComponent K v
      (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v x) = x := by
  classical
  apply Units.ext
  change RestrictedProduct.mulSingle
    (fun q : HeightOneSpectrum (𝓞 K) ↦ q.adicCompletionIntegers K) v
      (x : v.adicCompletion K) v = (x : v.adicCompletion K)
  exact RestrictedProduct.mulSingle_eq_same
    (fun q : HeightOneSpectrum (𝓞 K) ↦ q.adicCompletionIntegers K) v
      (x : v.adicCompletion K)

/-- A finite component away from the support of a locally supported idèle is `1`. -/
@[simp]
theorem finiteComponent_ofAdicCompletion_of_ne
    (v w : HeightOneSpectrum (𝓞 K)) (h : w ≠ v) (x : (v.adicCompletion K)ˣ) :
    finiteComponent K w
      (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v x) = 1 := by
  classical
  apply Units.ext
  change RestrictedProduct.mulSingle
    (fun q : HeightOneSpectrum (𝓞 K) ↦ q.adicCompletionIntegers K) v
      (x : v.adicCompletion K) w = 1
  exact RestrictedProduct.mulSingle_eq_of_ne
    (fun q : HeightOneSpectrum (𝓞 K) ↦ q.adicCompletionIntegers K)
      (x : v.adicCompletion K) h

/-! ### Idèles supported at one infinite place -/

/-- Every finite component of an idèle supported at one infinite place is `1`. -/
@[simp]
theorem finiteComponent_ofCompletion
    (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) (x : w.Completionˣ) :
    finiteComponent K v (NumberField.IdeleGroup.ofCompletion (𝓞 K) K w x) = 1 := by
  rfl

/-- The component at `w` of the idèle supported at `w` is its original local unit. -/
@[simp]
theorem infiniteComponent_ofCompletion_self (w : InfinitePlace K) (x : w.Completionˣ) :
    infiniteComponent K w (NumberField.IdeleGroup.ofCompletion (𝓞 K) K w x) = x := by
  apply Units.ext
  change (InfiniteAdeleRing.ofCompletion w (x : w.Completion)) w = _
  classical
  exact Pi.mulSingle_eq_same w (x : w.Completion)

/-- An infinite component away from the support of a locally supported idèle is `1`. -/
@[simp]
theorem infiniteComponent_ofCompletion_of_ne
    (v w : InfinitePlace K) (h : v ≠ w) (x : w.Completionˣ) :
    infiniteComponent K v (NumberField.IdeleGroup.ofCompletion (𝓞 K) K w x) = 1 := by
  apply Units.ext
  change (InfiniteAdeleRing.ofCompletion w (x : w.Completion)) v = 1
  classical
  exact Pi.mulSingle_eq_of_ne h (x : w.Completion)

end IdeleGroup

/-! ### Idèle homomorphisms given by local parts -/

namespace IdeleGroup

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M]

/-- The idèle homomorphism $I_K \to I_L$ with prescribed infinite part `f` and finite part `g`,
assembled through the component decompositions. The idèle norm, the inclusion of idèles, and the
idèle isomorphism induced by a field isomorphism are of this form. -/
def mapComponents (f : InfiniteLocalIdele K →* InfiniteLocalIdele L)
    (g : FiniteLocalIdele K →* FiniteLocalIdele L) :
    NumberField.IdeleGroup (𝓞 K) K →* NumberField.IdeleGroup (𝓞 L) L :=
  (componentsEquiv L).symm.toMonoidHom.comp <|
    (f.prodMap g).comp (componentsEquiv K).toMonoidHom

/-- The components of `mapComponents f g x` are the images of the components of `x`. -/
@[simp]
theorem componentsEquiv_mapComponents (f : InfiniteLocalIdele K →* InfiniteLocalIdele L)
    (g : FiniteLocalIdele K →* FiniteLocalIdele L) (x : NumberField.IdeleGroup (𝓞 K) K) :
    componentsEquiv L (mapComponents f g x) =
      (f (componentsEquiv K x).1, g (componentsEquiv K x).2) := by
  exact (componentsEquiv L).apply_symm_apply _

/-- The infinite components of `mapComponents f g x` are those of `f`. -/
@[simp]
theorem infiniteComponent_mapComponents (f : InfiniteLocalIdele K →* InfiniteLocalIdele L)
    (g : FiniteLocalIdele K →* FiniteLocalIdele L) (w : InfinitePlace L)
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    infiniteComponent L w (mapComponents f g x) = f (componentsEquiv K x).1 w := by
  rw [infiniteComponent_apply, componentsEquiv_mapComponents]

/-- The finite components of `mapComponents f g x` are those of `g`. -/
@[simp]
theorem finiteComponent_mapComponents (f : InfiniteLocalIdele K →* InfiniteLocalIdele L)
    (g : FiniteLocalIdele K →* FiniteLocalIdele L) (w : HeightOneSpectrum (𝓞 L))
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    finiteComponent L w (mapComponents f g x) = g (componentsEquiv K x).2 w := by
  rw [finiteComponent_apply, componentsEquiv_mapComponents]

/-- Idèle homomorphisms given by local parts compose partwise. -/
theorem mapComponents_mapComponents (f₁ : InfiniteLocalIdele K →* InfiniteLocalIdele L)
    (g₁ : FiniteLocalIdele K →* FiniteLocalIdele L)
    (f₂ : InfiniteLocalIdele L →* InfiniteLocalIdele M)
    (g₂ : FiniteLocalIdele L →* FiniteLocalIdele M) (x : NumberField.IdeleGroup (𝓞 K) K) :
    mapComponents f₂ g₂ (mapComponents f₁ g₁ x) = mapComponents (f₂.comp f₁) (g₂.comp g₁) x := by
  apply (componentsEquiv M).injective
  simp only [componentsEquiv_mapComponents, MonoidHom.comp_apply]

end IdeleGroup

end SIC

end
