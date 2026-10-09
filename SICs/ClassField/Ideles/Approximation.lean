/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Local.UnitGroups
import SICs.ClassField.Ideles.Topology
import SICs.ClassField.Completion.WeakApproximation

/-!
# Density of principal idèles modulo idèles away from a finite set

The subgroup of idèles that equal one at all infinite places and the finite places of a
chosen finite set has dense product with the principal idèles.

## The argument

The projection onto these selected components has a continuous section: extend by one at
the other places, using a finite product of single-component insertions. This projection is
an open quotient map. Mixed weak approximation makes the principal image dense in the
selected components, so its full preimage, the product of principal idèles and the kernel,
is dense. This is Milne, *Class Field Theory*, version 4.03, Chapter VII, proof of
Proposition 4.6, using [83, Neukirch (1999), Chapter II, Theorem 3.4].
-/

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField

namespace SIC

universe u

namespace IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

/-! ### Approximation modulo idèles away from a finite set

The subgroup $I^S$ has component one at every infinite place and at the finite places of $S$.
The projection onto these components has a continuous finite-support section and is therefore
open. Pulling back the dense principal image gives density of $K^\times I^S$ in $I_K$. -/

/-- The projection onto all infinite components and the finite components in $S$, used by
Milne's weak-approximation argument for `dense_principal_sup_awaySubgroup`. -/
def selectedComponents (S : Finset (HeightOneSpectrum (𝓞 K))) :
    NumberField.IdeleGroup (𝓞 K) K →*
      InfiniteLocalIdele K × (∀ v : S, (v.1.adicCompletion K)ˣ) :=
  (MonoidHom.pi (infiniteComponent K)).prod
    (MonoidHom.pi (fun v : S => finiteComponent K v.1))

/-- The selected-component projection evaluates the indicated local components. -/
@[simp]
theorem selectedComponents_apply (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    selectedComponents S x =
      ((fun v => infiniteComponent K v x), fun v : S => finiteComponent K v.1 x) := rfl

/-- The selected-component projection is continuous in the restricted-product topology. -/
private theorem continuous_selectedComponents (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Continuous (selectedComponents S) := by
  exact (componentsContinuousEquiv K).continuous.fst.prodMk
    (continuous_pi fun v : S => (_root_.RestrictedProduct.continuous_eval v.1).comp
      (componentsContinuousEquiv K).continuous.snd)

/-- Extend selected components by one at all other finite places. This is the finite-support
section of `selectedComponents`. -/
def selectedSection (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : InfiniteLocalIdele K × (∀ v : S, (v.1.adicCompletion K)ˣ)) :
    NumberField.IdeleGroup (𝓞 K) K := by
  classical
  exact (componentsContinuousEquiv K).symm
    (x.1, ∏ v : S, _root_.RestrictedProduct.mulSingle
      (fun w : HeightOneSpectrum (𝓞 K) =>
        FinitePlace.unitGroup w) v.1 (x.2 v))

/-- The finite-support section is continuous; used by
`isOpenQuotientMap_selectedComponents`. -/
private theorem continuous_selectedSection (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Continuous (selectedSection S) := by
  classical
  apply (componentsContinuousEquiv K).symm.continuous.comp
  apply continuous_fst.prodMk
  apply continuous_finsetProd
  intro v _
  exact (SIC.RestrictedProduct.continuous_mulSingle _ v.1).comp
    ((continuous_apply v).comp continuous_snd)

/-- Restricting the finite-support section recovers every selected component. -/
theorem selectedComponents_section (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.RightInverse (selectedSection S) (selectedComponents S) := by
  classical
  intro x
  change ((componentsContinuousEquiv K ((componentsContinuousEquiv K).symm _)).1,
    fun v : S => (componentsContinuousEquiv K ((componentsContinuousEquiv K).symm _)).2 v.1) = x
  rw [ContinuousMulEquiv.apply_symm_apply]
  apply Prod.ext
  · rfl
  · funext v
    change (_root_.RestrictedProduct.evalMonoidHom _ v.1)
      (∏ w : S, _root_.RestrictedProduct.mulSingle
        (fun q : HeightOneSpectrum (𝓞 K) =>
          FinitePlace.unitGroup q) w.1 (x.2 w)) = x.2 v
    rw [map_prod]
    simp only [_root_.RestrictedProduct.evalMonoidHom_apply]
    rw [Finset.prod_eq_single v]
    · exact _root_.RestrictedProduct.mulSingle_eq_same _ _ _
    · intro w _ hw
      exact _root_.RestrictedProduct.mulSingle_eq_of_ne _ _
        (fun h => hw (Subtype.ext h.symm))
    · simp

/-- The selected-component section has component one outside its finite support. -/
@[simp] theorem finiteComponent_selectedSection_of_notMem
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : InfiniteLocalIdele K × (∀ v : S, (v.1.adicCompletion K)ˣ))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    finiteComponent K v (selectedSection S x) = 1 := by
  classical
  change (componentsContinuousEquiv K ((componentsContinuousEquiv K).symm _)).2 v = 1
  rw [ContinuousMulEquiv.apply_symm_apply]
  change (_root_.RestrictedProduct.evalMonoidHom _ v)
    (∏ w : S, _root_.RestrictedProduct.mulSingle
      (fun q : HeightOneSpectrum (𝓞 K) =>
        FinitePlace.unitGroup q) w.1 (x.2 w)) = 1
  rw [map_prod]
  simp only [_root_.RestrictedProduct.evalMonoidHom_apply]
  apply Finset.prod_eq_one
  intro w _
  exact _root_.RestrictedProduct.mulSingle_eq_of_ne _ _
    (fun h => hv (h.symm ▸ w.2))

/-- Projection onto the selected places is an open quotient map, supplying the topology step
in `dense_principal_sup_awaySubgroup`. -/
theorem isOpenQuotientMap_selectedComponents (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsOpenQuotientMap (selectedComponents S) := by
  apply MonoidHom.isOpenQuotientMap_of_isQuotientMap
  apply Topology.IsQuotientMap.of_comp (continuous_selectedSection S)
    (continuous_selectedComponents S)
  convert (Topology.IsQuotientMap.id : Topology.IsQuotientMap
    (id : (InfiniteLocalIdele K × (∀ v : S, (v.1.adicCompletion K)ˣ)) → _)) using 1
  funext x
  exact selectedComponents_section S x

/-- Idèles whose components at the infinite places and at every finite place in $S$ are one.
This is $I^S$ in Milne, *Class Field Theory*, Chapter VII, proof of Proposition 4.6. -/
def awaySubgroup (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (NumberField.IdeleGroup (𝓞 K) K) :=
  (selectedComponents S).ker

/-- Membership in $I^S$ is the component-one condition. -/
theorem mem_awaySubgroup (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    x ∈ awaySubgroup S ↔
      (∀ v, infiniteComponent K v x = 1) ∧ (∀ v ∈ S, finiteComponent K v x = 1) := by
  simp only [awaySubgroup, MonoidHom.mem_ker, selectedComponents_apply, Prod.ext_iff,
    funext_iff, Subtype.forall]
  rfl

/-- The idèles away from $S$ are precisely the kernel of the selected-component projection. -/
@[simp]
theorem ker_selectedComponents (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (selectedComponents S).ker = awaySubgroup S := rfl

/-- Principal idèles times $I^S$ are dense, by simultaneous weak approximation. Milne,
*Class Field Theory*, Chapter VII, proof of Proposition 4.6. -/
theorem dense_principal_sup_awaySubgroup (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Dense (↑(NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔ awaySubgroup S) :
      Set (NumberField.IdeleGroup (𝓞 K) K)) := by
  let f := selectedComponents S
  have hdense : Dense (↑((NumberField.IdeleGroup.principalSubgroup (𝓞 K) K).map f) :
      Set (InfiniteLocalIdele K × (∀ v : S, (v.1.adicCompletion K)ˣ))) := by
    rw [← MonoidHom.range_comp, MonoidHom.coe_range]
    exact denseRange_mixedCompletionUnits S
  have hpre := hdense.preimage (isOpenQuotientMap_selectedComponents S).isOpenMap
  rw [← Subgroup.coe_comap, Subgroup.comap_map_eq, ker_selectedComponents] at hpre
  exact hpre

end IdeleGroup

end SIC

end
