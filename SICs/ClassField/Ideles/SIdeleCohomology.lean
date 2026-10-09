/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.SIdeles
import SICs.ClassField.Ideles.FiniteFiber
import SICs.ClassField.Ideles.InfiniteFiber
import SICs.GroupCohomology.Pi

/-!
# Cohomology of S-idèles

The subgroup of idèles integral outside a finite set is the product of its semilocal
coordinates as a Galois representation, and the idèles that are units at every finite place have
Herbrand quotient the product of the local degrees at the infinite places.

The coordinate decomposition follows Milne, *Class Field Theory*, version 4.03 (2020),
Chapter VII, Propositions 2.5 and 2.7. It intertwines the Galois action on the actual idèle
subgroup with the semilocal actions, and Tate cohomology commutes with their product. For an
arbitrary finite exceptional set, only finitely many integral-unit factors outside it can be
nontrivial, and each has Herbrand quotient one, so these factors contribute one. All infinite
places are allowed, and `S` records only the finite exceptional places.

At `S = ∅`, the idèles are units at every finite place. Their quotient is computed directly
from the infinite factors, by Shapiro's lemma and the local norm-index formula, and the finite
integral-unit factors, as in Childress, *Class Field Theory* (2009), Chapter IV,
Proposition 5.7 and the observation following its proof on p. 96. Thus the ordinary-unit
calculation does not require the norm-index formula for multiplicative groups of finite
completions.
-/
noncomputable section
open IsDedekindDomain NumberField
open scoped NumberField NumberField.LiesOver SIC.FinitePlace SIC.InfinitePlace
namespace SIC.IdeleGroup
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- The componentwise representation on semilocal coordinates of the `S`-idèle subgroup. -/
abbrev sCoordinateRep (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  (Representation.pi (fun v : NumberField.InfinitePlace K =>
    InfinitePlace.semilocal (L := L) v)).prod
    ((Representation.pi (fun v : S => FinitePlace.semilocal (L := L) v.1)).prod
      (Representation.pi (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
        FinitePlace.semilocalUnits (L := L) v.1)))

/-! ### The coordinate action

The multiplicative decomposition becomes an integer-linear map after commuting `Additive` with
products. At each transported place, its coordinate action is the completion transport defining
the corresponding semilocal representation. -/

/-- The integer-linear form of `sComponentsEquiv`, used by `sComponentsRepEquiv`. -/
private def sComponentsLinearEquiv (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (sSubrep (L := L) S).toSubmodule ≃ₗ[ℤ] ((∀ v : NumberField.InfinitePlace K,
        ∀ w : InfinitePlace.PlaceAbove (L := L) v, Additive w.1.Completionˣ) ×
      ((∀ v : S, ∀ w : FinitePlace.PrimeAbove (L := L) v.1,
        Additive ((FinitePlace.PrimeAbove.place v.1 w).adicCompletion L)ˣ) ×
      (∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        ∀ w : FinitePlace.PrimeAbove (L := L) v.1,
          Additive (FinitePlace.unitGroup (FinitePlace.PrimeAbove.place v.1 w))))) := by
  let eInf : Additive (∀ v : NumberField.InfinitePlace K,
      ∀ w : InfinitePlace.PlaceAbove (L := L) v, w.1.Completionˣ) ≃+
      (∀ v : NumberField.InfinitePlace K,
        ∀ w : InfinitePlace.PlaceAbove (L := L) v, Additive w.1.Completionˣ) :=
    (AddEquiv.piAdditive _).trans
      (AddEquiv.piCongrRight fun _ => AddEquiv.piAdditive _)
  let eF : Additive (∀ v : S,
      ∀ w : FinitePlace.PrimeAbove (L := L) v.1,
        ((FinitePlace.PrimeAbove.place v.1 w).adicCompletion L)ˣ) ≃+
      (∀ v : S, ∀ w : FinitePlace.PrimeAbove (L := L) v.1,
        Additive ((FinitePlace.PrimeAbove.place v.1 w).adicCompletion L)ˣ) :=
    (AddEquiv.piAdditive _).trans
      (AddEquiv.piCongrRight fun _ => AddEquiv.piAdditive _)
  let eU : Additive (∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      ∀ w : FinitePlace.PrimeAbove (L := L) v.1,
        FinitePlace.unitGroup (FinitePlace.PrimeAbove.place v.1 w)) ≃+
      (∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        ∀ w : FinitePlace.PrimeAbove (L := L) v.1,
          Additive (FinitePlace.unitGroup (FinitePlace.PrimeAbove.place v.1 w))) :=
    (AddEquiv.piAdditive _).trans
      (AddEquiv.piCongrRight fun _ => AddEquiv.piAdditive _)
  exact (((sComponentsEquiv S).toAdditive.trans
    (AddEquiv.prodAdditive _ _)).trans
      (eInf.prodCongr ((AddEquiv.prodAdditive _ _).trans (eF.prodCongr eU)))).toIntLinearEquiv

/-- The infinite coordinate of `sComponentsLinearEquiv`; used by `sComponentsRepEquiv`. -/
private theorem sComponentsLinearEquiv_infinite (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : (sSubrep (L := L) S).toSubmodule) (v : NumberField.InfinitePlace K)
    (w : InfinitePlace.PlaceAbove (L := L) v) :
    (sComponentsLinearEquiv S x).1 v w =
      Additive.ofMul (infiniteComponent L w.1 x.1.toMul) := rfl

/-- The finite coordinate at `S` of `sComponentsLinearEquiv`; used by
`sComponentsRepEquiv`. -/
private theorem sComponentsLinearEquiv_inside (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : (sSubrep (L := L) S).toSubmodule) (v : S)
    (w : FinitePlace.PrimeAbove (L := L) v.1) :
    (sComponentsLinearEquiv S x).2.1 v w =
      Additive.ofMul (finiteComponent L (FinitePlace.PrimeAbove.place v.1 w) x.1.toMul) := rfl

/-- The integral coordinate outside `S` of `sComponentsLinearEquiv`; used by
`sComponentsRepEquiv`. -/
private theorem sComponentsLinearEquiv_outside (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : (sSubrep (L := L) S).toSubmodule)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
    (w : FinitePlace.PrimeAbove (L := L) v.1) :
    (((sComponentsLinearEquiv S x).2.2 v w).toMul.1 :
      ((FinitePlace.PrimeAbove.place v.1 w).adicCompletion L)ˣ) =
      finiteComponent L (FinitePlace.PrimeAbove.place v.1 w) x.1.toMul := rfl

/-- The infinite coordinates of `sComponentsLinearEquiv` respect the Galois action; used by
`sComponentsRepEquiv`. -/
private theorem sComponentsLinearEquiv_smul_infinite
    (S : Finset (HeightOneSpectrum (𝓞 K))) (σ : L ≃ₐ[K] L)
    (x : (sSubrep (L := L) S).toSubmodule) (v : NumberField.InfinitePlace K)
    (w' : InfinitePlace.PlaceAbove (L := L) v) :
    (sComponentsLinearEquiv S ((sSubrep S).toRepresentation σ x)).1 v w' =
      InfinitePlace.semilocal (L := L) v σ ((sComponentsLinearEquiv S x).1 v) w' := by
  let w := σ⁻¹ • w'
  have hw : σ • w = w' := by simp [w]
  rw [sComponentsLinearEquiv_infinite,
    InfinitePlace.semilocal_apply_image v σ w w' hw,
    InfinitePlace.semilocalFamily_map v σ w w' hw]
  rw [sComponentsLinearEquiv_infinite]
  have hplace := InfinitePlace.PlaceAbove.mapEquiv_coe_eq_of_smul_eq v σ w w' hw
  change Additive.ofMul (infiniteComponent L w'.1 (σ • x.1.toMul)) =
    Additive.ofMul (Units.map (InfinitePlace.completionEquiv σ.toRingEquiv w.1 w'.1
      hplace) (infiniteComponent L w.1 x.1.toMul))
  rw [smul_def, infiniteComponent_congr σ.toRingEquiv w.1 w'.1 hplace]

/-- The finite coordinates above `S` of `sComponentsLinearEquiv` respect the Galois action;
used by `sComponentsRepEquiv`. -/
private theorem sComponentsLinearEquiv_smul_inside
    (S : Finset (HeightOneSpectrum (𝓞 K))) (σ : L ≃ₐ[K] L)
    (x : (sSubrep (L := L) S).toSubmodule) (v : S)
    (w' : FinitePlace.PrimeAbove (L := L) v.1) :
    (sComponentsLinearEquiv S ((sSubrep S).toRepresentation σ x)).2.1 v w' =
      FinitePlace.semilocal (L := L) v.1 σ ((sComponentsLinearEquiv S x).2.1 v) w' := by
  let w := σ⁻¹ • w'
  have hw : σ • w = w' := by simp [w]
  rw [sComponentsLinearEquiv_inside]
  change finiteComponent L (FinitePlace.PrimeAbove.place v.1 w') (σ • x.1.toMul) =
    ((FinitePlace.semilocal (L := L) v.1) σ
      ((sComponentsLinearEquiv S x).2.1 v) w').toMul
  rw [FinitePlace.semilocal_apply_image v.1 σ w w' hw,
    sComponentsLinearEquiv_inside]
  have hplace := FinitePlace.PrimeAbove.mapEquiv_place_eq_of_smul_eq v.1 σ w w' hw
  rw [smul_def, finiteComponent_congr σ.toRingEquiv _ _ hplace]
  rfl

/-- The integral coordinates outside `S` of `sComponentsLinearEquiv` respect the Galois
action; used by `sComponentsRepEquiv`. -/
private theorem sComponentsLinearEquiv_smul_outside
    (S : Finset (HeightOneSpectrum (𝓞 K))) (σ : L ≃ₐ[K] L)
    (x : (sSubrep (L := L) S).toSubmodule)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
    (w' : FinitePlace.PrimeAbove (L := L) v.1) :
    (sComponentsLinearEquiv S ((sSubrep S).toRepresentation σ x)).2.2 v w' =
      FinitePlace.semilocalUnits (L := L) v.1 σ ((sComponentsLinearEquiv S x).2.2 v) w' := by
  apply Subtype.ext
  let w := σ⁻¹ • w'
  have hw : σ • w = w' := by simp [w]
  change (((sComponentsLinearEquiv S ((sSubrep S).toRepresentation σ x)).2.2 v w').toMul.1 :
    ((FinitePlace.PrimeAbove.place v.1 w').adicCompletion L)ˣ) =
    (((FinitePlace.semilocalUnits (L := L) v.1) σ
      ((sComponentsLinearEquiv S x).2.2 v) w').toMul.1 :
        ((FinitePlace.PrimeAbove.place v.1 w').adicCompletion L)ˣ)
  rw [sComponentsLinearEquiv_outside,
    FinitePlace.semilocalUnits_apply_image v.1 σ w w' hw,
    sComponentsLinearEquiv_outside]
  have hplace := FinitePlace.PrimeAbove.mapEquiv_place_eq_of_smul_eq v.1 σ w w' hw
  change finiteComponent L (FinitePlace.PrimeAbove.place v.1 w') (σ • x.1.toMul) =
    Units.map (FinitePlace.completionEquiv σ.toRingEquiv
      (FinitePlace.PrimeAbove.place v.1 w)
      (FinitePlace.PrimeAbove.place v.1 w') hplace)
      (finiteComponent L (FinitePlace.PrimeAbove.place v.1 w) x.1.toMul)
  rw [smul_def, finiteComponent_congr σ.toRingEquiv _ _ hplace]

/-- Grouping idèle components intertwines the Galois action and the semilocal actions.
Milne, *Class Field Theory*, Chapter VII, Proposition 2.5, product decomposition. -/
def sComponentsRepEquiv (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (sSubrep (L := L) S).toRepresentation.Equiv (sCoordinateRep (L := L) S) := by
  apply Representation.Equiv.mk (sComponentsLinearEquiv S)
  intro σ
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · funext v w'
    exact sComponentsLinearEquiv_smul_infinite S σ x v w'
  · apply Prod.ext
    · funext v w'
      exact sComponentsLinearEquiv_smul_inside S σ x v w'
    · funext v w'
      exact sComponentsLinearEquiv_smul_outside S σ x v w'

/-! ### Integral-unit factors outside `S`

For arbitrary finite `S`, ramification occurs at only finitely many outside places. The
remaining unit factors have trivial Tate groups, while every exceptional unit factor has
Herbrand quotient one. -/

/-- The integral-unit coordinates outside `S` contribute quotient one to
`herbrandQuotient_sSubrep_empty`, even when some of those places ramify. -/
private theorem herbrandQuotient_outside [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Representation.herbrandQuotient
      (Representation.pi (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
        FinitePlace.semilocalUnits (L := L) v.1)) = 1 := by
  classical
  let R := FinitePlace.ramifiedSet K L
  let E : Finset {v : HeightOneSpectrum (𝓞 K) // v ∉ S} :=
    R.subtype (fun v => v ∉ S)
  let ρOut := fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
    FinitePlace.semilocalUnits (L := L) v.1
  have hUnramified (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (hv : v ∉ E)
      (w : FinitePlace.PrimeAbove (L := L) v.1) :
      w.1.ramificationIdx (𝓞 K) = 1 := by
    apply FinitePlace.ramificationIdx_eq_one_of_notMem_ramifiedSet
      (FinitePlace.PrimeAbove.place v.1 w)
    simpa only [FinitePlace.PrimeAbove.below_place] using
      (show v.1 ∉ R by simpa [E] using hv)
  have hZero : ∀ v, v ∉ E → Subsingleton (Representation.TateZero (ρOut v)) := by
    intro v hv
    let w : FinitePlace.PrimeAbove (L := L) v.1 := Classical.choice inferInstance
    exact FinitePlace.subsingleton_tateZero_semilocalUnits v.1 w (hUnramified v hv w)
  have hNeg : ∀ v, v ∉ E → Subsingleton (Representation.TateNegOne (ρOut v)) := by
    intro v hv
    let w : FinitePlace.PrimeAbove (L := L) v.1 := Classical.choice inferInstance
    exact FinitePlace.subsingleton_tateNegOne_semilocalUnits v.1 w (hUnramified v hv w)
  rw [show Representation.herbrandQuotient (Representation.pi ρOut) =
      (∏ v ∈ E, Representation.herbrandQuotient (ρOut v)) from
    Representation.herbrandQuotient_pi_of_subsingleton_outside ρOut E hZero hNeg]
  simp [ρOut, FinitePlace.herbrandQuotient_semilocalUnits]

/-! ### Ordinary-unit idèles

For idèles that are units at every finite place, the finite integral-unit factors contribute
one, including the ramified factors. The infinite factors therefore give the complete quotient.
The empty product of finite multiplicative groups is a finite trivial representation. -/

/-- The ordinary-unit idèles $E_L$ have Herbrand quotient
$h(E_L)=\prod_{v\mid\infty}[L_w:K_v]$. Childress, *Class Field Theory* (2009), Chapter IV,
Proposition 5.7 and the observation on p. 96. This directly evaluates the unit factors. -/
theorem herbrandQuotient_sSubrep_empty [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (wi : ∀ v : NumberField.InfinitePlace K, InfinitePlace.PlaceAbove (L := L) v) :
    Representation.herbrandQuotient (sSubrep (K := K) (L := L) ∅).toRepresentation =
      ∏ v : NumberField.InfinitePlace K,
        (Module.finrank v.Completion (wi v).1.Completion : ℚ) := by
  classical
  have hFin : Representation.herbrandQuotient (Representation.pi
      (fun v : (∅ : Finset (HeightOneSpectrum (𝓞 K))) =>
        FinitePlace.semilocal (L := L) v.1)) = 1 :=
    Representation.herbrandQuotient_eq_one_of_finite _
  rw [Representation.herbrandQuotient_equiv (sComponentsRepEquiv ∅),
    Representation.herbrandQuotient_prod, Representation.herbrandQuotient_prod,
    hFin, herbrandQuotient_outside ∅, mul_one, mul_one,
    Representation.herbrandQuotient_pi]
  apply Finset.prod_congr rfl
  intro v _
  exact InfinitePlace.herbrandQuotient_semilocal v (wi v)

/-- The ordinary-unit idèles have finite Tate groups, by the nonzero product in
`herbrandQuotient_sSubrep_empty`. -/
theorem hasHerbrandQuotient_sSubrep_empty [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    Representation.HasHerbrandQuotient (sSubrep (K := K) (L := L) ∅).toRepresentation := by
  classical
  let wi : ∀ v : NumberField.InfinitePlace K, InfinitePlace.PlaceAbove (L := L) v :=
    fun _ => Classical.choice inferInstance
  rw [Representation.hasHerbrandQuotient_iff_ne_zero, herbrandQuotient_sSubrep_empty wi]
  apply ne_of_gt
  apply Finset.prod_pos
  intro v _
  exact_mod_cast Module.finrank_pos

end SIC.IdeleGroup
