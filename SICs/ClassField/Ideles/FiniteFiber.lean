/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.GroupCohomology.Shapiro
import SICs.ClassField.Local.Unramified

/-!
# Semilocal multiplicative modules at finite places

The semilocal products of multiplicative completion groups and integral-unit groups above a
finite place, with their Galois actions; the Tate groups of the integral-unit product reduce to
one local fiber.

This follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, Propositions 2.2–2.3.
The completion maps supply the transports of `Representation.PermutedFamily`, and they preserve
integral units. The Galois group acts transitively on places above the base place, so the section
representation of integral units is coinduced from the stabilizer of any one place. Shapiro's
lemma and the decomposition-group isomorphism then identify its Tate groups with local Tate
groups. The Herbrand quotient of the integral-unit product is therefore one, and at an
unramified place both of its Tate groups vanish. These unit formulas supply the outside factors
in the S-idèle cohomology calculation.
-/
noncomputable section
open IsDedekindDomain NumberField
open scoped NumberField NumberField.LiesOver SIC.FinitePlace SIC.InfinitePlace
namespace SIC.FinitePlace
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

/-! ### Multiplicative completion transports

The algebra transports of `completionFamily` act on units and give the semilocal representation.
-/

/-- Completion transport on the multiplicative groups above `v`. -/
def semilocalFamily : Representation.PermutedFamily ℤ (L ≃ₐ[K] L) (PrimeAbove (L := L) v)
    (fun w => Additive ((PrimeAbove.place v w).adicCompletion L)ˣ) :=
  (completionFamily (L := L) v).toPermutedFamily

/-- The family transport is the completion map on units. -/
theorem semilocalFamily_map (σ : L ≃ₐ[K] L) (w w' : PrimeAbove (L := L) v)
    (h : σ • w = w') (x : Additive ((PrimeAbove.place v w).adicCompletion L)ˣ) :
    ((semilocalFamily (L := L) v).map σ w w' h x).toMul =
      Units.map (completionEquiv σ.toRingEquiv (PrimeAbove.place v w)
        (PrimeAbove.place v w')
        (PrimeAbove.mapEquiv_place_eq_of_smul_eq v σ w w' h))
        x.toMul := rfl
/-- The semilocal multiplicative representation $\prod_{w \mid v} L_w^\times$.
Milne, *Class Field Theory*, Chapter VII, Lemma 2.1. -/
abbrev semilocal := (semilocalFamily (L := L) v).sections

/-- The action on a semilocal component at a transported place. -/
theorem semilocal_apply_image (σ : L ≃ₐ[K] L) (w w' : PrimeAbove (L := L) v)
    (h : σ • w = w') (x : ∀ j : PrimeAbove (L := L) v,
      Additive ((PrimeAbove.place v j).adicCompletion L)ˣ) :
    ((semilocal (L := L) v) σ x w').toMul =
      Units.map (completionEquiv σ.toRingEquiv (PrimeAbove.place v w)
        (PrimeAbove.place v w')
        (PrimeAbove.mapEquiv_place_eq_of_smul_eq v σ w w' h))
        (x w).toMul := by
  rw [(semilocalFamily (L := L) v).sections_apply_image σ w w' h x]
  exact semilocalFamily_map v σ w w' h (x w)

/-! ### Integral units in the completion transports

Completion transport preserves valuation and hence restricts to integral units.
The generic subgroup-family construction supplies coherent transports. Transitivity identifies
the product with a coinduced module, Shapiro's lemma reduces its Tate groups to one fiber, and
the decomposition-group equivalence identifies that fiber with the local unit representation. -/

/-- Completion transport restricts to the integral units above `v`. -/
def semilocalUnitFamily :
    Representation.PermutedFamily ℤ (L ≃ₐ[K] L) (PrimeAbove (L := L) v)
      (fun w => Additive (unitGroup (PrimeAbove.place v w))) :=
  (completionFamily (L := L) v).toPermutedFamilyOfSubgroup
    (fun w => unitGroup (PrimeAbove.place v w)) (by
      intro σ w w' h x
      rw [mem_unitGroup_iff_valued, mem_unitGroup_iff_valued]
      change Valued.v (x : (PrimeAbove.place v w).adicCompletion L) = 1 ↔
        Valued.v (completionEquiv σ.toRingEquiv (PrimeAbove.place v w)
          (PrimeAbove.place v w')
          (PrimeAbove.mapEquiv_place_eq_of_smul_eq v σ w w' h)
          (x : (PrimeAbove.place v w).adicCompletion L)) = 1
      rw [valued_completionEquiv])

/-- The family transport on integral units is the restriction of completion transport. -/
theorem semilocalUnitFamily_map (σ : L ≃ₐ[K] L)
    (w w' : PrimeAbove (L := L) v) (h : σ • w = w')
    (x : Additive (unitGroup (PrimeAbove.place v w))) :
    (((semilocalUnitFamily (L := L) v).map σ w w' h x).toMul.1 :
      ((PrimeAbove.place v w').adicCompletion L)ˣ) =
      Units.map (completionEquiv σ.toRingEquiv (PrimeAbove.place v w)
        (PrimeAbove.place v w')
        (PrimeAbove.mapEquiv_place_eq_of_smul_eq v σ w w' h)) x.toMul.1 := rfl
/-- The semilocal integral-unit representation $\prod_{w \mid v} U_w$. -/
abbrev semilocalUnits := (semilocalUnitFamily (L := L) v).sections

/-- The action on an integral-unit component at a transported place. -/
theorem semilocalUnits_apply_image (σ : L ≃ₐ[K] L)
    (w w' : PrimeAbove (L := L) v) (h : σ • w = w')
    (x : ∀ j : PrimeAbove (L := L) v, Additive (unitGroup (PrimeAbove.place v j))) :
    (((semilocalUnits (L := L) v) σ x w').toMul.1 :
      ((PrimeAbove.place v w').adicCompletion L)ˣ) =
      Units.map (completionEquiv σ.toRingEquiv (PrimeAbove.place v w)
        (PrimeAbove.place v w')
        (PrimeAbove.mapEquiv_place_eq_of_smul_eq v σ w w' h)) (x w).toMul.1 := by
  rw [(semilocalUnitFamily (L := L) v).sections_apply_image σ w w' h x]
  exact semilocalUnitFamily_map v σ w w' h (x w)

/-- The integral-unit fiber is the local unit subrepresentation after reindexing. -/
private theorem semilocalUnitFiber_eq_comp [IsGalois K L]
    (w : PrimeAbove (L := L) v) :
    (semilocalUnitFamily (L := L) v).fiber w =
      (unitGroupSubrep v (PrimeAbove.place v w)).toRepresentation.comp
        (PrimeAbove.decompositionEquiv v w).toMonoidHom := by
  ext σ x
  rfl

/-- The semilocal integral-unit Tate group in degree zero is its local counterpart.
Milne, *Class Field Theory*, Chapter VII, Proposition 2.3, integral-unit clause. -/
def tateZeroSemilocalUnitsEquiv [IsGalois K L] (w : PrimeAbove (L := L) v) :
    Representation.TateZero (semilocalUnits (L := L) v) ≃ₗ[ℤ]
      Representation.TateZero (unitGroupSubrep v (PrimeAbove.place v w)).toRepresentation := by
  exact (semilocalUnitFamily (L := L) v).tateZeroEquivOfFiber w
    (PrimeAbove.exists_smul_eq v w) _ (PrimeAbove.decompositionEquiv v w)
    (semilocalUnitFiber_eq_comp v w)
/-- The semilocal integral-unit Tate group in degree minus one is its local counterpart.
Milne, *Class Field Theory*, Chapter VII, Proposition 2.3, integral-unit clause. -/
def tateNegOneSemilocalUnitsEquiv [IsGalois K L] (w : PrimeAbove (L := L) v) :
    Representation.TateNegOne (semilocalUnits (L := L) v) ≃ₗ[ℤ]
      Representation.TateNegOne (unitGroupSubrep v (PrimeAbove.place v w)).toRepresentation := by
  exact (semilocalUnitFamily (L := L) v).tateNegOneEquivOfFiber w
    (PrimeAbove.exists_smul_eq v w) _ (PrimeAbove.decompositionEquiv v w)
    (semilocalUnitFiber_eq_comp v w)
/-- The Herbrand quotient of semilocal integral units is one.
Milne, *Class Field Theory*, Chapter VII, Proposition 2.7, integral-unit factors. -/
theorem herbrandQuotient_semilocalUnits [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    Representation.herbrandQuotient (semilocalUnits (L := L) v) = 1 := by
  let w : PrimeAbove (L := L) v := Classical.choice inferInstance
  rw [(semilocalUnitFamily (L := L) v).herbrandQuotient_sections w
    (PrimeAbove.exists_smul_eq v w) _ (PrimeAbove.decompositionEquiv v w)
    (semilocalUnitFiber_eq_comp v w)]
  exact herbrandQuotient_unitGroupSubrep v (PrimeAbove.place v w)
/-- Unramified semilocal integral units have trivial degree-zero Tate group.
Milne, *Class Field Theory*, Chapter VII, Proposition 2.5, using Chapter III, Proposition 1.1. -/
theorem subsingleton_tateZero_semilocalUnits [IsGalois K L]
    (w : PrimeAbove (L := L) v) (h : w.1.ramificationIdx (𝓞 K) = 1) :
    Subsingleton (Representation.TateZero (semilocalUnits (L := L) v)) := by
  have hlocal := subsingleton_tateZero_unitGroupSubrep v (PrimeAbove.place v w) h
  let e := tateZeroSemilocalUnitsEquiv v w
  exact e.toEquiv.subsingleton_congr.mpr hlocal
/-- Unramified semilocal integral units have trivial degree-minus-one Tate group.
Milne, *Class Field Theory*, Chapter VII, Proposition 2.5, using Chapter III, Proposition 1.1. -/
theorem subsingleton_tateNegOne_semilocalUnits [IsGalois K L]
    (w : PrimeAbove (L := L) v) (h : w.1.ramificationIdx (𝓞 K) = 1) :
    Subsingleton (Representation.TateNegOne (semilocalUnits (L := L) v)) := by
  have hlocal := subsingleton_tateNegOne_unitGroupSubrep v (PrimeAbove.place v w) h
  let e := tateNegOneSemilocalUnitsEquiv v w
  exact e.toEquiv.subsingleton_congr.mpr hlocal
end SIC.FinitePlace
