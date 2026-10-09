/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.GroupCohomology.Shapiro
import SICs.ClassField.Local.NormIndex

/-!
# Semilocal multiplicative modules at infinite places

The product of multiplicative completion groups above an infinite place, with its Galois action;
its Herbrand quotient is the local degree.

This follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, Propositions 2.2–2.3.
The algebra transports of `completionFamily` induce the units representation. The Galois group
acts transitively on places above the base place, so its section representation is coinduced
from the stabilizer of any one place. Shapiro's lemma and the decomposition-group isomorphism
then identify its Tate groups with local Tate groups. The local norm-index calculation gives
the semilocal Herbrand quotient used in Proposition 2.7.
-/
noncomputable section
open IsDedekindDomain NumberField
open scoped NumberField NumberField.LiesOver SIC.FinitePlace SIC.InfinitePlace
namespace SIC.InfinitePlace
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (v : NumberField.InfinitePlace K)

/-! ### Completion transports and the semilocal action

The algebra transports of `completionFamily` act on units and give the semilocal representation.
-/

/-- Completion transport on the multiplicative groups above `v`. -/
def semilocalFamily : Representation.PermutedFamily ℤ (L ≃ₐ[K] L) (PlaceAbove (L := L) v)
    (fun w => Additive w.1.Completionˣ) :=
  (completionFamily (L := L) v).toPermutedFamily

omit [NumberField K] [NumberField L] in
/-- Transport in `semilocalFamily` is induced by completion transport on units. -/
theorem semilocalFamily_map (σ : L ≃ₐ[K] L) (w w' : PlaceAbove (L := L) v)
    (h : σ • w = w') (x : Additive w.1.Completionˣ) :
    (semilocalFamily (L := L) v).map σ w w' h x =
      Additive.ofMul (Units.map (completionEquiv σ.toRingEquiv w.1 w'.1
        (PlaceAbove.mapEquiv_coe_eq_of_smul_eq v σ w w' h)).toMonoidHom x.toMul) :=
  rfl
/-- The semilocal multiplicative representation $\prod_{w \mid v} L_w^\times$.
Milne, *Class Field Theory*, Chapter VII, Lemma 2.1. -/
abbrev semilocal := (semilocalFamily (L := L) v).sections

omit [NumberField K] [NumberField L] in
/-- The action on the component at a transported place is completion transport. -/
theorem semilocal_apply_image (σ : L ≃ₐ[K] L) (w w' : PlaceAbove (L := L) v)
    (h : σ • w = w') (x : ∀ u : PlaceAbove (L := L) v, Additive u.1.Completionˣ) :
    semilocal (L := L) v σ x w' =
      (semilocalFamily (L := L) v).map σ w w' h (x w) :=
  (semilocalFamily (L := L) v).sections_apply_image σ w w' h x

/-! ### Local Herbrand calculation

The stabilizer of a place above `v` is its decomposition group. Reindexing by its isomorphism
with the local Galois group identifies the fiber action; Shapiro then carries the Herbrand
quotient to that of one completion, which the local norm index computes. -/

/-- The semilocal Herbrand quotient is the local degree.
Milne, *Class Field Theory*, Chapter VII, Proposition 2.7, local factors. -/
theorem herbrandQuotient_semilocal [IsGalois K L]
    (w : PlaceAbove (L := L) v) :
    Representation.herbrandQuotient (semilocal (L := L) v) =
      Module.finrank v.Completion w.1.Completion := by
  rw [(semilocalFamily (L := L) v).herbrandQuotient_sections w
    (PlaceAbove.exists_smul_eq v w) _ (PlaceAbove.decompositionEquiv v w)
    ((completionFamily (L := L) v).toPermutedFamily_fiber
      (PlaceAbove.exists_smul_eq v) (sum_finrank_placeAbove v) w)]
  exact herbrandQuotient_units_completion v w.1

end SIC.InfinitePlace
