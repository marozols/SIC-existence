/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Galois extensions of an embedded number field inside `ℂ`

For a number field `H` embedded in `ℂ` by `ψ` and an algebraic number `z ∈ ℂ`, a finite Galois
extension `L/H` with an embedding `ι : L → ℂ` extending `ψ` whose image contains `z`.

This module supplies the field in which the reciprocity argument of
`SICs.Dilogarithm.Reciprocity.RayField` applies Frobenius elements to a complex value of the
finite quantum dilogarithm, the extension `F/H` of the proof of [RW26b, Radchenko, Wheeler
(2026b), Section 8, Proposition 4].

## The argument

Make `ℂ` an `H`-algebra through `ψ`. The number `z` is algebraic over `ℚ`, hence over `H`; let
`f` be its minimal polynomial over `H`. It splits in the algebraically closed `ℂ`, so the field
`L = H(roots of f) ⊆ ℂ` is a splitting field of `f` over `H`: finite and normal, and separable in
characteristic zero, hence Galois. It is finite over `ℚ` since `H` is, so it is a number field;
its inclusion in `ℂ` extends `ψ` and contains the root `z`.
-/

noncomputable section

namespace SIC

/-- **A finite Galois extension of an embedded number field containing a given algebraic
number**: for `ψ : H → ℂ` and `z ∈ ℂ` algebraic over `ℚ`, a number field `L` with `L/H` Galois and
an embedding `ι : L → ℂ` with `ι ∘ (H → L) = ψ` and `z ∈ ι(L)`. -/
theorem exists_isGalois_ringHom_complex {H : Type*} [Field H] [NumberField H] (ψ : H →+* ℂ)
    {z : ℂ} (hz : IsAlgebraic ℚ z) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra H L) (_ : IsGalois H L)
      (ι : L →+* ℂ), ι.comp (algebraMap H L) = ψ ∧ z ∈ ι.range := by
  let : Algebra H ℂ := ψ.toAlgebra
  have : IsScalarTower ℚ H ℂ := IsScalarTower.of_algebraMap_eq fun x => by
    exact congrArg (fun f : ℚ →+* ℂ => f x)
      (RingHom.ext_rat (algebraMap ℚ ℂ) ((algebraMap H ℂ).comp (algebraMap ℚ H)))
  have hzH : IsAlgebraic H z := hz.tower_top H
  let f : Polynomial H := minpoly H z
  let L : IntermediateField H ℂ := IntermediateField.adjoin H (f.rootSet ℂ)
  have : f.IsSplittingField H L :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : FiniteDimensional H L := Polynomial.IsSplittingField.finiteDimensional L f
  have : NumberField L := NumberField.of_module_finite H L
  have : IsGalois H L :=
    IsGalois.of_separable_splitting_field (minpoly.irreducible hzH.isIntegral).separable
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, L.val.toRingHom, ?_, ?_⟩
  · apply RingHom.ext
    intro x
    rfl
  · have hzroot : z ∈ f.rootSet ℂ := by
      apply Polynomial.mem_rootSet.mpr
      exact ⟨minpoly.ne_zero hzH.isIntegral, minpoly.aeval H z⟩
    exact ⟨⟨z, IntermediateField.subset_adjoin H (f.rootSet ℂ) hzroot⟩, rfl⟩

end SIC

end
