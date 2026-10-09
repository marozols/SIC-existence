/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Intertwining

/-!
# Representations: inclusions, images, products, and integral restriction

General constructions on representations of a group: the inclusion of a subrepresentation, the
range restriction of an intertwining map, products of representations, and restriction of scalars
to the integers.

## The argument

A stable submodule inherits the group action, and its subtype map intertwines the two actions.
An intertwining map factors through its invariant image. Restricting each action to integers or
acting coordinatewise on a family supplies the other constructions used by Tate cohomology.
-/

namespace SIC.Representation

/-! ### Subrepresentations

Stable submodules embed equivariantly into their ambient representation and one another. -/

section Subrepresentations

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  {ρ : _root_.Representation k G V}

/-- The inclusion $W \hookrightarrow V$ of a subrepresentation, as an intertwining map. -/
def Subrepresentation.subtype (W : _root_.Subrepresentation ρ) :
    W.toRepresentation.IntertwiningMap ρ where
  toLinearMap := W.toSubmodule.subtype
  isIntertwining' := by intro g; ext x; rfl

/-- The inclusion of a subrepresentation is the inclusion of its vectors. -/
@[simp]
theorem Subrepresentation.subtype_apply (W : _root_.Subrepresentation ρ) (x : W.toSubmodule) :
    Subrepresentation.subtype W x = x := rfl

/-- The inclusion of a subrepresentation is injective. -/
theorem Subrepresentation.subtype_injective (W : _root_.Subrepresentation ρ) :
    Function.Injective (Subrepresentation.subtype W) := Subtype.val_injective

/-- The inclusion $W \hookrightarrow W'$ of a subrepresentation in a larger one, as an
intertwining map. -/
def Subrepresentation.inclusion {W W' : _root_.Subrepresentation ρ} (h : W ≤ W') :
    W.toRepresentation.IntertwiningMap W'.toRepresentation where
  toLinearMap := Submodule.inclusion h
  isIntertwining' := by intro g; ext x; rfl

/-- The inclusion of one subrepresentation in another is injective. -/
theorem Subrepresentation.inclusion_injective {W W' : _root_.Subrepresentation ρ} (h : W ≤ W') :
    Function.Injective (Subrepresentation.inclusion h) := Submodule.inclusion_injective h

end Subrepresentations

/-! ### Images of intertwining maps

The range restriction factors an intertwining map through its stable image. -/

section RangeRestriction

variable {k G V W U : Type*} [CommRing k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]
  {ρ : _root_.Representation k G V} {σ : _root_.Representation k G W}
  {τ : _root_.Representation k G U} (f : ρ.IntertwiningMap σ)

namespace IntertwiningMap

/-- The equivariant surjection onto the image of `f`, used in the finite-kernel comparisons. -/
def rangeRestrict : ρ.IntertwiningMap f.range.toRepresentation where
  toLinearMap := f.toLinearMap.rangeRestrict
  isIntertwining' := by
    intro γ
    ext x
    exact _root_.Representation.IntertwiningMap.isIntertwining ρ σ f γ x

/-- Every image vector comes from the source under the equivariant range restriction. -/
theorem rangeRestrict_surjective : Function.Surjective (rangeRestrict f) :=
  f.toLinearMap.surjective_rangeRestrict

/-- Restricting the second map of an exact pair to its image preserves exactness. -/
theorem exact_rangeRestrict_iff (g : σ.IntertwiningMap τ) :
    Function.Exact f (rangeRestrict g) ↔ Function.Exact f g :=
  (g.range.toSubmodule.subtype_injective.comp_exact_iff_exact).symm

end IntertwiningMap

end RangeRestriction

/-! ### Restriction to the integers

The underlying group action does not change when a representation is restricted to integers. -/

/-- The integer restriction of a representation over a ring. -/
def integral {R G V : Type*} [Ring R] [Group G] [AddCommGroup V] [Module R V]
    (ρ : _root_.Representation R G V) : _root_.Representation ℤ G V where
  toFun g := (ρ g).restrictScalars ℤ
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/-- Integer restriction does not change the action on vectors. -/
@[simp] theorem integral_apply {R G V : Type*} [Ring R] [Group G]
    [AddCommGroup V] [Module R V] (ρ : _root_.Representation R G V) (g : G) (v : V) :
    integral ρ g v = ρ g v := rfl

/-! ### Product representations

Each group element acts on a family of modules coordinatewise. -/

section Products

variable {k G ι : Type*} [CommRing k] [Group G]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

/-- The componentwise representation on a product of modules. -/
def pi (ρ : ∀ i, _root_.Representation k G (V i)) :
    _root_.Representation k G (∀ i, V i) where
  toFun g := LinearMap.piMap fun i => ρ i g
  map_one' := by ext x i; simp
  map_mul' g h := by ext x i; simp

/-- The product action is componentwise. -/
@[simp] theorem pi_apply (ρ : ∀ i, _root_.Representation k G (V i))
    (g : G) (x : ∀ i, V i) (i : ι) : (pi ρ g x) i = ρ i g (x i) := rfl

end Products

end SIC.Representation
