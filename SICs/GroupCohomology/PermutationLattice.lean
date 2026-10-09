/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.GroupCohomology.Permutation
import SICs.GroupCohomology.RealLattices
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# The standard lattice in a real permutation representation

For a finite group set, integer-valued functions form a stable full lattice in its real
permutation representation.

This module follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII,
Proposition 3.1, in its construction of the first lattice $N=\operatorname{Hom}(T,\mathbb Z)$,
and Lemma 3.5 in comparing it with other stable full real lattices.

## The argument

Coordinatewise inclusion sends an integer-valued function to the same real-valued function and
commutes with the permutation action. Its range is the integral span of the standard coordinate
basis. The standard basis theorem makes that span discrete and full over $\mathbb R$. The range
equivalence identifies its Herbrand quotient with that of the integer permutation representation;
the general real-lattice comparison then applies to every other stable full lattice in the same
representation.
-/

noncomputable section

namespace SIC.Representation

variable {G X : Type*} [Group G] [MulAction G X]

/-! ### Coordinate inclusion and its range

The integral representation on real-valued functions uses the same permutation action as the
integer-valued one. Its stable range is Milne's first lattice.
-/

/-- Coordinatewise inclusion of $\operatorname{Hom}(X,\mathbb Z)$ into
$\operatorname{Hom}(X,\mathbb R)$, equivariant for $(g f)(x)=f(g^{-1}x)$. -/
def permutationIntToReal :
    (permutation (k := ℤ) (G := G) (X := X)).IntertwiningMap
      (integral (permutation (k := ℝ) (G := G) (X := X))) where
  toLinearMap := {
    toFun := fun f x => (f x : ℝ)
    map_add' := by intro f h; ext x; simp
    map_smul' := by intro z f; ext x; simp }
  isIntertwining' g := by
    ext f x
    simp [permutation_apply]

/-- Coordinatewise inclusion is injective; used by `permutationLatticeEquiv`. -/
theorem permutationIntToReal_injective :
    Function.Injective (permutationIntToReal (G := G) (X := X)) := by
  intro f h he
  funext x
  exact Int.cast_injective (congrFun he x)

/-- The standard integer-coordinate lattice inside the real permutation representation.
Milne, *Class Field Theory*, Chapter VII, Proposition 3.1, first lattice. -/
def permutationLattice :
    Subrepresentation (integral (permutation (k := ℝ) (G := G) (X := X))) :=
  (permutationIntToReal (G := G) (X := X)).range

/-- Membership in `permutationLattice` means that every real coordinate is an integer cast. -/
theorem mem_permutationLattice (v : X → ℝ) :
    v ∈ permutationLattice (G := G) (X := X) ↔
      ∃ f : X → ℤ, ∀ x, (f x : ℝ) = v x := by
  simp only [permutationLattice, _root_.Representation.IntertwiningMap.mem_range]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f, fun x => rfl⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, funext fun x => hf x⟩

/-- The range equivalence identifies integer functions with `permutationLattice` as
representations; used by the Herbrand comparison. -/
def permutationLatticeEquiv :
    (permutation (k := ℤ) (G := G) (X := X)).Equiv
      (permutationLattice (G := G) (X := X)).toRepresentation := by
  let f := permutationIntToReal (G := G) (X := X)
  let e : (X → ℤ) ≃ₗ[ℤ] f.toLinearMap.range :=
    LinearEquiv.ofInjective f.toLinearMap permutationIntToReal_injective
  refine _root_.Representation.Equiv.mk e ?_
  intro g
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change f ((permutation (k := ℤ) (G := G) (X := X)) g v) =
    (integral (permutation (k := ℝ) (G := G) (X := X))) g (f v)
  exact _root_.Representation.IntertwiningMap.isIntertwining _ _ f g v

section Finite

variable [Finite X]

/-- The standard lattice is the $\mathbb Z$-span of the coordinate basis; used to transfer
the lattice instances from `ZSpan`. -/
theorem permutationLattice_toSubmodule :
    (permutationLattice (G := G) (X := X)).toSubmodule =
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ X)) := by
  classical
  cases nonempty_fintype X
  apply le_antisymm
  · intro v hv
    obtain ⟨f, hf⟩ := (mem_permutationLattice (G := G) v).mp hv
    apply ((Pi.basisFun ℝ X).mem_span_iff_repr_mem ℤ v).mpr
    intro x
    exact ⟨f x, by simpa [Pi.basisFun_repr] using hf x⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨x, rfl⟩
    apply (mem_permutationLattice (G := G) _).mpr
    refine ⟨Pi.basisFun ℤ X x, ?_⟩
    intro y
    simp [Pi.basisFun_apply, Pi.single_apply]

/-! ### Full real lattice and Herbrand comparison

The coordinate basis gives the topological lattice structure. Milne's Lemma 3.5 compares any
other stable full lattice with this one, and the range equivalence returns to integer functions.
-/

/-- The standard coordinate lattice is discrete, by `ZSpan.discreteTopology_pi_basisFun`. -/
instance permutationLattice_discreteTopology :
    DiscreteTopology (permutationLattice (G := G) (X := X)).toSubmodule := by
  rw [permutationLattice_toSubmodule]
  exact ZSpan.discreteTopology_pi_basisFun

end Finite

variable [Fintype X]

/-- The standard coordinate lattice spans all real functions; this is the `ZSpan` lattice
instance for `Pi.basisFun`. -/
instance permutationLattice_isZLattice :
    IsZLattice ℝ (permutationLattice (G := G) (X := X)).toSubmodule := by
  refine ⟨?_⟩
  rw [permutationLattice_toSubmodule]
  exact ZSpan.span_top (Pi.basisFun ℝ X)

/-- For a stable full real lattice $M$, $h(M)=h(\operatorname{Hom}(X,\mathbb Z))$.
This specializes Milne, *Class Field Theory*, Chapter VII, Lemma 3.5, using the first lattice
of Proposition 3.1. -/
theorem herbrandQuotient_eq_permutation_of_isZLattice [Fintype G] [IsCyclic G]
    (M : Subrepresentation (integral (permutation (k := ℝ) (G := G) (X := X))))
    [DiscreteTopology M.toSubmodule] [IsZLattice ℝ M.toSubmodule] :
    herbrandQuotient M.toRepresentation =
      herbrandQuotient (permutation (k := ℤ) (G := G) (X := X)) := by
  calc
    _ = herbrandQuotient (permutationLattice (G := G) (X := X)).toRepresentation :=
      herbrandQuotient_eq_of_real_lattices
        (permutation (k := ℝ) (G := G) (X := X)) M permutationLattice
    _ = _ := (herbrandQuotient_equiv
      (permutationLatticeEquiv (G := G) (X := X))).symm

end SIC.Representation
