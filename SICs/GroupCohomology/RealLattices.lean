/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.GroupCohomology.RationalLattices
import SICs.RepresentationTheory.IsomorphismDescent
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Herbrand quotients of stable real lattices

Two stable full lattices in the same finite-dimensional real representation have equal Herbrand
Herbrand quotients; their definedness conditions are equivalent.

This module follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, Lemma 3.5.

## The argument

An integral basis of each lattice extends to a real basis. Its rational span is a finite-dimensional
rational representation, and the inclusion of that span into the real space is a scalar extension.
Milne's Lemma 3.2 therefore gives an equivariant rational equivalence between the two rational
spans. The original lattices embed as full integral lattices in those spans, so the rational-lattice
comparison from Lemma 3.4 gives both definedness and equality of Herbrand quotients.
-/

noncomputable section
namespace SIC.Representation

/-! ### Rational spans of full real lattices

The rational span is presented through an extended integral basis, which makes its inclusion into
the real representation a base change. It is then identified with the span of the lattice itself.
-/

variable {G V : Type*} [Group G]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The standard rational scalar action on a real vector space; used by `rationalSpan`. -/
local instance : Module ℚ V := Module.compHom V (algebraMap ℚ ℝ)

/-- An integral basis of the full lattice extends to a real basis; used by `rationalSpan` and
`rationalSpan_eq`. -/
private def latticeRealBasis (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ L) ℝ V := by
  letI : Module.Free ℤ L := ZLattice.module_free ℝ L
  exact (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L

/-- The rational span of a full real lattice, presented by its integral basis; used by
`rationalRepresentation`. -/
private def rationalSpan (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    Submodule ℚ V := Submodule.span ℚ (Set.range (latticeRealBasis L))

/-- The extended integral basis is a rational basis of `rationalSpan`; used by
`rationalSpan_baseChange`, `rationalLattice_full`, and `rationalSpan_finite`. -/
private def rationalBasis (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ L) ℚ (rationalSpan L) :=
  (latticeRealBasis L).restrictScalars ℚ

/-- The lattice lies in its rational span; used by `rationalLattice_equiv`. -/
private theorem lattice_le_rationalSpan (L : Submodule ℤ V)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    L ≤ (rationalSpan L).restrictScalars ℤ := by
  have hL : Submodule.span ℤ (Set.range (latticeRealBasis L)) = L :=
    (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ
  calc
    L = Submodule.span ℤ (Set.range (latticeRealBasis L)) := hL.symm
    _ ≤ (rationalSpan L).restrictScalars ℤ := Submodule.span_le_restrictScalars ℤ ℚ _

/-- The inclusion of a lattice's rational span into the real space is a scalar extension;
used by `rational_equiv`. -/
private theorem rationalSpan_baseChange (L : Submodule ℤ V)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    IsBaseChange ℝ (rationalSpan L).subtype := by
  let bR := latticeRealBasis L
  let bQ := rationalBasis L
  have he : IsBaseChange ℝ (Finsupp.linearCombination ℚ bR) :=
    IsBaseChange.of_basis ℚ bR
  let e : (Module.Free.ChooseBasisIndex ℤ L →₀ ℚ) ≃ₗ[ℚ] rationalSpan L := bQ.repr.symm
  have hcomm : (rationalSpan L).subtype.comp e.toLinearMap =
      Finsupp.linearCombination ℚ bR := by
    ext i
    change ((rationalSpan L).subtype) (bQ.repr.symm (Finsupp.single i 1)) =
      (Finsupp.linearCombination ℚ bR) (Finsupp.single i 1)
    simp only [bQ.repr_symm_single, one_smul, Finsupp.linearCombination_single]
    change ((bR.restrictScalars ℚ i : Submodule.span ℚ (Set.range bR)) : V) = bR i
    exact bR.restrictScalars_apply ℚ i
  exact (IsBaseChange.iff_of_equiv_comm e (LinearEquiv.refl ℝ V) hcomm).mp he

/-- The basis presentation of `rationalSpan` equals the rational span of the lattice;
used by `rationalRepresentation`. -/
private theorem rationalSpan_eq (L : Submodule ℤ V)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    rationalSpan L = Submodule.span ℚ (L : Set V) := by
  have hL : Submodule.span ℤ (Set.range (latticeRealBasis L)) = L :=
    (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ
  calc
    rationalSpan L = Submodule.span ℚ (Set.range (latticeRealBasis L)) := rfl
    _ = Submodule.span ℚ (Submodule.span ℤ (Set.range (latticeRealBasis L)) : Set V) :=
      (Submodule.span_span_of_tower ℤ ℚ _).symm
    _ = Submodule.span ℚ (L : Set V) := congrArg (fun P : Submodule ℤ V =>
      Submodule.span ℚ (P : Set V)) hL

/-- The rational span with the restricted $G$-action; used by `rationalLattice` and
`rational_equiv`. -/
private def rationalRepresentation (ρ : _root_.Representation ℝ G V)
    (M : Subrepresentation (integral ρ))
    [DiscreteTopology M.toSubmodule] [IsZLattice ℝ M.toSubmodule] :
    _root_.Representation ℚ G (rationalSpan M.toSubmodule) where
  toFun g := ((ρ g).restrictScalars ℚ).restrict (by
    intro x hx
    rw [rationalSpan_eq] at hx ⊢
    have hle : Submodule.span ℚ (M : Set V) ≤
        (Submodule.span ℚ (M : Set V)).comap ((ρ g).restrictScalars ℚ) :=
      Submodule.span_le.mpr (by
        intro y hy
        exact Submodule.subset_span (M.apply_mem_toSubmodule g hy))
    exact hle hx)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/-- The original stable lattice inside its rational representation; used by the real-lattice
comparison theorems. -/
private def rationalLattice (ρ : _root_.Representation ℝ G V)
    (M : Subrepresentation (integral ρ))
    [DiscreteTopology M.toSubmodule] [IsZLattice ℝ M.toSubmodule] :
    Subrepresentation (integral (rationalRepresentation ρ M)) where
  toSubmodule := M.toSubmodule.comap ((rationalSpan M.toSubmodule).subtype.restrictScalars ℤ)
  apply_mem_toSubmodule g := by
    intro x hx
    exact M.apply_mem_toSubmodule g hx

/-- The integral representation on `rationalLattice` is equivalent to the original one;
used by the real-lattice comparison theorems. -/
private def rationalLattice_equiv (ρ : _root_.Representation ℝ G V)
    (M : Subrepresentation (integral ρ))
    [DiscreteTopology M.toSubmodule] [IsZLattice ℝ M.toSubmodule] :
    (rationalLattice ρ M).toRepresentation.Equiv M.toRepresentation := by
  let E : (rationalLattice ρ M).toSubmodule ≃ₗ[ℤ] M.toSubmodule :=
    Submodule.comapSubtypeEquivOfLe (lattice_le_rationalSpan M.toSubmodule)
  apply _root_.Representation.Equiv.mk E
  intro g
  ext x
  rfl

/-- A full real lattice remains finitely generated in its rational span; used by the
real-lattice comparison theorems. -/
private theorem rationalLattice_fg (ρ : _root_.Representation ℝ G V)
    (M : Subrepresentation (integral ρ))
    [DiscreteTopology M.toSubmodule] [IsZLattice ℝ M.toSubmodule] :
    (rationalLattice ρ M).toSubmodule.FG := by
  let _ : Module.Finite ℤ M.toSubmodule := ZLattice.module_finite ℝ M.toSubmodule
  have : Module.Finite ℤ (rationalLattice ρ M).toSubmodule :=
    Module.Finite.equiv (rationalLattice_equiv ρ M).toLinearEquiv.symm
  exact (Submodule.fg_top _).mp Module.Finite.fg_top

/-- The original lattice spans its rational representation; used by the real-lattice
comparison theorems. -/
private theorem rationalLattice_full (ρ : _root_.Representation ℝ G V)
    (M : Subrepresentation (integral ρ))
    [DiscreteTopology M.toSubmodule] [IsZLattice ℝ M.toSubmodule] :
    Submodule.span ℚ (rationalLattice ρ M : Set (rationalSpan M.toSubmodule)) = ⊤ := by
  let bQ := rationalBasis M.toSubmodule
  apply top_unique
  rw [← bQ.span_eq]
  apply Submodule.span_mono
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  change (bQ i : V) ∈ M.toSubmodule
  change ((latticeRealBasis M.toSubmodule).restrictScalars ℚ i : V) ∈ M.toSubmodule
  rw [Module.Basis.restrictScalars_apply]
  change (((Module.Free.chooseBasis ℤ M.toSubmodule).ofZLatticeBasis ℝ M.toSubmodule) i) ∈
    M.toSubmodule
  rw [Module.Basis.ofZLatticeBasis_apply]
  exact (Module.Free.chooseBasis ℤ M.toSubmodule i).property

/-- The rational span of a full real lattice is finite-dimensional; used by `rational_equiv`. -/
private theorem rationalSpan_finite (L : Submodule ℤ V)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    FiniteDimensional ℚ (rationalSpan L) := by
  let _ : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let _ : Finite (Module.Free.ChooseBasisIndex ℤ L) :=
    Module.Finite.finite_basis (Module.Free.chooseBasis ℤ L)
  exact (rationalBasis L).finiteDimensional_of_finite

/-! ### Comparison through scalar descent

Both rational spans become the given real representation after scalar extension. Descent supplies
the rational equivalence used by the integral comparison theorem.
-/

/-- Stable full lattices in one real representation have isomorphic rational representations;
Milne, *Class Field Theory*, Chapter VII, Lemma 3.5, using Lemma 3.2. Used by the two
real-lattice comparison theorems. -/
private theorem rational_equiv [Finite G] (ρ : _root_.Representation ℝ G V)
    (M N : Subrepresentation (integral ρ))
    [DiscreteTopology M.toSubmodule] [IsZLattice ℝ M.toSubmodule]
    [DiscreteTopology N.toSubmodule] [IsZLattice ℝ N.toSubmodule] :
    Nonempty ((rationalRepresentation ρ M).Equiv (rationalRepresentation ρ N)) := by
  let _ : FiniteDimensional ℚ (rationalSpan M.toSubmodule) :=
    rationalSpan_finite M.toSubmodule
  let _ : FiniteDimensional ℚ (rationalSpan N.toSubmodule) :=
    rationalSpan_finite N.toSubmodule
  apply nonempty_equiv_of_baseChange (rationalRepresentation ρ M) (rationalRepresentation ρ N)
    ρ ρ (rationalSpan M.toSubmodule).subtype (rationalSpan N.toSubmodule).subtype
    (rationalSpan_baseChange M.toSubmodule) (rationalSpan_baseChange N.toSubmodule)
  · intro g v
    rfl
  · intro g v
    rfl
  · exact _root_.Representation.Equiv.refl ρ

/-- For stable full lattices $M,N$ in one real representation, $h(M)=h(N)$.
Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, Lemma 3.5. -/
theorem herbrandQuotient_eq_of_real_lattices [Fintype G] [IsCyclic G]
    (ρ : _root_.Representation ℝ G V)
    (M N : Subrepresentation (integral ρ))
    [DiscreteTopology M.toSubmodule] [IsZLattice ℝ M.toSubmodule]
    [DiscreteTopology N.toSubmodule] [IsZLattice ℝ N.toSubmodule] :
    herbrandQuotient M.toRepresentation = herbrandQuotient N.toRepresentation := by
  obtain ⟨e⟩ := rational_equiv ρ M N
  calc
    herbrandQuotient M.toRepresentation =
        herbrandQuotient (rationalLattice ρ M).toRepresentation :=
      (herbrandQuotient_equiv (rationalLattice_equiv ρ M)).symm
    _ = herbrandQuotient (rationalLattice ρ N).toRepresentation :=
      herbrandQuotient_eq_of_rational_equiv e
        (rationalLattice ρ M) (rationalLattice ρ N)
        (rationalLattice_fg ρ M) (rationalLattice_fg ρ N)
        (rationalLattice_full ρ M) (rationalLattice_full ρ N)
    _ = herbrandQuotient N.toRepresentation :=
      herbrandQuotient_equiv (rationalLattice_equiv ρ N)

end SIC.Representation
