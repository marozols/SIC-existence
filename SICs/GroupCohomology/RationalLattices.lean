/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.GroupCohomology.Herbrand
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Rational lattices and Herbrand quotients

Finitely generated integral lattices spanning isomorphic rational representations have the same
Herbrand quotient.

This module follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, Lemma 3.4.
An integral lattice in a rational representation is represented by a `Subrepresentation` of the
integer restriction from `SICs.RepresentationTheory.Basic`, with finite generation and full
rational span stated separately.

## The argument

For two full lattices in one rational representation, express each generator of the first in the
rational span of the second. Clearing the finitely many denominators gives a nonzero integer `d`
whose multiplication maps the first lattice into the second. The map is equivariant and injective.
The quotient is finitely generated and torsion, hence finite: every element of the second lattice
has a nonzero multiple in the first lattice, which multiplication by `d` sends into the image.
Milne's Chapter II, Corollary 3.9 then compares the Herbrand quotients. A rational equivariant
equivalence transports the second lattice to the first rational space, where this argument applies.
-/

noncomputable section

namespace SIC.Representation

/-! ### Common denominators

For rational representations, a full integral submodule has a nonzero integer multiple of
every rational vector; finite generation makes that multiplier uniform on another submodule. -/

variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- A vector in the rational span of an integral submodule has a nonzero integral multiple in
that submodule. Used by `commonDenominator`. -/
private theorem exists_nonzero_smul_mem (N : Submodule ℤ V) (x : V)
    (hx : x ∈ Submodule.span ℚ (N : Set V)) :
    ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ N := by
  obtain ⟨d, hd⟩ :=
    multiple_mem_span_of_mem_localization_span (nonZeroDivisors ℤ) ℚ (N : Set V) x hx
  exact ⟨d, (mem_nonZeroDivisors_iff_ne_zero.mp d.property),
    by simpa only [Submodule.span_eq, Submonoid.smul_def] using hd⟩

/-- Finite generation of `M` and full rational span of `N` give one nonzero integer `d` with
`dM ⊆ N`. Used by `exists_comparisonMap`. -/
private theorem commonDenominator (M N : Submodule ℤ V) (hM : M.FG)
    (hN : Submodule.span ℚ (N : Set V) = ⊤) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ M, d • x ∈ N := by
  classical
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp hM
  let _ : Fintype s := hsfin.fintype
  have hsingle (x : s) : ∃ d : nonZeroDivisors ℤ, (d : ℤ) • (x : V) ∈ N := by
    obtain ⟨d, hd, hdx⟩ := exists_nonzero_smul_mem N x (by rw [hN]; trivial)
    exact ⟨⟨d, mem_nonZeroDivisors_iff_ne_zero.mpr hd⟩, hdx⟩
  choose t ht using hsingle
  let d : nonZeroDivisors ℤ := ∏ x : s, t x
  have hgen : ∀ x ∈ s, (d : ℤ) • x ∈ N := by
    intro x hx
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem t (Finset.mem_univ (⟨x, hx⟩ : s))
    change d = t ⟨x, hx⟩ * c at hc
    rw [hc, mul_comm (t ⟨x, hx⟩) c, Submonoid.coe_mul, mul_smul]
    exact N.smul_mem _ (ht ⟨x, hx⟩)
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp d.property, ?_⟩
  intro x hx
  have hle : Submodule.span ℤ s ≤ N.comap ((LinearMap.lsmul ℤ V) (d : ℤ)) :=
    Submodule.span_le.mpr (by intro y hy; exact hgen y hy)
  exact hle (hs.symm ▸ hx)

/-! ### Comparison within one rational representation

Multiplication by a common denominator embeds the first lattice in the second. Its quotient is
torsion by the full-span condition on the first lattice and finite by finite generation of the
second. -/

/-- Multiplication by `d` as an equivariant integer-linear map from `M` to `N`, provided
`dM ⊆ N`. Used by `exists_comparisonMap`. -/
private def scaledMap (ρ : _root_.Representation ℚ G V)
    (M N : Subrepresentation (integral ρ)) (d : ℤ)
    (h : ∀ x ∈ M.toSubmodule, d • x ∈ N.toSubmodule) :
    M.toRepresentation.IntertwiningMap N.toRepresentation where
  toLinearMap :=
    ((LinearMap.lsmul ℤ V d).comp M.toSubmodule.subtype).codRestrict N.toSubmodule
      (by intro x; exact h x x.property)
  isIntertwining' g := by
    ext x
    change d • ρ g (x : V) = ρ g (d • (x : V))
    exact (map_zsmul (ρ g) d (x : V)).symm

/-- The map `scaledMap` is injective when its denominator is nonzero. Used by
`exists_comparisonMap`. -/
private theorem scaledMap_injective (ρ : _root_.Representation ℚ G V)
    (M N : Subrepresentation (integral ρ)) (d : ℤ) (hd : d ≠ 0)
    (h : ∀ x ∈ M.toSubmodule, d • x ∈ N.toSubmodule) :
    Function.Injective (scaledMap ρ M N d h) := by
  let _ : IsAddTorsionFree V := .of_module_rat V
  intro x y hxy
  apply Subtype.ext
  apply LinearMap.lsmul_injective hd
  exact congrArg Subtype.val hxy

/-- The cokernel of `scaledMap` is finite when `N` is finitely generated and `M` has full
rational span. Used by `exists_comparisonMap`. -/
private theorem scaledMap_finite_coker (ρ : _root_.Representation ℚ G V)
    (M N : Subrepresentation (integral ρ)) (d : ℤ) (hd : d ≠ 0)
    (h : ∀ x ∈ M.toSubmodule, d • x ∈ N.toSubmodule)
    (hN : N.toSubmodule.FG) (hMspan : Submodule.span ℚ (M : Set V) = ⊤) :
    Finite (N.toSubmodule ⧸ LinearMap.range (scaledMap ρ M N d h).toLinearMap) := by
  let f := scaledMap ρ M N d h
  let _ : Module.Finite ℤ N.toSubmodule := Module.Finite.of_fg hN
  let _ : Module.Finite ℤ (N.toSubmodule ⧸ LinearMap.range f.toLinearMap) :=
    Module.Finite.quotient ℤ _
  apply Module.finite_of_fg_torsion
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H y =>
    have hspan : Submodule.span ℚ (M.toSubmodule : Set V) = ⊤ := hMspan
    obtain ⟨t, ht, hty⟩ := exists_nonzero_smul_mem M.toSubmodule y (by rw [hspan]; trivial)
    let a : nonZeroDivisors ℤ := ⟨d * t, mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero hd ht)⟩
    refine ⟨a, ?_⟩
    rw [← Submodule.Quotient.mk_smul]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨⟨t • (y : V), hty⟩, ?_⟩
    apply Subtype.ext
    exact (mul_smul d t (y : V)).symm

/-- A full integral lattice `M` admits an equivariant integer-linear embedding into another
full lattice `N`, with finite cokernel, by common-denominator scaling. This is the map in
Milne, *Class Field Theory*, Chapter VII, proof of Lemma 3.4. -/
theorem exists_comparisonMap (ρ : _root_.Representation ℚ G V)
    (M N : Subrepresentation (integral ρ)) (hM : M.toSubmodule.FG)
    (hN : N.toSubmodule.FG) (hMspan : Submodule.span ℚ (M : Set V) = ⊤)
    (hNspan : Submodule.span ℚ (N : Set V) = ⊤) :
    ∃ f : M.toRepresentation.IntertwiningMap N.toRepresentation,
      Function.Injective f ∧
        Finite (N.toSubmodule ⧸ LinearMap.range f.toLinearMap) := by
  obtain ⟨d, hd, h⟩ := commonDenominator M.toSubmodule N.toSubmodule hM hNspan
  let f := scaledMap ρ M N d h
  have hf : Function.Injective f := scaledMap_injective ρ M N d hd h
  exact ⟨f, hf, scaledMap_finite_coker ρ M N d hd h hN hMspan⟩

/-- For two finitely generated full integral lattices in one rational representation,
$h(M) = h(N)$. Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, Lemma 3.4,
in the common-space case. -/
theorem herbrandQuotient_eq_of_rational_lattices [Fintype G] [IsCyclic G]
    (ρ : _root_.Representation ℚ G V)
    (M N : Subrepresentation (integral ρ)) (hM : M.toSubmodule.FG)
    (hN : N.toSubmodule.FG) (hMspan : Submodule.span ℚ (M : Set V) = ⊤)
    (hNspan : Submodule.span ℚ (N : Set V) = ⊤) :
    herbrandQuotient M.toRepresentation = herbrandQuotient N.toRepresentation := by
  obtain ⟨f, hf, hc⟩ := exists_comparisonMap ρ M N hM hN hMspan hNspan
  exact herbrandQuotient_eq_of_injective_of_finite_coker f hf hc

/-! ### Rationally isomorphic representations

An equivariant rational equivalence takes a full lattice to a full lattice. Transporting one
lattice back along the equivalence reduces Milne's formulation to the common-space comparison. -/

/-- The image of `N` under the inverse rational equivalence, as an integral
subrepresentation of `ρ`. Used by `herbrandQuotient_eq_of_rational_equiv`. -/
private def pullbackLattice {ρ : _root_.Representation ℚ G V}
    {σ : _root_.Representation ℚ G W} (e : ρ.Equiv σ)
    (N : Subrepresentation (integral σ)) : Subrepresentation (integral ρ) where
  toSubmodule := N.toSubmodule.map (e.symm.toLinearEquiv.restrictScalars ℤ).toLinearMap
  apply_mem_toSubmodule g := by
    rintro v ⟨w, hw, rfl⟩
    refine ⟨σ g w, N.apply_mem_toSubmodule g hw, ?_⟩
    exact _root_.Representation.IntertwiningMap.isIntertwining σ ρ
      e.symm.toIntertwiningMap g w

/-- Rational equivalences preserve finite generation of integral submodules. Used by
`herbrandQuotient_eq_of_rational_equiv`. -/
private theorem pullbackLattice_fg {ρ : _root_.Representation ℚ G V}
    {σ : _root_.Representation ℚ G W} (e : ρ.Equiv σ)
    (N : Subrepresentation (integral σ)) (hN : N.toSubmodule.FG) :
    (pullbackLattice e N).toSubmodule.FG :=
  hN.map (e.symm.toLinearEquiv.restrictScalars ℤ).toLinearMap

/-- Rational equivalences preserve the full-span condition on integral submodules. Used by
`herbrandQuotient_eq_of_rational_equiv`. -/
private theorem pullbackLattice_span {ρ : _root_.Representation ℚ G V}
    {σ : _root_.Representation ℚ G W} (e : ρ.Equiv σ)
    (N : Subrepresentation (integral σ)) (hN : Submodule.span ℚ (N : Set W) = ⊤) :
    Submodule.span ℚ (pullbackLattice e N : Set V) = ⊤ := by
  change Submodule.span ℚ
    ((N.toSubmodule.map (e.symm.toLinearEquiv.restrictScalars ℤ).toLinearMap :
      Submodule ℤ V) : Set V) = ⊤
  rw [Submodule.map_coe]
  change Submodule.span ℚ (e.symm.toLinearEquiv.toLinearMap '' (N : Set W)) = ⊤
  rw [Submodule.span_image]
  rw [hN, Submodule.map_top, LinearMap.range_eq_top.mpr e.symm.toLinearEquiv.surjective]

/-- The pullback lattice and `N` have equivalent integral representations. Used by the
rational-isomorphism form of Milne's Lemma 3.4. -/
private def pullbackLattice_equiv {ρ : _root_.Representation ℚ G V}
    {σ : _root_.Representation ℚ G W} (e : ρ.Equiv σ)
    (N : Subrepresentation (integral σ)) :
    (pullbackLattice e N).toRepresentation.Equiv N.toRepresentation := by
  let E := (e.symm.toLinearEquiv.restrictScalars ℤ).submoduleMap N.toSubmodule
  apply _root_.Representation.Equiv.mk E.symm
  intro g
  ext x
  change e.toLinearEquiv (ρ g (x : V)) = σ g (e.toLinearEquiv (x : V))
  exact _root_.Representation.IntertwiningMap.isIntertwining ρ σ
    e.toIntertwiningMap g (x : V)

/-- Finitely generated full integral lattices in rationally isomorphic representations have
equal Herbrand quotients. This is the torsion-free lattice case of Milne, *Class Field Theory*,
version 4.03 (2020), Chapter VII, Lemma 3.4. -/
theorem herbrandQuotient_eq_of_rational_equiv [Fintype G] [IsCyclic G]
    {ρ : _root_.Representation ℚ G V} {σ : _root_.Representation ℚ G W}
    (e : ρ.Equiv σ) (M : Subrepresentation (integral ρ))
    (N : Subrepresentation (integral σ)) (hM : M.toSubmodule.FG)
    (hN : N.toSubmodule.FG) (hMspan : Submodule.span ℚ (M : Set V) = ⊤)
    (hNspan : Submodule.span ℚ (N : Set W) = ⊤) :
    herbrandQuotient M.toRepresentation = herbrandQuotient N.toRepresentation := by
  calc
    herbrandQuotient M.toRepresentation =
        herbrandQuotient (pullbackLattice e N).toRepresentation :=
      herbrandQuotient_eq_of_rational_lattices ρ M (pullbackLattice e N) hM
        (pullbackLattice_fg e N hN) hMspan (pullbackLattice_span e N hNspan)
    _ = herbrandQuotient N.toRepresentation :=
      herbrandQuotient_equiv (pullbackLattice_equiv e N)

end SIC.Representation
