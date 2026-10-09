/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.FieldTheory.GaloisDescent
import SICs.OrbitStabilizer
import SICs.RepresentationTheory.PermutedFamily

/-!
# Decomposition groups of a permuted family of algebras

The automorphisms of a global field $E/K$ permute a family of fields over a local base $F$ and
act on each fiber through the stabilizer of its index. When the indices form one orbit and the
fiber degrees add to $[E:K]$, this action identifies the stabilizer with the local Galois group.

This is the common algebraic argument behind the finite and infinite decomposition groups in
Serre, *Local Fields*, Chapter II, §3, Corollary 4, and Milne, *Class Field Theory*, version 4.03
(2020), Chapter VII, §2. The induced representation of the units supplies the coordinate action
in Milne, Chapter VII, Proposition 2.2.

## The argument

Transport along an automorphism fixes the local base field and extends its action on the global
field.
Its restriction to a stabilizer is faithful because the global field embeds in each fiber. The
transports identify degrees along an orbit. Orbit-stabilizer and the sum of local degrees then
give the order of the stabilizer, equal to the local degree. Thus every local automorphism comes
from the stabilizer, giving Galois descent and the norm formula. A coset of the stabilizer
indexes the transports between two fibers; its product is the transported local norm, which is
fixed by transport because it belongs to the base field.
The transports act on units and restrict to any family of unit subgroups they preserve.
-/

noncomputable section

namespace SIC

/-! ### Algebra transports and the stabilizer action

The four fields of `PermutedAlgebraFamily` are exactly the transport data used by both kinds of
completion. Here `K` is the global base, `F` is its completion, `E` is the global extension, and
`C i` is a completion-like field.
-/

/-- A family of $F$-algebras receiving $E$, permuted compatibly by $\operatorname{Gal}(E/K)$.
The transports extend the automorphisms of `E`. -/
structure PermutedAlgebraFamily (K F E : Type*) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E]
    (ι : Type*) [MulAction (E ≃ₐ[K] E) ι] (C : ι → Type*) [∀ i, Field (C i)]
    [∀ i, Algebra K (C i)] [∀ i, Algebra F (C i)] [∀ i, Algebra E (C i)]
    [∀ i, IsScalarTower K F (C i)]
    [∀ i, IsScalarTower K E (C i)] where
  /-- Transport from `C i` to `C j` along an automorphism carrying `i` to `j`. -/
  map : ∀ (σ : E ≃ₐ[K] E) (i j : ι), σ • i = j → C i ≃ₐ[F] C j
  /-- Identity transport is the identity on each fiber. -/
  map_one : ∀ i, map 1 i i (one_smul _ i) = AlgEquiv.refl
  /-- Transport by a product is successive transport. -/
  map_mul : ∀ σ τ i j l (hij : τ • i = j) (hjl : σ • j = l),
    map (σ * τ) i l ((mul_smul σ τ i).trans (by rw [hij, hjl])) =
      (map τ i j hij).trans (map σ j l hjl)
  /-- Transport extends the action on the embedded global field. -/
  map_algebraMap : ∀ σ i j h (x : E), map σ i j h (algebraMap E (C i) x) =
    algebraMap E (C j) (σ x)

namespace PermutedAlgebraFamily

variable {K F E ι : Type*} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
  [MulAction (E ≃ₐ[K] E) ι] {C : ι → Type*} [∀ i, Field (C i)]
  [∀ i, Algebra K (C i)] [∀ i, Algebra F (C i)] [∀ i, Algebra E (C i)]
  [∀ i, IsScalarTower K F (C i)]
  [∀ i, IsScalarTower K E (C i)] (A : PermutedAlgebraFamily K F E ι C)

/-- The stabilizer of `i` acts by $F$-algebra automorphisms of `C i`. -/
def fiber (i : ι) : MulAction.stabilizer (E ≃ₐ[K] E) i →* (C i ≃ₐ[F] C i) where
  toFun σ := A.map σ i i (MulAction.mem_stabilizer_iff.mp σ.2)
  map_one' := A.map_one i
  map_mul' σ τ := A.map_mul σ τ i i i
    (MulAction.mem_stabilizer_iff.mp τ.2) (MulAction.mem_stabilizer_iff.mp σ.2)

/-- The fiber action restricts to the given action on `E`. -/
@[simp] theorem fiber_algebraMap (i : ι)
    (σ : MulAction.stabilizer (E ≃ₐ[K] E) i) (x : E) :
    A.fiber i σ (algebraMap E (C i) x) = algebraMap E (C i) ((σ : E ≃ₐ[K] E) x) :=
  A.map_algebraMap σ i i (MulAction.mem_stabilizer_iff.mp σ.2) x

/-- The stabilizer action on `C i` is faithful. -/
theorem fiber_injective (i : ι) : Function.Injective (A.fiber i) := by
  intro σ τ h
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E (C i)).injective
  rw [← A.fiber_algebraMap i σ x, ← A.fiber_algebraMap i τ x, h]

/-! ### Local Galois groups and norms

For a transitive index set, the sum of local degrees and orbit-stabilizer determine every fiber
degree. The faithful stabilizer action is therefore the full local Galois group.
-/

section Galois

variable [FiniteDimensional K E] [IsGalois K E] [Fintype ι]

include A

/-- A transitive family's local degree is the order of the stabilizer, provided its degrees add
to the degree of `E/F`. This is the shared counting step in Serre, Chapter II, §3, Corollary 4. -/
theorem finrank_eq_card_stabilizer (htrans : ∀ i j : ι, ∃ σ : E ≃ₐ[K] E, σ • i = j)
    (hsum : ∑ i, Module.finrank F (C i) = Module.finrank K E) (i : ι) :
    Module.finrank F (C i) = Nat.card (MulAction.stabilizer (E ≃ₐ[K] E) i) := by
  apply eq_card_stabilizer_of_sum_eq_card (fun i : ι => i) (fun _ _ h => h)
    (fun j => by
      ext k
      constructor
      · intro _
        exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩
        obtain ⟨σ, hσ⟩ := htrans j k
        exact MulAction.mem_orbit_iff.mpr ⟨σ, hσ⟩)
    (fun i => Module.finrank F (C i))
    (fun j k => by
      obtain ⟨σ, hσ⟩ := htrans j k
      exact (A.map σ j k hσ).toLinearEquiv.finrank_eq)
    (hsum.trans (IsGalois.card_aut_eq_finrank K E).symm) i

/-- Every fiber degree divides the global degree. -/
theorem finrank_dvd_finrank (htrans : ∀ i j : ι, ∃ σ : E ≃ₐ[K] E, σ • i = j)
    (hsum : ∑ i, Module.finrank F (C i) = Module.finrank K E) (i : ι) :
    Module.finrank F (C i) ∣ Module.finrank K E := by
  rw [A.finrank_eq_card_stabilizer htrans hsum i, ← IsGalois.card_aut_eq_finrank]
  exact Subgroup.card_subgroup_dvd_card _

variable [∀ i, FiniteDimensional F (C i)]

/-- The stabilizer action exhausts the automorphisms of a fiber. -/
theorem fiber_bijective (htrans : ∀ i j : ι, ∃ σ : E ≃ₐ[K] E, σ • i = j)
    (hsum : ∑ i, Module.finrank F (C i) = Module.finrank K E) (i : ι) :
    Function.Bijective (A.fiber i) :=
  bijective_of_injective_of_card_eq_finrank (A.fiber i) (A.fiber_injective i)
    (A.finrank_eq_card_stabilizer htrans hsum i).symm

/-- The decomposition group of a fiber is its $F$-algebra automorphism group. -/
def decompositionEquiv (htrans : ∀ i j : ι, ∃ σ : E ≃ₐ[K] E, σ • i = j)
    (hsum : ∑ i, Module.finrank F (C i) = Module.finrank K E) (i : ι) :
    MulAction.stabilizer (E ≃ₐ[K] E) i ≃* (C i ≃ₐ[F] C i) :=
  MulEquiv.ofBijective (A.fiber i) (A.fiber_bijective htrans hsum i)

/-- A fiber of a transitive Galois family with the degree-sum property is Galois over `F`. -/
theorem isGalois (htrans : ∀ i j : ι, ∃ σ : E ≃ₐ[K] E, σ • i = j)
    (hsum : ∑ i, Module.finrank F (C i) = Module.finrank K E) (i : ι) :
    IsGalois F (C i) :=
  isGalois_of_injective_of_card_eq_finrank (A.fiber i) (A.fiber_injective i)
    (A.finrank_eq_card_stabilizer htrans hsum i).symm

/-- Galois descent through the fiber action: an element of `C i` comes from `F` exactly when
every element of the stabilizer fixes it. -/
theorem mem_range_algebraMap_iff (htrans : ∀ i j : ι, ∃ σ : E ≃ₐ[K] E, σ • i = j)
    (hsum : ∑ i, Module.finrank F (C i) = Module.finrank K E) (i : ι) (x : C i) :
    x ∈ (algebraMap F (C i)).range ↔
      ∀ σ : MulAction.stabilizer (E ≃ₐ[K] E) i, A.fiber i σ x = x := by
  exact @mem_range_algebraMap_iff_of_surjective F (C i) _ _ _ _ _ _
    (A.isGalois htrans hsum i) (A.fiber i)
    (A.fiber_bijective htrans hsum i).2 x

/-- Galois descent after identifying another group with the stabilizer. -/
theorem mem_range_algebraMap_iff_reindex {H : Type*} [Group H]
    (htrans : ∀ i j : ι, ∃ σ : E ≃ₐ[K] E, σ • i = j)
    (hsum : ∑ i, Module.finrank F (C i) = Module.finrank K E) (i : ι)
    (e : H ≃* MulAction.stabilizer (E ≃ₐ[K] E) i) (x : C i) :
    x ∈ (algebraMap F (C i)).range ↔ ∀ σ : H, A.fiber i (e σ) x = x := by
  rw [A.mem_range_algebraMap_iff htrans hsum i x]
  exact ⟨fun h σ => h (e σ), fun h τ => by
    obtain ⟨σ, rfl⟩ := e.surjective τ
    exact h σ⟩

/-- The norm of a fiber element is the product of its stabilizer conjugates. -/
theorem algebraMap_norm_eq_prod (htrans : ∀ i j : ι, ∃ σ : E ≃ₐ[K] E, σ • i = j)
    (hsum : ∑ i, Module.finrank F (C i) = Module.finrank K E) (i : ι)
    [Fintype (MulAction.stabilizer (E ≃ₐ[K] E) i)] (x : C i) :
    algebraMap F (C i) (Algebra.norm F x) =
      ∏ σ : MulAction.stabilizer (E ≃ₐ[K] E) i, A.fiber i σ x := by
  exact @algebraMap_norm_eq_prod_of_bijective F (C i) _ _ _ _ _ _
    (A.isGalois htrans hsum i) _ (A.fiber i)
    (A.fiber_bijective htrans hsum i) x

/-- The product of all transports carrying `i` to `j` is the local norm of an element of
`C i`, embedded in `C j`. This is Milne, Chapter VII, §2, "The norm map on idèles". -/
theorem prod_map_eq_algebraMap_norm (htrans : ∀ i j : ι, ∃ σ : E ≃ₐ[K] E, σ • i = j)
    (hsum : ∑ i, Module.finrank F (C i) = Module.finrank K E) (i j : ι)
    [Fintype {σ : E ≃ₐ[K] E // σ • i = j}] (y : C i) :
    ∏ σ : {σ : E ≃ₐ[K] E // σ • i = j}, A.map σ i j σ.2 y =
      algebraMap F (C j) (Algebra.norm F y) := by
  obtain ⟨τ, hτ⟩ := htrans i j
  classical
  let e := stabilizerEquivSmulEq τ hτ
  calc
    ∏ σ : {σ : E ≃ₐ[K] E // σ • i = j}, A.map σ i j σ.2 y =
        ∏ δ : MulAction.stabilizer (E ≃ₐ[K] E) i, A.map (e δ) i j (e δ).2 y :=
      (e.prod_comp _).symm
    _ = ∏ δ : MulAction.stabilizer (E ≃ₐ[K] E) i,
          A.map τ i j hτ (A.fiber i δ y) := by
      apply Finset.prod_congr rfl
      intro δ _
      change A.map (τ * (δ : E ≃ₐ[K] E)) i j (e δ).2 y =
        A.map τ i j hτ
          (A.map δ i i (MulAction.mem_stabilizer_iff.mp δ.2) y)
      simpa only [e, coe_stabilizerEquivSmulEq_apply, AlgEquiv.trans_apply] using
        congrArg (fun f : C i ≃ₐ[F] C j => f y)
          (A.map_mul τ δ i i j (MulAction.mem_stabilizer_iff.mp δ.2) hτ)
    _ = A.map τ i j hτ
          (∏ δ : MulAction.stabilizer (E ≃ₐ[K] E) i, A.fiber i δ y) := by
      rw [map_prod]
    _ = A.map τ i j hτ (algebraMap F (C i) (Algebra.norm F y)) := by
      rw [A.algebraMap_norm_eq_prod htrans hsum i y]
    _ = algebraMap F (C j) (Algebra.norm F y) := (A.map τ i j hτ).commutes _

end Galois

/-! ### Multiplicative representations

Applying each algebra transport to units gives the permuted family used by the semilocal
representations of finite and infinite completions. A family of subgroups preserved by
transport inherits the same permuted action.
-/

/-- The unit groups of the fibers form a permuted family of integer modules. -/
def toPermutedFamily : Representation.PermutedFamily ℤ (E ≃ₐ[K] E) ι
    (fun i => Additive (C i)ˣ) where
  map σ i j h := (Units.mapEquiv (A.map σ i j h).toMulEquiv).toAdditive.toIntLinearEquiv
  map_one := by
    intro i
    ext x
    exact congrArg (fun e : C i ≃ₐ[F] C i => e (x.toMul : C i)) (A.map_one i)
  map_mul := by
    intro σ τ i j l hij hjl
    ext x
    exact congrArg (fun e : C i ≃ₐ[F] C l => e (x.toMul : C i))
      (A.map_mul σ τ i j l hij hjl)

/-- The permuted family of a transport-stable family of unit subgroups. -/
def toPermutedFamilyOfSubgroup (U : ∀ i, Subgroup (C i)ˣ)
    (hU : ∀ σ i j (h : σ • i = j) (x : (C i)ˣ),
      x ∈ U i ↔ Units.map (A.map σ i j h) x ∈ U j) :
    Representation.PermutedFamily ℤ (E ≃ₐ[K] E) ι (fun i => Additive (U i)) where
  map σ i j h := by
    let e := Units.mapEquiv (A.map σ i j h).toMulEquiv
    have hmap : (U i).map e.toMonoidHom = U j := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (hU σ i j h y).mp hy
      · intro hx
        refine ⟨e.symm x, (hU σ i j h (e.symm x)).mpr ?_, e.apply_symm_apply x⟩
        change e (e.symm x) ∈ U j
        simpa only [e.apply_symm_apply] using hx
    exact ((e.subgroupMap (U i)).trans (MulEquiv.subgroupCongr hmap)).toAdditive.toIntLinearEquiv
  map_one := by
    intro i
    ext x
    exact congrArg (fun e : C i ≃ₐ[F] C i => e (x.toMul.1 : C i)) (A.map_one i)
  map_mul := by
    intro σ τ i j l hij hjl
    ext x
    exact congrArg (fun e : C i ≃ₐ[F] C l => e (x.toMul.1 : C i))
      (A.map_mul σ τ i j l hij hjl)

variable [FiniteDimensional K E] [IsGalois K E] [Fintype ι]
  [∀ i, FiniteDimensional F (C i)]

/-- The unit representation of one fiber is the local Galois representation, reindexed by
its decomposition-group equivalence. -/
theorem toPermutedFamily_fiber (htrans : ∀ i j : ι, ∃ σ : E ≃ₐ[K] E, σ • i = j)
    (hsum : ∑ i, Module.finrank F (C i) = Module.finrank K E) (i : ι) :
    A.toPermutedFamily.fiber i =
      (_root_.Representation.ofMulDistribMulAction (C i ≃ₐ[F] C i) (C i)ˣ).comp
        (A.decompositionEquiv htrans hsum i).toMonoidHom := by
  ext σ x
  rfl

end PermutedAlgebraFamily

end SIC
