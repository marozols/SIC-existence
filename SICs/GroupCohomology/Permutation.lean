/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.GroupCohomology.Shapiro
import SICs.GroupCohomology.Pi

/-!
# Permutation lattices and their Herbrand quotients

The integral functions on a finite group set form a permutation lattice, whose Herbrand quotient
is the product of the orders of the stabilizers of its transitive components.

This module follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII,
Proposition 3.1, in its computation of the first lattice $N=\operatorname{Hom}(T,\mathbb Z)$.

## The argument

The action on functions is $(g f)(x)=f(g^{-1}x)$. It is the constant-fiber case of the
permuted-family representation, with identity transport on the coefficient ring. On a transitive
set, the permuted-family equivalence identifies the function module with coinduction from a
point stabilizer. Shapiro's lemma and $h(\mathbb Z)=|G|$ give the stabilizer order. A finite
invariant partition identifies functions with the product of the function modules on its fibers,
so their Herbrand quotients multiply.
-/

noncomputable section

namespace SIC.Representation

variable {k G X : Type*} [CommRing k] [Group G] [MulAction G X]

/-! ### Coordinate action -/

/-- The constant family with identity transports used to act on functions `X → k`. -/
def permutationFamily : PermutedFamily k G X (fun _ => k) where
  map := fun _ _ _ _ => LinearEquiv.refl k k
  map_one := by intro; rfl
  map_mul := by intros; rfl

/-- Every coordinate transport of `permutationFamily` is the identity. -/
@[simp] theorem permutationFamily_map (g : G) (x y : X) (h : g • x = y) (a : k) :
    (permutationFamily (k := k) (G := G) (X := X)).map g x y h a = a := rfl

/-- The permutation representation on coefficient-valued functions,
$(g f)(x)=f(g^{-1}x)$. -/
def permutation : _root_.Representation k G (X → k) :=
  (permutationFamily (k := k) (G := G) (X := X)).sections

/-- Evaluation of the permutation action at `x`. -/
@[simp] theorem permutation_apply (g : G) (f : X → k) (x : X) :
    permutation (k := k) (G := G) (X := X) g f x = f (g⁻¹ • x) := by
  simp [permutation, PermutedFamily.sections_apply]

/-! ### A transitive permutation lattice

The constant fiber carries the trivial stabilizer action. Thus the transitive family
equivalence `PermutedFamily.coindEquiv` and the two Shapiro equivalences apply directly. -/

/-- For a transitive set `X`, $h(\operatorname{Hom}(X,\mathbb Z))=|G_x|$.
Milne, *Class Field Theory*, Chapter VII, Proposition 3.1, first lattice. -/
theorem herbrandQuotient_permutation [Fintype G]
    (x : X) (htrans : ∀ y, ∃ g : G, g • x = y) :
    herbrandQuotient (permutation (k := ℤ) (G := G) (X := X)) =
      Nat.card (MulAction.stabilizer G x) := by
  let S := MulAction.stabilizer G x
  let _ : Fintype S := Fintype.ofFinite S
  calc
    herbrandQuotient (permutation (k := ℤ) (G := G) (X := X)) =
        herbrandQuotient (_root_.Representation.trivial ℤ S ℤ) :=
      (permutationFamily (k := ℤ) (G := G) (X := X)).herbrandQuotient_sections
        x htrans (_root_.Representation.trivial ℤ S ℤ) (MulEquiv.refl S) (by rfl)
    _ = Nat.card S := by
      rw [herbrandQuotient_trivial, Nat.card_eq_fintype_card]

/-! ### Finite invariant partitions

An invariant map `p : X → B` partitions `X` into stable fibers. The action on a fiber uses the
original action on `X`; grouping coordinates identifies the function representation with the
product of these fiber representations. -/

/-- The action on a fiber of an invariant map, used by `fiberPermutation`. -/
@[instance_reducible] private def fiberAction {B : Type*} (p : X → B)
    (hp : ∀ (g : G) (x : X), p (g • x) = p x) (b : B) :
    MulAction G {x : X // p x = b} where
  smul g x := ⟨g • x.1, (hp g x.1).trans x.2⟩
  one_smul x := by apply Subtype.ext; exact one_smul G x.1
  mul_smul g h x := by apply Subtype.ext; exact mul_smul g h x.1

/-- The permutation representation on one stable fiber of `p`. -/
def fiberPermutation {B : Type*} (p : X → B)
    (hp : ∀ (g : G) (x : X), p (g • x) = p x) (b : B) :
    _root_.Representation k G ({x : X // p x = b} → k) := by
  letI : MulAction G {x : X // p x = b} := fiberAction p hp b
  exact permutation (k := k) (G := G) (X := {x : X // p x = b})

/-- On a stable fiber, $(g f)(x)=f(g^{-1}x)$ with the inherited action. -/
@[simp] theorem fiberPermutation_apply {B : Type*} (p : X → B)
    (hp : ∀ (g : G) (x : X), p (g • x) = p x) (b : B)
    (g : G) (f : {x : X // p x = b} → k) (y : {x : X // p x = b}) :
    fiberPermutation (k := k) p hp b g f y =
      f ⟨g⁻¹ • y.1, (hp g⁻¹ y.1).trans y.2⟩ := by
  simp only [fiberPermutation, permutation_apply]
  congr 1

/-- Grouping functions by stable fibers is an equivalence of representations. -/
def permutationGroupedEquiv {B : Type*} (p : X → B)
    (hp : ∀ (g : G) (x : X), p (g • x) = p x) :
    (permutation (k := k) (G := G) (X := X)).Equiv
      (pi (fun b => fiberPermutation (k := k) p hp b)) := by
  let L : (X → k) ≃ₗ[k] (∀ b, {x : X // p x = b} → k) :=
    (LinearEquiv.piCongrLeft' k (fun _ : X => k) (Equiv.sigmaFiberEquiv p).symm).trans
      (LinearEquiv.piCurry k (fun _ _ => k))
  refine _root_.Representation.Equiv.mk L ?_
  intro g
  ext f b y
  simp only [LinearMap.comp_apply, pi_apply, fiberPermutation_apply]
  rfl

/-- The stabilizer of a point in a stable fiber is its stabilizer in `X`; used by the
finite-partition Herbrand formula. -/
private theorem fiber_stabilizer {B : Type*} (p : X → B)
    (hp : ∀ (g : G) (x : X), p (g • x) = p x) (b : B)
    (y : {x : X // p x = b}) :
    @MulAction.stabilizer G {x : X // p x = b} _ (fiberAction p hp b) y =
      MulAction.stabilizer G y.1 := by
  ext g
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- For a finite invariant partition into transitive fibers,
$h(\operatorname{Hom}(X,\mathbb Z))=\prod_{b\in B}|G_{x_b}|$.
Milne, *Class Field Theory*, Chapter VII, Proposition 3.1, first lattice. -/
theorem herbrandQuotient_permutation_grouped [Fintype G]
    {B : Type*} [Fintype B] (p : X → B)
    (hp : ∀ (g : G) (x : X), p (g • x) = p x)
    (x₀ : ∀ b, {x : X // p x = b})
    (htrans : ∀ b (y : X), p y = b → ∃ g : G, g • (x₀ b).1 = y) :
    herbrandQuotient (permutation (k := ℤ) (G := G) (X := X)) =
      ∏ b, (Nat.card (MulAction.stabilizer G (x₀ b).1) : ℚ) := by
  calc
    _ = herbrandQuotient (pi (fun b => fiberPermutation (k := ℤ) p hp b)) :=
      herbrandQuotient_equiv (permutationGroupedEquiv (k := ℤ) p hp)
    _ = ∏ b, herbrandQuotient (fiberPermutation (k := ℤ) p hp b) :=
      herbrandQuotient_pi _
    _ = ∏ b, (Nat.card (MulAction.stabilizer G (x₀ b).1) : ℚ) := by
      apply Finset.prod_congr rfl
      intro b _
      let _ : MulAction G {x : X // p x = b} := fiberAction p hp b
      change herbrandQuotient (permutation (k := ℤ) (G := G)
        (X := {x : X // p x = b})) = _
      have ht : ∀ y : {x : X // p x = b}, ∃ g : G, g • (x₀ b) = y := by
        intro y
        obtain ⟨g, hg⟩ := htrans b y.1 y.2
        exact ⟨g, Subtype.ext hg⟩
      rw [herbrandQuotient_permutation (x₀ b) ht,
        fiber_stabilizer p hp b (x₀ b)]

/-- Every transitive stable fiber of a finite invariant partition has finite Tate groups, and
so does the integral function lattice on the whole set. -/
theorem hasHerbrandQuotient_permutation_grouped [Fintype G]
    {B : Type*} [Finite B] (p : X → B)
    (hp : ∀ (g : G) (x : X), p (g • x) = p x)
    (x₀ : ∀ b, {x : X // p x = b})
    (htrans : ∀ b (y : X), p y = b → ∃ g : G, g • (x₀ b).1 = y) :
    HasHerbrandQuotient (permutation (k := ℤ) (G := G) (X := X)) := by
  let _ : Fintype B := Fintype.ofFinite B
  rw [hasHerbrandQuotient_iff_ne_zero,
    herbrandQuotient_permutation_grouped p hp x₀ htrans]
  apply ne_of_gt
  apply Finset.prod_pos
  intro b _
  exact_mod_cast (Nat.card_pos (α := MulAction.stabilizer G (x₀ b).1))

end SIC.Representation
