/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.GroupCohomology.Herbrand
import Mathlib.LinearAlgebra.Quotient.Pi

/-!
# Tate cohomology of products

The Tate groups in degrees zero and minus one commute with arbitrary products of modules for a
finite group, and Herbrand quotients multiply over finite products.

This is the product argument of Milne, *Class Field Theory*, version 4.03 (2020), Chapter II,
Proposition 1.25, for the explicit Tate groups of §3, used in Chapter VII, Propositions 2.5 and
2.7.

## The argument

Invariants and norm kernels are componentwise. Norm preimages assemble by choice. Every
augmentation element is a sum indexed by the finite group, so its componentwise preimages also
assemble, even in an infinite product. For two factors, the same submodule identities hold
directly for the binary representation product. Quotienting gives the product equivalences;
finite-group cardinalities then give the Herbrand quotient formulas.
-/
noncomputable section
namespace SIC.Representation
variable {k G ι : Type*} [CommRing k] [Group G] [Fintype G]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

/-! ### Quotients of products

The following quotient equivalence uses choice to lift one representative per coordinate.
It applies to the invariant and norm-kernel submodules below. -/

/-- A quotient by a product of submodules is the product of their quotients, extending
Mathlib's `Submodule.quotientPi` to infinite index types; used by both Tate product equivalences. -/
private def quotientPiEquiv {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module k (M i)] (p : ∀ i, Submodule k (M i)) :
    ((∀ i, M i) ⧸ Submodule.pi Set.univ p) ≃ₗ[k] (∀ i, M i ⧸ p i) := by
  let f := Submodule.quotientPiLift p (fun i => (p i).mkQ) (fun i => by simp)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    induction x using Submodule.Quotient.induction_on with
    | _ a =>
      induction y using Submodule.Quotient.induction_on with
      | _ b =>
        apply (Submodule.Quotient.eq (Submodule.pi Set.univ p)).2
        apply (Submodule.mem_pi).2
        intro i _
        exact (Submodule.Quotient.eq (p i)).1 (congrFun h i)
  · intro y
    choose x hx using (fun i => (p i).mkQ_surjective (y i))
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    ext i
    exact hx i

/-- A submodule whose membership is coordinatewise is linearly equivalent to the product of
its coordinate submodules; used by `tateZeroPiEquiv` and `tateNegOnePiEquiv`. -/
private def submodulePiEquiv {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module k (M i)] (P : Submodule k (∀ i, M i))
    (p : ∀ i, Submodule k (M i))
    (hP : ∀ x, x ∈ P ↔ ∀ i, x i ∈ p i) : P ≃ₗ[k] (∀ i, p i) where
  toFun x i := ⟨x.1 i, (hP x.1).1 x.2 i⟩
  invFun x := ⟨fun i => (x i).1, (hP _).2 fun i => (x i).2⟩
  left_inv x := by ext i; rfl
  right_inv x := by ext i; rfl
  map_add' x y := by ext i; rfl
  map_smul' c x := by ext i; rfl

/-- Quotient the coordinatewise submodule equivalence by coordinatewise denominators; used by
both Tate product equivalences. -/
private def submoduleQuotientPiEquiv {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module k (M i)] (P : Submodule k (∀ i, M i))
    (p : ∀ i, Submodule k (M i)) (e : P ≃ₗ[k] ∀ i, p i)
    (Q : Submodule k P) (q : ∀ i, Submodule k (p i))
    (hQ : ∀ x : P, x ∈ Q ↔ ∀ i, e x i ∈ q i) :
    (P ⧸ Q) ≃ₗ[k] (∀ i, p i ⧸ q i) := by
  have he : Q.map (e : P →ₗ[k] ∀ i, p i) = Submodule.pi Set.univ q := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Submodule.mem_pi).2 fun i _ => (hQ y).1 hy i
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      apply (hQ _).2
      intro i
      simpa using (Submodule.mem_pi).1 hx i (Set.mem_univ i)
  exact (Submodule.Quotient.equiv Q (Submodule.pi Set.univ q) e he).trans
    (quotientPiEquiv q)

/-- The norm of a product representation is componentwise. -/
@[simp] theorem norm_pi_apply (ρ : ∀ i, _root_.Representation k G (V i))
    (x : ∀ i, V i) (i : ι) : ((pi ρ).norm x) i = (ρ i).norm (x i) := by
  simp [_root_.Representation.norm, pi_apply]

omit [Fintype G] in
/-- Product invariants are the componentwise invariant vectors; used by
`tateZeroPiEquiv`. -/
private theorem mem_invariants_pi_iff (ρ : ∀ i, _root_.Representation k G (V i))
    (x : ∀ i, V i) :
    x ∈ (pi ρ).invariants ↔ ∀ i, x i ∈ (ρ i).invariants := by
  constructor
  · intro hx i
    apply ((ρ i).mem_invariants (x i)).2
    intro g
    exact congrFun (((pi ρ).mem_invariants x).1 hx g) i
  · intro hx
    apply ((pi ρ).mem_invariants x).2
    intro g
    funext i
    exact ((ρ i).mem_invariants (x i)).1 (hx i) g

/-- The kernel of the product norm is componentwise; used by
`tateNegOnePiEquiv`. -/
private theorem mem_ker_norm_pi_iff (ρ : ∀ i, _root_.Representation k G (V i))
    (x : ∀ i, V i) :
    x ∈ LinearMap.ker (pi ρ).norm ↔ ∀ i, x i ∈ LinearMap.ker (ρ i).norm := by
  simp only [LinearMap.mem_ker, funext_iff, Pi.zero_apply, norm_pi_apply]

/-- Norms of product vectors are precisely componentwise norms; used by
`tateZeroPiEquiv`. -/
private theorem mem_range_norm_pi_iff (ρ : ∀ i, _root_.Representation k G (V i))
    (x : ∀ i, V i) :
    x ∈ LinearMap.range (pi ρ).norm ↔ ∀ i, x i ∈ LinearMap.range (ρ i).norm := by
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, by simp⟩
  · intro hx
    choose y hy using hx
    refine ⟨y, ?_⟩
    funext i
    simpa using hy i

omit [Fintype G] in
/-- The augmentation submodule of a product is componentwise, using one summand per group
element; used by `tateNegOnePiEquiv`. -/
private theorem mem_coinvariantsKer_pi_iff [Finite G]
    (ρ : ∀ i, _root_.Representation k G (V i))
    (x : ∀ i, V i) :
    x ∈ _root_.Representation.Coinvariants.ker (pi ρ) ↔
      ∀ i, x i ∈ _root_.Representation.Coinvariants.ker (ρ i) := by
  have : Fintype G := Fintype.ofFinite G
  constructor
  · intro hx i
    obtain ⟨y, hy⟩ := (mem_coinvariantsKer_iff_exists_sum (pi ρ) x).1 hx
    apply (mem_coinvariantsKer_iff_exists_sum (ρ i) (x i)).2
    refine ⟨fun g => y g i, ?_⟩
    simpa [pi_apply] using congrFun hy i
  · intro hx
    have h : ∀ i, ∃ y : G → V i, ∑ g, (ρ i g (y g) - y g) = x i :=
      fun i => (mem_coinvariantsKer_iff_exists_sum (ρ i) (x i)).1 (hx i)
    choose y hy using h
    apply (mem_coinvariantsKer_iff_exists_sum (pi ρ) x).2
    refine ⟨fun g i => y i g, ?_⟩
    funext i
    simpa [pi_apply] using hy i

/-- Degree-zero Tate cohomology commutes with arbitrary products for a finite group.
Milne, *Class Field Theory*, Chapter II, Proposition 1.25 and §3. -/
def tateZeroPiEquiv (ρ : ∀ i, _root_.Representation k G (V i)) :
    TateZero (pi ρ) ≃ₗ[k] (∀ i, TateZero (ρ i)) := by
  let e := submodulePiEquiv ((pi ρ).invariants) (fun i => (ρ i).invariants)
    (mem_invariants_pi_iff ρ)
  refine submoduleQuotientPiEquiv _ _ e _ _ ?_
  intro x
  change (x : ∀ i, V i) ∈ LinearMap.range (pi ρ).norm ↔
    ∀ i, (x : ∀ i, V i) i ∈ LinearMap.range (ρ i).norm
  exact mem_range_norm_pi_iff ρ x.1

/-- Degree-minus-one Tate cohomology commutes with arbitrary products for a finite group.
Milne, *Class Field Theory*, Chapter II, Proposition 1.25 and §3. -/
def tateNegOnePiEquiv (ρ : ∀ i, _root_.Representation k G (V i)) :
    TateNegOne (pi ρ) ≃ₗ[k] (∀ i, TateNegOne (ρ i)) := by
  let e := submodulePiEquiv (LinearMap.ker (pi ρ).norm)
    (fun i => LinearMap.ker (ρ i).norm) (mem_ker_norm_pi_iff ρ)
  refine submoduleQuotientPiEquiv _ _ e _ _ ?_
  intro x
  change (x : ∀ i, V i) ∈ _root_.Representation.Coinvariants.ker (pi ρ) ↔
    ∀ i, (x : ∀ i, V i) i ∈ _root_.Representation.Coinvariants.ker (ρ i)
  exact mem_coinvariantsKer_pi_iff ρ x.1

/-! ### Finite support

When all Tate groups outside a finite set vanish, the product Tate groups have the same orders
as the finite products over that set. -/

/-- Restrict a product to a finite set when every remaining factor is a subsingleton; used by
`card_pi_of_subsingleton_outside`. -/
private def piSubtypeEquivOfSubsingleton {M : ι → Type*} [∀ i, Inhabited (M i)]
    (s : Finset ι) (h : ∀ i, i ∉ s → Subsingleton (M i)) :
    (∀ i, M i) ≃ (∀ i : s, M i) := by
  classical
  let f : (∀ i, M i) → (∀ i : s, M i) := fun x i => x i
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    funext i
    by_cases hi : i ∈ s
    · exact congrFun hxy ⟨i, hi⟩
    · exact @Subsingleton.elim _ (h i hi) (x i) (y i)
  · intro y
    refine ⟨(fun i => if hi : i ∈ s then y ⟨i, hi⟩ else default), ?_⟩
    funext i
    simp [f, i.2]

/-- The cardinality of a product with subsingleton factors outside a finite set is the product
of the remaining cardinalities; used by `herbrandQuotient_pi_of_subsingleton_outside`. -/
private theorem card_pi_of_subsingleton_outside {M : ι → Type*} [∀ i, Inhabited (M i)]
    (s : Finset ι) (h : ∀ i, i ∉ s → Subsingleton (M i)) :
    Nat.card (∀ i, M i) = ∏ i ∈ s, Nat.card (M i) := by
  classical
  rw [Nat.card_congr (piSubtypeEquivOfSubsingleton s h), Nat.card_pi]
  exact (Finset.prod_subtype s (fun _ => Iff.rfl) (fun i => Nat.card (M i))).symm

/-- The Herbrand quotient of a product with vanishing Tate groups outside a finite set is the
product over that set. -/
theorem herbrandQuotient_pi_of_subsingleton_outside
    (ρ : ∀ i, _root_.Representation k G (V i)) (s : Finset ι)
    (hZero : ∀ i, i ∉ s → Subsingleton (TateZero (ρ i)))
    (hNegOne : ∀ i, i ∉ s → Subsingleton (TateNegOne (ρ i))) :
    herbrandQuotient (pi ρ) = ∏ i ∈ s, herbrandQuotient (ρ i) := by
  unfold herbrandQuotient
  rw [Nat.card_congr (tateZeroPiEquiv ρ).toEquiv,
    Nat.card_congr (tateNegOnePiEquiv ρ).toEquiv,
    card_pi_of_subsingleton_outside s hZero,
    card_pi_of_subsingleton_outside s hNegOne]
  simp only [Nat.cast_prod, ← Finset.prod_div_distrib]

/-- The Herbrand quotient of a finite product is the product of the Herbrand quotients.
Milne, *Class Field Theory*, Chapter II, Proposition 1.25 and §3. -/
theorem herbrandQuotient_pi [Fintype ι]
    (ρ : ∀ i, _root_.Representation k G (V i)) :
    herbrandQuotient (pi ρ) = ∏ i, herbrandQuotient (ρ i) := by
  simpa using (herbrandQuotient_pi_of_subsingleton_outside ρ Finset.univ
    (by simp) (by simp))

/-! ### Binary products

For `ρ.prod σ`, the norm, invariant and augmentation submodules are componentwise. The quotient
of a product submodule by a product submodule then gives both binary Tate equivalences. -/

universe u v
section BinaryProducts
variable {C : Type u} {D : Type v} [AddCommGroup C] [Module k C]
  [AddCommGroup D] [Module k D]

/-- The norm of a binary product is componentwise; used by the binary Tate equivalences. -/
@[simp] theorem norm_prod_apply (ρ : _root_.Representation k G C)
    (σ : _root_.Representation k G D) (x : C × D) :
    (ρ.prod σ).norm x = (ρ.norm x.1, σ.norm x.2) := by
  apply Prod.ext
  · simp [_root_.Representation.norm, _root_.Representation.prod_apply_apply,
      Prod.fst_sum]
  · simp [_root_.Representation.norm, _root_.Representation.prod_apply_apply,
      Prod.snd_sum]

/-- The product norm is the product of the component norms; used by the range and kernel
formulas below. -/
private theorem norm_prod (ρ : _root_.Representation k G C)
    (σ : _root_.Representation k G D) :
    (ρ.prod σ).norm = ρ.norm.prodMap σ.norm := by
  apply LinearMap.ext
  intro x
  exact norm_prod_apply ρ σ x

omit [Fintype G] in
/-- Product invariants form the product of the invariant submodules; used by
`tateZeroProdEquiv`. -/
private theorem invariants_prod (ρ : _root_.Representation k G C)
    (σ : _root_.Representation k G D) :
    (ρ.prod σ).invariants = ρ.invariants.prod σ.invariants := by
  ext ⟨x, y⟩
  simp only [Submodule.mem_prod, _root_.Representation.mem_invariants]
  constructor
  · intro h
    constructor
    · intro g
      exact congrArg Prod.fst (h g)
    · intro g
      exact congrArg Prod.snd (h g)
  · rintro ⟨hx, hy⟩ g
    exact Prod.ext (hx g) (hy g)

/-- The range of a product norm is the product of the norm ranges; used by
`tateZeroProdEquiv`. -/
private theorem range_norm_prod (ρ : _root_.Representation k G C)
    (σ : _root_.Representation k G D) :
    LinearMap.range (ρ.prod σ).norm =
      (LinearMap.range ρ.norm).prod (LinearMap.range σ.norm) := by
  rw [norm_prod, LinearMap.range_prodMap]

/-- The kernel of a product norm is the product of the norm kernels; used by
`tateNegOneProdEquiv`. -/
private theorem ker_norm_prod (ρ : _root_.Representation k G C)
    (σ : _root_.Representation k G D) :
    LinearMap.ker (ρ.prod σ).norm =
      (LinearMap.ker ρ.norm).prod (LinearMap.ker σ.norm) := by
  rw [norm_prod, LinearMap.ker_prodMap]

omit [Fintype G] in
/-- The augmentation submodule of a binary product is the product of the augmentation
submodules; used by `tateNegOneProdEquiv`. -/
private theorem coinvariantsKer_prod [Finite G] (ρ : _root_.Representation k G C)
    (σ : _root_.Representation k G D) :
    _root_.Representation.Coinvariants.ker (ρ.prod σ) =
      (_root_.Representation.Coinvariants.ker ρ).prod
        (_root_.Representation.Coinvariants.ker σ) := by
  have : Fintype G := Fintype.ofFinite G
  ext ⟨x, y⟩
  simp only [Submodule.mem_prod]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (mem_coinvariantsKer_iff_exists_sum (ρ.prod σ) (x, y)).1 h
    constructor
    · apply (mem_coinvariantsKer_iff_exists_sum ρ x).2
      refine ⟨fun g => (z g).1, ?_⟩
      simpa [_root_.Representation.prod_apply_apply, Prod.fst_sum, Prod.snd_sum,
        Finset.sum_sub_distrib] using congrArg Prod.fst hz
    · apply (mem_coinvariantsKer_iff_exists_sum σ y).2
      refine ⟨fun g => (z g).2, ?_⟩
      simpa [_root_.Representation.prod_apply_apply, Prod.fst_sum, Prod.snd_sum,
        Finset.sum_sub_distrib] using congrArg Prod.snd hz
  · rintro ⟨hx, hy⟩
    obtain ⟨a, ha⟩ := (mem_coinvariantsKer_iff_exists_sum ρ x).1 hx
    obtain ⟨b, hb⟩ := (mem_coinvariantsKer_iff_exists_sum σ y).1 hy
    apply (mem_coinvariantsKer_iff_exists_sum (ρ.prod σ) (x, y)).2
    refine ⟨fun g => (a g, b g), ?_⟩
    apply Prod.ext
    · simpa [_root_.Representation.prod_apply_apply, Prod.fst_sum, Prod.snd_sum,
        Finset.sum_sub_distrib] using ha
    · simpa [_root_.Representation.prod_apply_apply, Prod.fst_sum, Prod.snd_sum,
        Finset.sum_sub_distrib] using hb

/-- A quotient by a product of submodules is the product of the quotients; used by both binary
Tate equivalences. -/
private def quotientProdEquiv {M : Type*} {N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (p : Submodule k M) (q : Submodule k N) :
    ((M × N) ⧸ p.prod q) ≃ₗ[k] (M ⧸ p) × (N ⧸ q) := by
  let f := p.mkQ.prodMap q.mkQ
  have hf : Function.Surjective f := by
    rintro ⟨x, y⟩
    obtain ⟨a, rfl⟩ := p.mkQ_surjective x
    obtain ⟨b, rfl⟩ := q.mkQ_surjective y
    exact ⟨(a, b), rfl⟩
  have hker : LinearMap.ker f = p.prod q := by simp [f]
  exact (Submodule.Quotient.equiv (p.prod q) (LinearMap.ker f)
    (LinearEquiv.refl k _) (by simp [hker])).trans
      (f.quotKerEquivOfSurjective hf)

/-- Quotients of componentwise submodules by componentwise denominators form a binary product;
used by both binary Tate equivalences. -/
private def submoduleQuotientProdEquiv {M : Type*} {N : Type*} [AddCommGroup M]
    [Module k M] [AddCommGroup N] [Module k N]
    (P : Submodule k (M × N)) (p : Submodule k M) (q : Submodule k N)
    (e : P ≃ₗ[k] p × q) (Q : Submodule k P)
    (r : Submodule k p) (s : Submodule k q)
    (hQ : ∀ x : P, x ∈ Q ↔ e x ∈ r.prod s) :
    (P ⧸ Q) ≃ₗ[k] (p ⧸ r) × (q ⧸ s) := by
  have he : Q.map (e : P →ₗ[k] p × q) = r.prod s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hQ y).1 hy
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      exact (hQ _).2 (by simpa using hx)
  exact (Submodule.Quotient.equiv Q (r.prod s) e he).trans
    (quotientProdEquiv r s)

end BinaryProducts

/-- Degree-zero Tate cohomology of a binary product is the product of its Tate groups.
Milne, *Class Field Theory*, Chapter II, Proposition 1.25 and §3. -/
def tateZeroProdEquiv {C : Type u} {D : Type v}
    [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]
    (ρ : _root_.Representation k G C)
    (σ : _root_.Representation k G D) :
    TateZero (ρ.prod σ) ≃ₗ[k] TateZero ρ × TateZero σ := by
  let e := (LinearEquiv.ofEq (ρ.prod σ).invariants
    (ρ.invariants.prod σ.invariants) (invariants_prod ρ σ)).trans
      (Submodule.prodEquiv ρ.invariants σ.invariants)
  refine submoduleQuotientProdEquiv _ _ _ e _ _ _ ?_
  intro x
  change (x : C × D) ∈ LinearMap.range (ρ.prod σ).norm ↔
    ((e x).1 : C) ∈ LinearMap.range ρ.norm ∧
      ((e x).2 : D) ∈ LinearMap.range σ.norm
  rw [range_norm_prod]
  rfl

/-- Degree-minus-one Tate cohomology of a binary product is the product of its Tate groups.
Milne, *Class Field Theory*, Chapter II, Proposition 1.25 and §3. -/
def tateNegOneProdEquiv {C : Type u} {D : Type v}
    [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]
    (ρ : _root_.Representation k G C)
    (σ : _root_.Representation k G D) :
    TateNegOne (ρ.prod σ) ≃ₗ[k] TateNegOne ρ × TateNegOne σ := by
  let e := (LinearEquiv.ofEq (LinearMap.ker (ρ.prod σ).norm)
    ((LinearMap.ker ρ.norm).prod (LinearMap.ker σ.norm)) (ker_norm_prod ρ σ)).trans
      (Submodule.prodEquiv (LinearMap.ker ρ.norm) (LinearMap.ker σ.norm))
  refine submoduleQuotientProdEquiv _ _ _ e _ _ _ ?_
  intro x
  change (x : C × D) ∈ _root_.Representation.Coinvariants.ker (ρ.prod σ) ↔
    ((e x).1 : C) ∈ _root_.Representation.Coinvariants.ker ρ ∧
      ((e x).2 : D) ∈ _root_.Representation.Coinvariants.ker σ
  rw [coinvariantsKer_prod]
  rfl

/-- The Herbrand quotient of a binary product is the product of the two Herbrand
quotients, by the same Tate equivalences as `herbrandQuotient_pi`. -/
theorem herbrandQuotient_prod {C : Type u} {D : Type v}
    [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]
    (ρ : _root_.Representation k G C)
    (σ : _root_.Representation k G D) :
    herbrandQuotient (ρ.prod σ) = herbrandQuotient ρ * herbrandQuotient σ := by
  unfold herbrandQuotient
  rw [Nat.card_congr (tateZeroProdEquiv ρ σ).toEquiv,
    Nat.card_congr (tateNegOneProdEquiv ρ σ).toEquiv, Nat.card_prod, Nat.card_prod]
  push_cast
  exact mul_div_mul_comm _ _ _ _
end SIC.Representation
