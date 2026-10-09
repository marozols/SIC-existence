/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Orbits, stabilizers, and products for group actions

Three facts about a group acting on a set, used for the decomposition groups of places: an
invariant quantity on a single orbit whose values add up to the order of the group equals the
orders of the stabilizers; the elements carrying one point of an orbit to another form a coset of
a stabilizer; and a product over the group regroups by the point each element carries to a fixed
point of the orbit.

These are the counting steps of Serre, *Local Fields*, Chapter II, §3, Corollary 4, and of
Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, §2, before Lemma 2.1 and "The
norm map on idèles", where the decomposition group $G_w$ of a place `w` above `v` is identified
with $\operatorname{Gal}(L_w/K_v)$ and the norm of an idèle with the product of its conjugates.
They are applied in `SICs.ClassField.Completion.FiniteDecomposition`,
`SICs.ClassField.Completion.InfiniteDecomposition`, and `SICs.ClassField.Ideles.Galois`.

## The argument

If the orbit of `p i` is the image of an injective `p : ι → X`, the orbit-stabilizer theorem
gives $|\iota| \cdot |G_{p i}| = |G|$; a constant `f : ι → ℕ` with $\sum_i f(i) = |G|$ then
satisfies $f(i) = |G_{p i}|$. If $\tau x' = x$, then $\sigma x' = x$ exactly when
$\tau^{-1}\sigma$ fixes $x'$, so $\delta \mapsto \tau\delta$ identifies $G_{x'}$ with these
elements. Finally, every $\sigma \in G$ carries exactly one point `p i` of the orbit to `x`,
namely $p(i) = \sigma^{-1} x$, so `G` is the disjoint union of the sets
$\{\sigma \mid \sigma\, p(i) = x\}$.
-/

namespace SIC

/-! ### Stabilizers of an orbit -/

/-- A constant `f : ι → ℕ` on an orbit `p : ι → X` whose values add up to $|G|$ is the order of
the stabilizers: $f(i) = |G_{p(i)}|$. -/
theorem eq_card_stabilizer_of_sum_eq_card {G X ι : Type*} [Group G] [MulAction G X]
    [Fintype ι] (p : ι → X) (hp : Function.Injective p)
    (horbit : ∀ i, MulAction.orbit G (p i) = Set.range p) (f : ι → ℕ) (hf : ∀ i j, f i = f j)
    (hsum : ∑ i, f i = Nat.card G) (i : ι) :
    f i = Nat.card (MulAction.stabilizer G (p i)) := by
  have hindex : (MulAction.stabilizer G (p i)).index = Fintype.card ι := by
    rw [MulAction.index_stabilizer, horbit i, Set.ncard_range_of_injective hp]
    simp
  have hsum' : Fintype.card ι * f i = Nat.card G := by
    simpa [Finset.sum_const_nat (s := Finset.univ) (m := f i)
      (fun j _ ↦ hf j i)] using hsum
  have hcard := (MulAction.stabilizer G (p i)).card_mul_index
  rw [hindex] at hcard
  rw [mul_comm] at hsum'
  exact Nat.mul_right_cancel (Fintype.card_pos_iff.mpr ⟨i⟩) (hsum'.trans hcard.symm)

/-- If `τ` carries `x'` to `x`, left multiplication by `τ` identifies the stabilizer of `x'`
with the elements carrying `x'` to `x`: $G_{x'} \cong \tau G_{x'}$. -/
def stabilizerEquivSmulEq {G X : Type*} [Group G] [MulAction G X] {x x' : X} (τ : G)
    (hτ : τ • x' = x) : MulAction.stabilizer G x' ≃ {σ : G // σ • x' = x} where
  toFun δ := ⟨τ * δ, by rw [mul_smul, MulAction.mem_stabilizer_iff.mp δ.2, hτ]⟩
  invFun σ := ⟨τ⁻¹ * σ, by
    apply MulAction.mem_stabilizer_iff.mpr
    rw [mul_smul, σ.2, ← hτ, inv_smul_smul]⟩
  left_inv δ := by
    apply Subtype.ext
    simp
  right_inv σ := by
    apply Subtype.ext
    simp

/-- The element attached to `δ` by `stabilizerEquivSmulEq` is `τ δ`. -/
@[simp]
theorem coe_stabilizerEquivSmulEq_apply {G X : Type*} [Group G] [MulAction G X] {x x' : X}
    (τ : G) (hτ : τ • x' = x) (δ : MulAction.stabilizer G x') :
    (stabilizerEquivSmulEq τ hτ δ : G) = τ * δ :=
  rfl

/-! ### Products regrouped by an orbit -/

/-- Grouping a product over `G` by the point of an orbit that each element carries to `x`:
$\prod_{\sigma \in G} f(\sigma) = \prod_i \prod_{\sigma \cdot p(i) = x} f(\sigma)$, when every
$\sigma^{-1} x$ is one of the distinct points `p i`. -/
theorem prod_eq_prod_prod_smul_eq {G X ι M : Type*} [Group G] [Fintype G] [MulAction G X]
    [Fintype ι] [CommMonoid M] (p : ι → X) (hp : Function.Injective p) {x : X}
    (horbit : ∀ σ : G, ∃ i, σ • p i = x) [∀ i, Fintype {σ : G // σ • p i = x}]
    (f : G → M) :
    ∏ σ, f σ = ∏ i, ∏ σ : {σ : G // σ • p i = x}, f σ := by
  classical
  choose g hg using horbit
  have key (σ : G) (i : ι) : g σ = i ↔ σ • p i = x :=
    ⟨fun h ↦ h ▸ hg σ, fun h ↦ hp ((smul_left_cancel_iff σ).mp ((hg σ).trans h.symm))⟩
  rw [← Fintype.prod_fiberwise g f]
  exact Fintype.prod_congr _ _ fun i ↦
    Fintype.prod_equiv (Equiv.subtypeEquivRight (key · i)) _ _ fun _ ↦ rfl

end SIC
