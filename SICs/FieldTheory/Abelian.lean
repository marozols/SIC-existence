/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Solvable

/-!
# Cyclic subextensions and prime-codegree induction

Finite solvable Galois extensions have nontrivial cyclic subextensions. Finite abelian Galois
extensions also support induction through prime-codegree subfields, and cyclic subextensions
separate automorphisms.

This module follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, proof of
Proposition 4.6 and Lemma 5.4, and Childress, *Class Field Theory* (2009),
Chapter V, proof of Theorem 2.1(ii),
p. 114. The two field-theory results supply the tower induction for the second inequality and
the cyclic reduction for reciprocity moduli, respectively.

## The argument

For a nontrivial finite solvable Galois group, the commutator subgroup is proper.
A maximal subgroup containing it is normal with a nontrivial cyclic quotient, whose fixed
field is a nontrivial cyclic subextension.

For a nontrivial finite Galois extension $L/K$, Cauchy's theorem gives an element of prime order
$p$ in $\operatorname{Gal}(L/K)$. Its fixed field $E$ has $[L:E]=p$. For abelian $L/K$, every
intermediate field $E/K$ is abelian; induction on $[L:K]$ can therefore pass from $E$ to $L$.
Milne's induction instead takes a subgroup of index $p$; the prime-codegree version keeps the
base field fixed at the top step.

For cyclic separation, decompose the finite abelian Galois group into cyclic factors. If
$g\ne 1$, some coordinate of $g$ is nontrivial. The kernel $H$ of that coordinate has cyclic
quotient and misses $g$, so $E=L^H$ is cyclic over $K$ and $g$ acts nontrivially on $E$.
-/

namespace SIC

/-! ### Cyclic subextensions of solvable extensions

A maximal subgroup containing the commutator gives a nontrivial cyclic quotient.
Galois correspondence turns it into a cyclic subextension. -/

open scoped IsMulCommutative in
/-- A nontrivial finite solvable group has a nontrivial cyclic quotient. This is the finite
group step used in `exists_cyclic_subextension`, as in Milne's proof of Lemma 4.5. -/
theorem exists_cyclic_quotient (G : Type*) [Group G] [Finite G]
    [Group.IsSolvable G] [Nontrivial G] :
    ∃ (N : Subgroup G) (_ : N.Normal), Nontrivial (G ⧸ N) ∧ IsCyclic (G ⧸ N) := by
  obtain ⟨N, hN, hle⟩ := (eq_top_or_exists_le_coatom (commutator G)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial G).ne
  have : N.Normal := Subgroup.Normal.of_commutator_le G hle
  have : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hN.ne_top
  have : IsMulCommutative (G ⧸ N) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hle
  have : IsSimpleOrder (Subgroup (G ⧸ N)) :=
    (QuotientGroup.comapMk'OrderIso N).isSimpleOrder_iff.mpr
      (Set.isSimpleOrder_Ici_iff_isCoatom.mpr hN)
  have : IsSimpleGroup (G ⧸ N) := ⟨fun H _ => IsSimpleOrder.eq_bot_or_eq_top H⟩
  exact ⟨N, inferInstance, inferInstance, inferInstance⟩

/-- A nontrivial solvable Galois extension has a nontrivial cyclic subextension. This is the
Galois-correspondence step in Milne, *Class Field Theory*, Chapter VII, proof of Lemma 4.5. -/
theorem exists_cyclic_subextension {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Group.IsSolvable (L ≃ₐ[K] L)]
    (hdegree : Module.finrank K L ≠ 1) :
    ∃ E : IntermediateField K L,
      IsGalois K E ∧ IsCyclic (E ≃ₐ[K] E) ∧ Module.finrank K E ≠ 1 := by
  have : Nontrivial (L ≃ₐ[K] L) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [IsGalois.card_aut_eq_finrank]
    exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Module.finrank_pos.ne', hdegree⟩)
  obtain ⟨N, hN, hnontrivial, hcyclic⟩ := exists_cyclic_quotient (L ≃ₐ[K] L)
  let e := IsGalois.normalAutEquivQuotient N
  have : IsGalois K (IntermediateField.fixedField N) :=
    IsGalois.of_fixedField_normal_subgroup N
  have : IsCyclic ((IntermediateField.fixedField N) ≃ₐ[K] (IntermediateField.fixedField N)) :=
    isCyclic_of_surjective e.toMonoidHom e.surjective
  have : Nontrivial ((IntermediateField.fixedField N) ≃ₐ[K] (IntermediateField.fixedField N)) :=
    e.symm.toEquiv.nontrivial
  refine ⟨IntermediateField.fixedField N, inferInstance, inferInstance, ?_⟩
  rw [← IsGalois.card_aut_eq_finrank]
  exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne'


/-! ### Induction through a subfield of prime codegree

A prime-order subgroup gives the top step of an abelian-extension induction. The smaller field
remains abelian over the original base field. -/

/-- A finite Galois extension of degree greater than one has an intermediate field $E$ with
$[L:E]$ prime: the fixed field of an element of prime order. This is the subgroup step of the
induction in Milne, *Class Field Theory*, Chapter VII, proof of Lemma 5.4, with a subgroup of
prime order in place of one of prime index. -/
theorem exists_intermediateField_finrank_eq_prime {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (h : 1 < Module.finrank K L) :
    ∃ p : ℕ, p.Prime ∧ ∃ E : IntermediateField K L, Module.finrank E L = p := by
  classical
  have hcard : Nat.card (L ≃ₐ[K] L) ≠ 1 := by
    rw [IsGalois.card_aut_eq_finrank]
    omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  refine ⟨p, hp, IntermediateField.fixedField (Subgroup.zpowers g), ?_⟩
  rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hg]

universe u in
/-- **Induction through prime codegree**: a property of finite abelian extensions of a field
$K$ in one universe holds for all of them if it holds in degree one and passes from an
intermediate field $E$ to $L$ whenever $[L:E]$ is prime. This is the induction of Milne, *Class
Field Theory*, Chapter VII, proof of Lemma 5.4, through
`exists_intermediateField_finrank_eq_prime`. -/
theorem IsAbelianGalois.induction_finrank_prime {K : Type*} [Field K]
    {P : ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L], Prop}
    (one : ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
      [IsAbelianGalois K L], Module.finrank K L = 1 → P L)
    (step : ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
      [IsAbelianGalois K L] (E : IntermediateField K L),
      (Module.finrank E L).Prime → P E → P L)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] :
    P L := by
  classical
  generalize hn : Module.finrank K L = n
  induction n using Nat.strong_induction_on generalizing L with
  | h n ih =>
    by_cases hone : n = 1
    · exact one L (hn.trans hone)
    · have hgt : 1 < Module.finrank K L := by
        have hpos : 0 < n := by rw [← hn]; exact Module.finrank_pos
        omega
      obtain ⟨p, hp, E, hEp⟩ := exists_intermediateField_finrank_eq_prime hgt
      have hdegree : Module.finrank K E * p = n := by
        rw [← hEp, Module.finrank_mul_finrank, hn]
      have hlt : Module.finrank K E < n := by
        nlinarith [Module.finrank_pos (R := K) (M := E), hp.two_le]
      exact step L E (hEp ▸ hp) (ih (Module.finrank K E) hlt (L := E) rfl)

/-! ### Separation by cyclic subextensions

A nonidentity automorphism has a nontrivial coordinate in a cyclic decomposition of the Galois
group. The coordinate kernel defines a cyclic fixed-field quotient where it remains nontrivial.
-/

section

open scoped IsMulCommutative

/-- For `IsAbelianGalois.eq_one_of_forall_isCyclic`: a nonidentity automorphism survives in a
cyclic fixed-field quotient, as in Childress, Chapter V, proof of Theorem 2.1(ii). -/
private theorem exists_cyclic_subextension_separating {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    {g : L ≃ₐ[K] L} (hg : g ≠ 1) :
    ∃ E : IntermediateField K L, IsCyclic (E ≃ₐ[K] E) ∧ g.restrictNormal E ≠ 1 := by
  classical
  let G := L ≃ₐ[K] L
  obtain ⟨ι, _, n, _, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  obtain ⟨i, hi⟩ : ∃ i : ι, e g i ≠ 1 := by
    by_contra hn
    apply hg
    apply e.injective
    funext i
    simp only [not_exists, not_not] at hn
    simpa using hn i
  let φ : G →* Multiplicative (ZMod (n i)) :=
    (Pi.evalMonoidHom (fun i : ι ↦ Multiplicative (ZMod (n i))) i).comp e.toMonoidHom
  let H : Subgroup G := φ.ker
  have hnot : g ∉ H := by
    change φ g ≠ 1
    simpa [φ, Pi.evalMonoidHom_apply] using hi
  have hcyc : IsCyclic (G ⧸ H) :=
    isCyclic_of_injective (QuotientGroup.kerLift φ) (QuotientGroup.kerLift_injective φ)
  let E : IntermediateField K L := IntermediateField.fixedField H
  refine ⟨E, isCyclic_of_surjective (IsGalois.normalAutEquivQuotient H).toMonoidHom
      (IsGalois.normalAutEquivQuotient H).surjective, ?_⟩
  intro he
  apply hnot
  rw [← IntermediateField.fixingSubgroup_fixedField H]
  exact (IntermediateField.mem_fixingSubgroup_iff E g).mpr
    ((AlgEquiv.restrictNormal_eq_one_iff E g).mp he)

end

/-- **Cyclic subextensions separate automorphisms**: an automorphism of a finite abelian
extension that is trivial on every cyclic subextension is trivial. Childress, *Class Field
Theory*, Chapter V, proof of Theorem 2.1(ii), p. 114, by characters of the Galois group. -/
theorem IsAbelianGalois.eq_one_of_forall_isCyclic {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] {g : L ≃ₐ[K] L}
    (h : ∀ E : IntermediateField K L, IsCyclic (E ≃ₐ[K] E) → g.restrictNormal E = 1) :
    g = 1 := by
  by_contra hg
  obtain ⟨E, hcyc, hne⟩ := exists_cyclic_subextension_separating hg
  exact hne (h E hcyc)

end SIC
