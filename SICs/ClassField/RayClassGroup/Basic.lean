/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.RealFields
import SICs.DedekindDomain.Ideals

/-!
# The ray class group of the Stark modulus

The monoid of integral ray ideals and the ray-principal congruence on it, the ray class group
presentation interface with the trivial class of the unit ideal, and the triviality of every
presentation at the bottom finite modulus.

This module defines the relational interface for the ray class group `Cl_(m * infinity_2)(O_K)`
of [AFK25, Definition 2.1, `defn:rayclassgroup`], in the maximal-order case with the real places
other than the distinguished one; for a real quadratic field this is precisely the modulus
`m * infinity_2` of [AFK25, Conjecture 2.7, `conj:stark`].

The interface is relational rather than computational: integral ideals coprime to `m` map onto
an abstract commutative group, and equality there is characterized exactly by ray-principal
equivalence with positivity at the non-selected real place. Surjectivity, the equality criterion,
and multiplicativity determine the group up to unique isomorphism; that uniqueness is not
formalized.
The coprimality lemmas for principal ideals are in `SICs.DedekindDomain.Ideals`. The integral
ray ideals form a commutative monoid under ideal multiplication, and the
ray-principal relation is an equivalence relation and a congruence for it
(`RayIdeal.IsEquivalent.refl`, `RayIdeal.IsEquivalent.symm`, `RayIdeal.IsEquivalent.trans`,
`RayIdeal.IsEquivalent.mul`); `SICs.ClassField.RayClassGroup.Quotient` constructs the group as the
quotient by this congruence. A Bézout inverse of one generator modulo `m` supplies a common
nonzero multiplier that makes both ray-congruent generators separately congruent to `1`; this is
the normalized witness form used by the idèle/ideal comparison.

At the bottom finite modulus, coprimality forces every ray ideal to be the unit ideal, so every
presentation there is trivial.
-/

noncomputable section

open NumberField

namespace SIC

/-! ### Integral ray ideals and the presentation interface

The quotient of [AFK25, Definition 2.1, `defn:rayclassgroup`] is represented relationally:
integral ideals coprime to `m` map onto an abstract commutative group, and equality there is
characterized exactly by ray-principal equivalence with positivity at the non-selected real
place. The integral ideals coprime to `𝔪` are the integral members of the group `J^𝔪` of
[83, Neukirch (1999), Chapter VI, §1, p. 365]; they form the submonoid `rayIdeals K m` of the
ideals of `𝒪_K`, and the ray-principal relation `RayIdeal.IsEquivalent` is a congruence on it,
expressed through the multiplicative ray congruence `RayCongruent` of generators. -/

/-- **The nonzero integral ideals coprime to `𝔪`**, as a submonoid of `Ideal (𝒪_K)`: the
integral members of `J^𝔪` [83, Neukirch (1999), Chapter VI, §1, p. 365], the integral
representatives used in `Cl_(m * infinity_2)(O_K)`. The unit ideal belongs to it
(`isCoprime_top_left`), and a product of two members is nonzero and coprime to `𝔪`. -/
def rayIdeals (K : Type*) [Field K] (m : Ideal (NumberField.RingOfIntegers K)) :
    Submonoid (Ideal (NumberField.RingOfIntegers K)) where
  carrier := {I | I ≠ ⊥ ∧ IsCoprime I m}
  one_mem' := ⟨by rw [Ideal.one_eq_top]; exact top_ne_bot,
    by rw [Ideal.one_eq_top]; exact isCoprime_top_left⟩
  mul_mem' {I J} hI hJ :=
    ⟨by rw [Ne, Ideal.mul_eq_bot, not_or]; exact ⟨hI.1, hJ.1⟩, hI.2.mul_left hJ.2⟩

/-- A nonzero integral ideal coprime to the finite modulus `𝔪`: an element of `rayIdeals K m`,
with the commutative monoid structure of the submonoid (`Submonoid.coe_mul`, `RayIdeal.coe_one`). -/
abbrev RayIdeal (K : Type*) [Field K] (m : Ideal (NumberField.RingOfIntegers K)) : Type _ :=
  rayIdeals K m

section RayIdealAPI

variable {K : Type*} [Field K] {m : Ideal (NumberField.RingOfIntegers K)}

/-- A ray ideal is nonzero. -/
theorem RayIdeal.ne_bot (I : RayIdeal K m) : (I : Ideal (NumberField.RingOfIntegers K)) ≠ ⊥ :=
  I.2.1

/-- A ray ideal is coprime to `𝔪`. -/
theorem RayIdeal.isCoprime (I : RayIdeal K m) :
    IsCoprime (I : Ideal (NumberField.RingOfIntegers K)) m :=
  I.2.2

/-- The unit ray ideal is `𝒪_K`. -/
@[simp] theorem RayIdeal.coe_one :
    ((1 : RayIdeal K m) : Ideal (NumberField.RingOfIntegers K)) = ⊤ :=
  Ideal.one_eq_top

end RayIdealAPI

/-! ### The bottom finite modulus

At the bottom ideal, coprimality forces every ray ideal to be the unit ideal. These elementary
facts make every presentation at the bottom modulus trivial. -/

/-- Every ray ideal coprime to the bottom modulus is the unit ideal as an ideal. -/
theorem RayIdeal.coe_eq_top_of_modulus_bot
    {K : Type*} [Field K]
    (I : RayIdeal K (⊥ : Ideal (NumberField.RingOfIntegers K))) :
    (I : Ideal (NumberField.RingOfIntegers K)) = ⊤ := by
  simpa only [sup_bot_eq] using
    (Ideal.isCoprime_iff_sup_eq.mp I.isCoprime)

/-- Every ray ideal at the bottom modulus is the unit of the ray-ideal monoid. -/
theorem RayIdeal.eq_one_of_modulus_bot
    {K : Type*} [Field K]
    (I : RayIdeal K (⊥ : Ideal (NumberField.RingOfIntegers K))) : I = 1 := by
  apply Subtype.ext
  rw [RayIdeal.coe_one]
  exact I.coe_eq_top_of_modulus_bot

/-! ### The multiplicative ray congruence of generators

For `a, b ∈ 𝒪_K`, `RayCongruent F m a b` says that `a/b` is `≡ 1 (mod 𝔪)` in the multiplicative
sense of [83, Neukirch (1999), Chapter VI, §1, p. 365] ("the quotient `b/c` of two integers
relatively prime to `𝔪` such that `b ≡ c (mod 𝔪)`") and positive at `∞₂`: the condition on a
generator of an ideal of `P_{𝔪∞₂}` [AFK25, Definition 2.1, `defn:rayclassgroup`]. It is
reflexive on nonzero generators coprime to `𝔪`, symmetric, and multiplicative. -/

section RayCongruent

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
  {F : RealQuadraticFieldData K} {m : Ideal (NumberField.RingOfIntegers K)}

variable (F m) in
/-- **The multiplicative ray congruence** `a/b ≡ 1 (mod^× 𝔪∞₂)`: `(a)` is coprime to `𝔪`,
`a ≡ b (mod 𝔪)`, and `ρ_w(a)ρ_w(b) > 0` at every real place `w` other than the selected one, so
that `a/b ≡ 1 (mod 𝔪)` in the multiplicative sense of [83, Neukirch (1999), Chapter VI, §1,
p. 365] and `a/b > 0` at `∞₂`, the condition on a generator of an ideal of `P_{𝔪∞₂}`
[AFK25, Definition 2.1, `defn:rayclassgroup`]. Coprimality of `(b)` and `a, b ≠ 0` follow
(`RayCongruent.isCoprime_right`, `RayCongruent.ne_zero_left`, `RayCongruent.ne_zero_right`). -/
structure RayCongruent (a b : NumberField.RingOfIntegers K) : Prop where
  /-- `(a)` is coprime to `𝔪`. -/
  isCoprime : IsCoprime (Ideal.span {a}) m
  /-- `a ≡ b (mod 𝔪)`. -/
  sub_mem : a - b ∈ m
  /-- `ρ_w(a)ρ_w(b) > 0` at every real place `w ≠ ∞₁`, that is, at `∞₂`. -/
  pos : ∀ w : InfinitePlace K, w ≠ F.place →
    0 < realEmbeddingAt K w (a : K) * realEmbeddingAt K w (b : K)

/-- `(b)` is coprime to `𝔪` as well, since `b ≡ a (mod 𝔪)`
(`isCoprime_span_singleton_of_sub_mem`). -/
theorem RayCongruent.isCoprime_right {a b : NumberField.RingOfIntegers K}
    (h : RayCongruent F m a b) : IsCoprime (Ideal.span {b}) m := by
  apply isCoprime_span_singleton_of_sub_mem h.isCoprime
  simpa only [neg_sub] using m.neg_mem h.sub_mem

/-- `a ≠ 0`, since `ρ_w(a)ρ_w(b) > 0` at the other real place
(`RealQuadraticFieldData.exists_ne_place`). -/
theorem RayCongruent.ne_zero_left {a b : NumberField.RingOfIntegers K}
    (h : RayCongruent F m a b) : a ≠ 0 := by
  obtain ⟨w, hw⟩ := F.exists_ne_place
  intro ha
  simpa only [ha, map_zero, zero_mul, lt_self_iff_false] using h.pos w hw

/-- `b ≠ 0`, since `ρ_w(a)ρ_w(b) > 0` at the other real place. -/
theorem RayCongruent.ne_zero_right {a b : NumberField.RingOfIntegers K}
    (h : RayCongruent F m a b) : b ≠ 0 := by
  obtain ⟨w, hw⟩ := F.exists_ne_place
  intro hb
  simpa only [hb, map_zero, mul_zero, lt_self_iff_false] using h.pos w hw

/-- `RayCongruent F m a a` for every nonzero `a` with `(a)` coprime to `𝔪`. -/
protected theorem RayCongruent.refl {a : NumberField.RingOfIntegers K} (ha : a ≠ 0)
    (hcop : IsCoprime (Ideal.span {a}) m) : RayCongruent F m a a := by
  refine ⟨hcop, by simp only [sub_self, Submodule.zero_mem], fun w _ => ?_⟩
  exact mul_self_pos.mpr (realEmbeddingAt_coe_ne_zero ha w)

/-- The congruence `1 ≡ 1`, the witnesses of `RayIdeal.IsEquivalent.refl`. -/
protected theorem RayCongruent.one : RayCongruent F m 1 1 :=
  RayCongruent.refl one_ne_zero isCoprime_span_singleton_one

/-- Symmetry: `b/a ≡ 1` when `a/b ≡ 1`. -/
protected theorem RayCongruent.symm {a b : NumberField.RingOfIntegers K}
    (h : RayCongruent F m a b) : RayCongruent F m b a := by
  refine ⟨h.isCoprime_right, ?_, fun w hw => ?_⟩
  · simpa only [neg_sub] using m.neg_mem h.sub_mem
  · simpa only [mul_comm] using h.pos w hw

/-- **Multiplicativity**: `aa'/bb' ≡ 1` when `a/b ≡ 1` and `a'/b' ≡ 1`; the witnesses of
`RayIdeal.IsEquivalent.trans` and `RayIdeal.IsEquivalent.mul`. -/
protected theorem RayCongruent.mul {a b a' b' : NumberField.RingOfIntegers K}
    (h : RayCongruent F m a b) (h' : RayCongruent F m a' b') :
    RayCongruent F m (a * a') (b * b') := by
  refine ⟨?_, m.mul_sub_mul_mem h.sub_mem h'.sub_mem, fun w hw => ?_⟩
  · rw [← Ideal.span_singleton_mul_span_singleton]
    exact h.isCoprime.mul_left h'.isCoprime
  · simpa only [map_mul, mul_mul_mul_comm] using mul_pos (h.pos w hw) (h'.pos w hw)

/-- **Common normalization of ray-congruent generators.** Multiplying both generators by one
nonzero integer makes each congruent to `1` modulo `m`, without changing their multiplicative ray
congruence. This is the normalization in Milne, *Class Field Theory*, version 4.03 (2020),
Chapter V, Proposition 1.6. -/
theorem RayCongruent.exists_common_normalizer {a b : NumberField.RingOfIntegers K}
    (h : RayCongruent F m a b) :
    ∃ c : NumberField.RingOfIntegers K,
      c ≠ 0 ∧ a * c - 1 ∈ m ∧ b * c - 1 ∈ m ∧
        RayCongruent F m (a * c) (b * c) := by
  by_cases hm : m = ⊤
  · subst m
    exact ⟨1, one_ne_zero, by simp, by simp, h.mul RayCongruent.one⟩
  obtain ⟨c, hac⟩ := exists_mul_sub_one_mem_of_isCoprime_span_singleton h.isCoprime
  have hc0 : c ≠ 0 := by
    intro hc
    apply hm
    rw [Ideal.eq_top_iff_one]
    simpa only [hc, mul_zero, zero_sub, neg_neg] using m.neg_mem hac
  have hbc : b * c - 1 ∈ m := by
    have habc : (a - b) * c ∈ m := m.mul_mem_right c h.sub_mem
    convert m.sub_mem hac habc using 1
    ring
  have hcCop : IsCoprime (Ideal.span {c}) m := by
    have hacCop : IsCoprime (Ideal.span {a * c}) m :=
      isCoprime_span_singleton_of_sub_mem isCoprime_span_singleton_one hac
    rw [← Ideal.span_singleton_mul_span_singleton] at hacCop
    exact hacCop.of_mul_left_right
  exact ⟨c, hc0, hac, hbc, h.mul (RayCongruent.refl hc0 hcCop)⟩

end RayCongruent

/-- **The ray-principal equivalence relation** on two integral ideals coprime to `𝔪`: `I` and
`J` are equivalent when `I/J = (a/b)` for ray-congruent generators `a, b`
(`RayCongruent F m a b`), that is, `(b)·I = (a)·J` with `a/b ≡ 1 (mod 𝔪)` and `a/b > 0` at
`∞₂`. This is the integral-representative criterion of Milne, *Class Field Theory*, version 4.03
(2020), Chapter V, Proposition 1.6, for the quotient `J^𝔪/P^𝔪` [83, Neukirch (1999), Chapter VI,
§1, p. 365]. -/
def RayIdeal.IsEquivalent
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (F : RealQuadraticFieldData K) (m : Ideal (NumberField.RingOfIntegers K))
    (I J : RayIdeal K m) : Prop :=
  ∃ a b : NumberField.RingOfIntegers K, RayCongruent F m a b ∧
    (I : Ideal (NumberField.RingOfIntegers K)) * Ideal.span {b} =
      (J : Ideal (NumberField.RingOfIntegers K)) * Ideal.span {a}

section IsEquivalent

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
  {F : RealQuadraticFieldData K} {m : Ideal (NumberField.RingOfIntegers K)}

/-- **Reflexivity of the ray-principal relation**, with the witnesses `a = b = 1`
(`RayCongruent.one`). -/
protected theorem RayIdeal.IsEquivalent.refl (I : RayIdeal K m) : I.IsEquivalent F m I :=
  ⟨1, 1, RayCongruent.one, rfl⟩

/-- **Symmetry of the ray-principal relation**: exchange the witnesses (`RayCongruent.symm`). -/
protected theorem RayIdeal.IsEquivalent.symm {I J : RayIdeal K m} (h : I.IsEquivalent F m J) :
    J.IsEquivalent F m I := by
  obtain ⟨a, b, hab, heq⟩ := h
  exact ⟨b, a, hab.symm, heq.symm⟩

/-- **Transitivity of the ray-principal relation**: if `I/J = (a/b)` and `J/L = (a'/b')`, then
`I/L = (aa'/bb')` (`RayCongruent.mul`). -/
protected theorem RayIdeal.IsEquivalent.trans {I J L : RayIdeal K m}
    (h₁ : I.IsEquivalent F m J) (h₂ : J.IsEquivalent F m L) : I.IsEquivalent F m L := by
  obtain ⟨a, b, hab, hIJ⟩ := h₁
  obtain ⟨a', b', hab', hJL⟩ := h₂
  refine ⟨a * a', b * b', hab.mul hab', ?_⟩
  simp only [← Ideal.span_singleton_mul_span_singleton]
  calc
    I.1 * (Ideal.span {b} * Ideal.span {b'}) =
        (I.1 * Ideal.span {b}) * Ideal.span {b'} := (mul_assoc _ _ _).symm
    _ = (J.1 * Ideal.span {a}) * Ideal.span {b'} := by rw [hIJ]
    _ = (J.1 * Ideal.span {b'}) * Ideal.span {a} := by ac_rfl
    _ = (L.1 * Ideal.span {a'}) * Ideal.span {a} := by rw [hJL]
    _ = L.1 * (Ideal.span {a} * Ideal.span {a'}) := by ac_rfl

/-- **The ray-principal relation is a congruence for ideal multiplication**: if `I/I' = (a/b)`
and `J/J' = (a'/b')`, then `IJ/I'J' = (aa'/bb')` (`RayCongruent.mul`). -/
protected theorem RayIdeal.IsEquivalent.mul {I I' J J' : RayIdeal K m}
    (h : I.IsEquivalent F m I') (h' : J.IsEquivalent F m J') :
    (I * J).IsEquivalent F m (I' * J') := by
  obtain ⟨a, b, hab, hII'⟩ := h
  obtain ⟨a', b', hab', hJJ'⟩ := h'
  refine ⟨a * a', b * b', hab.mul hab', ?_⟩
  simp only [Submonoid.coe_mul, ← Ideal.span_singleton_mul_span_singleton]
  rw [mul_mul_mul_comm I.1 J.1, hII', hJJ', mul_mul_mul_comm]

end IsEquivalent

/-- An exact presentation of the ray class group `Cl_(m * infinity_2)(O_K)` of
[AFK25, Definition 2.1, `defn:rayclassgroup`].

Surjectivity and `class_eq_iff` say that `Class` is precisely the quotient of nonzero integral
ideals coprime to `m` by `RayIdeal.IsEquivalent`; `classOf_mul` identifies its group law with
ideal multiplication. This formalizes the definition restricted to the maximal order of a real
quadratic field with `S = {∞₂}`. -/
@[source "AFK25, Definition 2.1, p. 26, defn:rayclassgroup (maximal order, S = {∞₂})"
  (symbol := "Cl_{𝔪∞₂}(𝒪_K)")]
structure RayClassGroupPresentation
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (F : RealQuadraticFieldData K) (m : Ideal (NumberField.RingOfIntegers K))
    (Class : Type*) [CommGroup Class] where
  /-- The ray class of an integral ideal coprime to `m`. -/
  classOf : RayIdeal K m → Class
  /-- Ideal multiplication represents multiplication of ray classes. -/
  classOf_mul : ∀ I J, classOf (I * J) = classOf I * classOf J
  /-- Every ray class has an integral ideal representative coprime to `m`. -/
  classOf_surjective : Function.Surjective classOf
  /-- Two integral ideals represent the same ray class exactly when they differ by a generator
  congruent to one modulo `m` and positive at `infinity_2`. -/
  class_eq_iff : ∀ I J, classOf I = classOf J ↔ I.IsEquivalent F m J

/-! ### The unit ideal

Multiplicativity `P.classOf_mul` makes the class map a monoid homomorphism, so `[(1)] = 1`. -/

section UnitClass

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
  {F : RealQuadraticFieldData K} {m : Ideal (NumberField.RingOfIntegers K)}
  {Class : Type*} [CommGroup Class] (P : RayClassGroupPresentation F m Class)

/-- The class map is a monoid homomorphism; used by `classOf_one`. -/
def RayClassGroupPresentation.classHom : RayIdeal K m →* Class :=
  MonoidHom.mk' P.classOf P.classOf_mul

/-- **The unit ray ideal has the trivial ray class**, `map_one` for `classHom`. -/
theorem RayClassGroupPresentation.classOf_one : P.classOf 1 = 1 :=
  P.classHom.map_one

end UnitClass

/-! ### The bottom-modulus presentation -/

/-- Every class in a presentation at the bottom finite modulus is trivial. -/
theorem RayClassGroupPresentation.eq_one_of_modulus_bot
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {F : RealQuadraticFieldData K} {Class : Type*} [CommGroup Class]
    (P : RayClassGroupPresentation F ⊥ Class) (A : Class) : A = 1 := by
  obtain ⟨I, rfl⟩ := P.classOf_surjective A
  rw [I.eq_one_of_modulus_bot, P.classOf_one]

/-- A ray class group presented at the bottom finite modulus is a subsingleton. -/
theorem RayClassGroupPresentation.subsingleton_of_modulus_bot
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {F : RealQuadraticFieldData K} {Class : Type*} [CommGroup Class]
    (P : RayClassGroupPresentation F ⊥ Class) : Subsingleton Class := by
  constructor
  intro A B
  exact (P.eq_one_of_modulus_bot A).trans (P.eq_one_of_modulus_bot B).symm

/-! ### Generators positive at `∞₂`

A generator positive at the real place other than the selected one is nonzero. -/

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
  {m : Ideal (NumberField.RingOfIntegers K)}

/-- An element positive at a place other than the selected one is nonzero. -/
lemma cosetGenerator_ne_zero (F : RealQuadraticFieldData K)
    {γ₀ : NumberField.RingOfIntegers K}
    (hpos : ∀ w : InfinitePlace K, w ≠ F.place → 0 < realEmbeddingAt K w (γ₀ : K)) :
    γ₀ ≠ 0 := by
  obtain ⟨w, hw⟩ := F.exists_ne_place
  intro hzero
  simpa only [hzero, map_zero, lt_self_iff_false] using hpos w hw

end SIC

end
