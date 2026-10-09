/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ramification.Basic
import SICs.ClassField.Completion.FiniteConjugation
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius

/-!
# Frobenius automorphisms at unramified primes

The Frobenius predicate, its existence and uniqueness, decomposition-group consequences, and
transport along an isomorphism of number fields.

This module follows [83, Neukirch (1999), Chapter I, §9], Milne, *Class Field Theory*,
Chapter V, §1, and Childress, *Class Field Theory*, Chapter V, §1. The independent
ramification facts live in `SICs.ClassField.Ramification.Basic`; powers and restrictions in
towers live in `SICs.ClassField.Frobenius.Tower`. The ideal Artin map of
`SICs.ClassField.Reciprocity.ArtinMap` uses this predicate at unramified primes.

## The argument

A Frobenius automorphism at a prime $Q$ above $\mathfrak p$ acts on integral elements modulo
$Q$ as the $N(\mathfrak p)$th power map. This agrees with Mathlib's arithmetic Frobenius
condition for the induced algebra automorphism of the ring of integers. At a prime of
ramification index one, Mathlib's unramified uniqueness theorem makes two such automorphisms
equal. A lift exists because the decomposition group surjects onto the residue-field Galois
group. When inertia is trivial, this identifies the decomposition group with the residue-field
Galois group; finite-field Frobenius generates it, so the order of Frobenius is the residue
degree. An isomorphism carries a Frobenius congruence to the corresponding congruence at the
image prime. In an abelian extension, conjugacy then makes Frobenius independent of the chosen
prime above the base prime.
The same conjugation action preserves Frobenius sets selected by any condition on the base
prime, so the subgroups they generate are normal.

## References

- [83, Neukirch (1999), Chapter I, Proposition 9.6 and §9, exercise 2, p. 58]
- Milne, *Class Field Theory*, version 4.03 (2020), Chapter V, §1
- Childress, *Class Field Theory* (2009), Chapter V, §1
-/

noncomputable section

open scoped Pointwise

open NumberField IsDedekindDomain

namespace SIC

universe u v

/-! ### Frobenius at a prime

The generic condition is the standard power-map congruence on the ring of integers. It is
independent of any ray class group or ray class field presentation. -/

/-- A `K`-automorphism of `H` is Frobenius at a prime `P` above `p` when it has the standard
power-map action modulo `P`: `g(x) ≡ x^{N(p)} (mod P)` for all `x ∈ O_H`
[83, Neukirch (1999), Chapter I, §9, exercise 2, p. 58]. -/
@[source "83, Chapter I, §9, Exercise 2, p. 58 (definition)"]
def IsFrobeniusAt
    (K : Type u) (H : Type v) [Field K] [NumberField K] [Field H]
    [Algebra K H] (g : H ≃ₐ[K] H)
    (p : Ideal (NumberField.RingOfIntegers K))
    (P : Ideal (NumberField.RingOfIntegers H)) : Prop :=
  P.IsPrime ∧ Ideal.comap (algebraMap _ _) P = p ∧
    ∀ x : NumberField.RingOfIntegers H,
      NumberField.RingOfIntegers.mapRingEquiv g.toRingEquiv x - x ^ Ideal.absNorm p ∈ P

/-- The prime in a Frobenius condition is prime. -/
theorem IsFrobeniusAt.isPrime {K H : Type*} [Field K] [NumberField K] [Field H]
    [Algebra K H] {g : H ≃ₐ[K] H} {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)}
    (hg : IsFrobeniusAt K H g p Q) : Q.IsPrime := hg.1

/-- The Frobenius prime lies over its base prime. -/
theorem IsFrobeniusAt.liesOver {K H : Type*} [Field K] [NumberField K] [Field H]
    [Algebra K H] {g : H ≃ₐ[K] H} {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)}
    (hg : IsFrobeniusAt K H g p Q) : Q.LiesOver p := ⟨hg.2.1.symm⟩

/-- The Frobenius congruence $g(x)\equiv x^{N(p)}\pmod Q$. -/
theorem IsFrobeniusAt.sub_mem {K H : Type*} [Field K] [NumberField K] [Field H]
    [Algebra K H] {g : H ≃ₐ[K] H} {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)}
    (hg : IsFrobeniusAt K H g p Q) (x : 𝓞 H) :
    RingOfIntegers.mapRingEquiv g.toRingEquiv x - x ^ Ideal.absNorm p ∈ Q := hg.2.2 x

/-- Introduce `IsFrobeniusAt` from a prime above the base prime and its congruence. -/
theorem IsFrobeniusAt.intro {K H : Type*} [Field K] [NumberField K] [Field H]
    [Algebra K H] {g : H ≃ₐ[K] H} {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)}
    (hprime : Q.IsPrime) (hover : Q.LiesOver p)
    (hsub : ∀ x : 𝓞 H,
      RingOfIntegers.mapRingEquiv g.toRingEquiv x - x ^ Ideal.absNorm p ∈ Q) :
    IsFrobeniusAt K H g p Q := ⟨hprime, hover.1.symm, hsub⟩

variable {K : Type u} [Field K] [NumberField K] {H : Type v} [Field H] [NumberField H]
  [Algebra K H]

omit [NumberField H] in
/-- A Frobenius congruence forces the norm of its base prime to be nonzero. This supplies
the nonvanishing step in `IsFrobeniusAt.ne_bot`. -/
private lemma frobenius_absNorm_ne_zero {g : H ≃ₐ[K] H} {p : Ideal (𝓞 K)}
    {Q : Ideal (𝓞 H)} [Q.IsPrime]
    (hFrob : ∀ x : 𝓞 H, RingOfIntegers.mapRingEquiv g.toRingEquiv x -
      x ^ Ideal.absNorm p ∈ Q) :
    Ideal.absNorm p ≠ 0 := by
  intro hzero
  have hnegone : -(1 : 𝓞 H) ∈ Q := by
    simpa only [hzero, pow_zero, map_zero, zero_sub] using hFrob 0
  exact (inferInstance : Q.IsPrime).ne_top
    ((Ideal.eq_top_iff_one Q).mpr (by simpa using Q.neg_mem hnegone))

omit [NumberField H] in
/-- A Frobenius congruence at `Q` forces its base prime `p` to be nonzero. -/
theorem IsFrobeniusAt.ne_bot {g : H ≃ₐ[K] H} {p : Ideal (𝓞 K)}
    {Q : Ideal (𝓞 H)} (hg : IsFrobeniusAt K H g p Q) : p ≠ ⊥ := by
  have : Q.IsPrime := hg.isPrime
  exact Ideal.absNorm_eq_zero_iff.not.mp (frobenius_absNorm_ne_zero hg.sub_mem)

/-! ### Uniqueness of the Frobenius automorphism at an unramified prime

The Frobenius congruence `g(x) ≡ x^{N(𝔭)} (mod Q)` determines `g ∈ Gal(H/K)` when `Q` is
unramified over `𝔭`: two solutions differ by an element of the inertia group of `Q`, which is
trivial. Mathlib's `IsArithFrobAt` is the same congruence for a monoid action, with the exponent
`|𝒪_K/𝔭|` in place of `N(𝔭)`; the bridge `IsFrobeniusAt.isArithFrobAt_mapAlgEquiv`
lets its uniqueness theorem apply without a Galois hypothesis. -/

omit [NumberField H] in
/-- The project Frobenius condition gives Mathlib's arithmetic Frobenius condition for the
endomorphism of the integer ring induced by $g$. -/
theorem IsFrobeniusAt.isArithFrobAt_mapAlgEquiv {g : H ≃ₐ[K] H}
    {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)}
    (hg : IsFrobeniusAt K H g p Q) :
    (RingOfIntegers.mapAlgEquiv g).toAlgHom.IsArithFrobAt Q := by
  have : Q.LiesOver p := hg.liesOver
  intro x
  change RingOfIntegers.mapRingEquiv g.toRingEquiv x -
    x ^ Nat.card ((𝓞 K) ⧸ Q.under (𝓞 K)) ∈ Q
  rw [← Ideal.over_def Q p]
  simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using hg.sub_mem x

/-- For a prime `Q` above `p`, the project Frobenius condition agrees with Mathlib's
`IsArithFrobAt`; the two exponents are the same residue-field cardinality. -/
theorem isFrobeniusAt_iff_isArithFrobAt [IsGalois K H] {g : H ≃ₐ[K] H}
    {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)} [Q.IsPrime] [Q.LiesOver p] :
    IsFrobeniusAt K H g p Q ↔ IsArithFrobAt (𝓞 K) g Q := by
  have hnorm : Nat.card ((𝓞 K) ⧸ Q.under (𝓞 K)) = Ideal.absNorm p := by
    rw [← Ideal.over_def Q p, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  constructor
  · intro hg x
    change g • x - x ^ Nat.card ((𝓞 K) ⧸ Q.under (𝓞 K)) ∈ Q
    rw [hnorm]
    exact hg.sub_mem x
  · intro hg
    refine ⟨inferInstance, (Ideal.over_def Q p).symm, fun x ↦ ?_⟩
    have hx := hg x
    change g • x - x ^ Nat.card ((𝓞 K) ⧸ Q.under (𝓞 K)) ∈ Q at hx
    rwa [hnorm] at hx

/-- `IsFrobeniusAt` is Mathlib's arithmetic Frobenius condition `IsArithFrobAt` for the action of
`Gal(H/K)` on `𝒪_H`: the exponent `N(𝔭) = |𝒪_K/𝔭|` is `Nat.card (𝒪_K ⧸ Q ∩ 𝒪_K)` because `Q`
lies over `𝔭`. The Galois hypothesis only supplies the instance that the action of `Gal(H/K)`
commutes with the `𝒪_K`-scalars, which Mathlib's statement requires. -/
theorem IsFrobeniusAt.isArithFrobAt [IsGalois K H] {g : H ≃ₐ[K] H} {p : Ideal (𝓞 K)}
    {Q : Ideal (𝓞 H)} (hg : IsFrobeniusAt K H g p Q) : IsArithFrobAt (𝓞 K) g Q := by
  have : Q.IsPrime := hg.isPrime
  have : Q.LiesOver p := hg.liesOver
  exact isFrobeniusAt_iff_isArithFrobAt.mp hg

/-- Frobenius at a prime of ramification index one is unique. This is the uniqueness statement of
[83, Neukirch (1999), Chapter I, §9, exercise 2, p. 58]. -/
@[source "83, Chapter I, §9, Exercise 2, p. 58 (uniqueness)"]
theorem IsFrobeniusAt.eq_of_ramificationIdx_eq_one {g g' : H ≃ₐ[K] H}
    {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)} (hg : IsFrobeniusAt K H g p Q)
    (hg' : IsFrobeniusAt K H g' p Q) (hunr : Q.ramificationIdx (𝓞 K) = 1) : g = g' := by
  have : Q.IsPrime := hg.isPrime
  have : Q.LiesOver p := hg.liesOver
  let _ : Algebra.IsUnramifiedAt (𝓞 K) Q := Ideal.ramificationIdx_eq_one_iff.mp hunr
  have hrestr := hg.isArithFrobAt_mapAlgEquiv.eq_of_isUnramifiedAt
    hg'.isArithFrobAt_mapAlgEquiv
    Q.primeCompl_le_nonZeroDivisors
  have hring : g.toRingEquiv.toRingHom = g'.toRingEquiv.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := 𝓞 H)
    intro x
    exact congrArg Subtype.val (DFunLike.congr_fun hrestr x)
  ext x
  exact DFunLike.congr_fun hring x

/-! ### Roots of unity

Mathlib's arithmetic Frobenius theorem applies to any root of unity whose exponent is a unit
at the base prime. -/

omit [NumberField H] in
/-- Frobenius sends an $n$th root of unity to its $N(\mathfrak p)$th power when
$n\notin\mathfrak p$. This follows from Mathlib's arithmetic Frobenius theorem and includes
Childress, *Class Field Theory*, Chapter V, proof of Theorem 2.1(ii), and Milne,
*Class Field Theory*, Chapter V, Example 3.2. -/
theorem IsFrobeniusAt.apply_of_pow_eq_one {g : H ≃ₐ[K] H} {p : Ideal (𝓞 K)}
    {Q : Ideal (𝓞 H)} (hg : IsFrobeniusAt K H g p Q) {n : ℕ} {ζ : H}
    (hζ : ζ ^ n = 1) (hn : (n : 𝓞 K) ∉ p) : g ζ = ζ ^ Ideal.absNorm p := by
  have hn0 : n ≠ 0 := by
    intro h
    apply hn
    simp [h]
  let z : 𝓞 H := ⟨ζ, IsIntegral.of_pow (Nat.pos_of_ne_zero hn0)
    (hζ ▸ isIntegral_one)⟩
  have hz : z ^ n = 1 := RingOfIntegers.coe_injective hζ
  have hnQ : (n : 𝓞 H) ∉ Q := by
    intro h
    apply hn
    rw [← hg.liesOver.1.symm]
    change algebraMap (𝓞 K) (𝓞 H) (n : 𝓞 K) ∈ Q
    simpa using h
  have h := hg.isArithFrobAt_mapAlgEquiv.apply_of_pow_eq_one hz hnQ
  have h' := congrArg Subtype.val h
  change g ζ = ζ ^ Nat.card ((𝓞 K) ⧸ Q.under (𝓞 K)) at h'
  have : Q.LiesOver p := hg.liesOver
  have hnorm : Nat.card ((𝓞 K) ⧸ Q.under (𝓞 K)) = Ideal.absNorm p := by
    rw [← Ideal.over_def Q p, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rwa [hnorm] at h'

/-! ### Frobenius existence and decomposition groups

A Frobenius automorphism exists above every nonzero prime. At an unramified prime it
generates the decomposition group; restriction to a Galois subfield preserves its congruence. -/

/-- Existence of an arithmetic Frobenius above a nonzero prime. Milne, *Class Field Theory*,
Chapter V, §1, definition of the Frobenius element. -/
theorem exists_isFrobeniusAt [IsGalois K H]
    (p : Ideal (𝓞 K)) (Q : Ideal (𝓞 H)) [Q.IsPrime] [Q.LiesOver p] (hp : p ≠ ⊥) :
    ∃ g : H ≃ₐ[K] H, IsFrobeniusAt K H g p Q := by
  have : Q.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot Q
    (Ideal.ne_bot_of_liesOver_of_ne_bot hp Q)
  obtain ⟨g, hg⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (H ≃ₐ[K] H) Q
  exact ⟨g, isFrobeniusAt_iff_isArithFrobAt.mpr hg⟩

/-- At an unramified prime, reduction identifies the decomposition group with the residue
Galois group. Milne, *Class Field Theory*, Chapter V, §1, definition of the Frobenius element. -/
def decompositionResidueEquiv [IsGalois K H] (p : Ideal (𝓞 K)) (Q : Ideal (𝓞 H))
    [Q.IsPrime] [Q.LiesOver p] (hp : p ≠ ⊥) (hunr : Q.ramificationIdx (𝓞 K) = 1) :
    MulAction.stabilizer (H ≃ₐ[K] H) Q ≃* ((𝓞 H) ⧸ Q) ≃ₐ[(𝓞 K) ⧸ p] ((𝓞 H) ⧸ Q) :=
  MulEquiv.ofBijective (Ideal.Quotient.stabilizerHom Q p (H ≃ₐ[K] H)) ⟨by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply (Subgroup.map_eq_bot_iff_of_injective _
      (MulAction.stabilizer (H ≃ₐ[K] H) Q).subtype_injective).mp
    rw [Ideal.Quotient.map_ker_stabilizer_subtype]
    exact inertia_eq_bot_of_ramificationIdx_eq_one hp Q hunr,
    Ideal.Quotient.stabilizerHom_surjective (H ≃ₐ[K] H) p Q⟩

/-- The residue-action equivalence sends the class of `x` to the class of `g(x)`. -/
@[simp] theorem decompositionResidueEquiv_apply_mk [IsGalois K H]
    (p : Ideal (𝓞 K)) (Q : Ideal (𝓞 H)) [Q.IsPrime] [Q.LiesOver p]
    (hp : p ≠ ⊥) (hunr : Q.ramificationIdx (𝓞 K) = 1)
    (g : MulAction.stabilizer (H ≃ₐ[K] H) Q) (x : 𝓞 H) :
    decompositionResidueEquiv p Q hp hunr g (Ideal.Quotient.mk Q x) =
      Ideal.Quotient.mk Q ((g : H ≃ₐ[K] H) • x) := rfl

/-- At an unramified nonzero prime, Frobenius generates the decomposition group.
Milne, *Class Field Theory*, Chapter V, §1, definition of the Frobenius element. -/
theorem IsFrobeniusAt.zpowers_eq_decomposition [IsGalois K H]
    {g : H ≃ₐ[K] H} {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)}
    (hg : IsFrobeniusAt K H g p Q)
    (hunr : Q.ramificationIdx (𝓞 K) = 1) :
    Subgroup.zpowers g = MulAction.stabilizer (H ≃ₐ[K] H) Q := by
  have : Q.IsPrime := hg.isPrime
  have : Q.LiesOver p := hg.liesOver
  have hp := hg.ne_bot
  have : p.IsPrime := Ideal.isPrime_of_liesOver Q p
  have : p.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot p hp
  have : Q.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot Q
    (Ideal.ne_bot_of_liesOver_of_ne_bot hp Q)
  let _ := Ideal.Quotient.field p
  let _ := Ideal.Quotient.field Q
  let _ := Fintype.ofFinite ((𝓞 K) ⧸ p)
  let e := decompositionResidueEquiv p Q hp hunr
  have hgD := hg.isArithFrobAt.mem_stabilizer
  let gD : MulAction.stabilizer (H ≃ₐ[K] H) Q := ⟨g, hgD⟩
  have heq : e gD = FiniteField.frobeniusAlgEquivOfAlgebraic ((𝓞 K) ⧸ p) ((𝓞 H) ⧸ Q) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [decompositionResidueEquiv_apply_mk,
      FiniteField.frobeniusAlgEquivOfAlgebraic_apply, ← map_pow, Ideal.Quotient.eq]
    change RingOfIntegers.mapRingEquiv g.toRingEquiv x -
      x ^ Fintype.card ((𝓞 K) ⧸ p) ∈ Q
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
      using hg.sub_mem x
  apply le_antisymm (Subgroup.zpowers_le.mpr hgD)
  intro τ hτ
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
    ((𝓞 K) ⧸ p) ((𝓞 H) ⧸ Q)).2 (e ⟨τ, hτ⟩)
  have he : gD ^ (n : ℕ) = ⟨τ, hτ⟩ := e.injective (by rw [map_pow, heq]; exact hn)
  have he' : g ^ (n : ℕ) = τ := congrArg Subtype.val he
  rw [← he']
  exact Subgroup.npow_mem_zpowers g n

/-- **The order of Frobenius is the residue degree** at an unramified nonzero prime, since
Frobenius generates the decomposition group, of order `e f = f`. Milne, *Class Field Theory*,
Chapter V, §1, definition of the Frobenius element. -/
theorem IsFrobeniusAt.orderOf_eq_inertiaDeg [IsGalois K H]
    {g : H ≃ₐ[K] H} {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)}
    (hg : IsFrobeniusAt K H g p Q)
    (hunr : Q.ramificationIdx (𝓞 K) = 1) : orderOf g = Q.inertiaDeg (𝓞 K) := by
  have : Q.IsPrime := hg.isPrime
  have : Q.LiesOver p := hg.liesOver
  have hp := hg.ne_bot
  have : p.IsPrime := Ideal.isPrime_of_liesOver Q p
  have hdec := hg.zpowers_eq_decomposition hunr
  have hI : Q.inertia (H ≃ₐ[K] H) = ⊥ :=
    inertia_eq_bot_of_ramificationIdx_eq_one hp Q hunr
  have hcard := Ideal.card_stabilizer_eq_card_inertia_mul_finrank
    (G := H ≃ₐ[K] H) p Q
  rw [← hdec, Nat.card_zpowers, hI, Subgroup.card_bot, one_mul] at hcard
  exact hcard

/-! ### Semilinear transport

Compatible isomorphisms of integer rings carry the base prime, the upper prime, and the
Frobenius congruence together. Conjugation is the case of a field automorphism over the
unchanged base field. It also preserves Frobenius sets defined by conditions on the base prime,
so their generated subgroups are normal. -/

omit [NumberField H] in
/-- A compatible pair of isomorphisms of integer rings transports a Frobenius element across
base and upper fields. The equality of absolute norms follows from the induced equivalence of
ideal quotients. This is the common congruence argument behind conjugation here and the
normal-restriction transport used for Artin maps. -/
theorem IsFrobeniusAt.map_semilinear {K₂ H₂ : Type*} [Field K₂] [NumberField K₂]
    [Field H₂] [Algebra K₂ H₂] (eK : 𝓞 K ≃+* 𝓞 K₂) (eH : 𝓞 H ≃+* 𝓞 H₂)
    (hbase : eH.symm.toRingHom.comp (algebraMap (𝓞 K₂) (𝓞 H₂)) =
      (algebraMap (𝓞 K) (𝓞 H)).comp eK.symm.toRingHom)
    {g : H ≃ₐ[K] H} {g₂ : H₂ ≃ₐ[K₂] H₂}
    (hconj : ∀ y : 𝓞 H₂,
      eH.symm (RingOfIntegers.mapRingEquiv g₂.toRingEquiv y) =
        RingOfIntegers.mapRingEquiv g.toRingEquiv (eH.symm y))
    {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)} (hg : IsFrobeniusAt K H g p Q) :
    IsFrobeniusAt K₂ H₂ g₂ (p.map eK) (Q.map eH) := by
  have hnorm : Ideal.absNorm (p.map eK) = Ideal.absNorm p := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv p (p.map eK) eK rfl).toEquiv).symm
  have : Q.IsPrime := hg.isPrime
  refine ⟨Ideal.map_isPrime_of_equiv eH, ?_, ?_⟩
  · rw [show Q.map eH = Q.comap eH.symm from Ideal.map_comap_of_equiv eH]
    change (Q.comap eH.symm.toRingHom).comap (algebraMap (𝓞 K₂) (𝓞 H₂)) = p.map eK
    rw [Ideal.comap_comap, hbase, ← Ideal.comap_comap, hg.2.1]
    exact (Ideal.map_comap_of_equiv eK).symm
  · intro y
    rw [show Q.map eH = Q.comap eH.symm from Ideal.map_comap_of_equiv eH,
      Ideal.mem_comap, map_sub, map_pow, hnorm, hconj]
    exact hg.sub_mem (eH.symm y)

omit [NumberField H] in
/-- Conjugating Frobenius conjugates its prime. Milne, *Class Field Theory*, Chapter V,
1.9; this is `IsFrobeniusAt.map_semilinear` for an automorphism over the same base field. -/
theorem IsFrobeniusAt.conj {g : H ≃ₐ[K] H} {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)}
    (hg : IsFrobeniusAt K H g p Q) (τ : H ≃ₐ[K] H) :
    IsFrobeniusAt K H (τ * g * τ⁻¹) p (τ • Q) := by
  let e := RingOfIntegers.mapRingEquiv τ.toRingEquiv
  have hbase : e.symm.toRingHom.comp (algebraMap (𝓞 K) (𝓞 H)) =
      (algebraMap (𝓞 K) (𝓞 H)).comp (RingEquiv.refl (𝓞 K)).symm.toRingHom := by
    ext x
    exact τ.symm.commutes (x : K)
  have hconj (y : 𝓞 H) :
      e.symm (RingOfIntegers.mapRingEquiv (τ.autCongr g).toRingEquiv y) =
        RingOfIntegers.mapRingEquiv g.toRingEquiv (e.symm y) := by
    apply RingOfIntegers.ext
    change τ.symm ((τ.autCongr g) (y : H)) = g (τ.symm (y : H))
    simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  have h := hg.map_semilinear (RingEquiv.refl (𝓞 K)) e hbase hconj
  have hpid : p.map (RingEquiv.refl (𝓞 K)) = p := by
    change p.map (RingHom.id (𝓞 K)) = p
    exact Ideal.map_id p
  rw [hpid] at h
  exact h

omit [NumberField H] in
/-- A condition on the base prime defines a conjugation-stable set of Frobenius elements.
Milne, *Class Field Theory*, Chapter VII, proof of Proposition 4.7. -/
theorem closure_isFrobeniusAt_normal
    (P : HeightOneSpectrum (𝓞 K) → Prop) :
    (Subgroup.closure {g : H ≃ₐ[K] H | ∃ w : HeightOneSpectrum (𝓞 H),
      P (FinitePlace.below (K := K) w) ∧
        IsFrobeniusAt K H g (FinitePlace.below (K := K) w).asIdeal w.asIdeal}).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [Subgroup.le_normalizer_closure_iff]
  rintro τ _ g ⟨w, hw, hg⟩
  have hbelow : FinitePlace.below (K := K) (τ • w) = FinitePlace.below (K := K) w :=
    FinitePlace.below_eq_of_liesOver (FinitePlace.below (K := K) w) (τ • w)
  apply Subgroup.subset_closure
  refine ⟨τ • w, by simpa only [hbelow] using hw, ?_⟩
  rw [hbelow, FinitePlace.asIdeal_smul]
  exact hg.conj τ

/-! ### Transport over a normal base subfield

A field automorphism of the upper field transports its relative automorphisms and their
Frobenius congruences across the induced automorphism of the normal base field. -/

variable {F E L : Type*} [Field F] [Field E] [Field L] [NumberField E] [NumberField L]
  [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L] [Normal F E]

omit [NumberField E] [NumberField L] in
/-- The conjugate of an `E`-automorphism by an `F`-automorphism fixing `E` setwise, used in
`frobeniusAt_mapEquiv`. -/
def conjugateOver (τ : L ≃ₐ[F] L) (g : L ≃ₐ[E] L) : L ≃ₐ[E] L :=
  AlgEquiv.ofRingEquiv
    (f := τ.toRingEquiv.symm.trans (g.toRingEquiv.trans τ.toRingEquiv)) (by
      intro x
      let σ := τ.restrictNormal E
      obtain ⟨y, rfl⟩ := σ.surjective x
      change τ (g (τ.symm (algebraMap E L (σ y)))) = algebraMap E L (σ y)
      rw [AlgEquiv.restrictNormal_commutes τ E y, τ.symm_apply_apply,
        g.commutes])

omit [NumberField E] [NumberField L] in
/-- The `F`-automorphism underlying `conjugateOver τ g` is `τ g τ⁻¹`. -/
theorem conjugateOver_restrictScalars (τ : L ≃ₐ[F] L) (g : L ≃ₐ[E] L) :
    (conjugateOver τ g).restrictScalars F = τ * g.restrictScalars F * τ⁻¹ := by
  ext x
  rfl

omit [NumberField L] in
/-- Frobenius congruences move with a compatible pair of field automorphisms; used by
`frobeniusAt_mapEquiv`. -/
theorem IsFrobeniusAt.map_restrictNormal (τ : L ≃ₐ[F] L)
    {g : L ≃ₐ[E] L} {p : Ideal (𝓞 E)} {Q : Ideal (𝓞 L)}
    (hg : IsFrobeniusAt E L g p Q) :
    IsFrobeniusAt E L (conjugateOver τ g)
      (p.map (RingOfIntegers.mapRingEquiv (τ.restrictNormal E).toRingEquiv))
      (Q.map (RingOfIntegers.mapRingEquiv τ.toRingEquiv)) := by
  let eE := RingOfIntegers.mapRingEquiv (τ.restrictNormal E).toRingEquiv
  let eL := RingOfIntegers.mapRingEquiv τ.toRingEquiv
  have hbase : eL.symm.toRingHom.comp (algebraMap (𝓞 E) (𝓞 L)) =
      (algebraMap (𝓞 E) (𝓞 L)).comp eE.symm.toRingHom :=
    FinitePlace.integers_restrictNormal_commutes_symm τ
  have hconj (y : 𝓞 L) :
      eL.symm (RingOfIntegers.mapRingEquiv (conjugateOver τ g).toRingEquiv y) =
        RingOfIntegers.mapRingEquiv g.toRingEquiv (eL.symm y) := by
    apply RingOfIntegers.ext
    change τ.symm (τ (g (τ.symm (y : L)))) = g (τ.symm (y : L))
    rw [τ.symm_apply_apply]
  exact hg.map_semilinear eE eL hbase hconj

open scoped IsMulCommutative in
/-- In an abelian extension, Frobenius is independent of the prime above a fixed unramified
base prime. Milne, *Class Field Theory*, Chapter V, 1.9 and the following remark. -/
theorem IsFrobeniusAt.eq_of_same_base [IsGalois K H] [IsMulCommutative (H ≃ₐ[K] H)]
    {g g' : H ≃ₐ[K] H} {p : Ideal (𝓞 K)} {Q Q' : Ideal (𝓞 H)}
    (hg : IsFrobeniusAt K H g p Q) (hg' : IsFrobeniusAt K H g' p Q')
    (hunr : Q.ramificationIdx (𝓞 K) = 1) : g = g' := by
  have : Q.IsPrime := hg.isPrime
  have : Q'.IsPrime := hg'.isPrime
  have : Q.LiesOver p := hg.liesOver
  have : Q'.LiesOver p := hg'.liesOver
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p Q' Q (H ≃ₐ[K] H)
  have hconj : IsFrobeniusAt K H g' p Q := by
    simpa only [hσ, mul_comm σ g', mul_assoc, mul_inv_cancel, mul_one] using hg'.conj σ
  exact hg.eq_of_ramificationIdx_eq_one hconj hunr

end SIC

end
