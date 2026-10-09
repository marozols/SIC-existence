/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import SICs.Source

/-!
# Ideals in Dedekind domains

Coprime principal ideals, finite prime support, coprime ideal representatives, prime-factor
induction, and denominators coprime to a modulus.

The first section establishes coprimality facts for principal ideals in any commutative ring.
The remaining sections prove ideal-theoretic inputs of ray-class arithmetic, among them the
coprime witness lemma used to prove ray-class finiteness in Milne, *Class Field Theory*, version
4.03 (2020), Chapter V, Theorem 1.7. The basic input is the classical fact that in a Dedekind
domain `R` every ideal class contains an integral ideal coprime to a given nonzero ideal `J`: for
nonzero ideals `I` and `J` there are nonzero `y ∈ I` and `C ≠ ⊥` with

$$
(y) = I\,C, \qquad C + J = R.
$$

This is [73, Kopp, Lagarias (2022), Lemma 5.12, `lem:reldok`] for the maximal order and the
trivial modulus.

## Mathematical argument

Mathlib's Dedekind-domain approximation lemma gives `IJ + (y) = I`, since `0 < IJ ≤ I`.
Writing `(y) = IC` and cancelling the nonzero ideal `I` gives `C + J = R`. The equality also
forces `y ≠ 0` and `C ≠ 0`.

If `I` and `J` have the same ordinary ideal class and are both coprime to `M`, apply this
construction to `I` and `M`, obtaining `(y) = IC` with `C` coprime to `M`. Then `JC` has the
same class as the principal ideal `IC`, so `JC = (a)` for some nonzero `a`. Both `(a)` and `(y)`
are coprime to `M`, and `(a)I = (y)J`; these are the integral witnesses used in the ray-class
finiteness argument.

For an integral ideal coprime to a modulus, prime factorization reduces any property
stable under prime multiplication to the unit ideal. A denominator ideal of an element is
nonzero and avoids each prime at which the element is integral, so it supplies a denominator
coprime to a prescribed modulus.

## References

- Milne, *Class Field Theory*, version 4.03 (2020), Chapter V, Lemma 1.5 and Theorem 1.7.
- [73, Kopp, Lagarias (2022), Lemma 5.12, `lem:reldok`].
-/

namespace SIC

/-! ### Principal ideals coprime to an ideal

The unit ideal and `(1)` are coprime to any ideal. Coprimality of a principal ideal depends only
on its generator modulo that ideal, and gives an inverse of the generator modulo that ideal. -/

section CoprimeModulus

variable {R : Type*} [CommRing R] {m : Ideal R}

/-- `R + 𝔪 = R`: the unit ideal is coprime to every ideal
(`Ideal.one_eq_top`, `isCoprime_one_left`). -/
theorem isCoprime_top_left : IsCoprime (⊤ : Ideal R) m := by
  simpa only [← Ideal.one_eq_top] using (isCoprime_one_left : IsCoprime (1 : Ideal R) m)

/-- `(1) = R` is coprime to every ideal; the witness `1` of a ray-principal equivalence. -/
theorem isCoprime_span_singleton_one : IsCoprime (Ideal.span {(1 : R)}) m := by
  rw [Ideal.span_singleton_one]
  exact isCoprime_top_left

/-- Coprimality to `𝔪` of a principal ideal is a condition modulo `𝔪`: if `(γ₀)` is coprime to
`𝔪` and `γ ≡ γ₀ (mod 𝔪)`, then `(γ)` is coprime to `𝔪`. -/
lemma isCoprime_span_singleton_of_sub_mem {γ₀ γ : R}
    (hcop : IsCoprime (Ideal.span {γ₀}) m) (hγ : γ - γ₀ ∈ m) :
    IsCoprime (Ideal.span {γ}) m := by
  rw [Ideal.isCoprime_iff_exists] at hcop ⊢
  obtain ⟨x, hx, y, hy, hxy⟩ := hcop
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hx
  refine ⟨γ * c, Ideal.mem_span_singleton.mpr ⟨c, rfl⟩,
    y - c * (γ - γ₀), m.sub_mem hy (m.mul_mem_left c hγ), ?_⟩
  calc
    γ * c + (y - c * (γ - γ₀)) = γ₀ * c + y := by ring
    _ = 1 := hxy

/-- An element whose principal ideal is coprime to `m` has a multiplicative inverse modulo `m`.
This is the Bézout step used to normalize both generators of a ray-principal relation. -/
lemma exists_mul_sub_one_mem_of_isCoprime_span_singleton {a : R}
    (hcop : IsCoprime (Ideal.span {a}) m) :
    ∃ c : R, a * c - 1 ∈ m := by
  rw [Ideal.isCoprime_iff_exists] at hcop
  obtain ⟨i, hi, j, hj, hij⟩ := hcop
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hi
  refine ⟨c, ?_⟩
  have heq : a * c - 1 = -j := by
    rw [← hij]
    ring
  rw [heq]
  exact m.neg_mem hj

end CoprimeModulus

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
open IsDedekindDomain

/-! ### Prime support of an element -/

/-- Only finitely many height-one primes contain a nonzero element of a Dedekind domain. -/
theorem finite_primes_containing {c : R} (hc : c ≠ 0) :
    {P : HeightOneSpectrum R | c ∈ P.asIdeal}.Finite := by
  have hspan : Ideal.span {c} ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hc
  convert Ideal.finite_factors hspan using 1
  ext P
  simp only [Set.mem_ofPred_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]

/-! ### Coprime ideal representatives

Mathlib's Dedekind-domain approximation lemma gives a principal ideal complement of `IJ` in
`I`. Cancellation yields a representative coprime to `J`. -/

/-- **Every ideal class contains a nonzero integral ideal coprime to `J`**
[73, Kopp, Lagarias (2022), Lemma 5.12, `lem:reldok`], for the maximal order and the trivial
modulus: for nonzero ideals `I`, `J` there are nonzero `y ∈ I` and `C ≠ ⊥` with `(y) = IC`
and `C` coprime to `J`. -/
@[source "73, Lemma 5.12, p. 29, lem:reldok (maximal order, trivial modulus)"]
theorem exists_mem_span_singleton_eq_mul_isCoprime {I J : Ideal R} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    ∃ y ∈ I, y ≠ 0 ∧ ∃ C : Ideal R, C ≠ ⊥ ∧ Ideal.span {y} = I * C ∧ IsCoprime C J := by
  by_cases hJtop : J = ⊤
  · subst J
    obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨C, hC⟩ := Ideal.dvd_span_singleton.mpr hyI
    have hC0 : C ≠ ⊥ := by
      intro hC0
      exact hy0 (Ideal.span_singleton_eq_bot.mp (by simpa [hC0] using hC))
    exact ⟨y, hyI, hy0, C, hC0, hC, Ideal.isCoprime_iff_sup_eq.mpr (by simp)⟩
  have hIJ : I * J ≤ I := Ideal.mul_le_left
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_sup_span_eq hIJ (mul_ne_zero hI hJ)
  have hyI : y ∈ I := (Ideal.span_singleton_le_iff_mem I).mp (le_sup_right.trans_eq hy)
  obtain ⟨C, hC⟩ := Ideal.dvd_span_singleton.mpr hyI
  have hy0 : y ≠ 0 := by
    intro hy0
    have : I * J = I := by simpa [hy0] using hy
    exact hJtop (mul_left_cancel₀ hI (by simpa using this))
  have hC0 : C ≠ ⊥ := by
    intro hC0
    exact hy0 (Ideal.span_singleton_eq_bot.mp (by simpa [hC0] using hC))
  refine ⟨y, hyI, hy0, C, hC0, hC, Ideal.isCoprime_iff_sup_eq.mpr ?_⟩
  apply mul_left_cancel₀ hI
  calc
    I * (C ⊔ J) = I * C ⊔ I * J := Ideal.mul_sup I C J
    _ = Ideal.span {y} ⊔ I * J := by rw [← hC]
    _ = I := by rw [sup_comm, hy]
    _ = I * ⊤ := (Ideal.mul_top I).symm

/-- **Coprime integral witnesses for equality of ordinary ideal classes**: if nonzero ideals
`I` and `J` are coprime to `M` and have the same class, then there are nonzero `a, b`, each
coprime to `M`, with `(a)I = (b)J`.  This is the integral-witness form of Milne, *Class Field
Theory*, version 4.03 (2020), Chapter V, Lemma 1.5, used in the proof of Theorem 1.7. -/
theorem exists_isCoprime_generators_mul_eq_of_class_eq {I J M : Ideal R}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIM : IsCoprime I M) (hJM : IsCoprime J M)
    (hclass :
      ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ =
        ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩) :
    ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧
      IsCoprime (Ideal.span {a}) M ∧ IsCoprime (Ideal.span {b}) M ∧
        Ideal.span {a} * I = Ideal.span {b} * J := by
  by_cases hM : M = ⊥
  · subst M
    have hItop : I = ⊤ := by
      simpa using Ideal.isCoprime_iff_sup_eq.mp hIM
    have hJtop : J = ⊤ := by
      simpa using Ideal.isCoprime_iff_sup_eq.mp hJM
    subst I
    subst J
    exact ⟨1, 1, one_ne_zero, one_ne_zero,
      by simpa only [Ideal.span_singleton_one] using hIM,
      by simpa only [Ideal.span_singleton_one] using hJM, by simp⟩
  obtain ⟨y, _, hy0, C, hC0, hy, hCM⟩ :=
    exists_mem_span_singleton_eq_mul_isCoprime hI hM
  have hIC0 : I * C ≠ ⊥ := mul_ne_zero hI hC0
  have hJC0 : J * C ≠ ⊥ := mul_ne_zero hJ hC0
  have hmulclass :
      ClassGroup.mk0 ⟨I * C, mem_nonZeroDivisors_of_ne_zero hIC0⟩ =
        ClassGroup.mk0 ⟨J * C, mem_nonZeroDivisors_of_ne_zero hJC0⟩ := by
    change
      ClassGroup.mk0 (⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ *
        ⟨C, mem_nonZeroDivisors_of_ne_zero hC0⟩) =
      ClassGroup.mk0 (⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩ *
        ⟨C, mem_nonZeroDivisors_of_ne_zero hC0⟩)
    rw [map_mul, map_mul, hclass]
  have hJCPrincipal : (J * C).IsPrincipal := by
    apply (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_of_ne_zero hJC0)).mp
    rw [← hmulclass]
    apply (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_of_ne_zero hIC0)).mpr
    rw [← hy]
    infer_instance
  obtain ⟨a, ha⟩ := @Submodule.IsPrincipal.principal _ _ _ _ _ _ hJCPrincipal
  have ha' : Ideal.span {a} = J * C := ha.symm
  have ha0 : a ≠ 0 := by
    intro ha0
    exact hJC0 (ha'.symm.trans (Ideal.span_singleton_eq_bot.mpr ha0))
  refine ⟨a, y, ha0, hy0, ?_, ?_, ?_⟩
  · rw [ha']
    exact hJM.mul_left hCM
  · rw [hy]
    exact hIM.mul_left hCM
  · rw [ha', hy]
    ac_rfl

/-! ### Induction on ideals coprime to a modulus

Unique factorization reduces a nonzero ideal coprime to `m` to the unit ideal and prime
factors that are themselves coprime to `m`. -/

/-- Induction on integral ideals coprime to a fixed ideal, with a prime multiplication step.
Used by `normCharacter_integral_of_coprime`. -/
theorem induction_on_prime_coprime {R : Type*} [CommRing R] [IsDedekindDomain R]
    (m : Ideal R) (P : Ideal R → Prop) (hunit : P ⊤)
    (hprime : ∀ (J Q : Ideal R), Q ≠ ⊥ → Q.IsPrime → IsCoprime Q m →
      J ≠ ⊥ → IsCoprime J m → P J → P (Q * J))
    (I : Ideal R) (hI0 : I ≠ ⊥) (hIm : IsCoprime I m) : P I := by
  let P' : Ideal R → Prop := fun J => J ≠ ⊥ → IsCoprime J m → P J
  suffices h : P' I from h hI0 hIm
  refine UniqueFactorizationMonoid.induction_on_prime I ?_ ?_ ?_
  · intro hzero _
    exact (hzero rfl).elim
  · intro J hJ hJ0 _
    obtain rfl := Ideal.isUnit_iff.mp hJ
    exact hunit
  · intro J Q hJ0 hQ ih _hQJ0 hQJcop
    exact hprime J Q hQ.ne_zero (Ideal.isPrime_of_prime hQ)
      hQJcop.of_mul_left_left
      hJ0 hQJcop.of_mul_left_right (ih hJ0 hQJcop.of_mul_left_right)

/-! ### Primes and denominators in a number field

A prime avoiding a rational integer `n` has absolute norm prime to `n`, and the denominator ideal
of an element integral at the primes of a modulus is coprime to that modulus. -/

open NumberField

variable {K : Type*} [Field K] [NumberField K]

open IsDedekindDomain

/-- A prime not containing `n` has absolute norm prime to `n`; used by
`normCharacter_integral_of_coprime` and `artinMap_apply_of_isPrimitiveRoot`. -/
theorem absNorm_coprime_iff_natCast_notMem
    (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} :
    (Ideal.absNorm v.asIdeal).Coprime n ↔ (n : 𝓞 K) ∉ v.asIdeal := by
  constructor
  · intro hcop hn
    exact Ideal.IsPrime.notMem_of_isCoprime_of_mem (Nat.Coprime.cast hcop)
      (Ideal.absNorm_mem v.asIdeal) hn
  · intro hn
    have : v.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot v.asIdeal v.ne_bot
    obtain ⟨p, k, _, hpv, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
    rw [hnorm]
    apply Nat.Coprime.pow_left
    apply hp.coprime_iff_not_dvd.mpr
    intro hpn
    apply hn
    obtain ⟨q, rfl⟩ := hpn
    simpa only [Nat.cast_mul] using v.asIdeal.mul_mem_right (q : 𝓞 K) hpv

/-- A maximal ideal avoiding an element is coprime to its principal ideal. -/
theorem isCoprime_span_singleton_of_notMem {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsMaximal] {c : R} (hc : c ∉ P) :
    IsCoprime P (Ideal.span {c}) := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra hne
  have hmax : P.IsMaximal := inferInstance
  have heq : P = P ⊔ Ideal.span {c} := hmax.eq_of_le hne le_sup_left
  exact hc ((Ideal.span_singleton_le_iff_mem _).mp (by rw [heq]; exact le_sup_right))

/-- The denominator ideal of a number-field element is nonzero and avoids every
prime at which that element is integral. Used by `exists_integral_ratio_coprime_modulus`. -/
private theorem denominatorIdeal_properties (a : K) :
    let D : Ideal (𝓞 K) := (1 : Submodule (𝓞 K) K).comap
      (LinearMap.toSpanSingleton (𝓞 K) K a)
    D ≠ ⊥ ∧ ∀ v : HeightOneSpectrum (𝓞 K),
      v.valuation K a ≤ 1 → ¬ D ≤ v.asIdeal := by
  let D : Ideal (𝓞 K) := (1 : Submodule (𝓞 K) K).comap
    (LinearMap.toSpanSingleton (𝓞 K) K a)
  have hD0 : D ≠ ⊥ := by
    obtain ⟨α, β, hβ0, hab⟩ := IsFractionRing.div_surjective (𝓞 K) (a : K)
    have hβ0' : β ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hβ0
    have hβK : (β : K) ≠ 0 := (map_ne_zero_iff _
      (IsFractionRing.injective (𝓞 K) K)).mpr hβ0'
    have hβD : β ∈ D := by
      simp only [D, Submodule.mem_comap, LinearMap.toSpanSingleton_apply,
        Algebra.smul_def, Submodule.mem_one]
      refine ⟨α, ?_⟩
      rw [mul_comm, ← hab]
      exact (div_mul_cancel₀ (α : K) hβK).symm
    intro hDbot
    have : β = 0 := by
      simpa only [hDbot, Ideal.mem_bot] using hβD
    exact hβ0' this
  have hDlocal (v : HeightOneSpectrum (𝓞 K))
      (hv : v.valuation K (a : K) ≤ 1) : ¬ D ≤ v.asIdeal := by
    obtain ⟨α, β, hab⟩ := v.exists_primeCompl_mul_eq_of_integer (a : K) hv
    have hβD : (β : 𝓞 K) ∈ D := by
      simp only [D, Submodule.mem_comap, LinearMap.toSpanSingleton_apply,
        Algebra.smul_def, Submodule.mem_one]
      exact ⟨α, by simpa only [mul_comm] using hab.symm⟩
    intro hDle
    exact β.property (hDle hβD)
  exact ⟨hD0, hDlocal⟩

/-- A global element integral at the places of a modulus has a denominator avoiding that
modulus. This supplies the integral ratio for `normCharacter_toPrincipalIdeal_eq_one`. -/
theorem exists_integral_ratio_coprime_modulus (m : Ideal (𝓞 K)) (hm0 : m ≠ ⊥)
    (a : Kˣ) (ha : ∀ v : HeightOneSpectrum (𝓞 K),
      m ≤ v.asIdeal → v.valuation K (a : K) ≤ 1) :
    ∃ α β : 𝓞 K, β ≠ 0 ∧ (a : K) * (β : K) = (α : K) ∧
      IsCoprime (Ideal.span {β}) m := by
  let D : Ideal (𝓞 K) := (1 : Submodule (𝓞 K) K).comap
    (LinearMap.toSpanSingleton (𝓞 K) K (a : K))
  obtain ⟨hD0, hDlocal⟩ := denominatorIdeal_properties (a : K)
  have hDcop : IsCoprime D m := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    by_contra htop
    obtain ⟨P, hPmax, hP⟩ := Ideal.exists_le_maximal (D ⊔ m) htop
    have hP0 : P ≠ ⊥ := by
      intro h
      exact hm0 (le_bot_iff.mp ((le_sup_right : m ≤ D ⊔ m).trans (hP.trans_eq h)))
    let v : HeightOneSpectrum (𝓞 K) := ⟨P, hPmax.isPrime, hP0⟩
    have hv : m ≤ v.asIdeal := (le_sup_right : m ≤ D ⊔ m).trans hP
    exact hDlocal v (ha v hv) (le_sup_left.trans hP)
  obtain ⟨β, hβD, hβ0, C, _, hspan, hCcop⟩ :=
    exists_mem_span_singleton_eq_mul_isCoprime hD0 hm0
  have hbInt : (LinearMap.toSpanSingleton (𝓞 K) K (a : K)) β ∈
      (1 : Submodule (𝓞 K) K) := hβD
  obtain ⟨α, hα⟩ := Submodule.mem_one.mp hbInt
  refine ⟨α, β, hβ0, ?_, ?_⟩
  · simpa only [LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_comm] using hα.symm
  rw [hspan]
  exact hDcop.mul_left hCcop

end SIC
