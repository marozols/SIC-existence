/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ramification.Basic
import SICs.ClassField.Completion.PlacesAbove
import SICs.FieldTheory.Kummer.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Ramification in Kummer extensions

Radicals of local units, including roots of unity, are unramified away from primes dividing
their exponent.

This follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, Appendix A.5.

The printed hypothesis that each $na_i$ is a local unit is insufficient without local
integrality of the $a_i$. For $K = \mathbb Q$, $n = 2$, and $a_1 = 1/2$, the product is a unit
at $2$, but $\mathbb Q(\sqrt{1/2}) = \mathbb Q(\sqrt 2)$ ramifies there, since $X^2 - 2$ is
Eisenstein. We require $n$ and every radicand separately to be local units, as the source's
discriminant argument needs.

## The argument

Milne uses the discriminant of $X^n-a$: it is invertible when $n$ and $a$ are local units.
We use the equivalent separable reduction criterion. An inertia automorphism preserves the
residue of a local unit radical. Its quotient with that radical is an nth root of unity
congruent to one. The geometric sum shows that such a root is one when n is invertible.
Thus inertia fixes every radical generator and is trivial; its order is the ramification index.
The argument also covers n = 1. For a cyclotomic extension, the radicands are roots of
the unit $1$ and generate the field, so the same inertia argument applies. The tower law
then transfers this unramifiedness through a cyclotomic extension of a number field.
-/

noncomputable section

open IsDedekindDomain NumberField

namespace SIC

/-! ### Reduction of radical generators

An integral numerator and a denominator outside the prime extend the defining inertia
congruence to local units. Separability then forces an inertia automorphism to fix a radical. -/

/-- An nth root of unity congruent to one modulo an ideal is one if n is outside that ideal:
the separable reduction of $X^n-1$, as in the proof of [83, Neukirch (1999), Chapter I,
Proposition 10.3]. It supplies the reduction step in `inertia_fixes_unit_radical`. -/
private theorem eq_one_of_pow_eq_one_of_sub_mem {R : Type*} [CommRing R] [IsDomain R]
    (I : Ideal R) {n : ℕ} {u : R} (hu : u ^ n = 1)
    (hn : (n : R) ∉ I) (h : u - 1 ∈ I) : u = 1 := by
  by_contra hne
  have hs : ∑ i ∈ Finset.range n, u ^ i = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right (sub_ne_zero.mpr hne)
    rw [geom_sum_mul, hu, sub_self]
  have huq : Ideal.Quotient.mk I u = 1 := by
    simpa only [map_one] using (Ideal.Quotient.mk_eq_mk_iff_sub_mem u 1).2 h
  have hnq := congrArg (Ideal.Quotient.mk I) hs
  simp only [map_sum, map_pow, huq, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, map_zero] at hnq
  exact hn (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_natCast] using hnq))

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]

/-- If inertia scales a local unit by an integral factor, that factor reduces to one.
The denominator argument supplies the reduction step in `inertia_fixes_unit_radical`. -/
private theorem inertia_factor_sub_mem (w : HeightOneSpectrum (𝓞 L))
    (σ : L ≃ₐ[K] L) (hσ : σ ∈ w.asIdeal.inertia (L ≃ₐ[K] L))
    {x : L} (hx : w.valuation L x = 1) (u : 𝓞 L) (hu : σ x = (u : L) * x) :
    u - 1 ∈ w.asIdeal := by
  obtain ⟨a, d, hxd⟩ := w.exists_primeCompl_mul_eq_of_integer x hx.le
  change x * ((d : 𝓞 L) : L) = (a : L) at hxd
  have hd : w.intValuation (d : 𝓞 L) = 1 :=
    (w.intValuation_eq_one_iff_mem_primeCompl d).2 d.property
  have ha : a ∉ w.asIdeal := by
    apply HeightOneSpectrum.intValuation_eq_one_iff.mp
    rw [← w.valuation_of_algebraMap (K := L)]
    change w.valuation L (a : L) = 1
    rw [← hxd, map_mul, hx]
    change 1 * w.valuation L (algebraMap (𝓞 L) L (d : 𝓞 L)) = 1
    rw [w.valuation_of_algebraMap, hd, one_mul]
  have heq : (σ • a) * (d : 𝓞 L) = u * a * (σ • (d : 𝓞 L)) := by
    apply RingOfIntegers.coe_injective
    change σ (a : L) * ((d : 𝓞 L) : L) = (u : L) * (a : L) * σ ((d : 𝓞 L) : L)
    rw [← hxd, map_mul, hu]
    ring
  let q := Ideal.Quotient.mk w.asIdeal
  have hred (b : 𝓞 L) : q (σ • b) = q b :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 (hσ b)
  have heq' := congrArg q heq
  simp only [map_mul, hred] at heq'
  have hdq : q (d : 𝓞 L) ≠ 0 := fun h =>
    d.property (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have haq : q a ≠ 0 := fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have huq : q u = 1 := by
    apply mul_right_cancel₀ (mul_ne_zero haq hdq)
    simpa only [one_mul, mul_assoc] using heq'.symm
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, map_one, huq, sub_self]

/-- Inertia fixes an nth root of a base element when that root and n are local units.
Milne, *Class Field Theory*, Chapter VII, Appendix A.5, expressed by separable reduction. -/
theorem inertia_fixes_unit_radical (w : HeightOneSpectrum (𝓞 L))
    (σ : L ≃ₐ[K] L) (hσ : σ ∈ w.asIdeal.inertia (L ≃ₐ[K] L))
    {n : ℕ} (hnw : (n : 𝓞 L) ∉ w.asIdeal)
    {a : K} {x : L} (hpow : x ^ n = algebraMap K L a)
    (hx : w.valuation L x = 1) : σ x = x := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by
    intro h
    apply hnw
    simp [h])
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hratio : (σ x / x) ^ n = 1 := by
    rw [div_pow, ← map_pow, hpow, σ.commutes, ← hpow, div_self (pow_ne_zero _ hx0)]
  let u : 𝓞 L := ⟨σ x / x, IsIntegral.of_pow hn (hratio ▸ isIntegral_one)⟩
  have hu : σ x = (u : L) * x := (div_mul_cancel₀ _ hx0).symm
  have hueq : u = 1 := eq_one_of_pow_eq_one_of_sub_mem w.asIdeal
    (RingOfIntegers.coe_injective hratio) hnw (inertia_factor_sub_mem w σ hσ hx u hu)
  simpa [hueq] using hu

/-! ### The radical extension

The homomorphism extensionality API for the Kummer extension lets the preceding local
calculation prove that its entire inertia group is trivial. -/

variable [NumberField K]

/-- The radical extension of a finitely generated group of local units is unramified away
from n. Milne, *Class Field Theory*, Chapter VII, Appendix A.5, for a group of radicands.
The separate unit hypotheses on $n$ and the radicands correct the source's insufficient
product-unit hypothesis; see the counterexample in the module docstring. -/
theorem ramificationIdx_kummerExtension_eq_one {n : ℕ}
    (B : Subgroup Kˣ) (hB : B.FG)
    (v : HeightOneSpectrum (𝓞 K)) (hunit : ∀ b : B, v.valuation K (b.val : K) = 1)
    (hnv : (n : 𝓞 K) ∉ v.asIdeal)
    (w : HeightOneSpectrum (𝓞 (kummerExtension K n B))) [w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  have hn0 : n ≠ 0 := by
    intro h
    apply hnv
    simp [h]
  have : NeZero n := ⟨hn0⟩
  let M := kummerExtension K n B
  let : FiniteDimensional K M := kummerExtension_finiteDimensional (NeZero.pos n) hB
  let : NumberField M := NumberField.of_module_finite K M
  let : Normal K M := kummerExtension_normal (n := n)
  let : IsGalois K M := ⟨⟩
  have hnw : (n : 𝓞 M) ∉ w.asIdeal := by
    simpa only [map_natCast] using
      (not_congr (Ideal.mem_of_liesOver w.asIdeal v.asIdeal (n : 𝓞 K))).mp hnv
  have hinertia : w.asIdeal.inertia (M ≃ₐ[K] M) = ⊥ := by
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro σ hσ
    apply AlgEquiv.coe_toAlgHom_injective
    apply kummerExtension_algHom_ext
    intro b x hx
    apply inertia_fixes_unit_radical w σ hσ hnw hx
    apply (pow_eq_one_iff_left (NeZero.ne n)).mp
    rw [← map_pow, hx, ← v.valuation_liesOver M w, hunit, one_pow]
  exact ramificationIdx_eq_one_of_inertia_eq_bot v.ne_bot w.asIdeal hinertia

/-! ### Cyclotomic extensions

Roots of unity are radicals of the unit $1$. They generate a cyclotomic extension, so inertia
fixes the entire extension away from primes dividing the cyclotomic level. -/

variable {M : Type*} [Field M] [NumberField M] [Algebra K M]

/-- **Cyclotomic extensions are unramified away from their level**: every prime of a
cyclotomic extension `K(ζ_n)/K` above $\mathfrak p \nmid n$ has ramification index one.
[83, Neukirch (1999), Chapter I, Corollary 10.4], which states the equivalence over `ℚ` (with the
exception `p = 2 = (4, n)`), of which only the unramified direction is formalized, over any base
field; Milne, *Class Field Theory*,
Chapter VII, Appendix A.5, for the radicals of the unit `1`. -/
@[source "83, Chapter I, Corollary 10.4, p. 63 (unramified direction, over a number field)"]
theorem ramificationIdx_eq_one_of_isCyclotomicExtension {n : ℕ}
    [IsCyclotomicExtension {n} K M] (v : HeightOneSpectrum (𝓞 K))
    (hnv : (n : 𝓞 K) ∉ v.asIdeal) (w : HeightOneSpectrum (𝓞 M))
    [w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  have hn0 : n ≠ 0 := by
    intro h
    apply hnv
    simp [h]
  have : NeZero n := ⟨hn0⟩
  let _ : IsGalois K M := IsCyclotomicExtension.isGalois {n} K M
  have hnw : (n : 𝓞 M) ∉ w.asIdeal := by
    simpa only [map_natCast] using
      (not_congr (Ideal.mem_of_liesOver w.asIdeal v.asIdeal (n : 𝓞 K))).mp hnv
  have hinertia : w.asIdeal.inertia (M ≃ₐ[K] M) = ⊥ := by
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro σ hσ
    apply IsCyclotomicExtension.algEquiv_eq_of_apply_eq {n} K M
    intro m hm hm0
    have hmn : m = n := Set.mem_singleton_iff.mp hm
    subst m
    obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K M
      (Set.mem_singleton n) (NeZero.ne n)
    refine ⟨ζ, hζ, ?_⟩
    apply inertia_fixes_unit_radical w σ hσ hnw (a := (1 : K))
    · simpa using hζ.pow_eq_one
    · apply (pow_eq_one_iff_left (NeZero.ne n)).mp
      rw [← map_pow, hζ.pow_eq_one, map_one]
  exact ramificationIdx_eq_one_of_inertia_eq_bot v.ne_bot w.asIdeal hinertia


/-! ### Ramification of `L(ζ_M)/K` -/

variable {Ω : Type*} [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]

omit [NumberField K] in
/-- A prime of $L(\zeta_M)$ above a prime `v ∤ M` of `K` is unramified over `K` when the prime of
`L` below it is: $e(w\mid v) = e(w\mid w_L)\,e(w_L\mid v) = e(w_L\mid v)$. -/
theorem IsCyclotomicExtension.ramificationIdx_eq_one_of_below [NumberField Ω]
    {M : ℕ} [NeZero M] [IsCyclotomicExtension {M} L Ω]
    (w : HeightOneSpectrum (𝓞 Ω))
    (hL : (FinitePlace.below (K := L) w).asIdeal.ramificationIdx (𝓞 K) = 1)
    (hM : (M : 𝓞 K) ∉ (FinitePlace.below (K := K) w).asIdeal) :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  let v := FinitePlace.below (K := L) w
  have hMv : (M : 𝓞 L) ∉ v.asIdeal := by
    have hMK : (M : 𝓞 K) ∉ (FinitePlace.below (K := K) v).asIdeal := by
      simpa only [v, FinitePlace.below_below] using hM
    simpa only [map_natCast] using
      (not_congr (Ideal.mem_of_liesOver v.asIdeal
        (FinitePlace.below (K := K) v).asIdeal (M : 𝓞 K))).mp hMK
  have hΩ := ramificationIdx_eq_one_of_isCyclotomicExtension v hMv w
  rw [Ideal.ramificationIdx_tower (R := 𝓞 K) (S := 𝓞 L) (T := 𝓞 Ω)
    (q := v.asIdeal) (r := w.asIdeal), hL, hΩ, one_mul]

end SIC
