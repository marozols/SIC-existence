/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Frobenius.DegreeOne
import SICs.Dilogarithm.Reciprocity.SignedGenerator
import SICs.FieldTheory.EmbeddedGalois

/-!
# The squared dilogarithm values lie in the narrow ray class field

For a modulus `M` with `M𝒪_K x ⊆ I` on `G_{I,ε}` and the narrow ray class field `H` of `K` of
modulus `M𝒪_K`, every squared normalized value `(E_{I,ε}(x)/E_{I,ε}(0))²` lies in the image of
every embedding `H → ℂ`.

This module is the containment step of [RW26b, Radchenko, Wheeler (2026b), Section 8,
Proposition 4] ("every `E_I(x)/E_I(0)` belongs to `H`") for the squared values, by the
identity-class argument with Frobenius generation at primes of absolute degree one in place of
Chebotarev's theorem. The source's field `H⁺_{𝒪,m}` of the
order is replaced by the narrow ray class field of the maximal order with the integer modulus `M`
(`exists_narrowRayClassField`), whose trivial class is described by
`isFrobeniusAt_one_iff_hasSignedRayGenerator`. Squaring removes `E(0) = √ε`, which need not lie
in `H`.

## The argument

Let `u = E(x)/E(0)` and `z = u²`. The values are algebraic (`pseudolatticeDilog_isAlgebraic`),
so `z` lies in a finite Galois extension `L/H` embedded in `ℂ` over `ψ`
(`exists_isGalois_ringHom_complex`); it is an algebraic integer, since `E(x)` and `E(0)` are
units at every valuation above every prime (`pseudolatticeDilog_valuation_eq_one`,
`isIntegral_of_forall_valuation_le_one`).

Let `S` be the primes of `H` above `2`, the primes dividing `M`, and those dividing `disc K`. Let
`w` be a prime of `L` whose prime `𝔓` of `H` below has prime absolute norm `p` and lies outside `S`.
The prime `𝔭 = 𝔓 ∩ 𝒪_K` also has norm `p`, and the identity is the Frobenius element of `H/K` at `𝔓`
(`isFrobeniusAt_one_of_absNorm_prime`); as `𝔭` is prime to `M`, it has a totally positive generator
`≡ 1 (mod M)` (`isFrobeniusAt_one_iff_hasSignedRayGenerator`). At a valuation `v` of `ℂ` above `w`
(`exists_valuation_complex_lt_one_iff`), `v(p) < 1`, and the identity-class congruence
(`pseudolatticeDilog_frobenius_signed` at `s = 1`) gives `u^p ≡ u`, hence `z^p ≡ z`, that is
`z^{N𝔓} - z ∈ w`. By the congruence criterion (`mem_range_of_pow_absNorm_sub_mem`), `z ∈ H`.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped NNReal

namespace SIC

variable {K : Type*} [Field K] [NumberField K]

/-! ### The finite prime exclusion -/

/-- **The prime conditions of the reciprocity argument hold outside a finite set**: for `M > 0`
and an extension `H/K`, all but finitely many primes `𝔓` of `H` of prime absolute norm `p`
satisfy `p ≠ 2`, `p ∤ disc K`, and `𝔓 ∩ 𝒪_K` coprime to `M𝒪_K`: the primes dividing
`2M disc K` are finite in number. The exclusion of [RW26b, Radchenko, Wheeler (2026b),
Section 8, proof of Proposition 4] of the primes dividing `cm` and of `2`; with `H = K` it
applies to primes of `K` (`FinitePlace.below_self`). -/
theorem exists_rayPrime_exclusion {M : ℕ} (hM0 : 0 < M)
    {H : Type*} [Field H] [NumberField H] [Algebra K H] :
    ∃ S : Finset (HeightOneSpectrum (𝓞 H)),
      ∀ P : HeightOneSpectrum (𝓞 H), P ∉ S → (Ideal.absNorm P.asIdeal).Prime →
        Ideal.absNorm P.asIdeal ≠ 2 ∧
          ¬ ((Ideal.absNorm P.asIdeal : ℕ) : ℤ) ∣ NumberField.discr K ∧
            IsCoprime (FinitePlace.below (K := K) P).asIdeal (Ideal.span {(M : 𝓞 K)}) := by
  classical
  let N : ℕ := 2 * M * (NumberField.discr K).natAbs
  have hN : N ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) hM0.ne')
    (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K))
  let S := (finite_primes_containing (R := 𝓞 H) (Nat.cast_ne_zero.mpr hN)).toFinset
  refine ⟨S, ?_⟩
  intro P hPS hp
  let p := Ideal.absNorm P.asIdeal
  have hNnot : (N : 𝓞 H) ∉ P.asIdeal := by
    intro hmem
    exact hPS (by simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hmem)
  have hcopN : p.Coprime N :=
    (absNorm_coprime_iff_natCast_notMem P).mpr hNnot
  have hcop2M : p.Coprime (2 * M) := (Nat.coprime_mul_iff_right.mp hcopN).1
  have hcop2 : p.Coprime 2 := (Nat.coprime_mul_iff_right.mp hcop2M).1
  have hcopM : p.Coprime M := (Nat.coprime_mul_iff_right.mp hcop2M).2
  have hcopD : p.Coprime (NumberField.discr K).natAbs :=
    (Nat.coprime_mul_iff_right.mp hcopN).2
  have hp2 : p ≠ 2 := by
    intro heq
    have hbad : (2 : ℕ).Coprime 2 := by simpa only [← heq] using hcop2
    norm_num at hbad
  have hdisc : ¬ (p : ℤ) ∣ NumberField.discr K := by
    intro hdiv
    exact (hp.coprime_iff_not_dvd.mp hcopD) (Int.natCast_dvd.mp hdiv)
  have hnormK : Ideal.absNorm (FinitePlace.below (K := K) P).asIdeal = p :=
    FinitePlace.absNorm_below_eq_of_prime P hp
  have hMnot : (M : 𝓞 K) ∉ (FinitePlace.below (K := K) P).asIdeal :=
    (absNorm_coprime_iff_natCast_notMem _).mp (by rw [hnormK]; exact hcopM)
  have : (FinitePlace.below (K := K) P).asIdeal.IsMaximal :=
    (FinitePlace.below (K := K) P).isMaximal
  exact ⟨hp2, hdisc, isCoprime_span_singleton_of_notMem _ hMnot⟩

variable [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K} {B : PseudolatticeBasis F} {ε : K}

/-! ### Integrality of squared values -/

/-- **The squared normalized values are algebraic integers**: in a number field `L` embedded in
`ℂ` by `ι`, an element `z` with `ι(z) = (E_{I,ε}(x)/E_{I,ε}(0))²` is integral, since `E_{I,ε}(x)`
and `E_{I,ε}(0)` are units at every valuation above a prime (`pseudolatticeDilog_valuation_eq_one`,
[RW26b, Radchenko, Wheeler (2026b), Section 5, Theorem 5]). -/
theorem pseudolatticeDilog_sq_isIntegral (h : B.IsPeriod ε)
    {x : K} (hx : (ε - 1) * x ∈ B.submodule)
    {L : Type*} [Field L] [NumberField L] (ι : L →+* ℂ) {z : L}
    (hz : ι z = (pseudolatticeDilog h x / pseudolatticeDilog h 0) ^ 2) :
    IsIntegral ℤ z := by
  apply isIntegral_of_forall_valuation_le_one ι
  intro v p hp hvp
  let _ : Fact p.Prime := ⟨hp⟩
  have hvx := pseudolatticeDilog_valuation_eq_one v hvp h hx
  have hv0 : v (pseudolatticeDilog h 0) = 1 :=
    pseudolatticeDilog_valuation_eq_one v hvp h (by simp)
  have hvu : v (pseudolatticeDilog h x / pseudolatticeDilog h 0) = 1 := by
    rw [v.map_div, hvx, hv0]
    simp
  rw [hz, v.map_pow, hvu]
  norm_num

/-! ### From the local congruence to a prime ideal -/

/-- At an eligible degree-one prime of `H`, the square of a normalized value satisfies the
congruence in the integer ring of an embedded extension; used by
`pseudolatticeDilog_sq_mem_rayField`. -/
private theorem pseudolatticeDilog_sq_pow_sub_mem (h : B.IsPeriod ε)
    {M : ℕ} (hM : ∀ a : 𝓞 K, ∀ x : K, (ε - 1) * x ∈ B.submodule →
      (M : K) * (a : K) * x ∈ B.submodule)
    {H : Type*} [Field H] [NumberField H] [Algebra K H] [IsAbelianGalois K H]
    (hU : (IdeleClassGroup.norm (K := K) (L := H)).range =
      IdeleClassGroup.raySubgroup Set.univ (Ideal.span {(M : 𝓞 K)}))
    {L : Type*} [Field L] [NumberField L] [Algebra H L] (ι : L →+* ℂ)
    (zO : 𝓞 L) {x : K} (hx : (ε - 1) * x ∈ B.submodule)
    (hzO : ι (zO : L) = (pseudolatticeDilog h x / pseudolatticeDilog h 0) ^ 2)
    (w : HeightOneSpectrum (𝓞 L))
    (hwprime : (Ideal.absNorm (FinitePlace.below (K := H) w).asIdeal).Prime)
    (hgood : Ideal.absNorm (FinitePlace.below (K := H) w).asIdeal ≠ 2 ∧
      ¬ ((Ideal.absNorm (FinitePlace.below (K := H) w).asIdeal : ℕ) : ℤ) ∣ NumberField.discr K ∧
        IsCoprime (FinitePlace.below (K := K) (FinitePlace.below (K := H) w)).asIdeal
          (Ideal.span {(M : 𝓞 K)})) :
    zO ^ Ideal.absNorm (FinitePlace.below (K := H) w).asIdeal - zO ∈ w.asIdeal := by
  obtain ⟨hp2, hdisc, hcop⟩ := hgood
  let P : HeightOneSpectrum (𝓞 H) := FinitePlace.below (K := H) w
  let 𝔭 : HeightOneSpectrum (𝓞 K) := FinitePlace.below (K := K) P
  let p : ℕ := Ideal.absNorm P.asIdeal
  let _ : Fact p.Prime := ⟨hwprime⟩
  have hnormK : Ideal.absNorm 𝔭.asIdeal = p :=
    FinitePlace.absNorm_below_eq_of_prime P hwprime
  let _ : P.asIdeal.LiesOver 𝔭.asIdeal := FinitePlace.liesOver_below P
  have hgen : HasSignedRayGenerator (Ideal.span {(M : 𝓞 K)}) 1 𝔭.asIdeal :=
    (isFrobeniusAt_one_iff_hasSignedRayGenerator hU hcop P).mp
      (isFrobeniusAt_one_of_absNorm_prime P hwprime)
  have hpMemW : (p : 𝓞 L) ∈ w.asIdeal := by
    have hp' : (p : 𝓞 H) ∈ w.asIdeal.under (𝓞 H) := Ideal.absNorm_mem P.asIdeal
    rw [Ideal.mem_under] at hp'
    simpa only [map_natCast] using hp'
  exact pseudolatticeDilog_sq_signed_mem h hM ι hx zO zO
    (s := 1) hzO (by simpa using hzO) hp2 hdisc hnormK w hpMemW hgen

/-- **The squared normalized values lie in the narrow ray class field**: let `M > 0` with
`M𝒪_K x ⊆ I` for every `x ∈ G_{I,ε}` (`IsPeriod.exists_modulus_mul_mem`), and let `H/K` be
abelian with norm group the ray subgroup of modulus `M𝒪_K` positive at both real places, the
narrow ray class field (`exists_narrowRayClassField`). Then for every embedding `ψ : H → ℂ` and
every `x ∈ G_{I,ε}`, `(E_{I,ε}(x)/E_{I,ε}(0))² ∈ ψ(H)`. The squared form of the first assertion of
[RW26b, Radchenko, Wheeler (2026b), Section 8, Proposition 4], proved by its identity-class
argument. -/
@[source "RW26b, Proposition 4, p. 14 (first assertion, squared)"]
theorem pseudolatticeDilog_sq_mem_rayField (h : B.IsPeriod ε) {M : ℕ} (hM0 : 0 < M)
    (hM : ∀ a : 𝓞 K, ∀ x : K, (ε - 1) * x ∈ B.submodule →
      (M : K) * (a : K) * x ∈ B.submodule)
    {H : Type*} [Field H] [NumberField H] [Algebra K H] [IsAbelianGalois K H]
    (hU : (IdeleClassGroup.norm (K := K) (L := H)).range =
      IdeleClassGroup.raySubgroup Set.univ (Ideal.span {(M : 𝓞 K)}))
    (ψ : H →+* ℂ) {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    (pseudolatticeDilog h x / pseudolatticeDilog h 0) ^ 2 ∈ ψ.fieldRange := by
  classical
  let u : ℂ := pseudolatticeDilog h x / pseudolatticeDilog h 0
  have hu_alg : IsAlgebraic ℚ u := by
    dsimp [u]
    exact (pseudolatticeDilog_isAlgebraic h hx).mul
      (pseudolatticeDilog_isAlgebraic h (by simp)).inv
  obtain ⟨L, hFL, hNFL, hAHL, hGHL, ι, hιψ, z, hz⟩ :=
    exists_isGalois_ringHom_complex ψ (hu_alg.pow 2)
  let _ : Field L := hFL
  let _ : NumberField L := hNFL
  let _ : Algebra H L := hAHL
  let _ : IsGalois H L := hGHL
  have hz_int : IsIntegral ℤ z :=
    pseudolatticeDilog_sq_isIntegral h hx ι (by simpa only [u] using hz)
  obtain ⟨zO, hzO⟩ :=
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 L) (R := ℤ) (B := L)).mp hz_int
  have hιzO : ι (zO : L) = u ^ 2 := by
    change ι ((algebraMap (𝓞 L) L) zO) = u ^ 2
    rw [hzO, hz]
  obtain ⟨S, hS⟩ := exists_rayPrime_exclusion (K := K) (H := H) hM0
  have hz_range : (zO : L) ∈ (algebraMap H L).range := by
    apply mem_range_of_pow_absNorm_sub_mem S zO
    intro w hwS hwprime
    exact pseudolatticeDilog_sq_pow_sub_mem h hM hU ι zO hx
      (by simpa only [u] using hιzO) w hwprime (hS _ hwS hwprime)
  obtain ⟨a, ha⟩ := hz_range
  apply RingHom.mem_fieldRange.mpr
  refine ⟨a, ?_⟩
  calc
    ψ a = ι ((algebraMap H L) a) := by rw [← hιψ]; rfl
    _ = u ^ 2 := by
      rw [ha]
      change ι ((algebraMap (𝓞 L) L) zO) = u ^ 2
      rw [hzO, hz]

end SIC

end
