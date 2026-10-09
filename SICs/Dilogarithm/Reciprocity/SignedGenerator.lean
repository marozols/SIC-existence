/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.RayClassField.Narrow
import SICs.Dilogarithm.Frobenius.SplitCongruence
import SICs.Dilogarithm.Reciprocity.IdealTranslation
import SICs.Valuation.NumberField

/-!
# The signed Frobenius congruence and its squared form

If a prime `𝔭` of `K` of absolute norm an odd prime `p ∤ disc K` has a generator `α ≡ 1 (mod M𝒪_K)`
of the same sign `s = ±1` at both real places, then `u_x^p ≡ u_{sx}` at every valuation of `ℂ`
above `p`, for the normalized values `u_x = E_{I,ε}(x)/E_{I,ε}(0)`.
Squaring gives a congruence for integral representatives in a number field embedded in `ℂ`.

This module is the case of the classes `1` and `s₁s₂` in the proof of [RW26b, Radchenko, Wheeler
(2026b), Section 8, Proposition 4]: the split Frobenius congruence of Theorem 8 at the two primes
`𝔭 = (α)` and `𝔮 = (α')` above `p`, whose translations act by Lemma 8 and positive homothety. For
`s = 1` this is the trivial class; for `s = -1` the generator `β = -α ≫ 0` is `≡ -1`, and both
translations replace `x` by `-x`, so the two split-prime congruences agree. The modulus `M`
is that of `IsPeriod.exists_modulus_mul_mem`. `SICs.Dilogarithm.Reciprocity.RayField` and
`SICs.Dilogarithm.Reciprocity.SignClass` combine it with Frobenius elements.

## The argument

*The generator.* `𝔭 = (α)` with `α ∈ 𝒪_K`, `α - 1 ∈ M𝒪_K` and `sα ≫ 0`; put `β = sα`, so
`β ≫ 0` and `β - s ∈ M𝒪_K`. Then `N(β) = |N(β)| = N𝔭 = p`, positive since `β ≫ 0`. The
conjugate `β' = Tr β - β` satisfies `β' - s = (Tr β - 2s) - (β - s)` with
`Tr β - 2s = Tr(β - s) ∈ M Tr(𝒪_K) ⊆ Mℤ`, so also `β' - s ∈ M𝒪_K`. If `p ∣ t = Tr β`, then
`β, β' ∈ 𝔭`, hence `p = ββ' ∈ 𝔭²`; unramifiedness excludes this
(`NumberField.not_dvd_discr_iff_forall_mem`).

*The congruence.* `β, β'` preserve `I` (as `M𝒪_K I ⊆ I`), so `β⁻¹I`, `β'⁻¹I` are a split pair of
lines (`isSplitLinePair_inv_smul`), and Theorem 8 (`pseudolatticeDilog_frobenius_split`) gives
`E_{J,ε}(x)/E_{I,ε}(0) ≡ (E_{I,ε}(x)/E_{I,ε}(0))^p` for one of them, `J`. Both `βx - sx` and
`β'x - sx` lie in `M𝒪_K x ⊆ I`, so `E_{J,ε}(x) = E_{I,ε}(sx)` (`pseudolatticeDilog_inv_smul`).
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped NNReal

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

/-! ### A generator of constant sign congruent to one

Its norm, its trace, and its conjugate. -/

omit [NumberField.IsTotallyReal K] in
/-- A prime ideal of norm `p` above a prime not dividing the field discriminant cannot contain
`p` in its square; used by `trace_not_dvd_of_unramified_prime_generator`. -/
private theorem not_mem_square_of_unramified_prime {p : ℕ} [Fact p.Prime]
    (hdisc : ¬ (p : ℤ) ∣ NumberField.discr K) (P : Ideal (𝓞 K))
    (hnorm : Ideal.absNorm P = p) : (p : 𝓞 K) ∉ P ^ 2 := by
  have hp : p.Prime := Fact.out
  have hPprime : P.IsPrime :=
    Ideal.isPrime_of_irreducible_absNorm
      (by simpa [hnorm] using (Nat.irreducible_iff_nat_prime p).mpr hp)
  have : P.IsPrime := hPprime
  have hp_mem : (p : 𝓞 K) ∈ P := by
    simpa [hnorm] using Ideal.absNorm_mem P
  have : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨by simpa [hnorm, Ideal.under] using
      (Ideal.span_singleton_absNorm (I := P) (by simpa [hnorm] using hp))⟩
  have hunram : Algebra.IsUnramifiedAt ℤ P :=
    (NumberField.not_dvd_discr_iff_forall_mem K (𝓞 K)
      (Nat.prime_iff_prime_int.mp hp)).mp hdisc P hPprime (by simpa using hp_mem)
  have : Algebra.IsUnramifiedAt ℤ P := hunram
  have hpIdeal_ne : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using (Int.ofNat_ne_zero.mpr hp.ne_zero)
  have he : (Ideal.span {(p : ℤ)}).ramificationIdx' P = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hpIdeal_ne]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := ℤ) (p := P)
  have hmap_le (Q : Ideal (𝓞 K)) (h : (p : 𝓞 K) ∈ Q) :
      Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ Q := by
    apply Ideal.map_le_of_le_comap
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    simpa using h
  intro hp_sq
  exact ((Ideal.ramificationIdx'_ne_one_iff (hmap_le P hp_mem)).mpr
    (hmap_le (P ^ 2) hp_sq)) he

/-- For the generator of a prime ideal of norm `p`, unramifiedness forces its integral trace to
be prime to `p`; used by `HasSignedRayGenerator.exists_split_generator`. -/
private theorem trace_not_dvd_of_unramified_prime_generator
    (F : RealQuadraticFieldData K) {p : ℕ} [Fact p.Prime]
    (hdisc : ¬ (p : ℤ) ∣ NumberField.discr K) (a : 𝓞 K)
    (hnorm : Ideal.absNorm (Ideal.span {a}) = p)
    (hN : Algebra.norm ℚ (a : K) = p) :
    ¬ (p : ℤ) ∣ Algebra.trace ℤ (𝓞 K) a := by
  let P : Ideal (𝓞 K) := Ideal.span {a}
  let t : ℤ := Algebra.trace ℤ (𝓞 K) a
  have hp_mem : (p : 𝓞 K) ∈ P := by
    simpa [P, hnorm] using Ideal.absNorm_mem P
  intro hpt
  obtain ⟨z, hz⟩ := hpt
  have ht_mem : (t : 𝓞 K) ∈ P := by
    dsimp only [t]
    rw [hz, Int.cast_mul]
    exact Ideal.mul_mem_right _ P (by simpa using hp_mem)
  have ha_mem : a ∈ P := Ideal.mem_span_singleton_self a
  have ha'_mem : (t : 𝓞 K) - a ∈ P := P.sub_mem ht_mem ha_mem
  have htraceK : ((Algebra.trace ℚ K (a : K) : ℚ) : K) = (t : K) := by
    rw [← Algebra.coe_trace_int a]
    norm_cast
  have hnormK : ((Algebra.norm ℚ (a : K) : ℚ) : K) = (p : K) := by
    rw [hN]
    norm_cast
  have hprod : a * ((t : 𝓞 K) - a) = (p : 𝓞 K) := by
    apply RingOfIntegers.coe_injective
    change (a : K) * ((t : K) - (a : K)) = (p : K)
    have hsq := sq_eq_trace_mul_sub_norm F.finrank_eq_two (a : K)
    rw [htraceK, hnormK] at hsq
    linear_combination -hsq
  have hp_mem_sq : (p : 𝓞 K) ∈ P ^ 2 := by
    rw [← hprod, pow_two]
    exact Ideal.mul_mem_mul ha_mem ha'_mem
  exact (not_mem_square_of_unramified_prime hdisc P hnorm) hp_mem_sq

/-- Total positivity removes the absolute value from the norm of a principal ideal; used by
`HasSignedRayGenerator.exists_split_generator`. -/
private theorem norm_eq_prime_of_totally_positive (F : RealQuadraticFieldData K) {p : ℕ}
    (a : 𝓞 K) (hpos : F.IsTotallyPositive (a : K))
    (hnorm : Ideal.absNorm (Ideal.span {a}) = p) : Algebra.norm ℚ (a : K) = p := by
  have hnormabs : (Algebra.norm ℤ a).natAbs = p := by
    simpa [Ideal.absNorm_span_singleton] using hnorm
  have hnormpos : 0 < Algebra.norm ℚ (a : K) := by
    have h := F.mul_realEmbeddingAt_otherPlace_eq_norm (a : K)
    have h' : 0 < ((Algebra.norm ℚ (a : K) : ℚ) : ℝ) := by
      rw [← h]
      exact mul_pos hpos.place_pos hpos.otherPlace_pos
    exact_mod_cast h'
  have hnormIntPos : 0 < Algebra.norm ℤ a := by
    rw [← Algebra.coe_norm_int a] at hnormpos
    exact_mod_cast hnormpos
  have hnormInt : Algebra.norm ℤ a = (p : ℤ) := by omega
  rw [← Algebra.coe_norm_int a, hnormInt]
  norm_cast

/-- Congruence `a ≡ s (mod M)` also holds for its trace conjugate in a quadratic field; used by
`HasSignedRayGenerator.exists_split_generator`. -/
private theorem conjugate_sub_int_eq_modulus_mul (F : RealQuadraticFieldData K) {M : ℕ}
    (s : ℤ) {a b : 𝓞 K} (hM : a - s = (M : 𝓞 K) * b) :
    (Algebra.trace ℚ K (a : K) : K) - (a : K) - s =
      (M : K) * (((Algebra.trace ℤ (𝓞 K) b : 𝓞 K) - b : 𝓞 K) : K) := by
  have htraceS : Algebra.trace ℤ (𝓞 K) (s : 𝓞 K) = 2 * s := by
    simpa [RingOfIntegers.rank K, F.finrank_eq_two] using
      (Algebra.trace_algebraMap (R := ℤ) (S := 𝓞 K) s)
  have htraceMul : Algebra.trace ℤ (𝓞 K) ((M : 𝓞 K) * b) =
      (M : ℤ) * Algebra.trace ℤ (𝓞 K) b := by
    simpa [Algebra.smul_def, smul_eq_mul] using
      (map_smul (Algebra.trace ℤ (𝓞 K)) (M : ℤ) b)
  have ht := congrArg (Algebra.trace ℤ (𝓞 K)) hM
  simp only [map_sub, htraceS, htraceMul] at ht
  have htK : (Algebra.trace ℤ (𝓞 K) a : K) - 2 * s =
      (M : K) * (Algebra.trace ℤ (𝓞 K) b : K) := by exact_mod_cast ht
  have hMcast : (a : K) - s = (M : K) * (b : K) := by
    simpa only [map_sub, map_intCast, map_natCast, map_mul] using
      congrArg (fun z : 𝓞 K => (z : K)) hM
  rw [← Algebra.coe_trace_int a]
  push_cast
  calc
    (Algebra.trace ℤ (𝓞 K) a : K) - (a : K) - s =
        ((Algebra.trace ℤ (𝓞 K) a : K) - 2 * s) - ((a : K) - s) := by ring
    _ = (M : K) * ((Algebra.trace ℤ (𝓞 K) b : K) - (b : K)) := by
      rw [htK, hMcast]
      ring

/-- **A prime with a generator of constant sign congruent to one**: if `𝔭` has absolute norm a
prime `p ∤ disc K` and `HasSignedRayGenerator (M) s 𝔭` for a constant sign `s = ±1`, then
`𝔭 = (α)` and `β = sα` satisfies `β ≫ 0`, `N(β) = p`, `Tr β` an integer prime to `p`, and
`β - s`, `β' - s ∈ M𝒪_K` for the conjugate `β' = Tr β - β`. The generators of `𝔭` and `𝔮 = 𝔭'`
in [RW26b, Radchenko, Wheeler (2026b), Section 8, proof of Proposition 4], for the classes `1`
and `s₁s₂`; consumed by `pseudolatticeDilog_frobenius_signed`. -/
private theorem HasSignedRayGenerator.exists_split_generator
    (F : RealQuadraticFieldData K) {M p : ℕ}
    [Fact p.Prime] (hdisc : ¬ (p : ℤ) ∣ NumberField.discr K) {𝔭 : Ideal (𝓞 K)}
    (hnorm : Ideal.absNorm 𝔭 = p) {s : ℤˣ}
    (hgen : HasSignedRayGenerator (Ideal.span {(M : 𝓞 K)}) (fun _ => s) 𝔭) :
    ∃ β : K, F.IsTotallyPositive β ∧ Algebra.norm ℚ β = p ∧
      (∃ t : ℤ, Algebra.trace ℚ K β = t ∧ ¬ (p : ℤ) ∣ t) ∧
      (∃ a : 𝓞 K, β - ((s : ℤ) : K) = (M : K) * (a : K)) ∧
      ∃ a : 𝓞 K, (Algebra.trace ℚ K β : K) - β - ((s : ℤ) : K) = (M : K) * (a : K) := by
  obtain ⟨a, h𝔭, haM, hpos⟩ := hgen
  let β : 𝓞 K := (s : ℤ) * a
  have hβpos : F.IsTotallyPositive (β : K) :=
    ⟨by simpa [β, mul_assoc] using hpos F.place,
      by simpa [β, mul_assoc] using hpos F.otherPlace⟩
  have hsunit : IsUnit ((s : ℤ) : 𝓞 K) := by
    apply isUnit_iff_dvd_one.mpr
    refine ⟨((s : ℤ) : 𝓞 K), ?_⟩
    exact_mod_cast (Int.units_coe_mul_self s).symm
  have hspan : Ideal.span {β} = Ideal.span {a} := by
    exact Ideal.span_singleton_mul_left_unit hsunit a
  have hnorm' : Ideal.absNorm (Ideal.span {β}) = p := by
    rw [hspan]
    simpa [← h𝔭] using hnorm
  have hnormK := norm_eq_prime_of_totally_positive F β hβpos hnorm'
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp haM
  have hM : β - (s : ℤ) = (M : 𝓞 K) * ((s : ℤ) * b) := by
    calc
      β - (s : ℤ) = (s : 𝓞 K) * (a - 1) := by dsimp [β]; ring
      _ = (s : 𝓞 K) * ((M : 𝓞 K) * b) := by rw [hb]
      _ = _ := by ring
  let t : ℤ := Algebra.trace ℤ (𝓞 K) β
  have htr : Algebra.trace ℚ K (β : K) = (t : ℚ) := (Algebra.coe_trace_int β).symm
  refine ⟨(β : K), hβpos, hnormK,
    ⟨t, htr, trace_not_dvd_of_unramified_prime_generator F hdisc β hnorm' hnormK⟩,
    ⟨(s : ℤ) * b, by
      simpa only [map_sub, map_intCast, map_natCast, map_mul] using
        congrArg (fun z : 𝓞 K => (z : K)) hM⟩,
    ⟨(Algebra.trace ℤ (𝓞 K) ((s : ℤ) * b) : 𝓞 K) - (s : ℤ) * b,
      conjugate_sub_int_eq_modulus_mul F (s : ℤ) hM⟩⟩

/-! ### The congruence at a generator of constant sign -/

variable {F : RealQuadraticFieldData K} {B : PseudolatticeBasis F} {ε : K}

/-- A scalar congruent to a sign modulo a modulus for `G_{I,ε}` preserves `I`; used by
`pseudolatticeDilog_frobenius_signed`. -/
private theorem mul_mem_of_modulus_congr (h : B.IsPeriod ε) {M : ℕ}
    (hM : ∀ a : 𝓞 K, ∀ x : K, (ε - 1) * x ∈ B.submodule →
      (M : K) * (a : K) * x ∈ B.submodule)
    {α : K} {a : 𝓞 K} {s : ℤˣ} (ha : α - ((s : ℤ) : K) = (M : K) * (a : K)) :
    ∀ x ∈ B.submodule, α * x ∈ B.submodule := by
  intro x hx
  have hperiod : (ε - 1) * x ∈ B.submodule := by
    rw [sub_mul, one_mul]
    exact B.submodule.sub_mem (h.mul_mem hx) hx
  have hmove := hM a x hperiod
  have heq : α * x = ((s : ℤ) : K) * x + (M : K) * (a : K) * x := by rw [← ha]; ring
  rw [heq]
  exact B.submodule.add_mem
    (by simpa only [zsmul_eq_mul] using B.submodule.smul_mem (s : ℤ) hx) hmove

/-- A positive scalar congruent to `s` modulo `M` sends the value at `x` on its inverse
translate to the value at `sx` on `I`; used by `pseudolatticeDilog_frobenius_signed`. -/
private theorem pseudolatticeDilog_signed_translate (h : B.IsPeriod ε) {M : ℕ}
    (hM : ∀ a : 𝓞 K, ∀ x : K, (ε - 1) * x ∈ B.submodule →
      (M : K) * (a : K) * x ∈ B.submodule)
    {β : K} (hβ : F.IsTotallyPositive β) {s : ℤˣ} {a : 𝓞 K}
    (ha : β - ((s : ℤ) : K) = (M : K) * (a : K))
    {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    pseudolatticeDilog (h.smul β⁻¹ hβ.inv) x =
      pseudolatticeDilog h (((s : ℤ) : K) * x) := by
  have hβx : β * x - ((s : ℤ) : K) * x ∈ B.submodule := by
    have heq : β * x - ((s : ℤ) : K) * x = (M : K) * (a : K) * x := by
      rw [← ha]
      ring
    rw [heq]
    exact hM a x hx
  have hsx : (ε - 1) * (((s : ℤ) : K) * x) ∈ B.submodule := by
    have hh := B.submodule.smul_mem (s : ℤ) hx
    convert hh using 1
    simp only [zsmul_eq_mul]
    ring
  exact pseudolatticeDilog_inv_smul h hβ hsx hβx

/-- **The Frobenius congruence at a prime with a generator of constant sign**: let `p ∤ disc K` be
an odd prime, `v` a valuation of `ℂ` with `v(p) < 1`, `M` a modulus with `M𝒪_K x ⊆ I` for every
`x ∈ G_{I,ε}`, and `𝔭` a prime of absolute norm `p` with a generator `≡ 1 (mod M)` of sign
`s = ±1` at both real places. Then for every `x ∈ G_{I,ε}`, with `u_x = E_{I,ε}(x)/E_{I,ε}(0)`,
$$u_x^p\equiv u_{sx}\pmod{\mathfrak m}.$$
[RW26b, Radchenko, Wheeler (2026b), Section 7, Theorem 8] at `𝔭⁻¹I`, `𝔮⁻¹I`, whose values are
those of `I` at `sx` by Lemma 8: the classes `1` and `s₁s₂` in the proof of Proposition 4. -/
theorem pseudolatticeDilog_frobenius_signed (v : Valuation ℂ ℝ≥0) {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hvp : v (p : ℂ) < 1) (hdisc : ¬ (p : ℤ) ∣ NumberField.discr K)
    (h : B.IsPeriod ε) {M : ℕ}
    (hM : ∀ a : 𝓞 K, ∀ x : K, (ε - 1) * x ∈ B.submodule →
      (M : K) * (a : K) * x ∈ B.submodule)
    {𝔭 : Ideal (𝓞 K)} (hnorm : Ideal.absNorm 𝔭 = p) {s : ℤˣ}
    (hgen : HasSignedRayGenerator (Ideal.span {(M : 𝓞 K)}) (fun _ => s) 𝔭)
    {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    v ((pseudolatticeDilog h x / pseudolatticeDilog h 0) ^ p -
      pseudolatticeDilog h (((s : ℤ) : K) * x) / pseudolatticeDilog h 0) < 1 := by
  obtain ⟨β, hβ, hN, ⟨t, ht, hpt⟩, ⟨a, ha⟩, ⟨a', ha'⟩⟩ :=
    hgen.exists_split_generator F hdisc hnorm
  let δ : K := (Algebra.trace ℚ K β : K) - β
  have hδ : F.IsTotallyPositive δ := hβ.trace_sub
  have hβI := mul_mem_of_modulus_congr h hM ha
  have hδI := mul_mem_of_modulus_congr h hM
    (show δ - ((s : ℤ) : K) = (M : K) * (a' : K) from ha')
  let B' : Fin 2 → PseudolatticeBasis F :=
    ![B.smul β⁻¹ hβ.inv, B.smul δ⁻¹ hδ.inv]
  have hJ : IsSplitLinePair p B.submodule fun i => (B' i).submodule := by
    exact isSplitLinePair_inv_smul hβ hN ht hpt hβI hδI
  obtain ⟨i, hi⟩ := pseudolatticeDilog_frobenius_split v hp hvp h hJ
  have hval : pseudolatticeDilog
      (h.of_mul_mem (hJ.mul_mem i ε (fun _ hy => h.mul_mem hy))) x =
      pseudolatticeDilog h (((s : ℤ) : K) * x) := by
    fin_cases i
    · change pseudolatticeDilog (h.smul β⁻¹ hβ.inv) x = _
      exact pseudolatticeDilog_signed_translate h hM hβ ha hx
    · change pseudolatticeDilog (h.smul δ⁻¹ hδ.inv) x = _
      exact pseudolatticeDilog_signed_translate h hM hδ
        (show δ - ((s : ℤ) : K) = (M : K) * (a' : K) from ha') hx
  have hcongr := hi x hx
  rw [hval] at hcongr
  have hneg :
      (pseudolatticeDilog h x / pseudolatticeDilog h 0) ^ p -
        pseudolatticeDilog h (((s : ℤ) : K) * x) / pseudolatticeDilog h 0 =
      -(pseudolatticeDilog h (((s : ℤ) : K) * x) / pseudolatticeDilog h 0 -
        (pseudolatticeDilog h x / pseudolatticeDilog h 0) ^ p) := by ring
  rw [hneg, v.map_neg]
  exact hcongr

/-! ### Squared congruences in valuations and integer rings

Squaring the signed Frobenius congruence gives the form used by both ray-field containment and
the action of the totally negative sign class. -/

/-- For a constant sign `s`, the square of the normalized value at `x` satisfies
`u_x^{2p} ≡ u_{sx}²` at a valuation above `p`, where `u_y = E(y)/E(0)`.
Derived from `pseudolatticeDilog_frobenius_signed`. -/
private theorem pseudolatticeDilog_sq_frobenius_signed (h : B.IsPeriod ε)
    {M : ℕ} (hM : ∀ a : 𝓞 K, ∀ x : K, (ε - 1) * x ∈ B.submodule →
      (M : K) * (a : K) * x ∈ B.submodule)
    (v : Valuation ℂ ℝ≥0) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hvp : v (p : ℂ) < 1)
    (hdisc : ¬ (p : ℤ) ∣ NumberField.discr K)
    {𝔭 : Ideal (𝓞 K)} (hnorm : Ideal.absNorm 𝔭 = p) {s : ℤˣ}
    (hgen : HasSignedRayGenerator (Ideal.span {(M : 𝓞 K)}) (fun _ => s) 𝔭)
    {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    v (((pseudolatticeDilog h x / pseudolatticeDilog h 0) ^ 2) ^ p -
      (pseudolatticeDilog h (((s : ℤ) : K) * x) / pseudolatticeDilog h 0) ^ 2) < 1 := by
  let u : ℂ := pseudolatticeDilog h x / pseudolatticeDilog h 0
  let t : ℂ := pseudolatticeDilog h (((s : ℤ) : K) * x) / pseudolatticeDilog h 0
  have hsx : (ε - 1) * (((s : ℤ) : K) * x) ∈ B.submodule := by
    have hh := B.submodule.smul_mem (s : ℤ) hx
    convert hh using 1
    simp only [zsmul_eq_mul]
    ring
  have hunit (y : K) (hy : (ε - 1) * y ∈ B.submodule) :
      v (pseudolatticeDilog h y / pseudolatticeDilog h 0) = 1 := by
    rw [v.map_div, pseudolatticeDilog_valuation_eq_one v hvp h hy,
      pseudolatticeDilog_valuation_eq_one v hvp h (by simp)]
    simp
  have hcong : v (u ^ p - t) < 1 := by
    simpa only [u, t] using
      (pseudolatticeDilog_frobenius_signed v hp2 hvp hdisc h hM hnorm hgen hx)
  have hsq := valuation_pow_sub_pow_lt_one v
    (by rw [v.map_pow, hunit x hx]; simp)
    (by rw [hunit _ hsx]) hcong 2
  simpa only [u, t, ← pow_mul, Nat.mul_comm] using hsq

/-- The squared signed valuation congruence for integral representatives becomes a prime ideal
congruence under an embedding into `ℂ`. -/
theorem pseudolatticeDilog_sq_signed_mem (h : B.IsPeriod ε)
    {M : ℕ} (hM : ∀ a : 𝓞 K, ∀ x : K, (ε - 1) * x ∈ B.submodule →
      (M : K) * (a : K) * x ∈ B.submodule)
    {L : Type*} [Field L] [NumberField L] (ι : L →+* ℂ)
    {x : K} (hx : (ε - 1) * x ∈ B.submodule) (a b : 𝓞 L)
    {s : ℤˣ}
    (ha : ι (a : L) = (pseudolatticeDilog h x / pseudolatticeDilog h 0) ^ 2)
    (hb : ι (b : L) =
      (pseudolatticeDilog h (((s : ℤ) : K) * x) / pseudolatticeDilog h 0) ^ 2)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hdisc : ¬ (p : ℤ) ∣ NumberField.discr K)
    {𝔭 : Ideal (𝓞 K)} (hnorm : Ideal.absNorm 𝔭 = p)
    (P : HeightOneSpectrum (𝓞 L)) (hpP : (p : 𝓞 L) ∈ P.asIdeal)
    (hgen : HasSignedRayGenerator (Ideal.span {(M : 𝓞 K)}) (fun _ => s) 𝔭) :
    a ^ p - b ∈ P.asIdeal := by
  obtain ⟨v, hv⟩ := exists_valuation_complex_lt_one_iff ι P
  have hvp : v (p : ℂ) < 1 := by
    simpa only [map_natCast] using (hv (p : 𝓞 L)).2.mpr hpP
  apply (hv (a ^ p - b)).2.mp
  simpa only [map_sub, map_pow, ha, hb] using
    pseudolatticeDilog_sq_frobenius_signed h hM v hp2 hvp hdisc hnorm hgen hx

end SIC

end
