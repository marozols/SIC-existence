/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Valuation.Basic
import Mathlib.Basic.NNReal.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.RingTheory.Valuation.Basic

/-!
# Valuations of roots of unity above a prime

For a valuation `v` with values in `ℝ≥0` and `v(p) < 1`: natural numbers prime to `p` and roots
of unity are units, `p`-power roots of unity are congruent to `1`, an integral `p`-th root of a
number congruent to `1` is congruent to `1`, sums of `p`-power roots have the same valuation as
the sums of their inverses, and the `q`-Pochhammer symbols `(ζ; ζ)_j` at a
primitive `p^s`-th root of unity strictly decrease, with `v((ζ; ζ)_j) v((ζ; ζ)_{p^s - 1 - j})`
equal to `v(p^s)`.

This module supplies the valuation estimates used in the proofs of [RW26b, Radchenko, Wheeler
(2026b), Section 4, Lemma 1 and Theorem 4]. The source writes valuations additively with
`v(p) = 1`; here a valuation is multiplicative, `v : L → ℝ≥0`, an element is integral when
`v(x) ≤ 1`, a unit when `v(x) = 1`, and `x ≡ y (mod 𝔪)` means `v(x - y) < 1`. Only `v(p) < 1` is
assumed: the estimates hold for every valuation above `p`, without a normalization.

## The argument

*Integers and roots of unity.* `SICs.Valuation.Basic` proves that natural numbers prime to `p`
are valuation units when `v(p) < 1`. A root of unity `ζ` with `ζ^n = 1`, `n ≠ 0`, has
`v(ζ)^n = 1`, so `v(ζ) = 1`.

*`p`-power roots of unity.* If `ζ^{p^s} = 1`, the binomial theorem gives
`(1 - ζ)^{p^s} ≡ 1 - ζ^{p^s} = 0` modulo `p`, so `v(1 - ζ) < 1`. Similarly, if `v(x) ≤ 1` and
`v(x^p - 1) < 1`, then `(x - 1)^p ≡ x^p - 1` modulo `p` and `v(x - 1) < 1`: the residue field
of characteristic `p` has no nontrivial `p`-th roots of unity.

*Pochhammer symbols.* For a primitive `n`-th root `ζ`,
`(ζ; ζ)_{n - 1} = ∏_{r=1}^{n-1}(1 - ζ^r) = n` (`IsPrimitiveRoot.prod_one_sub_pow_eq_order`), and
`1 - ζ^{-r} = -ζ^{-r}(1 - ζ^r)` has the valuation of `1 - ζ^r`, so the factors with
`j < r ≤ n - 1` contribute `v((ζ; ζ)_{n - 1 - j})`: `v((ζ; ζ)_j) v((ζ; ζ)_{n-1-j}) = v(n)`. Each
factor `1 - ζ^r` with `0 < r < n` is nonzero, and for `n = p^s` it has valuation below `1`, so
`v((ζ; ζ)_j)` strictly decreases while `j + 1 < p^s`.

*Conjugate sums.* The `p`-power roots in `L` form a finite cyclic group. If its order is one,
all roots are `1`. Otherwise, for a generator `ζ` of order `p^e`, reduce an integer polynomial
in `ζ` modulo `Φ_{p^e}(1 + Y)`, obtaining a polynomial
of degree below `φ(p^e)` in `π = ζ - 1`. Since `v(π)^φ = v(p)` and integer coefficients have
valuations that are powers of `v(p)`, its nonzero terms have distinct valuations. The same holds
for `ζ⁻¹ - 1 = -ζ⁻¹π`, so polynomial evaluations at `ζ` and `ζ⁻¹` have equal valuations.
-/

open scoped NNReal
open Polynomial

namespace SIC

variable {L : Type*} [Field L] (v : Valuation L ℝ≥0)

/-! ### Integers and roots of unity

Natural numbers are integral, those prime to `p` are units, and roots of unity are units. -/

/-- A root of unity is a unit: `ζ^n = 1` with `n ≠ 0` gives `v(ζ) = 1`. -/
theorem valuation_eq_one_of_pow_eq_one {ζ : L} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) :
    v ζ = 1 := by
  have h : v ζ ^ n = 1 := by simpa only [← v.map_pow, hζ] using v.map_one
  exact (pow_eq_one_iff_of_nonneg (by positivity) hn).mp h

/-! ### `p`-power roots of unity and `p`-th roots

The residue field has characteristic `p`, so `p`-power roots of unity reduce to `1`. -/

/-- The prime-power binomial correction has valuation below one; used by
`valuation_one_sub_lt_one` and `valuation_sub_one_lt_one_of_pow`. -/
private theorem valuation_add_pow_sub_lt_one {p s : ℕ} [Fact p.Prime]
    (hp : v (p : L) < 1) {a b : L} (ha : v a ≤ 1) (hb : v b ≤ 1) :
    v ((a + b) ^ p ^ s - (a ^ p ^ s + b ^ p ^ s)) < 1 := by
  rw [add_pow_prime_pow_eq' (Fact.out : p.Prime) a b s, add_sub_cancel_left, v.map_mul]
  have hs : v (∑ k ∈ Finset.Ioo 0 (p ^ s),
      a ^ k * b ^ (p ^ s - k) * (((p ^ s).choose k / p : ℕ) : L)) ≤ 1 := by
    apply v.map_sum_le
    intro k _
    simp only [v.map_mul, v.map_pow]
    exact mul_le_one'
      (mul_le_one' (pow_le_one₀ zero_le ha) (pow_le_one₀ zero_le hb))
      (valuation_natCast_le_one v _)
  calc
    v (p : L) * v (∑ k ∈ Finset.Ioo 0 (p ^ s),
        a ^ k * b ^ (p ^ s - k) * (((p ^ s).choose k / p : ℕ) : L)) ≤
        v (p : L) * 1 := mul_le_mul_of_nonneg_left hs zero_le
    _ = v (p : L) := mul_one _
    _ < 1 := hp

/-- A `p^s`-th root of unity is congruent to `1`: `v(1 - ζ) < 1`, as used in the proof of
[RW26b, Radchenko, Wheeler (2026b), Section 4, Lemma 1] (`ζ ≡ 1 (mod 𝔪)`). -/
theorem valuation_one_sub_lt_one {p s : ℕ} [Fact p.Prime] (hp : v (p : L) < 1) {ζ : L}
    (hζ : ζ ^ p ^ s = 1) : v (1 - ζ) < 1 := by
  have hn : p ^ s ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hunit := valuation_eq_one_of_pow_eq_one v hn hζ
  have h := valuation_add_pow_sub_lt_one v (s := s) hp
    (v.map_sub_le (le_of_eq v.map_one) hunit.le) hunit.le
  have heq : ((1 - ζ) + ζ) ^ p ^ s - ((1 - ζ) ^ p ^ s + ζ ^ p ^ s) =
      -((1 - ζ) ^ p ^ s) := by rw [sub_add_cancel, hζ]; ring
  rw [heq, v.map_neg, v.map_pow] at h
  exact (pow_lt_one_iff_of_nonneg zero_le hn).mp h

/-- An integral `x` with `x^p ≡ 1` satisfies `x ≡ 1`: the residue field has no nontrivial
`p`-th roots of unity. Used at the end of the proof of [RW26b, Radchenko, Wheeler (2026b),
Section 4, Theorem 4]. -/
theorem valuation_sub_one_lt_one_of_pow {p : ℕ} [Fact p.Prime] (hp : v (p : L) < 1) {x : L}
    (hx : v x ≤ 1) (hxp : v (x ^ p - 1) < 1) : v (x - 1) < 1 := by
  have hc := valuation_add_pow_sub_lt_one v (s := 1) hp
    (v.map_sub_le hx (le_of_eq v.map_one)) (le_of_eq v.map_one)
  have heq : ((x - 1) + 1) ^ p ^ 1 - ((x - 1) ^ p ^ 1 + 1 ^ p ^ 1) =
      (x ^ p - 1) - (x - 1) ^ p := by simp only [sub_add_cancel, pow_one]; ring
  rw [heq] at hc
  have hpow : v ((x - 1) ^ p) < 1 := by
    have heq' : (x - 1) ^ p = (x ^ p - 1) - ((x ^ p - 1) - (x - 1) ^ p) := by ring
    rw [heq']
    exact v.map_sub_lt hxp hc
  rw [v.map_pow] at hpow
  exact (pow_lt_one_iff_of_nonneg zero_le (Fact.out : p.Prime).ne_zero).mp hpow

/-! ### Pochhammer symbols at roots of unity

`(ζ; ζ)_j = ∏_{r=1}^{j} (1 - ζ^r)`, its pairing identity and strict monotonicity. -/

/-- **The finite `q`-Pochhammer symbol** `(q; q)_j = ∏_{r=1}^{j} (1 - q^r)` of the proof of
[RW26b, Radchenko, Wheeler (2026b), Section 4, Lemma 1]. -/
def finiteQPochhammer (q : L) (j : ℕ) : L :=
  ∏ r ∈ Finset.range j, (1 - q ^ (r + 1))

/-- `(ζ; ζ)_j ≠ 0` for a primitive `n`-th root of unity `ζ` and `j < n`. -/
theorem finiteQPochhammer_ne_zero {ζ : L} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) {j : ℕ} (hj : j < n) :
    finiteQPochhammer ζ j ≠ 0 := by
  unfold finiteQPochhammer
  apply Finset.prod_ne_zero_iff.mpr
  intro r hr
  have hrj := Finset.mem_range.mp hr
  have hrn : r + 1 < n := lt_of_le_of_lt (Nat.succ_le_of_lt hrj) hj
  exact sub_ne_zero.mpr (hζ.pow_ne_one_of_pos_of_lt (Nat.succ_ne_zero r) hrn).symm

/-- Reflected factors have equal valuations in `valuation_finiteQPochhammer_mul`. -/
private theorem valuation_one_sub_pow_reflect {ζ : L} {n r : ℕ} (hζ : IsPrimitiveRoot ζ n)
    (hrn : r < n) : v (1 - ζ ^ (n - r)) = v (1 - ζ ^ r) := by
  have hunit : v (ζ ^ r) = 1 := by
    rw [v.map_pow, valuation_eq_one_of_pow_eq_one v (ne_of_gt (lt_of_le_of_lt
      (Nat.zero_le r) hrn)) hζ.pow_eq_one, one_pow]
  have hpow : ζ ^ (n - r) * ζ ^ r = 1 := by
    rw [← pow_add, Nat.sub_add_cancel (le_of_lt hrn), hζ.pow_eq_one]
  have heq : (1 - ζ ^ (n - r)) * ζ ^ r = ζ ^ r - 1 := by
    rw [sub_mul, one_mul, hpow]
  calc
    v (1 - ζ ^ (n - r)) = v (1 - ζ ^ (n - r)) * v (ζ ^ r) := by rw [hunit, mul_one]
    _ = v ((1 - ζ ^ (n - r)) * ζ ^ r) := (v.map_mul _ _).symm
    _ = v (ζ ^ r - 1) := congrArg v heq
    _ = v (1 - ζ ^ r) := v.map_sub_swap _ _

/-- The pairing identity `v((ζ; ζ)_j) v((ζ; ζ)_{n-1-j}) = v(n)` for a primitive `n`-th root of
unity `ζ`, from `∏_{r=1}^{n-1}(1 - ζ^r) = n`; the proof of [RW26b, Radchenko, Wheeler (2026b),
Section 4, Lemma 1] writes it additively for `n = p^s`. -/
theorem valuation_finiteQPochhammer_mul {ζ : L} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) {j : ℕ}
    (hj : j < n) : v (finiteQPochhammer ζ j) * v (finiteQPochhammer ζ (n - 1 - j)) = v (n : L) := by
  let m := n - 1 - j
  let f : ℕ → ℝ≥0 := fun r => v (1 - ζ ^ (r + 1))
  have hn : n ≠ 0 := ne_of_gt (lt_of_le_of_lt (Nat.zero_le j) hj)
  have hnm : n - 1 = j + m := by dsimp [m]; omega
  have hv (t : ℕ) : v (finiteQPochhammer ζ t) = ∏ r ∈ Finset.range t, f r := by
    simp only [finiteQPochhammer, f, map_prod]
  have htotal : (∏ r ∈ Finset.range (n - 1), f r) = v (n : L) := by
    have hpred : n - 1 + 1 = n := by omega
    have hroot : IsPrimitiveRoot ζ (n - 1 + 1) := hpred ▸ hζ
    have h := hroot.prod_one_sub_pow_eq_order
    have h' := congrArg v h
    have hc : ((n - 1 : ℕ) : L) + 1 = (n : L) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun t : ℕ => (t : L)) hpred
    simpa only [f, map_prod, hc] using h'
  have htail : (∏ r ∈ Finset.range m, f (j + r)) = ∏ r ∈ Finset.range m, f r := by
    calc
      _ = ∏ r ∈ Finset.range m, f (m - 1 - r) := by
        apply Finset.prod_congr rfl
        intro r hr
        have hrm := Finset.mem_range.mp hr
        have hra : j + r + 1 < n := by omega
        have heq : n - (j + r + 1) = m - 1 - r + 1 := by omega
        simpa only [f, heq] using
          (valuation_one_sub_pow_reflect v hζ hra).symm
      _ = _ := Finset.prod_range_reflect f m
  rw [hv, hv]
  calc
    (∏ r ∈ Finset.range j, f r) * (∏ r ∈ Finset.range m, f r) =
        (∏ r ∈ Finset.range j, f r) * (∏ r ∈ Finset.range m, f (j + r)) := by rw [htail]
    _ = ∏ r ∈ Finset.range (j + m), f r := (Finset.prod_range_add f j m).symm
    _ = v (n : L) := by rw [← hnm, htotal]

/-- Strict monotonicity `v((ζ; ζ)_{j+1}) < v((ζ; ζ)_j)` for `j + 1 < p^s` at a primitive `p^s`-th
root of unity, from the proof of [RW26b, Radchenko, Wheeler (2026b), Section 4, Lemma 1]. -/
theorem valuation_finiteQPochhammer_succ_lt {p s : ℕ} [Fact p.Prime] (hp : v (p : L) < 1) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (p ^ s)) {j : ℕ} (hj : j + 1 < p ^ s) :
    v (finiteQPochhammer ζ (j + 1)) < v (finiteQPochhammer ζ j) := by
  have hroot : (ζ ^ (j + 1)) ^ p ^ s = 1 := by
    rw [pow_right_comm, hζ.pow_eq_one, one_pow]
  have hfactor := valuation_one_sub_lt_one v hp hroot
  have hprod : 0 < v (finiteQPochhammer ζ j) :=
    (v.pos_iff).mpr (finiteQPochhammer_ne_zero (L := L) hζ (lt_trans (Nat.lt_succ_self j) hj))
  calc
    v (finiteQPochhammer ζ (j + 1)) =
        v (finiteQPochhammer ζ j) * v (1 - ζ ^ (j + 1)) := by
      simp only [finiteQPochhammer, Finset.prod_range_succ, v.map_mul]
    _ < v (finiteQPochhammer ζ j) * 1 := mul_lt_mul_of_pos_left hfactor hprod
    _ = v (finiteQPochhammer ζ j) := mul_one _

/-! ### Conjugate sums of `p`-power roots of unity

A sum of `p`-power roots of unity and the sum of their inverses have the same valuation. In
`ℚ(ζ_{p^e})` the prime above `p` is totally ramified, so the automorphism `ζ ↦ ζ⁻¹` preserves `v`;
concretely, with `π = ζ - 1`, an integer polynomial in `ζ` is `∑_{i<φ(p^e)} c_i π^i` with
`c_i ∈ ℤ`, the terms have pairwise distinct valuations because `v(π)^{φ(p^e)} = v(p)`, and
`ζ⁻¹ - 1 = -ζ⁻¹π` has the valuation of `π`. The choice `ζ - 1` in place of `1 - ζ` makes
`Φ_{p^e}(1 + Y)` monic. -/

/-- A nonzero natural coefficient has valuation a power of `v(p)`; used by
`valuation_intCast_eq_pow`. -/
private theorem valuation_natCast_eq_pow {p : ℕ} [Fact p.Prime] (hp : v (p : L) < 1) {n : ℕ}
    (hn : n ≠ 0) : ∃ t : ℕ, v (n : L) = v (p : L) ^ t := by
  obtain ⟨t, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p
    (Fact.out : p.Prime).ne_one
  refine ⟨t, ?_⟩
  simp only [Nat.cast_mul, Nat.cast_pow, v.map_mul, v.map_pow,
    valuation_natCast_eq_one v hp hu, mul_one]

/-- A nonzero integer coefficient has valuation a power of `v(p)`; used by
`valuation_eval₂_eq`. -/
private theorem valuation_intCast_eq_pow {p : ℕ} [Fact p.Prime] (hp : v (p : L) < 1) {c : ℤ}
    (hc : c ≠ 0) : ∃ t : ℕ, v (c : L) = v (p : L) ^ t := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · simpa only [Int.cast_natCast] using valuation_natCast_eq_pow v hp (by exact_mod_cast hc)
  · obtain ⟨t, ht⟩ := valuation_natCast_eq_pow v hp (by simpa using hc)
    exact ⟨t, by simpa only [Int.cast_neg, Int.cast_natCast, v.map_neg] using ht⟩

/-- For a primitive `n`-th root `ζ` and `a` coprime to `n`, the factors
`ζ^a - 1` and `ζ - 1` have equal valuations; used by `valuation_sub_one_pow_totient`. -/
private theorem valuation_sub_pow_eq_of_coprime {ζ : L} {n a : ℕ} (hζ : IsPrimitiveRoot ζ n)
    (hn : 1 < n) (ha : a.Coprime n) : v (ζ ^ a - 1) = v (ζ - 1) := by
  have hζv : v ζ = 1 := valuation_eq_one_of_pow_eq_one v (by omega) hζ.pow_eq_one
  have hpowv : v (ζ ^ a) = 1 := by rw [v.map_pow, hζv, one_pow]
  have hsum_le (x : L) (hx : v x = 1) (m : ℕ) :
      v (∑ j ∈ Finset.range m, x ^ j) ≤ 1 := by
    apply v.map_sum_le
    intro j hj
    rw [v.map_pow, hx, one_pow]
  have hfwd : v (ζ ^ a - 1) ≤ v (ζ - 1) := by
    rw [← mul_geom_sum ζ a, v.map_mul]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hsum_le ζ hζv a) (by positivity)
  obtain ⟨b, -, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime ha hn
  have hpow : (ζ ^ a) ^ b = ζ := by
    rw [← pow_mul, ← pow_mod_orderOf, ← hζ.eq_orderOf, hb, pow_one]
  have hrev : v (ζ - 1) ≤ v (ζ ^ a - 1) := by
    calc
      v (ζ - 1) = v ((ζ ^ a) ^ b - 1) := by rw [hpow]
      _ = v (ζ ^ a - 1) * v (∑ j ∈ Finset.range b, (ζ ^ a) ^ j) := by
        rw [← mul_geom_sum, v.map_mul]
      _ ≤ v (ζ ^ a - 1) * 1 :=
        mul_le_mul_of_nonneg_left (hsum_le (ζ ^ a) hpowv b) (by positivity)
      _ = v (ζ ^ a - 1) := mul_one _
  exact le_antisymm hfwd hrev


/-- At a primitive `p^(e+1)`-th root `ζ`, the `φ(p^(e+1))`-th power of
`v(ζ - 1)` is `v(p)`; used by `valuation_sum_inv_eq_primitive`. -/
private theorem valuation_sub_one_pow_totient {p e : ℕ} [Fact p.Prime] {ζ : L}
    (hζ : IsPrimitiveRoot ζ (p ^ (e + 1))) :
    v (ζ - 1) ^ (p ^ (e + 1)).totient = v (p : L) := by
  have hn : 1 < p ^ (e + 1) := by
    exact one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
  have hcycl := Polynomial.eval_one_cyclotomic_prime_pow (R := L) (p := p) e
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ] at hcycl
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at hcycl
  have hvprod := congrArg v hcycl
  simp only [map_prod] at hvprod
  calc
    v (ζ - 1) ^ (p ^ (e + 1)).totient =
        ∏ μ ∈ primitiveRoots (p ^ (e + 1)) L, v (ζ - 1) := by
      rw [Finset.prod_const, hζ.card_primitiveRoots]
    _ = ∏ μ ∈ primitiveRoots (p ^ (e + 1)) L, v (1 - μ) := by
      apply Finset.prod_congr rfl
      intro μ hμ
      have hμroot : IsPrimitiveRoot μ (p ^ (e + 1)) :=
        (mem_primitiveRoots (by omega)).mp hμ
      obtain ⟨a, _, ha⟩ := hζ.eq_pow_of_pow_eq_one hμroot.pow_eq_one
      have hacoprime : a.Coprime (p ^ (e + 1)) :=
        (hζ.pow_iff_coprime (by omega) a).mp (ha ▸ hμroot)
      calc
        v (ζ - 1) = v (ζ ^ a - 1) := (valuation_sub_pow_eq_of_coprime v hζ hn hacoprime).symm
        _ = v (1 - ζ ^ a) := v.map_sub_swap _ _
        _ = v (1 - μ) := by rw [ha]
    _ = v (p : L) := hvprod


/-- Distinct coefficients below degree `φ` give terms with distinct valuations;
used by `valuation_eval₂_eq`. -/
private theorem valuation_poly_terms_distinct {p φ : ℕ} [Fact p.Prime]
    (hp : v (p : L) < 1) {π : L} (hπpos : 0 < v π) (hπlt : v π < 1)
    (hπpow : v π ^ φ = v (p : L)) (f : ℤ[X]) (hf : f.natDegree < φ)
    {i j : ℕ} (hi : i ∈ f.support) (hj : j ∈ f.support) (hij : i ≠ j) :
    v ((f.coeff i : L) * π ^ i) ≠ v ((f.coeff j : L) * π ^ j) := by
  have hip : i < φ := lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp i hi) hf
  have hjp : j < φ := lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp j hj) hf
  obtain ⟨a, ha⟩ := valuation_intCast_eq_pow v hp (Polynomial.mem_support_iff.mp hi)
  obtain ⟨b, hb⟩ := valuation_intCast_eq_pow v hp (Polynomial.mem_support_iff.mp hj)
  have hv_i : v ((f.coeff i : L) * π ^ i) = v π ^ (φ * a + i) := by
    rw [v.map_mul, v.map_pow, ha, pow_add, pow_mul, hπpow]
  have hv_j : v ((f.coeff j : L) * π ^ j) = v π ^ (φ * b + j) := by
    rw [v.map_mul, v.map_pow, hb, pow_add, pow_mul, hπpow]
  intro heq
  have heqexp : φ * a + i = φ * b + j :=
    pow_right_injective₀ hπpos (ne_of_lt hπlt)
      (hv_i.symm.trans (heq.trans hv_j))
  have hmod := congrArg (· % φ) heqexp
  have : i = j := by
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hip,
      Nat.mod_eq_of_lt hjp] using hmod
  exact hij this

/-- Integer polynomials of degree below `φ` have the same evaluation valuation at
two uniformizers with equal valuation and `v(π)^φ = v(p)`; used by
`valuation_sum_inv_eq_primitive`. -/
private theorem valuation_eval₂_eq {p φ : ℕ} [Fact p.Prime]
    (hp : v (p : L) < 1) {π π' : L} (hπpos : 0 < v π)
    (hπlt : v π < 1) (hπ' : v π' = v π)
    (hπpow : v π ^ φ = v (p : L)) (f : ℤ[X]) (hf : f.natDegree < φ) :
    v (f.eval₂ (Int.castRingHom L) π) = v (f.eval₂ (Int.castRingHom L) π') := by
  classical
  by_cases hf0 : f = 0
  · simp [hf0]
  have hterm (i : ℕ) :
      v ((f.coeff i : L) * π ^ i) = v ((f.coeff i : L) * π' ^ i) := by
    simp only [v.map_mul, v.map_pow, hπ']
  obtain ⟨i, hi, hmax⟩ := f.support.exists_max_image
    (fun j => v ((f.coeff j : L) * π ^ j))
    ⟨f.natDegree, f.natDegree_mem_support_of_nonzero hf0⟩
  have hlt (j : ℕ) (hj : j ∈ f.support \ {i}) :
      v ((f.coeff j : L) * π ^ j) < v ((f.coeff i : L) * π ^ i) := by
    have hj' := Finset.mem_sdiff.mp hj
    exact lt_of_le_of_ne (hmax j hj'.1)
      (valuation_poly_terms_distinct v hp hπpos hπlt hπpow f hf
        hj'.1 hi (by simpa using hj'.2))
  have hlt' (j : ℕ) (hj : j ∈ f.support \ {i}) :
      v ((f.coeff j : L) * π' ^ j) < v ((f.coeff i : L) * π' ^ i) := by
    simpa only [← hterm] using hlt j hj
  calc
    v (f.eval₂ (Int.castRingHom L) π) =
        v ((f.coeff i : L) * π ^ i) := by
      simpa [Polynomial.eval₂_eq_sum, Polynomial.sum_def] using
        v.map_sum_eq_of_lt hi hlt
    _ = v ((f.coeff i : L) * π' ^ i) := hterm i
    _ = v (f.eval₂ (Int.castRingHom L) π') := by
      symm
      simpa [Polynomial.eval₂_eq_sum, Polynomial.sum_def] using
        v.map_sum_eq_of_lt hi hlt'


/-- A primitive root annihilates the cyclotomic polynomial translated by one;
used by `valuation_cyclotomic_remainder`. -/
private theorem valuation_shifted_cyclotomic_root {p e : ℕ} [Fact p.Prime]
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (e + 1))) :
    ((cyclotomic (p ^ (e + 1)) ℤ).comp (X + C 1)).eval₂
      (Int.castRingHom L) (ζ - 1) = 0 := by
  have hcycl : (cyclotomic (p ^ (e + 1)) ℤ).eval₂ (Int.castRingHom L) ζ = 0 := by
    rw [← eval_map, map_cyclotomic_int]
    exact hζ.isRoot_cyclotomic (pow_pos (Fact.out : p.Prime).pos _)
  rw [eval₂_comp]
  have hxadd : (X + C 1 : ℤ[X]).eval₂ (Int.castRingHom L) (ζ - 1) = ζ := by
    simp [eval₂_add, eval₂_one]
  rw [hxadd]
  exact hcycl

/-- Reduction modulo the shifted cyclotomic polynomial gives one integer polynomial
of degree below `φ(p^(e+1))` for evaluations at `ζ` and `ζ⁻¹`; used by
`valuation_int_poly_eval_inv_eq`. -/
private theorem valuation_cyclotomic_remainder {p e : ℕ} [Fact p.Prime]
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (e + 1))) (P : ℤ[X]) :
    ∃ Q : ℤ[X], Q.natDegree < (p ^ (e + 1)).totient ∧
      Q.eval₂ (Int.castRingHom L) (ζ - 1) = P.eval₂ (Int.castRingHom L) ζ ∧
      Q.eval₂ (Int.castRingHom L) (ζ⁻¹ - 1) = P.eval₂ (Int.castRingHom L) ζ⁻¹ := by
  let n := p ^ (e + 1)
  let D : ℤ[X] := (cyclotomic n ℤ).comp (X + C 1)
  let Q : ℤ[X] := (P.comp (X + C 1)) %ₘ D
  have hDmonic : D.Monic :=
    (cyclotomic.monic n ℤ).comp (monic_X_add_C 1) (by simp)
  have hDdegree : D.natDegree = n.totient := by
    simp only [D, natDegree_comp, natDegree_X_add_C, mul_one,
      natDegree_cyclotomic]
  have hDne : D ≠ 1 := by
    intro h
    have hφ : 0 < n.totient :=
      Nat.totient_pos.mpr (pow_pos (Fact.out : p.Prime).pos _)
    rw [h, natDegree_one] at hDdegree
    omega
  have hQdegree : Q.natDegree < n.totient := by
    simpa only [Q, hDdegree] using
      (natDegree_modByMonic_lt (P.comp (X + C 1)) hDmonic hDne)
  refine ⟨Q, hQdegree, ?_, ?_⟩
  · calc
      _ = (P.comp (X + C 1)).eval₂ (Int.castRingHom L) (ζ - 1) :=
        eval₂_modByMonic_eq_self_of_root (valuation_shifted_cyclotomic_root hζ)
      _ = P.eval₂ (Int.castRingHom L) ζ := by
        rw [eval₂_comp]
        simp [eval₂_add]
  · calc
      _ = (P.comp (X + C 1)).eval₂ (Int.castRingHom L) (ζ⁻¹ - 1) :=
        eval₂_modByMonic_eq_self_of_root (valuation_shifted_cyclotomic_root hζ.inv)
      _ = P.eval₂ (Int.castRingHom L) ζ⁻¹ := by
        rw [eval₂_comp]
        simp [eval₂_add]

/-- Inversion preserves the valuation of an integer polynomial at a primitive
`p^(e+1)`-th root; used by `valuation_sum_inv_eq_primitive`. -/
private theorem valuation_int_poly_eval_inv_eq {p e : ℕ} [Fact p.Prime]
    (hp : v (p : L) < 1) {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (e + 1)))
    (P : ℤ[X]) :
    v (P.eval₂ (Int.castRingHom L) ζ⁻¹) = v (P.eval₂ (Int.castRingHom L) ζ) := by
  obtain ⟨Q, hQdegree, hQζ, hQζinv⟩ := valuation_cyclotomic_remainder hζ P
  have hn : 1 < p ^ (e + 1) :=
    one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
  have hζval : v ζ = 1 := valuation_eq_one_of_pow_eq_one v (by omega) hζ.pow_eq_one
  have hζne : ζ ≠ 0 := by
    intro h
    simp [h] at hζval
  have hπval : v (ζ⁻¹ - 1) = v (ζ - 1) := by
    have heq : ζ⁻¹ - 1 = -ζ⁻¹ * (ζ - 1) := by
      field_simp
      ring
    rw [heq, v.map_mul, v.map_neg, v.map_inv, hζval, inv_one, one_mul]
  have hπpos : 0 < v (ζ - 1) :=
    (v.pos_iff).mpr (sub_ne_zero.mpr (hζ.ne_one hn))
  have hπlt : v (ζ - 1) < 1 := by
    rw [v.map_sub_swap]
    exact valuation_one_sub_lt_one v hp hζ.pow_eq_one
  have hπpow : v (ζ - 1) ^ (p ^ (e + 1)).totient = v (p : L) :=
    valuation_sub_one_pow_totient v hζ
  rw [← hQζinv, ← hQζ]
  exact (valuation_eval₂_eq v hp hπpos hπlt hπval hπpow Q hQdegree).symm

/-- The conjugate-sum identity when the root group has a specified primitive
`p^(e+1)`-th root; used by `valuation_sum_inv_eq`. -/
private theorem valuation_sum_inv_eq_primitive {p e : ℕ} [Fact p.Prime]
    (hp : v (p : L) < 1) {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ (e + 1)))
    {ι : Type*} (s : Finset ι) (z : ι → L)
    (hz : ∀ i ∈ s, z i ^ p ^ (e + 1) = 1) :
    v (∑ i ∈ s, (z i)⁻¹) = v (∑ i ∈ s, z i) := by
  classical
  let a (i : ι) : ℕ := if hi : i ∈ s then
    (hζ.eq_pow_of_pow_eq_one (hz i hi)).choose else 0
  have ha (i : ι) (hi : i ∈ s) : ζ ^ a i = z i := by
    simp only [a, dite_eq_left hi]
    exact (hζ.eq_pow_of_pow_eq_one (hz i hi)).choose_spec.2
  let P : ℤ[X] := ∑ i ∈ s, X ^ a i
  have hPζ : P.eval₂ (Int.castRingHom L) ζ = ∑ i ∈ s, z i := by
    simp only [P, eval₂_finsetSum, eval₂_pow, eval₂_X]
    exact Finset.sum_congr rfl ha
  have hPζinv : P.eval₂ (Int.castRingHom L) ζ⁻¹ = ∑ i ∈ s, (z i)⁻¹ := by
    simp only [P, eval₂_finsetSum, eval₂_pow, eval₂_X]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inv_pow, ha i hi]
  rw [← hPζinv, ← hPζ]
  exact valuation_int_poly_eval_inv_eq v hp hζ P

/-- Any `n`-th root in `L` is killed by the order of the finite group of
`n`-th roots; used by `exists_primitive_root_power`. -/
private theorem rootsOfUnity_pow_card {n : ℕ} [NeZero n] {z : L} (hz : z ^ n = 1) :
    z ^ Nat.card (rootsOfUnity n L) = 1 := by
  let G := rootsOfUnity n L
  let u : G := rootsOfUnity.mkOfPowEq z hz
  have hu : u ^ Nat.card G = 1 := by
    simpa only [@Nat.card_eq_fintype_card G (Fintype.ofFinite G)] using
      (@pow_card_eq_one G _ (Fintype.ofFinite G) u)
  have hcoe : ((u : Lˣ) : L) = z := rootsOfUnity.coe_mkOfPowEq hz
  have hc : ((u : Lˣ) : L) ^ Nat.card G = 1 := by
    calc
      _ = (((u ^ Nat.card G : G) : Lˣ) : L) := (rootsOfUnity.coe_pow u _).symm
      _ = (((1 : G) : Lˣ) : L) := by rw [hu]
      _ = 1 := rfl
  rw [hcoe] at hc
  exact hc

/-- The group of `p^k`-th roots has a primitive generator of order `p^e`
for some `e ≤ k`; used by `valuation_sum_inv_eq`. -/
private theorem exists_primitive_root_power {p k : ℕ} [Fact p.Prime] :
    ∃ e ≤ k, ∃ ζ : L, IsPrimitiveRoot ζ (p ^ e) ∧
      (∀ {z : L}, z ^ p ^ k = 1 → z ^ p ^ e = 1) := by
  let G := rootsOfUnity (p ^ k) L
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  let ζ : L := ((g : Lˣ) : L)
  have hζpow : ζ ^ p ^ k = 1 := by
    change (((g : Lˣ) : L) ^ p ^ k) = 1
    exact (mem_rootsOfUnity' (p ^ k) (g : Lˣ)).mp g.property
  have horder : orderOf ζ = Nat.card G := by
    calc
      orderOf ζ = orderOf (g : Lˣ) := orderOf_units
      _ = orderOf g := Subgroup.orderOf_coe g
      _ = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  have hdiv : Nat.card G ∣ p ^ k := by
    rw [← horder]
    exact orderOf_dvd_of_pow_eq_one hζpow
  obtain ⟨e, he, hcard⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdiv
  refine ⟨e, he, ζ, ?_, ?_⟩
  · rw [← hcard, ← horder]
    exact IsPrimitiveRoot.orderOf ζ
  · intro z hz
    rw [← hcard]
    exact rootsOfUnity_pow_card hz

/-- **Conjugate sums of `p`-power roots of unity have equal valuations**: if `v(p) < 1` and
`z_i^{p^k} = 1` for every `i`, then `v(∑ z_i⁻¹) = v(∑ z_i)`. This is the step of the valuation
proof that the normalized Gauss sum of a metric group is a unit (`MetricGroup.valuation_gaussSum`)
at the `p`-primary part. -/
theorem valuation_sum_inv_eq {p : ℕ} [Fact p.Prime] (hp : v (p : L) < 1) {ι : Type*}
    (s : Finset ι) (z : ι → L) {k : ℕ} (hz : ∀ i ∈ s, z i ^ p ^ k = 1) :
    v (∑ i ∈ s, (z i)⁻¹) = v (∑ i ∈ s, z i) := by
  classical
  obtain ⟨e, -, ζ, hζ, hzall⟩ := exists_primitive_root_power (L := L) (p := p) (k := k)
  cases e with
  | zero =>
      have hzi (i : ι) (hi : i ∈ s) : z i = 1 := by
        simpa using hzall (hz i hi)
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp [hzi i hi]
  | succ e =>
      have hζ' : IsPrimitiveRoot ζ (p ^ (e + 1)) := by
        simpa only [Nat.succ_eq_add_one] using hζ
      have hz' (i : ι) (hi : i ∈ s) : z i ^ p ^ (e + 1) = 1 := by
        simpa only [Nat.succ_eq_add_one] using hzall (hz i hi)
      exact valuation_sum_inv_eq_primitive v hp hζ' s z hz'

end SIC
