/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Valuation.RootsOfUnity
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Interval.Set.Monotone

/-!
# Gaussian binomial coefficients and Fourier integrality

On `H = (ℤ/p^s)^d` with `d ≤ 2`, if `f` is integral and its Fourier sums `∑_x f(x)ζ^{a·x}` have
valuation at most that of `p^{sd/2}`, then `∑_x f(x) ∏_i C(x_i, j_i)` lies in the maximal ideal
whenever `∑_i j_i < d(p^s - 1)/2`.

This module follows the first half of the proof of [RW26b, Radchenko, Wheeler (2026b), Section 4,
Lemma 1], up to and including the congruence after (13); the source bases this step on the
integral `q`-Pascal calculation of its reference KW04 (Lemma 3.5 and Corollary 3.12). The group is
the model `ι → ZMod (p^s)` with `|ι| = d`, the Fourier kernel is `ζ^{a·x}` with the integer
representatives `0 ≤ x_i < p^s`, and the normalization `√|H|` of the source is replaced by the
squared bound `v(∑_x f(x)ζ^{a·x})² ≤ v(p)^{sd}`, so no square root of `p^s` is needed in the
field.

## The argument

*Gaussian binomials.* `[i, j]_q` is defined by the `q`-Pascal recursion
`[i + 1, j + 1]_q = [i, j]_q + q^{j+1}[i, j + 1]_q`, `[i, 0]_q = 1`, `[0, j + 1]_q = 0`. Its values
at a root of unity `ζ` are integral, and since `ζ ≡ 1 (mod 𝔪)` they reduce to the ordinary
binomial coefficients `C(i, j)`, by induction on `i` along Pascal's rule. They satisfy
`(ζ; ζ)_j [i, j]_ζ = (ζ^i; ζ^{-1})_j = ∏_{r<j}(1 - ζ^{i-r})`.

*The congruence (13).* Expand `∏_ν (X_ν; ζ^{-1})_{j_ν} = ∑_a c_a X^a` with integral `c_a ∈ ℤ[ζ]`.
Substituting `X_ν = ζ^{x_ν}` and summing against `f` gives
`∏_ν (ζ; ζ)_{j_ν} ∑_x f(x) ∏_ν [x_ν, j_ν]_ζ = ∑_a c_a ∑_x f(x) ζ^{a·x}`, whose square has
valuation at most `v(p)^{sd}`.

*Positivity of the bound.* By the pairing identity `v((ζ; ζ)_j) v((ζ; ζ)_{p^s-1-j}) = v(p^s)`
and strict monotonicity (`SICs.Valuation.RootsOfUnity`): for `d = 1`, `2j < p^s - 1` gives
`j < p^s - 1 - j` and `v((ζ; ζ)_j)² > v(p^s)`; for `d = 2`, `j₁ + j₂ < p^s - 1` gives
`v((ζ; ζ)_{j₁}) v((ζ; ζ)_{j₂}) > v((ζ; ζ)_{j₁}) v((ζ; ζ)_{p^s-1-j₁}) = v(p^s)`. In both cases
`∑_x f(x) ∏_ν [x_ν, j_ν]_ζ` lies in the maximal ideal, and reducing the Gaussian binomials gives the
congruence for the ordinary binomial coefficients.
-/

open scoped NNReal

namespace SIC

variable {L : Type*} [Field L] (v : Valuation L ℝ≥0)

/-! ### Gaussian binomial coefficients

The `q`-Pascal recursion, the product formula, integrality, and reduction at roots of unity. -/

/-- **The Gaussian binomial coefficient** `[i, j]_q`, by the `q`-Pascal recursion
`[i + 1, j + 1]_q = [i, j]_q + q^{j+1}[i, j + 1]_q` of the proof of
[RW26b, Radchenko, Wheeler (2026b), Section 4, Lemma 1]. -/
def qBinomial (q : L) : ℕ → ℕ → L
  | _, 0 => 1
  | 0, _ + 1 => 0
  | i + 1, j + 1 => qBinomial q i j + q ^ (j + 1) * qBinomial q i (j + 1)

/-- The numerator `(q^i; q⁻¹)_j` gains its first factor when both indices increase;
used by `finiteQPochhammer_mul_qBinomial`. -/
private lemma qBinomial_numerator_succ {q : L} (hq : q ≠ 0) (i j : ℕ) :
    (∏ r ∈ Finset.range (j + 1), (1 - q ^ (i + 1) * q⁻¹ ^ r)) =
      (1 - q ^ (i + 1)) * ∏ r ∈ Finset.range j, (1 - q ^ i * q⁻¹ ^ r) := by
  rw [Finset.prod_range_succ']
  simp only [pow_zero, mul_one]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro r _
  congr 1
  rw [pow_succ, pow_succ]
  field_simp

/-- The Gaussian binomial product formula
`(q;q)_j [i,j]_q = (q^i;q⁻¹)_j` for `q ≠ 0`, as used in
[RW26b, Radchenko, Wheeler (2026b), Section 4, proof of Lemma 1]. -/
theorem finiteQPochhammer_mul_qBinomial {q : L} (hq : q ≠ 0) (i j : ℕ) :
    finiteQPochhammer q j * qBinomial q i j =
      ∏ r ∈ Finset.range j, (1 - q ^ i * q⁻¹ ^ r) := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => simp [finiteQPochhammer, qBinomial]
    | succ j =>
      simp [qBinomial, Finset.prod_range_succ']
  | succ i ih =>
    cases j with
    | zero => simp [finiteQPochhammer, qBinomial]
    | succ j =>
      have hP : finiteQPochhammer q (j + 1) =
          finiteQPochhammer q j * (1 - q ^ (j + 1)) := by
        simp [finiteQPochhammer, Finset.prod_range_succ]
      have hN : (∏ r ∈ Finset.range (j + 1), (1 - q ^ i * q⁻¹ ^ r)) =
          (∏ r ∈ Finset.range j, (1 - q ^ i * q⁻¹ ^ r)) *
            (1 - q ^ i * q⁻¹ ^ j) := Finset.prod_range_succ _ _
      rw [qBinomial, hP, qBinomial_numerator_succ hq]
      have hpow : q ^ (j + 1) * (q ^ i * q⁻¹ ^ j) = q ^ (i + 1) := by
        calc
          q ^ (j + 1) * (q ^ i * q⁻¹ ^ j) = q ^ i * (q ^ j * q⁻¹ ^ j) * q := by
            rw [pow_succ]
            ring
          _ = q ^ (i + 1) := by simp [hq, pow_succ, mul_comm]
      calc
        (finiteQPochhammer q j * (1 - q ^ (j + 1))) *
            (qBinomial q i j + q ^ (j + 1) * qBinomial q i (j + 1)) =
          (1 - q ^ (j + 1)) * (finiteQPochhammer q j * qBinomial q i j) +
            q ^ (j + 1) * (finiteQPochhammer q (j + 1) * qBinomial q i (j + 1)) := by
              rw [hP]
              ring
        _ = (1 - q ^ (j + 1)) *
              (∏ r ∈ Finset.range j, (1 - q ^ i * q⁻¹ ^ r)) +
            q ^ (j + 1) * (∏ r ∈ Finset.range (j + 1), (1 - q ^ i * q⁻¹ ^ r)) := by
              rw [ih j, ih (j + 1)]
        _ = (1 - q ^ (i + 1)) *
            (∏ r ∈ Finset.range j, (1 - q ^ i * q⁻¹ ^ r)) := by
              rw [hN, ← hpow]
              ring

/-- Gaussian binomial coefficients at an integral parameter are integral;
used by `valuation_qBinomial_root_le_one` and `valuation_qBinomial_sub_choose_lt_one`. -/
theorem valuation_qBinomial_le_one {q : L} (hq : v q ≤ 1) (i j : ℕ) :
    v (qBinomial q i j) ≤ 1 := by
  induction i generalizing j with
  | zero =>
    cases j <;> simp [qBinomial]
  | succ i ih =>
    cases j with
    | zero => simp [qBinomial]
    | succ j =>
      rw [qBinomial]
      apply v.map_add_le (ih j)
      rw [v.map_mul, v.map_pow]
      calc
        v q ^ (j + 1) * v (qBinomial q i (j + 1)) ≤
            1 * v (qBinomial q i (j + 1)) :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ zero_le hq) zero_le
        _ ≤ 1 := by simpa using ih (j + 1)

/-- At a parameter congruent to `1`, `[i,j]_q` reduces to the ordinary binomial coefficient;
used by `valuation_qBinomial_root_sub_choose_lt_one`. -/
theorem valuation_qBinomial_sub_choose_lt_one {q : L} (hq : v q ≤ 1)
    (h1 : v (q - 1) < 1) (i j : ℕ) :
    v (qBinomial q i j - (i.choose j : L)) < 1 := by
  induction i generalizing j with
  | zero =>
    cases j <;> simp [qBinomial]
  | succ i ih =>
    cases j with
    | zero => simp [qBinomial]
    | succ j =>
      have h : qBinomial q (i + 1) (j + 1) - ((i + 1).choose (j + 1) : L) =
          (qBinomial q i j - (i.choose j : L)) +
          ((q ^ (j + 1) - 1) * qBinomial q i (j + 1) +
            (qBinomial q i (j + 1) - (i.choose (j + 1) : L))) := by
        simp only [qBinomial, Nat.choose_succ_succ, Nat.cast_add]
        ring
      rw [h]
      apply v.map_add_lt (ih j)
      apply v.map_add_lt
      · rw [v.map_mul]
        calc
          v (q ^ (j + 1) - 1) * v (qBinomial q i (j + 1)) ≤
              v (q ^ (j + 1) - 1) * 1 :=
            mul_le_mul_of_nonneg_left (valuation_qBinomial_le_one v hq _ _) zero_le
          _ < 1 := by simpa using valuation_pow_sub_pow_lt_one v hq (by simp) h1 (j + 1)
      · exact ih (j + 1)

/-- The coefficient of the monomial indexed by a subset of factors in `qProduct_expand`. -/
private def qProductCoeff (q : L) (t : Finset ℕ) : L :=
  (-1) ^ t.card * ∏ r ∈ t, q⁻¹ ^ r

/-- The finite product `(X;q⁻¹)_j` is a sum of monomials with coefficients integral at a
root of unity, used by `qProduct_expand_pi`. -/
private lemma qProduct_expand (q X : L) (j : ℕ) :
    (∏ r ∈ Finset.range j, (1 - q⁻¹ ^ r * X)) =
      ∑ t ∈ (Finset.range j).powerset, qProductCoeff q t * X ^ t.card := by
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib,
    Finset.prod_const, qProductCoeff]
  ring

/-- At a unit parameter, each subset-indexed summand coefficient
`(-1)^|t| ∏_{r∈t} q⁻¹^r` in `qProduct_expand` has valuation one;
used by `valuation_qBinomial_moment_sq_le`. -/
private lemma valuation_qProductCoeff_eq_one {q : L} (hq : v q = 1) (t : Finset ℕ) :
    v (qProductCoeff q t) = 1 := by
  simp [qProductCoeff, v.map_mul, v.map_pow, v.map_inv, hq, map_prod]

/-- A Gaussian binomial coefficient at a primitive `p^s`-th root of unity is integral,
as in [RW26b, Radchenko, Wheeler (2026b), Section 4, proof of Lemma 1]. -/
theorem valuation_qBinomial_root_le_one {p s : ℕ} [Fact p.Prime] {ζ : L}
    (hζ : IsPrimitiveRoot ζ (p ^ s)) (i j : ℕ) : v (qBinomial ζ i j) ≤ 1 := by
  have hn : p ^ s ≠ 0 := pow_ne_zero _ (Nat.Prime.ne_zero Fact.out)
  have hu : v ζ = 1 := valuation_eq_one_of_pow_eq_one v hn hζ.pow_eq_one
  exact valuation_qBinomial_le_one v hu.le i j

/-- A Gaussian binomial coefficient at a primitive `p^s`-th root reduces to `C(i,j)`,
as in [RW26b, Radchenko, Wheeler (2026b), Section 4, proof of Lemma 1]. -/
theorem valuation_qBinomial_root_sub_choose_lt_one {p s : ℕ} [Fact p.Prime]
    (hvp : v (p : L) < 1) {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ s)) (i j : ℕ) :
    v (qBinomial ζ i j - (i.choose j : L)) < 1 := by
  have hn : p ^ s ≠ 0 := pow_ne_zero _ (Nat.Prime.ne_zero Fact.out)
  have hu : v ζ = 1 := valuation_eq_one_of_pow_eq_one v hn hζ.pow_eq_one
  have h1 : v (ζ - 1) < 1 := by
    have h : ζ - 1 = -(1 - ζ) := by ring
    rw [h, v.map_neg]
    exact valuation_one_sub_lt_one v hvp hζ.pow_eq_one
  exact valuation_qBinomial_sub_choose_lt_one v hu.le h1 i j

/-- Expand the coordinatewise finite products into integral monomial coefficients;
used by `qBinomial_prod_expand`. -/
private lemma qProduct_expand_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : L) (j x : ι → ℕ) :
    (∏ i, ∏ r ∈ Finset.range (j i), (1 - q⁻¹ ^ r * q ^ (x i))) =
      ∑ a ∈ Fintype.piFinset (fun i => (Finset.range (j i)).powerset),
        (∏ i, qProductCoeff q (a i)) * q ^ (∑ i, (a i).card * x i) := by
  calc
    (∏ i, ∏ r ∈ Finset.range (j i), (1 - q⁻¹ ^ r * q ^ (x i))) =
        ∏ i, ∑ t ∈ (Finset.range (j i)).powerset,
          qProductCoeff q t * (q ^ (x i)) ^ t.card := by
            apply Finset.prod_congr rfl
            intro i _
            exact qProduct_expand q (q ^ (x i)) (j i)
    _ = ∑ a ∈ Fintype.piFinset (fun i => (Finset.range (j i)).powerset),
          ∏ i, qProductCoeff q (a i) * (q ^ (x i)) ^ (a i).card :=
        Finset.prod_univ_sum _ _
    _ = ∑ a ∈ Fintype.piFinset (fun i => (Finset.range (j i)).powerset),
          (∏ i, qProductCoeff q (a i)) * q ^ (∑ i, (a i).card * x i) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.prod_mul_distrib]
            simp_rw [← pow_mul, Nat.mul_comm (x _) (a _).card]
            rw [Finset.prod_pow_eq_pow_sum]

/-- The square of the valuation of a finite sum is bounded by a common bound for its terms;
used by `valuation_qBinomial_moment_sq_le`. -/
private lemma valuation_sum_sq_le {α : Type*} (t : Finset α) (g : α → L)
    (b : ℝ≥0) (hg : ∀ a ∈ t, v (g a) ^ 2 ≤ b) : v (∑ a ∈ t, g a) ^ 2 ≤ b := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha]
    have hle := ValuationClass.map_add_le_max v (g a) (∑ x ∈ t, g x)
    calc
      v (g a + ∑ x ∈ t, g x) ^ 2 ≤
          max (v (g a)) (v (∑ x ∈ t, g x)) ^ 2 :=
        pow_le_pow_left₀ zero_le hle 2
      _ ≤ b := by
        rcases le_total (v (g a)) (v (∑ x ∈ t, g x)) with h | h
        · rw [max_eq_right h]
          exact ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))
        · rw [max_eq_left h]
          exact hg a (Finset.mem_insert_self a t)

/-- Pointwise expansion of a product of Gaussian binomials into monomials;
used by `qBinomial_fourier_expansion`. -/
private lemma qBinomial_prod_expand {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : L} (hq : q ≠ 0) (j x : ι → ℕ) :
    (∏ i, finiteQPochhammer q (j i)) * (∏ i, qBinomial q (x i) (j i)) =
      ∑ a ∈ Fintype.piFinset (fun i => (Finset.range (j i)).powerset),
        (∏ i, qProductCoeff q (a i)) * q ^ (∑ i, (a i).card * x i) := by
  calc
    (∏ i, finiteQPochhammer q (j i)) * (∏ i, qBinomial q (x i) (j i)) =
        ∏ i, finiteQPochhammer q (j i) * qBinomial q (x i) (j i) :=
      (Finset.prod_mul_distrib).symm
    _ = ∏ i, ∏ r ∈ Finset.range (j i),
          (1 - q ^ (x i) * q⁻¹ ^ r) := by
            apply Finset.prod_congr rfl
            intro i _
            exact finiteQPochhammer_mul_qBinomial hq (x i) (j i)
    _ = ∏ i, ∏ r ∈ Finset.range (j i),
          (1 - q⁻¹ ^ r * q ^ (x i)) := by
            apply Finset.prod_congr rfl
            intro i _
            apply Finset.prod_congr rfl
            intro r _
            rw [mul_comm]
    _ = ∑ a ∈ Fintype.piFinset (fun i => (Finset.range (j i)).powerset),
          (∏ i, qProductCoeff q (a i)) * q ^ (∑ i, (a i).card * x i) :=
      qProduct_expand_pi q j x

/-- Sum the pointwise Gaussian-binomial expansion against a function on the residue group;
used by `valuation_qBinomial_moment_sq_le`. -/
private lemma qBinomial_fourier_expansion {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {q : L} (hq : q ≠ 0) (f : (ι → ZMod n) → L) (j : ι → ℕ) :
    (∏ i, finiteQPochhammer q (j i)) *
      (∑ x : ι → ZMod n, f x * ∏ i, qBinomial q (x i).val (j i)) =
    ∑ a ∈ Fintype.piFinset (fun i => (Finset.range (j i)).powerset),
      (∏ i, qProductCoeff q (a i)) *
        ∑ x : ι → ZMod n, f x * q ^ (∑ i, (a i).card * (x i).val) := by
  let A : Finset (ι → Finset ℕ) :=
    Fintype.piFinset (fun i => (Finset.range (j i)).powerset)
  calc
    (∏ i, finiteQPochhammer q (j i)) *
        (∑ x : ι → ZMod n, f x * ∏ i, qBinomial q (x i).val (j i)) =
      ∑ x : ι → ZMod n,
        f x * ((∏ i, finiteQPochhammer q (j i)) *
          (∏ i, qBinomial q (x i).val (j i))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ = ∑ x : ι → ZMod n,
          f x * ∑ a ∈ A, (∏ i, qProductCoeff q (a i)) *
            q ^ (∑ i, (a i).card * (x i).val) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [qBinomial_prod_expand hq j (fun i => (x i).val)]
    _ = ∑ x : ι → ZMod n, ∑ a ∈ A,
          f x * ((∏ i, qProductCoeff q (a i)) *
            q ^ (∑ i, (a i).card * (x i).val)) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [Finset.mul_sum]
    _ = ∑ a ∈ A, ∑ x : ι → ZMod n,
          f x * ((∏ i, qProductCoeff q (a i)) *
            q ^ (∑ i, (a i).card * (x i).val)) := Finset.sum_comm
    _ = ∑ a ∈ A, (∏ i, qProductCoeff q (a i)) *
          ∑ x : ι → ZMod n,
            f x * q ^ (∑ i, (a i).card * (x i).val) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _
              ring

/-- The multiplicative form of the Fourier estimate (13) for Gaussian-binomial moments, from
[RW26b, Radchenko, Wheeler (2026b), Section 4, proof of Lemma 1]. -/
theorem valuation_qBinomial_moment_sq_le {p s : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {ζ : L}
    (hζ : IsPrimitiveRoot ζ (p ^ s)) (f : (ι → ZMod (p ^ s)) → L)
    (hS : ∀ a : ι → ZMod (p ^ s),
      v (∑ x, f x * ζ ^ (∑ i, (a i).val * (x i).val)) ^ 2 ≤
        v (p : L) ^ (s * Fintype.card ι))
    (j : ι → ℕ) (hj : ∀ i, j i < p ^ s) :
    v ((∏ i, finiteQPochhammer ζ (j i)) *
      ∑ x : ι → ZMod (p ^ s), f x * ∏ i, qBinomial ζ (x i).val (j i)) ^ 2 ≤
        v (p : L) ^ (s * Fintype.card ι) := by
  let A : Finset (ι → Finset ℕ) :=
    Fintype.piFinset (fun i => (Finset.range (j i)).powerset)
  have hn : p ^ s ≠ 0 := pow_ne_zero _ (Nat.Prime.ne_zero Fact.out)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn
  have hu : v ζ = 1 := valuation_eq_one_of_pow_eq_one v hn hζ.pow_eq_one
  have hcard (a : ι → Finset ℕ) (ha : a ∈ A) (i : ι) : (a i).card < p ^ s := by
    have ht : a i ⊆ Finset.range (j i) :=
      Finset.mem_powerset.mp ((Fintype.mem_piFinset.mp ha) i)
    exact lt_of_le_of_lt (by simpa using Finset.card_le_card ht) (hj i)
  rw [qBinomial_fourier_expansion hζ0 f j]
  apply valuation_sum_sq_le v A _ _
  intro a ha
  have hc : v (∏ i, qProductCoeff ζ (a i)) = 1 := by
    simp [map_prod, valuation_qProductCoeff_eq_one v hu]
  have hfreq (x : ι → ZMod (p ^ s)) :
      ζ ^ (∑ i, (a i).card * (x i).val) =
        ζ ^ (∑ i, ((a i).card : ZMod (p ^ s)).val * (x i).val) := by
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [ZMod.val_natCast_of_lt (hcard a ha i)]
  have hsum :
      (∑ x : ι → ZMod (p ^ s), f x * ζ ^ (∑ i, (a i).card * (x i).val)) =
      ∑ x : ι → ZMod (p ^ s),
        f x * ζ ^ (∑ i, ((a i).card : ZMod (p ^ s)).val * (x i).val) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [hfreq x]
  rw [v.map_mul, hc, one_mul, hsum]
  exact hS (fun i => ((a i).card : ZMod (p ^ s)))

/-- Strict decrease of `v((ζ;ζ)_j)` over indices below the order of `ζ`;
used by `valuation_finiteQPochhammer_prod_sq_gt`. -/
private lemma valuation_finiteQPochhammer_lt_of_lt {p s : ℕ} [Fact p.Prime]
    (hvp : v (p : L) < 1) {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ s))
    {j k : ℕ} (hjk : j < k) (hk : k < p ^ s) :
    v (finiteQPochhammer ζ k) < v (finiteQPochhammer ζ j) := by
  have hn : 0 < p ^ s := pow_pos (Fact.out : p.Prime).pos _
  have hanti : StrictAntiOn (fun m => v (finiteQPochhammer ζ m))
      (Set.Iic (p ^ s - 1)) := by
    apply strictAntiOn_Iic_of_succ_lt
    intro m hm
    exact valuation_finiteQPochhammer_succ_lt v hvp hζ (by omega)
  exact hanti (by simp only [Set.mem_Iic]; omega)
    (by simp only [Set.mem_Iic]; omega) hjk

/-- The Pochhammer denominator is strictly larger than the Fourier bound in dimensions
one and two when the total Gaussian-binomial order is below half the group length;
used by `valuation_sum_mul_prod_choose_lt_one`. -/
private lemma valuation_finiteQPochhammer_prod_sq_gt {p s : ℕ} [Fact p.Prime]
    (hvp : v (p : L) < 1) {ι : Type*} [Fintype ι]
    (hd : Fintype.card ι ≤ 2) {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ s))
    (j : ι → ℕ) (hj : 2 * ∑ i, j i < Fintype.card ι * (p ^ s - 1)) :
    v (p : L) ^ (s * Fintype.card ι) <
      v (∏ i, finiteQPochhammer ζ (j i)) ^ 2 := by
  classical
  have hn : 0 < p ^ s := pow_pos (Fact.out : p.Prime).pos _
  have hnp : v ((p ^ s : ℕ) : L) = v (p : L) ^ s := by
    rw [Nat.cast_pow, v.map_pow]
  rcases (show Fintype.card ι = 0 ∨ Fintype.card ι = 1 ∨ Fintype.card ι = 2 by omega)
    with hzero | hone | htwo
  · simp [hzero] at hj
  · obtain ⟨i, hu⟩ := Finset.card_eq_one.mp (show (Finset.univ : Finset ι).card = 1 by
      simpa using hone)
    have hj' : 2 * j i < p ^ s - 1 := by simpa [hone, hu] using hj
    have hji : j i < p ^ s := by omega
    have hlt : j i < p ^ s - 1 - j i := by omega
    have hpair := valuation_finiteQPochhammer_mul v hζ hji
    have hanti := valuation_finiteQPochhammer_lt_of_lt v hvp hζ hlt (by omega)
    have hpos : 0 < v (finiteQPochhammer ζ (j i)) :=
      (Valuation.pos_iff v).2 (finiteQPochhammer_ne_zero hζ hji)
    have hgt : v ((p ^ s : ℕ) : L) < v (finiteQPochhammer ζ (j i)) ^ 2 := by
      rw [← hpair, pow_two]
      exact mul_lt_mul_of_pos_left hanti hpos
    simpa [hone, hu, hnp] using hgt
  · obtain ⟨i₁, i₂, hne, hu⟩ :=
      Finset.card_eq_two.mp (show (Finset.univ : Finset ι).card = 2 by simpa using htwo)
    have hj' : j i₁ + j i₂ < p ^ s - 1 := by
      simpa [htwo, hu, Finset.sum_pair hne] using (show
        2 * (∑ i, j i) < 2 * (p ^ s - 1) by simpa [htwo] using hj)
    have hji : j i₁ < p ^ s := by omega
    have hlt : j i₂ < p ^ s - 1 - j i₁ := by omega
    have hpair := valuation_finiteQPochhammer_mul v hζ hji
    have hanti := valuation_finiteQPochhammer_lt_of_lt v hvp hζ hlt (by omega)
    have hpos : 0 < v (finiteQPochhammer ζ (j i₁)) :=
      (Valuation.pos_iff v).2 (finiteQPochhammer_ne_zero hζ hji)
    have hgt : v (p : L) ^ s <
        v (finiteQPochhammer ζ (j i₁)) * v (finiteQPochhammer ζ (j i₂)) := by
      rw [← hnp, ← hpair]
      exact mul_lt_mul_of_pos_left hanti hpos
    have hsq := pow_lt_pow_left₀ hgt zero_le (by decide : (2 : ℕ) ≠ 0)
    simpa [htwo, hu, Finset.prod_pair hne, v.map_mul, pow_mul] using hsq

/-- Gaussian-binomial moments and ordinary binomial moments agree modulo the valuation ideal;
used by `valuation_sum_mul_prod_choose_lt_one`. -/
private lemma valuation_qBinomial_sum_sub_choose_lt_one {p s : ℕ} [Fact p.Prime]
    (hvp : v (p : L) < 1) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ s)) (f : (ι → ZMod (p ^ s)) → L)
    (hf : ∀ x, v (f x) ≤ 1) (j : ι → ℕ) :
    v ((∑ x : ι → ZMod (p ^ s), f x * ∏ i, qBinomial ζ (x i).val (j i)) -
      ∑ x : ι → ZMod (p ^ s),
        f x * ∏ i, (((x i).val.choose (j i) : ℕ) : L)) < 1 := by
  have hprod (x : ι → ZMod (p ^ s)) :
      v ((∏ i, qBinomial ζ (x i).val (j i)) -
        ∏ i, (((x i).val.choose (j i) : ℕ) : L)) < 1 := by
    apply valuation_prod_sub_prod_lt_one v Finset.univ
      (fun i => qBinomial ζ (x i).val (j i))
      (fun i => (((x i).val.choose (j i) : ℕ) : L))
    · intro i _
      exact valuation_qBinomial_root_le_one v hζ _ _
    · intro i _
      exact valuation_natCast_le_one v _
    · intro i _
      exact valuation_qBinomial_root_sub_choose_lt_one v hvp hζ _ _
  exact valuation_sum_mul_sub_lt_one v f
    (fun x => ∏ i, qBinomial ζ (x i).val (j i))
    (fun x => ∏ i, (((x i).val.choose (j i) : ℕ) : L)) hf hprod

/-! ### The congruence after (13)

Fourier integrality on `(ℤ/p^s)^d`, `d ≤ 2`, kills the binomial moments of total order below
`d(p^s - 1)/2` modulo `𝔪`. -/

/-- **The binomial congruence of [RW26b, Radchenko, Wheeler (2026b), Section 4, proof of
Lemma 1]**, following (13): on `H = (ℤ/p^s)^d` with `d = |ι| ≤ 2`, if `f` is integral and
`v(∑_x f(x)ζ^{a·x})² ≤ v(p)^{sd}` for every `a`, then
`∑_x f(x) ∏_i C(x_i, j_i) ≡ 0 (mod 𝔪)` whenever `∑_i j_i < d(p^s - 1)/2`. -/
theorem valuation_sum_mul_prod_choose_lt_one {p s : ℕ} [Fact p.Prime] (hvp : v (p : L) < 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hd : Fintype.card ι ≤ 2) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (p ^ s)) (f : (ι → ZMod (p ^ s)) → L) (hf : ∀ x, v (f x) ≤ 1)
    (hS : ∀ a : ι → ZMod (p ^ s),
      v (∑ x, f x * ζ ^ (∑ i, (a i).val * (x i).val)) ^ 2 ≤
        v (p : L) ^ (s * Fintype.card ι))
    (j : ι → ℕ) (hj : 2 * ∑ i, j i < Fintype.card ι * (p ^ s - 1)) :
    v (∑ x, f x * ∏ i, (((x i).val.choose (j i) : ℕ) : L)) < 1 := by
  have hn : 0 < p ^ s := pow_pos (Fact.out : p.Prime).pos _
  have hbound : Fintype.card ι * (p ^ s - 1) ≤ 2 * (p ^ s - 1) :=
    Nat.mul_le_mul_right _ hd
  have hsum : (∑ i, j i) < p ^ s := by omega
  have hji (i : ι) : j i < p ^ s :=
    lt_of_le_of_lt (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) hsum
  let P := ∏ i, finiteQPochhammer ζ (j i)
  let G := ∑ x : ι → ZMod (p ^ s), f x * ∏ i, qBinomial ζ (x i).val (j i)
  let C := ∑ x : ι → ZMod (p ^ s),
    f x * ∏ i, (((x i).val.choose (j i) : ℕ) : L)
  have hfourier : v (P * G) ^ 2 ≤ v (p : L) ^ (s * Fintype.card ι) :=
    valuation_qBinomial_moment_sq_le v hζ f hS j hji
  have hden : v (p : L) ^ (s * Fintype.card ι) < v P ^ 2 :=
    valuation_finiteQPochhammer_prod_sq_gt v hvp hd hζ j hj
  have hgauss : v G < 1 := by
    have hlt : (v P * v G) ^ 2 < v P ^ 2 := by
      simpa only [v.map_mul] using hfourier.trans_lt hden
    rw [mul_pow] at hlt
    have hsq : v G ^ 2 < 1 :=
      lt_of_mul_lt_mul_left (by simpa only [mul_one] using hlt) zero_le
    exact (sq_lt_sq₀ zero_le zero_le).mp (by simpa using hsq)
  have hdiff : v (G - C) < 1 :=
    valuation_qBinomial_sum_sub_choose_lt_one v hvp hζ f hf j
  have heq : C = G - (G - C) := by ring
  change v C < 1
  rw [heq]
  exact v.map_sub_lt hgauss hdiff

end SIC
