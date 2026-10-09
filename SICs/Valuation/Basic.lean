/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Basic.NNReal.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Data.ZMod.Basic

/-!
# Basic valuation congruences and residues

Integrality, congruences, and residues for valuations into `ℝ≥0`.

This module supplies the common valuation facts used by the root-of-unity, Gaussian-binomial,
coset-moment, and Fourier-integrality arguments of [RW26b, Radchenko, Wheeler (2026b), Section 4].
Here `v(x) ≤ 1` means integral and `v(x-y) < 1` means congruent modulo the maximal ideal.

## The argument

Natural and integer casts are integral by the ultrametric inequality; Bézout's identity makes
those prime to `p` valuation units when `v(p) < 1`. An integral product or
integral-weighted sum of congruent terms remains congruent. Naturals congruent modulo a prime
with valuation below one have congruent images. The valuation subring identifies its maximal
ideal with elements of valuation below one, so equality of residues is the same congruence.
-/

open scoped NNReal

namespace SIC

variable {L : Type*} [Field L] (v : Valuation L ℝ≥0)

/-! ### Integral casts and congruences -/

/-- Natural numbers are integral: `v(n) ≤ 1`. -/
theorem valuation_natCast_le_one (n : ℕ) : v (n : L) ≤ 1 := by
  exact (show IsNonarchimedean (v : L → ℝ≥0) from v.map_add).apply_natCast_le_one
    (by simp [v.map_zero, v.map_one]) v.map_one

/-- Integer coefficients are integral: `v(z) ≤ 1`. -/
theorem valuation_intCast_le_one (z : ℤ) : v (z : L) ≤ 1 := by
  exact (show IsNonarchimedean (v : L → ℝ≥0) from v.map_add).apply_intCast_le_one
    (by simp [v.map_zero, v.map_one]) v.map_one v.map_neg

/-- A natural number prime to `p` is a unit at a valuation with `v(p) < 1`. -/
theorem valuation_natCast_eq_one {p : ℕ} [Fact p.Prime] (hp : v (p : L) < 1) {n : ℕ}
    (hn : ¬p ∣ n) : v (n : L) = 1 := by
  have hnp : n.Coprime p := (Nat.coprime_comm).mpr
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hn)
  obtain ⟨a, b, hab⟩ := Nat.Coprime.isCoprime hnp
  have habL : (a : L) * n + (b : L) * p = 1 := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one] using
      congrArg (fun z : ℤ => (z : L)) hab
  have hnle := valuation_natCast_le_one v n
  by_contra hne
  have hlt : v (n : L) < 1 := lt_of_le_of_ne hnle hne
  have hale : v ((a : L) * n) < 1 := by
    rw [v.map_mul]
    calc
      _ ≤ 1 * v (n : L) :=
        mul_le_mul_of_nonneg_right (valuation_intCast_le_one v a) zero_le
      _ = v (n : L) := one_mul _
      _ < 1 := hlt
  have hble : v ((b : L) * p) < 1 := by
    rw [v.map_mul]
    calc
      _ ≤ 1 * v (p : L) :=
        mul_le_mul_of_nonneg_right (valuation_intCast_le_one v b) zero_le
      _ = v (p : L) := one_mul _
      _ < 1 := hp
  have h := v.map_add_lt hale hble
  rw [habL, v.map_one] at h
  exact (lt_irrefl 1 h)

/-- Products of integral factors preserve congruences modulo the valuation ideal;
used by the Gaussian-binomial and coset moment congruences. -/
lemma valuation_prod_sub_prod_lt_one {α : Type*} (t : Finset α)
    (g h : α → L) (hg : ∀ a ∈ t, v (g a) ≤ 1)
    (hh : ∀ a ∈ t, v (h a) ≤ 1)
    (hdiff : ∀ a ∈ t, v (g a - h a) < 1) :
    v ((∏ a ∈ t, g a) - ∏ a ∈ t, h a) < 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have heq : g a * (∏ x ∈ t, g x) - h a * (∏ x ∈ t, h x) =
        (g a - h a) * (∏ x ∈ t, g x) +
          h a * ((∏ x ∈ t, g x) - ∏ x ∈ t, h x) := by ring
    rw [heq]
    apply v.map_add_lt
    · rw [v.map_mul]
      have hprod : v (∏ x ∈ t, g x) ≤ 1 := by
        rw [map_prod]
        exact (Finset.prod_le_prod (fun x hx => hg x (Finset.mem_insert_of_mem hx))).trans_eq
          (by simp)
      calc
        v (g a - h a) * v (∏ x ∈ t, g x) ≤ v (g a - h a) * 1 :=
          mul_le_mul_of_nonneg_left hprod zero_le
        _ < 1 := by simpa using hdiff a (Finset.mem_insert_self a t)
    · rw [v.map_mul]
      calc
        v (h a) * v ((∏ x ∈ t, g x) - ∏ x ∈ t, h x) ≤
            1 * v ((∏ x ∈ t, g x) - ∏ x ∈ t, h x) :=
          mul_le_mul_of_nonneg_right (hh a (Finset.mem_insert_self a t)) zero_le
        _ < 1 := by
          simpa using ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))
            (fun x hx => hh x (Finset.mem_insert_of_mem hx))
            (fun x hx => hdiff x (Finset.mem_insert_of_mem hx))

/-- Division by congruent valuation units preserves congruence. -/
theorem valuation_div_sub_div_lt_one {a b c d : L}
    (hb : v b ≤ 1) (hc : v c = 1) (hd : v d = 1)
    (hab : v (a - b) < 1) (hcd : v (c - d) < 1) :
    v (a / c - b / d) < 1 := by
  have hc0 : c ≠ 0 := by
    intro hz
    simp [hz] at hc
  have hd0 : d ≠ 0 := by
    intro hz
    simp [hz] at hd
  rw [div_sub_div a b hc0 hd0, v.map_div, v.map_mul, hc, hd]
  simp only [one_mul, div_one]
  have heq : a * d - c * b = (a - b) * d + b * (d - c) := by ring
  rw [heq]
  apply v.map_add_lt
  · rw [v.map_mul, hd, mul_one]
    exact hab
  · have hdc : v (d - c) < 1 := by
      rw [show d - c = -(c - d) by ring, v.map_neg]
      exact hcd
    rw [v.map_mul]
    calc
      v b * v (d - c) ≤ 1 * v (d - c) := mul_le_mul_of_nonneg_right hb zero_le
      _ < 1 := by simpa using hdc

/-- Multiplying a pointwise congruence by integral weights and summing preserves it. Used in
`valuation_sum_coset_mul_prod_pow_lt_one`. -/
lemma valuation_sum_mul_sub_lt_one {α : Type*} [Fintype α] (f a b : α → L)
    (hf : ∀ x, v (f x) ≤ 1) (hab : ∀ x, v (a x - b x) < 1) :
    v ((∑ x, f x * a x) - ∑ x, f x * b x) < 1 := by
  rw [← Finset.sum_sub_distrib]
  apply v.map_sum_lt' (by positivity)
  intro x hx
  rw [← mul_sub, map_mul]
  calc
    v (f x) * v (a x - b x) ≤ 1 * v (a x - b x) :=
      mul_le_mul_of_nonneg_right (hf x) (by positivity)
    _ = v (a x - b x) := one_mul _
    _ < 1 := hab x

/-- A congruence of natural numbers modulo `p` gives congruence at `v` when `v(p) < 1`.
Used by the coset moment congruences. -/
lemma valuation_natCast_sub_lt_one_of_modEq {p a b : ℕ} (hvp : v (p : L) < 1)
    (h : a ≡ b [MOD p]) : v ((a : L) - (b : L)) < 1 := by
  obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp h
  have hcast : (b : L) - (a : L) = (p : L) * (k : L) := by
    calc
      (b : L) - (a : L) = ((b : ℤ) - (a : ℤ) : L) := by norm_cast
      _ = ((p : ℤ) * k : L) := by
        simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using
          congrArg (fun z : ℤ => (z : L)) hk
      _ = (p : L) * (k : L) := by norm_cast
  have hkval : v (k : L) ≤ 1 := valuation_intCast_le_one v k
  rw [v.map_sub_swap, hcast, map_mul]
  calc
    v (p : L) * v (k : L) ≤ v (p : L) * 1 :=
      mul_le_mul_of_nonneg_left hkval (by positivity)
    _ = v (p : L) := mul_one _
    _ < 1 := hvp

/-- Subtraction in `ZMod p` agrees with subtraction of natural representatives modulo the
maximal ideal. Used by the coset moment congruences. -/
lemma valuation_zmod_sub_val_lt_one {p : ℕ} [Fact p.Prime] (hvp : v (p : L) < 1)
    (x y : ZMod p) :
    v ((((x - y).val : ℕ) : L) - ((x.val : L) - (y.val : L))) < 1 := by
  have hm : (x - y).val + y.val ≡ x.val [MOD p] := by
    rw [Nat.ModEq, ← ZMod.val_add, sub_add_cancel, Nat.mod_eq_of_lt (ZMod.val_lt x)]
  have h := valuation_natCast_sub_lt_one_of_modEq v hvp hm
  have heq : (((x - y).val : ℕ) : L) - ((x.val : L) - (y.val : L)) =
      (((x - y).val + y.val : ℕ) : L) - (x.val : L) := by
    push_cast
    ring
  rw [heq]
  exact h

/-- Powers preserve congruence of integral elements, as used to translate affine coset
coordinates in `valuation_sum_coset_mul_prod_pow_lt_one`. -/
lemma valuation_pow_sub_pow_lt_one {x y : L} (hx : v x ≤ 1) (hy : v y ≤ 1)
    (hxy : v (x - y) < 1) (n : ℕ) : v (x ^ n - y ^ n) < 1 := by
  have h := valuation_prod_sub_prod_lt_one v (Finset.range n) (g := fun _ => x) (h := fun _ => y)
    (by intro i hi; exact hx) (by intro i hi; exact hy) (by intro i hi; exact hxy)
  simpa using h


/-! ### The valuation residue field -/

/-- The residue field of a valuation above `p` has characteristic `p`.
Used by both prime-field moment arguments. -/
theorem valuation_residue_charP {p : ℕ} [Fact p.Prime] (hvp : v (p : L) < 1) :
    CharP (IsLocalRing.ResidueField v.valuationSubring) p := by
  let R := v.valuationSubring
  apply (CharP.charP_iff_prime_eq_zero (R := IsLocalRing.ResidueField R) Fact.out).mpr
  have hp : (p : R) ∈ IsLocalRing.maximalIdeal R := by
    apply (Valuation.mem_maximalIdeal_iff L v).mpr
    exact hvp
  have hzero := (IsLocalRing.residue_eq_zero_iff (p : R)).mpr hp
  simpa only [map_natCast] using hzero

/-- Reduction of an integral element vanishes exactly when its valuation is below one.
Used by both Lemma 1 conclusions. -/
theorem valuation_residue_eq_zero_iff {x : L} (hx : v x ≤ 1) :
    (IsLocalRing.residue v.valuationSubring) (⟨x, hx⟩ : v.valuationSubring) = 0 ↔
      v x < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]

/-- Two integral elements have the same residue exactly when their difference has valuation
below one. Used by `valuation_sub_lt_one`. -/
theorem valuation_residue_eq_iff {x y : L} (hx : v x ≤ 1) (hy : v y ≤ 1) :
    (IsLocalRing.residue v.valuationSubring) (⟨x, hx⟩ : v.valuationSubring) =
      (IsLocalRing.residue v.valuationSubring) (⟨y, hy⟩ : v.valuationSubring) ↔
        v (x - y) < 1 := by
  have hsub : v (x - y) ≤ 1 := v.map_sub_le hx hy
  rw [← sub_eq_zero, ← map_sub]
  exact valuation_residue_eq_zero_iff (v := v) hsub

/-- Reduction carries the inverse of a valuation unit to the inverse of its reduction.
Used by `valuation_sub_lt_one`. -/
theorem valuation_residue_inv_eq {x : L} (hx : v x ≤ 1) (hxi : v x⁻¹ ≤ 1)
    (hx0 : x ≠ 0) :
    (IsLocalRing.residue v.valuationSubring) (⟨x⁻¹, hxi⟩ : v.valuationSubring) =
      ((IsLocalRing.residue v.valuationSubring) (⟨x, hx⟩ : v.valuationSubring))⁻¹ := by
  let R := v.valuationSubring
  have hmul : (⟨x, hx⟩ : R) * (⟨x⁻¹, hxi⟩ : R) = 1 := by
    apply Subtype.ext
    simp [hx0]
  exact eq_inv_of_mul_eq_one_right (by
    simpa only [map_mul, map_one] using congrArg (IsLocalRing.residue R) hmul)


end SIC
