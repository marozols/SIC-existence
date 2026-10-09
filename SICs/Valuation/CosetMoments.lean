/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Valuation.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.Enumerative.Stirling

/-!
# Binomial moments and moments on cosets of the `p`-torsion

On `H = (ℤ/p^s)^d` with `d ≤ 2`, if the binomial moments `∑_x f(x) ∏_i C(x_i, j_i)` of an integral
`f` lie in the maximal ideal for `∑_i j_i < d(p^s - 1)/2`, then on every coset of `H[p]` the
moments `∑_{u ∈ 𝔽_p^d} f(b + p^{s-1}u) ∏_i u_i^{r_i}` lie in the maximal ideal for
`∑_i r_i < d(p - 1)/2`.

This module follows the second half of the proof of [RW26b, Radchenko, Wheeler (2026b),
Section 4, Lemma 1], from the binomial congruence after (13) to (14). The binomial congruence is
the conclusion of `valuation_sum_mul_prod_choose_lt_one` (`SICs.Valuation.GaussianBinomial`);
the passage to residues of moments is in `SICs.FieldTheory.PrimeFieldMoments`.

## The argument

Write `x_i = b_i + p^{s-1}u_i` and `j_i = c_i + p^{s-1}r_i` with `0 ≤ b_i, c_i < p^{s-1}` and
`0 ≤ u_i, r_i < p`. For `d = 1`, the strict bound `2 ∑ r_i < p - 1` gives
`2 ∑ r_i ≤ p - 2`; for `d = 2`, it gives
`∑ r_i ≤ p - 2`. Thus even the largest `c_i = p^{s-1} - 1` satisfy
`2 ∑ j_i < d(p^s - 1)`, so the binomial congruence applies for every `c`.
The partial Lucas congruence
`C(b + p^{s-1}u, c + p^{s-1}r) ≡ C(b, c) C(u, r) (mod p)`, from
`(1 + T)^{b + p^{s-1}u} = (1 + T)^b (1 + T^{p^{s-1}})^u` in characteristic `p`
(`Choose.choose_modEq_choose_mod_mul_choose_div_nat` iterated), turns it into
`∑_b ∏_i C(b_i, c_i) S_b ≡ 0` with inner sums `S_b = ∑_u f(b + p^{s-1}u) ∏_i C(u_i, r_i)`. The
matrix `(C(b, c))_{b, c < p^{s-1}}` is unitriangular, and so is its tensor square, so every
`S_b ≡ 0`. Finally the Stirling expansion `u^r = ∑_{j ≤ r} S(r,j) j! C(u,j)` replaces
binomial weights by
monomials using only lower degree moments. A coset `b + H[p]` with arbitrary `b` is the coset of
its reduced representative, reparametrized by a translation of `𝔽_p^d`; the binomial theorem
shows that this translation preserves the degree bound.
-/

open scoped NNReal

namespace SIC

variable {L : Type*} [Field L] (v : Valuation L ℝ≥0)

/-! ### Moments on cosets

Lucas's congruence and unitriangular inversion, coset by coset. -/

/-- Lower base-`p` digits are unaffected by adding a multiple of `p^t`; used in the
partial Lucas congruence for `valuation_sum_coset_mul_prod_pow_lt_one`. -/
private lemma digit_add_pow_mul {p t b u i : ℕ} [Fact p.Prime] (hi : i < t) :
    (b + p ^ t * u) / p ^ i % p = b / p ^ i % p := by
  have hpow : p ^ t = p ^ i * p ^ (t - i) := by
    rw [← pow_add, Nat.add_sub_of_le hi.le]
  rw [hpow, mul_assoc, Nat.add_mul_div_left _ _ (pow_pos (Fact.out : p.Prime).pos _)]
  have hdvd : p ∣ p ^ (t - i) * u := by
    apply dvd_mul_of_dvd_left
    exact dvd_pow_self p (by omega)
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd]
  simp

/-- The partial Lucas congruence of [RW26b, Radchenko, Wheeler (2026b), Section 4], used in
`valuation_sum_coset_mul_prod_pow_lt_one`. -/
private lemma choose_add_pow_mul_modEq {p t b c u r : ℕ} [Fact p.Prime]
    (hb : b < p ^ t) (hc : c < p ^ t) :
    (b + p ^ t * u).choose (c + p ^ t * r) ≡ b.choose c * u.choose r [MOD p] := by
  have hbig := (Choose.choose_modEq_choose_mul_prod_range_choose (p := p) (n := b + p^t*u)
    (k := c + p^t*r) t)
  have hlow := (Choose.choose_modEq_prod_range_choose (p := p) hb hc)
  have hdivb : (b + p^t*u) / p^t = u := by
    rw [Nat.add_mul_div_left _ _ (pow_pos (Fact.out : p.Prime).pos _), Nat.div_eq_of_lt hb,
      zero_add]
  have hdivc : (c + p^t*r) / p^t = r := by
    rw [Nat.add_mul_div_left _ _ (pow_pos (Fact.out : p.Prime).pos _), Nat.div_eq_of_lt hc,
      zero_add]
  have hprod : (∏ i ∈ Finset.range t,
      ((b + p ^ t * u) / p ^ i % p).choose ((c + p ^ t * r) / p ^ i % p)) =
      ∏ i ∈ Finset.range t, (b / p ^ i % p).choose (c / p ^ i % p) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [digit_add_pow_mul (Finset.mem_range.mp hi), digit_add_pow_mul (Finset.mem_range.mp hi)]
  rw [hdivb, hdivc, hprod] at hbig
  simp only [← Nat.cast_prod] at hlow
  have h : ((b + p ^ t * u).choose (c + p ^ t * r) : ℤ) ≡
      (b.choose c : ℤ) * (u.choose r : ℤ) [ZMOD p] := by
    convert hbig.trans (hlow.symm.mul_left (u.choose r : ℤ)) using 1; ring
  exact Int.natCast_modEq_iff.mp (by simpa only [Nat.cast_mul] using h)

/-- Euclidean division identifies a reduced representative and a `p`-torsion coordinate;
used in `valuation_sum_coset_mul_prod_pow_lt_one`. -/
private def coordEquiv {p q : ℕ} [Fact p.Prime] (hq : 0 < q) :
    (Fin q × ZMod p) ≃ ZMod (q * p) := by
  letI : NeZero (q * p) := ⟨by exact Nat.ne_of_gt (Nat.mul_pos hq (Fact.out : p.Prime).pos)⟩
  refine {
    toFun := fun z => ((z.1.val + q * z.2.val : ℕ) : ZMod (q * p))
    invFun := fun x => (⟨x.val % q, Nat.mod_lt _ hq⟩, (x.val / q : ZMod p))
    left_inv := ?_
    right_inv := ?_
  }
  · rintro ⟨b, u⟩
    have hu : u.val < p := ZMod.val_lt u
    have hn : b.val + q * u.val < q * p := by
      have h : u.val + 1 ≤ p := hu
      nlinarith [b.isLt, Nat.mul_le_mul_left q h]
    apply Prod.ext
    · apply Fin.ext
      change (↑(b.val + q * u.val) : ZMod (q * p)).val % q = b.val
      rw [ZMod.val_natCast_of_lt hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
    · change ((↑(b.val + q * u.val) : ZMod (q * p)).val / q : ZMod p) = u
      rw [ZMod.val_natCast_of_lt hn, Nat.add_mul_div_left _ _ hq,
        Nat.div_eq_of_lt b.isLt, zero_add, ZMod.natCast_zmod_val]
  · intro x
    apply ZMod.val_injective
    have hdiv : x.val / q < p := (Nat.div_lt_iff_lt_mul hq).2 (by
      simpa [mul_comm] using ZMod.val_lt x)
    change (↑(x.val % q + q * (↑(x.val / q) : ZMod p).val) : ZMod (q * p)).val = x.val
    rw [ZMod.val_natCast_of_lt hdiv, Nat.mod_add_div]
    exact ZMod.val_natCast_of_lt (ZMod.val_lt x)

/-- An off diagonal Pascal term vanishes or has a strictly larger row index.
Used by `val_of_choose_moments`. -/
private lemma val_choose_offdiag {q : ℕ} {ι : Type*} [Fintype ι]
    (S : (ι → Fin q) → L) (b x : ι → Fin q) (hxb : x ≠ b)
    (ih : ∀ y : ι → Fin q,
      Finset.univ.sum (fun i => q - (y i).val) <
        Finset.univ.sum (fun i => q - (b i).val) → v (S y) < 1) :
    v (S x * ∏ i, (((x i).val.choose (b i).val : ℕ) : L)) < 1 := by
  classical
  by_cases hle : ∀ i, (b i).val ≤ (x i).val
  · have hstrict : ∃ i, (b i).val < (x i).val := by
      by_contra hn
      push Not at hn
      apply hxb
      funext i
      exact Fin.ext (le_antisymm (hn i) (hle i))
    have hμ : Finset.univ.sum (fun i => q - (x i).val) <
        Finset.univ.sum (fun i => q - (b i).val) := by
      apply Finset.sum_lt_sum
      · intro i hi
        have hle_i := hle i
        omega
      · obtain ⟨i, hi⟩ := hstrict
        exact ⟨i, Finset.mem_univ _, by omega⟩
    rw [map_mul]
    have hC : v (∏ i, (((x i).val.choose (b i).val : ℕ) : L)) ≤ 1 := by
      rw [map_prod]
      apply Finset.prod_le_one
      intro i hi
      exact valuation_natCast_le_one v _
    calc
      v (S x) * v (∏ i, (((x i).val.choose (b i).val : ℕ) : L)) ≤ v (S x) * 1 :=
        mul_le_mul_of_nonneg_left hC (by positivity)
      _ = v (S x) := mul_one _
      _ < 1 := ih x hμ
  · push Not at hle
    obtain ⟨i, hi⟩ := hle
    have hz : (∏ i, (((x i).val.choose (b i).val : ℕ) : L)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [Nat.choose_eq_zero_of_lt hi]
    simp [hz]

/-- Unitriangular Pascal inversion for the coset moments in
`valuation_sum_coset_mul_prod_pow_lt_one`. -/
private lemma val_of_choose_moments {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : (ι → Fin q) → L)
    (h : ∀ c : ι → Fin q,
      v (∑ b : ι → Fin q, S b * ∏ i, (((b i).val.choose (c i).val : ℕ) : L)) < 1)
    (b : ι → Fin q) : v (S b) < 1 := by
  classical
  let μ : (ι → Fin q) → ℕ := fun x => Finset.univ.sum (fun i => q - (x i).val)
  refine (measure μ).wf.induction (C := fun x => v (S x) < 1) b ?_
  intro b ih
  let C : (ι → Fin q) → L := fun x => ∏ i, (((x i).val.choose (b i).val : ℕ) : L)
  have hdiag : C b = 1 := by simp [C]
  have hother (x : ι → Fin q) (hxb : x ≠ b) : v (S x * C x) < 1 := by
    exact val_choose_offdiag v S b x hxb (fun y hy => ih y hy)
  have htail : v (∑ x ∈ (Finset.univ : Finset (ι → Fin q)).erase b, S x * C x) < 1 := by
    apply v.map_sum_lt' (by positivity)
    intro x hx
    exact hother x (Finset.ne_of_mem_erase hx)
  have hall : v (∑ x : ι → Fin q, S x * C x) < 1 := h b
  have heq : S b = (∑ x : ι → Fin q, S x * C x) -
      ∑ x ∈ (Finset.univ : Finset (ι → Fin q)).erase b, S x * C x := by
    rw [← Finset.sum_erase_add Finset.univ (fun x => S x * C x) (Finset.mem_univ b)]
    simp [hdiag]
  rw [heq]
  exact v.map_sub_lt hall htail

/-- The Stirling expansion of a power in the binomial basis, used in
`valuation_sum_coset_mul_prod_pow_lt_one`. -/
private lemma pow_eq_sum_stirling_choose (n r : ℕ) :
    n ^ r = ∑ j ∈ Finset.range (r + 1), r.stirlingSecond j * j.factorial * n.choose j := by
  rw [Nat.pow_eq_sum_stirlingSecond_mul_descFactorial]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  ring

/-- Expands a product of bounded degree sums and exchanges the resulting finite sums.
Used by `val_moment_of_expansion`. -/
private lemma sum_prod_expansion {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (g : (ι → α) → L) (r : ι → ℕ)
    (P : ι → α → L) (Q : ι → ℕ → α → L) (C : ι → ℕ → L)
    (hP : ∀ i x, P i x = ∑ j ∈ Finset.range (r i + 1), C i j * Q i j x) :
    (∑ u : ι → α, g u * ∏ i, P i (u i)) =
      ∑ j ∈ Fintype.piFinset (fun i => Finset.range (r i + 1)),
        (∏ i, C i (j i)) * ∑ u : ι → α, g u * ∏ i, Q i (j i) (u i) := by
  classical
  let J : Finset (ι → ℕ) := Fintype.piFinset (fun i => Finset.range (r i + 1))
  have hprod (u : ι → α) : (∏ i, P i (u i)) =
      ∑ j ∈ J, ∏ i, C i (j i) * Q i (j i) (u i) := by
    calc
      (∏ i, P i (u i)) =
          ∏ i, ∑ j ∈ Finset.range (r i + 1), C i j * Q i j (u i) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact hP i (u i)
      _ = ∑ j ∈ J, ∏ i, C i (j i) * Q i (j i) (u i) :=
        Finset.prod_univ_sum _ _
  have hid : (∑ u : ι → α, g u * ∏ i, P i (u i)) =
      ∑ j ∈ J, (∏ i, C i (j i)) *
        ∑ u : ι → α, g u * ∏ i, Q i (j i) (u i) := by
    calc
      _ = ∑ u : ι → α, g u * ∑ j ∈ J, ∏ i, C i (j i) * Q i (j i) (u i) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [hprod]
      _ = ∑ u : ι → α, ∑ j ∈ J, g u * ∏ i, C i (j i) * Q i (j i) (u i) := by
        simp_rw [Finset.mul_sum]
      _ = ∑ j ∈ J, ∑ u : ι → α, g u * ∏ i, C i (j i) * Q i (j i) (u i) :=
        Finset.sum_comm
      _ = ∑ j ∈ J, (∏ i, C i (j i)) *
          ∑ u : ι → α, g u * ∏ i, Q i (j i) (u i) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.prod_mul_distrib]
        ring
  exact hid

/-- Products of bounded degree expansions preserve the corresponding moment congruences.
Used twice in `valuation_sum_coset_mul_prod_pow_lt_one`. -/
private lemma val_moment_of_expansion {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (g : (ι → α) → L) (r : ι → ℕ)
    (P : ι → α → L) (Q : ι → ℕ → α → L) (C : ι → ℕ → L)
    (hP : ∀ i x, P i x = ∑ j ∈ Finset.range (r i + 1), C i j * Q i j x)
    (hC : ∀ i j, j ≤ r i → v (C i j) ≤ 1)
    (hQ : ∀ j : ι → ℕ, (∀ i, j i ≤ r i) →
      v (∑ u : ι → α, g u * ∏ i, Q i (j i) (u i)) < 1) :
    v (∑ u : ι → α, g u * ∏ i, P i (u i)) < 1 := by
  classical
  rw [sum_prod_expansion g r P Q C hP]
  apply v.map_sum_lt' (by positivity)
  intro j hj
  have hjr (i : ι) : j i ≤ r i := by
    have := (Fintype.mem_piFinset.mp hj) i
    simpa using this
  rw [map_mul]
  have hcoeff : v (∏ i, C i (j i)) ≤ 1 := by
    rw [map_prod]
    apply Finset.prod_le_one
    intro i hi
    exact hC i (j i) (hjr i)
  calc
    v (∏ i, C i (j i)) * v (∑ u : ι → α, g u * ∏ i, Q i (j i) (u i)) ≤
        1 * v (∑ u : ι → α, g u * ∏ i, Q i (j i) (u i)) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = v (∑ u : ι → α, g u * ∏ i, Q i (j i) (u i)) := one_mul _
    _ < 1 := hQ j hjr

/-- The triangular change from binomial to monomial moments in
`valuation_sum_coset_mul_prod_pow_lt_one`. -/
private lemma val_pow_moment_of_choose_moments {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : Type*} [Fintype α] (g : (ι → α) → L) (z : α → ℕ) (r : ι → ℕ)
    (h : ∀ j : ι → ℕ, (∀ i, j i ≤ r i) →
      v (∑ u : ι → α, g u * ∏ i, (((z (u i)).choose (j i) : ℕ) : L)) < 1) :
    v (∑ u : ι → α, g u * ∏ i, ((z (u i) : ℕ) : L) ^ r i) < 1 := by
  apply val_moment_of_expansion v g r
    (fun i x => (z x : L) ^ r i)
    (fun _ j x => (((z x).choose j : ℕ) : L))
    (fun i j => (((r i).stirlingSecond j * j.factorial : ℕ) : L))
  · intro i x
    have hcast := congrArg (fun n : ℕ => (n : L))
      (pow_eq_sum_stirling_choose (z x) (r i))
    simpa only [Nat.cast_pow, Nat.cast_sum, Nat.cast_mul] using hcast
  · intro i j hj
    exact valuation_natCast_le_one v _
  · intro j hj
    exact h j hj

/-- The degree bound for indices after separating the `p`-torsion cosets in
`valuation_sum_coset_mul_prod_pow_lt_one`. -/
private lemma coset_index_bound {d p q C R : ℕ} (hd : d ≤ 2) (hp : 2 ≤ p) (hq : 1 ≤ q)
    (hC : C ≤ d * (q - 1)) (hR : 2 * R < d * (p - 1)) :
    2 * (C + q * R) < d * (q * p - 1) := by
  interval_cases d
  · omega
  · have hR' : 2 * R ≤ p - 2 := by omega
    have hmul := Nat.mul_le_mul_left q hR'
    have hq' : q - 1 + 1 = q := Nat.sub_add_cancel hq
    have hp' : p - 2 + 2 = p := Nat.sub_add_cancel hp
    have hqp : q * p - 1 + 1 = q * p :=
      Nat.sub_add_cancel (by nlinarith : 1 ≤ q * p)
    nlinarith
  · have hR' : R ≤ p - 2 := by omega
    have hmul := Nat.mul_le_mul_left q hR'
    have hq' : q - 1 + 1 = q := Nat.sub_add_cancel hq
    have hp' : p - 2 + 2 = p := Nat.sub_add_cancel hp
    have hqp : q * p - 1 + 1 = q * p :=
      Nat.sub_add_cancel (by nlinarith : 1 ≤ q * p)
    nlinarith

/-- The reduced representative plus a `p`-torsion coordinate has the expected natural value.
Used in `valuation_sum_coset_mul_prod_pow_lt_one`. -/
private lemma coord_val {p q : ℕ} [Fact p.Prime] (b : Fin q) (u : ZMod p) :
    (↑(b.val + q * u.val) : ZMod (q * p)).val = b.val + q * u.val := by
  have hu : u.val < p := ZMod.val_lt u
  have h : b.val + q * u.val < q * p := by
    have hh : u.val + 1 ≤ p := hu
    nlinarith [b.isLt, Nat.mul_le_mul_left q hh]
  exact ZMod.val_natCast_of_lt h

/-- Coordinatewise Euclidean division identifies `H` with reduced cosets and `H[p]`.
Used in `valuation_sum_coset_mul_prod_pow_lt_one`. -/
private def cosetPiEquiv {p q : ℕ} [Fact p.Prime] {ι : Type*} (hq : 0 < q) :
    ((ι → Fin q) × (ι → ZMod p)) ≃ (ι → ZMod (q * p)) :=
  (Equiv.arrowProdEquivProdArrow ι (fun _ => Fin q) (fun _ => ZMod p)).symm.trans
    (Equiv.piCongrRight (fun _ => coordEquiv hq))

/-- The partial Lucas congruence survives taking products over the coordinates in
`valuation_sum_coset_mul_prod_pow_lt_one`. -/
private lemma val_lucas_prod {p t : ℕ} [Fact p.Prime] (hvp : v (p : L) < 1)
    {ι : Type*} [Fintype ι] (b c : ι → Fin (p ^ t))
    (u : ι → ZMod p) (r : ι → ℕ) :
    v ((∏ i, ((Nat.choose ((b i).val + p ^ t * (u i).val)
        ((c i).val + p ^ t * r i) : ℕ) : L)) -
      ∏ i, ((Nat.choose (b i).val (c i).val * Nat.choose (u i).val (r i) : ℕ) : L)) < 1 := by
  apply valuation_prod_sub_prod_lt_one v _
  · intro i hi
    exact valuation_natCast_le_one v _
  · intro i hi
    exact valuation_natCast_le_one v _
  · intro i hi
    exact valuation_natCast_sub_lt_one_of_modEq v hvp
      (choose_add_pow_mul_modEq (b i).isLt (c i).isLt)

/-- The coordinate equivalence evaluates to the stated reduced representative.
Used in `valuation_sum_coset_mul_prod_pow_lt_one`. -/
private lemma cosetPiEquiv_val {p q : ℕ} [Fact p.Prime] {ι : Type*}
    (hq : 0 < q) (z : (ι → Fin q) × (ι → ZMod p)) (i : ι) :
    ((cosetPiEquiv hq z) i).val = (z.1 i).val + q * (z.2 i).val := by
  change (↑((z.1 i).val + q * (z.2 i).val) : ZMod (q * p)).val = _
  exact coord_val (z.1 i) (z.2 i)

/-- The degree bound and Euclidean coordinates give the original binomial moment on pairs.
Used by `val_choose_matrix_moment`. -/
private lemma val_raw_choose_moment {p t : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hd : Fintype.card ι ≤ 2) (f : (ι → ZMod (p ^ t * p)) → L)
    (hchoose : ∀ j : ι → ℕ,
      2 * ∑ i, j i < Fintype.card ι * (p ^ t * p - 1) →
      v (∑ x, f x * ∏ i, (((x i).val.choose (j i) : ℕ) : L)) < 1)
    (r : ι → ℕ) (hr : 2 * ∑ i, r i < Fintype.card ι * (p - 1))
    (c : ι → Fin (p ^ t)) :
    v (∑ z : (ι → Fin (p ^ t)) × (ι → ZMod p),
      f (cosetPiEquiv (pow_pos (Fact.out : p.Prime).pos t) z) *
        ∏ i, ((Nat.choose ((z.1 i).val + p ^ t * (z.2 i).val)
          ((c i).val + p ^ t * r i) : ℕ) : L)) < 1 := by
  classical
  let q := p ^ t
  have hq : 0 < q := pow_pos (Fact.out : p.Prime).pos t
  let e : ((ι → Fin q) × (ι → ZMod p)) ≃ (ι → ZMod (q * p)) := cosetPiEquiv hq
  let j : ι → ℕ := fun i => (c i).val + q * r i
  let A : ((ι → Fin q) × (ι → ZMod p)) → L := fun z =>
    ∏ i, ((Nat.choose ((z.1 i).val + q * (z.2 i).val) (j i) : ℕ) : L)
  have hC : (∑ i, (c i).val) ≤ Fintype.card ι * (q - 1) := by
    calc
      (∑ i, (c i).val) ≤ ∑ i : ι, (q - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have := (c i).isLt
        omega
      _ = Fintype.card ι * (q - 1) := by simp
  have hjsum : (∑ i, j i) = (∑ i, (c i).val) + q * ∑ i, r i := by
    simp [j, Finset.sum_add_distrib, Finset.mul_sum]
  have hj : 2 * ∑ i, j i < Fintype.card ι * (q * p - 1) := by
    rw [hjsum]
    exact coset_index_bound hd (Fact.out : p.Prime).two_le (by omega) hC hr
  have h := hchoose j hj
  rw [← Equiv.sum_comp e (fun x : ι → ZMod (q * p) =>
    f x * ∏ i, (((x i).val.choose (j i) : ℕ) : L))] at h
  have heq : (∑ z : (ι → Fin q) × (ι → ZMod p), f (e z) * A z) =
      ∑ z : (ι → Fin q) × (ι → ZMod p),
        f (e z) * ∏ i, (((e z i).val.choose (j i) : ℕ) : L) := by
    apply Fintype.sum_congr
    intro z
    congr 1
    dsimp [A]
    apply Finset.prod_congr rfl
    intro i hi
    rw [cosetPiEquiv_val hq z i]
  change v (∑ z : (ι → Fin q) × (ι → ZMod p), f (e z) * A z) < 1
  rw [heq]
  exact h

/-- Lucas's congruence gives the triangular system of coset moments in
`valuation_sum_coset_mul_prod_pow_lt_one`. -/
private lemma val_choose_matrix_moment {p t : ℕ} [Fact p.Prime]
    (hvp : v (p : L) < 1) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hd : Fintype.card ι ≤ 2) (f : (ι → ZMod (p ^ t * p)) → L)
    (hf : ∀ x, v (f x) ≤ 1)
    (hchoose : ∀ j : ι → ℕ,
      2 * ∑ i, j i < Fintype.card ι * (p ^ t * p - 1) →
      v (∑ x, f x * ∏ i, (((x i).val.choose (j i) : ℕ) : L)) < 1)
    (r : ι → ℕ) (hr : 2 * ∑ i, r i < Fintype.card ι * (p - 1))
    (c : ι → Fin (p ^ t)) :
    v (∑ b : ι → Fin (p ^ t),
      (∑ u : ι → ZMod p,
        f (cosetPiEquiv (pow_pos (Fact.out : p.Prime).pos t) (b, u)) *
          ∏ i, (((u i).val.choose (r i) : ℕ) : L)) *
        ∏ i, (((b i).val.choose (c i).val : ℕ) : L)) < 1 := by
  classical
  let q := p ^ t
  have hq : 0 < q := pow_pos (Fact.out : p.Prime).pos t
  let e : ((ι → Fin q) × (ι → ZMod p)) ≃ (ι → ZMod (q * p)) := cosetPiEquiv hq
  let j : ι → ℕ := fun i => (c i).val + q * r i
  let A : ((ι → Fin q) × (ι → ZMod p)) → L := fun z =>
    ∏ i, ((Nat.choose ((z.1 i).val + q * (z.2 i).val) (j i) : ℕ) : L)
  let B : ((ι → Fin q) × (ι → ZMod p)) → L := fun z =>
    ∏ i, ((Nat.choose (z.1 i).val (c i).val * Nat.choose (z.2 i).val (r i) : ℕ) : L)
  have hraw : v (∑ z : (ι → Fin q) × (ι → ZMod p), f (e z) * A z) < 1 :=
    val_raw_choose_moment v hd f hchoose r hr c
  have hnear : v ((∑ z : (ι → Fin q) × (ι → ZMod p), f (e z) * A z) -
      ∑ z : (ι → Fin q) × (ι → ZMod p), f (e z) * B z) < 1 := by
    apply valuation_sum_mul_sub_lt_one v (fun z => f (e z)) A B
    · intro z
      exact hf (e z)
    · rintro ⟨b, u⟩
      exact val_lucas_prod v hvp b c u r
  have hB : v (∑ z : (ι → Fin q) × (ι → ZMod p), f (e z) * B z) < 1 := by
    have heq : (∑ z : (ι → Fin q) × (ι → ZMod p), f (e z) * B z) =
        (∑ z : (ι → Fin q) × (ι → ZMod p), f (e z) * A z) -
        ((∑ z : (ι → Fin q) × (ι → ZMod p), f (e z) * A z) -
          ∑ z : (ι → Fin q) × (ι → ZMod p), f (e z) * B z) := by ring
    rw [heq]
    exact v.map_sub_lt hraw hnear
  have heq : (∑ b : ι → Fin q,
      (∑ u : ι → ZMod p, f (e (b, u)) *
        ∏ i, (((u i).val.choose (r i) : ℕ) : L)) *
        ∏ i, (((b i).val.choose (c i).val : ℕ) : L)) =
      ∑ z : (ι → Fin q) × (ι → ZMod p), f (e z) * B z := by
    rw [Fintype.sum_prod_type]
    apply Fintype.sum_congr
    intro b
    rw [Finset.sum_mul]
    apply Fintype.sum_congr
    intro u
    dsimp [B]
    simp only [Nat.cast_mul, Finset.prod_mul_distrib]
    ring
  rw [heq]
  exact hB

/-- The binomial theorem transfers low moments to powers of translated natural coordinates.
Used by `val_translate_moment`. -/
private lemma val_sub_pow_moment_of_pow_moments {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ZMod p) → L) (a : ι → ZMod p) (r : ι → ℕ)
    (hmono : ∀ j : ι → ℕ, (∀ i, j i ≤ r i) →
      v (∑ w : ι → ZMod p, g w * ∏ i, (((w i).val : ℕ) : L) ^ j i) < 1) :
    v (∑ w : ι → ZMod p, g w *
      ∏ i, (((w i).val : L) - ((a i).val : L)) ^ r i) < 1 := by
  apply val_moment_of_expansion v g r
    (fun i x => ((x.val : L) - ((a i).val : L)) ^ r i)
    (fun _ j x => (x.val : L) ^ j)
    (fun i j => (-((a i).val : L)) ^ (r i - j) * ((r i).choose j : L))
  · intro i x
    rw [sub_eq_add_neg, add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · intro i j hj
    rw [map_mul, map_pow, v.map_neg]
    have hA : v ((a i).val : L) ^ (r i - j) ≤ 1 :=
      pow_le_one₀ (by positivity) (valuation_natCast_le_one v _)
    have hC : v ((r i).choose j : L) ≤ 1 := valuation_natCast_le_one v _
    calc
      v ((a i).val : L) ^ (r i - j) * v ((r i).choose j : L) ≤ 1 * 1 :=
        mul_le_mul hA hC (by positivity) (by positivity)
      _ = 1 := one_mul _
  · intro j hj
    exact hmono j hj

/-- Coordinatewise reduction modulo `p` preserves translated power weights modulo the
maximal ideal. Used by `val_translate_moment`. -/
private lemma val_translate_weight_congr {p : ℕ} [Fact p.Prime]
    (hvp : v (p : L) < 1) {ι : Type*} [Fintype ι]
    (a w : ι → ZMod p) (r : ι → ℕ) :
    v ((∏ i, ((((w - a) i).val : ℕ) : L) ^ r i) -
      ∏ i, (((w i).val : L) - ((a i).val : L)) ^ r i) < 1 := by
  apply valuation_prod_sub_prod_lt_one v _
  · intro i hi
    rw [map_pow]
    exact pow_le_one₀ (by positivity) (valuation_natCast_le_one v _)
  · intro i hi
    rw [map_pow]
    have hsub : v (((w i).val : L) - ((a i).val : L)) ≤ 1 :=
      v.map_sub_le (valuation_natCast_le_one v _) (valuation_natCast_le_one v _)
    exact pow_le_one₀ (by positivity) hsub
  · intro i hi
    exact valuation_pow_sub_pow_lt_one v (valuation_natCast_le_one v _)
      (v.map_sub_le (valuation_natCast_le_one v _) (valuation_natCast_le_one v _))
      (valuation_zmod_sub_val_lt_one v hvp (w i) (a i)) (r i)

/-- Translation in the affine coordinates of `H[p]` preserves the low degree moment
congruences in `valuation_sum_coset_mul_prod_pow_lt_one`. -/
private lemma val_translate_moment {p : ℕ} [Fact p.Prime] (hvp : v (p : L) < 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ZMod p) → L) (hg : ∀ w, v (g w) ≤ 1)
    (a : ι → ZMod p) (r : ι → ℕ)
    (hmono : ∀ j : ι → ℕ, (∀ i, j i ≤ r i) →
      v (∑ w : ι → ZMod p, g w * ∏ i, (((w i).val : ℕ) : L) ^ j i) < 1) :
    v (∑ u : ι → ZMod p, g (a + u) *
      ∏ i, (((u i).val : ℕ) : L) ^ r i) < 1 := by
  classical
  let P (u : ι → ZMod p) : L := ∏ i, (((u i).val : ℕ) : L) ^ r i
  let Q (w : ι → ZMod p) : L :=
    ∏ i, ((((w i).val : ℕ) : L) - (((a i).val : ℕ) : L)) ^ r i
  have hpoly : v (∑ w : ι → ZMod p, g w * Q w) < 1 :=
    val_sub_pow_moment_of_pow_moments v g a r hmono
  have hdiff : v ((∑ w : ι → ZMod p, g w * P (w - a)) -
      ∑ w : ι → ZMod p, g w * Q w) < 1 := by
    apply valuation_sum_mul_sub_lt_one v g (fun w => P (w - a)) Q hg
    intro w
    exact val_translate_weight_congr v hvp a w r
  have hshift : v (∑ w : ι → ZMod p, g w * P (w - a)) < 1 := by
    have heq : (∑ w : ι → ZMod p, g w * P (w - a)) =
        (∑ w : ι → ZMod p, g w * Q w) +
        ((∑ w : ι → ZMod p, g w * P (w - a)) -
          ∑ w : ι → ZMod p, g w * Q w) := by ring
    rw [heq]
    exact v.map_add_lt hpoly hdiff
  have hreindex : (∑ u : ι → ZMod p, g (a + u) * P u) =
      ∑ w : ι → ZMod p, g w * P (w - a) := by
    have h := Equiv.sum_comp (Equiv.addLeft a) (fun w => g w * P (w - a))
    convert h using 1
    apply Fintype.sum_congr
    intro u
    simp [Equiv.addLeft, add_sub_cancel_left]
  change v (∑ u : ι → ZMod p, g (a + u) * P u) < 1
  rw [hreindex]
  exact hshift

/-- The `p`-torsion coordinate map is additive, for translating an arbitrary coset
representative in `valuation_sum_coset_mul_prod_pow_lt_one`. -/
private lemma coord_add {p q : ℕ} [Fact p.Prime] (b : Fin q) (a u : ZMod p) :
    (↑(b.val + q * a.val) : ZMod (q * p)) + (↑(q * u.val) : ZMod (q * p)) =
      (↑(b.val + q * (a + u).val) : ZMod (q * p)) := by
  have hmod : (a + u).val ≡ a.val + u.val [MOD p] := by
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ _
  have hmod' : b.val + q * (a + u).val ≡ b.val + q * a.val + q * u.val [MOD q * p] := by
    convert (hmod.mul_left' q).add_left b.val using 1; ring
  have hcast := (ZMod.natCast_eq_natCast_iff
    (b.val + q * (a + u).val) (b.val + q * a.val + q * u.val) (q * p)).2 hmod'
  simpa only [Nat.cast_add, Nat.cast_mul, add_assoc] using hcast.symm

/-- Low degree monomial moments vanish on the coset with its reduced representative, as in
(14) of [RW26b, Radchenko, Wheeler (2026b), Section 4]. -/
private lemma val_reduced_pow_moment {p t : ℕ} [Fact p.Prime] (hvp : v (p : L) < 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hd : Fintype.card ι ≤ 2)
    (f : (ι → ZMod (p ^ t * p)) → L) (hf : ∀ x, v (f x) ≤ 1)
    (hchoose : ∀ j : ι → ℕ,
      2 * ∑ i, j i < Fintype.card ι * (p ^ t * p - 1) →
      v (∑ x, f x * ∏ i, (((x i).val.choose (j i) : ℕ) : L)) < 1)
    (b : ι → Fin (p ^ t)) (r : ι → ℕ)
    (hr : 2 * ∑ i, r i < Fintype.card ι * (p - 1)) :
    v (∑ u : ι → ZMod p,
      f (cosetPiEquiv (pow_pos (Fact.out : p.Prime).pos t) (b, u)) *
      ∏ i, (((u i).val : ℕ) : L) ^ r i) < 1 := by
  classical
  apply val_pow_moment_of_choose_moments v
    (g := fun u => f (cosetPiEquiv (pow_pos (Fact.out : p.Prime).pos t) (b, u)))
    (z := ZMod.val) r
  intro j hj
  have hsum : (∑ i, j i) ≤ ∑ i, r i :=
    Finset.sum_le_sum (by intro i hi; exact hj i)
  have hj : 2 * ∑ i, j i < Fintype.card ι * (p - 1) :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 hsum) hr
  apply val_of_choose_moments v
    (S := fun b => ∑ u : ι → ZMod p,
      f (cosetPiEquiv (pow_pos (Fact.out : p.Prime).pos t) (b, u)) *
      ∏ i, (((u i).val.choose (j i) : ℕ) : L))
    (b := b)
  intro c
  exact val_choose_matrix_moment v hvp hd f hf hchoose j hj c

/-- **(14) of [RW26b, Radchenko, Wheeler (2026b), Section 4, proof of Lemma 1]**, from the
binomial congruence: on `H = (ℤ/p^s)^d` with `d = |ι| ≤ 2` and `s ≥ 1`, if `f` is integral and
`∑_x f(x) ∏_i C(x_i, j_i) ≡ 0 (mod 𝔪)` whenever `∑_i j_i < d(p^s - 1)/2`, then
`∑_{u ∈ 𝔽_p^d} f(b + p^{s-1}u) ∏_i u_i^{r_i} ≡ 0 (mod 𝔪)` for every `b` and every `r` with
`∑_i r_i < d(p - 1)/2`. -/
theorem valuation_sum_coset_mul_prod_pow_lt_one {p s : ℕ} [Fact p.Prime] (hvp : v (p : L) < 1)
    (hs : 1 ≤ s) {ι : Type*} [Fintype ι] [DecidableEq ι] (hd : Fintype.card ι ≤ 2)
    (f : (ι → ZMod (p ^ s)) → L) (hf : ∀ x, v (f x) ≤ 1)
    (hchoose : ∀ j : ι → ℕ, 2 * ∑ i, j i < Fintype.card ι * (p ^ s - 1) →
      v (∑ x, f x * ∏ i, (((x i).val.choose (j i) : ℕ) : L)) < 1)
    (b : ι → ZMod (p ^ s)) (r : ι → ℕ) (hr : 2 * ∑ i, r i < Fintype.card ι * (p - 1)) :
    v (∑ u : ι → ZMod p, f (b + fun i => ((p ^ (s - 1) * (u i).val : ℕ) : ZMod (p ^ s))) *
      ∏ i, (((u i).val : ℕ) : L) ^ (r i)) < 1 := by
  cases s with
  | zero => omega
  | succ t =>
    change (ι → ZMod (p ^ t * p)) → L at f
    change ι → ZMod (p ^ t * p) at b
    simp only [pow_succ] at hchoose
    change v (∑ u : ι → ZMod p,
      f (b + fun i => ((p ^ t * (u i).val : ℕ) : ZMod (p ^ t * p))) *
        ∏ i, (((u i).val : ℕ) : L) ^ r i) < 1
    let q := p ^ t
    have hq : 0 < q := pow_pos (Fact.out : p.Prime).pos t
    let e : ((ι → Fin q) × (ι → ZMod p)) ≃ (ι → ZMod (q * p)) := cosetPiEquiv hq
    let z := e.symm b
    have hz : e z = b := e.apply_symm_apply b
    let g : (ι → ZMod p) → L := fun w => f (e (z.1, w))
    have hg (w : ι → ZMod p) : v (g w) ≤ 1 := hf _
    have hmono (j : ι → ℕ) (hj : ∀ i, j i ≤ r i) :
        v (∑ w : ι → ZMod p, g w * ∏ i, (((w i).val : ℕ) : L) ^ j i) < 1 := by
      have hsum : (∑ i, j i) ≤ ∑ i, r i :=
        Finset.sum_le_sum (by intro i hi; exact hj i)
      have hjr : 2 * ∑ i, j i < Fintype.card ι * (p - 1) :=
        lt_of_le_of_lt (Nat.mul_le_mul_left 2 hsum) hr
      exact val_reduced_pow_moment v hvp hd f hf hchoose z.1 j hjr
    have htranslated := val_translate_moment v hvp g hg z.2 r hmono
    have hcoord (u : ι → ZMod p) :
        b + (fun i => ((q * (u i).val : ℕ) : ZMod (q * p))) = e (z.1, z.2 + u) := by
      rw [← hz]
      funext i
      change (↑((z.1 i).val + q * (z.2 i).val) : ZMod (q * p)) +
        (↑(q * (u i).val) : ZMod (q * p)) =
        (↑((z.1 i).val + q * ((z.2 + u) i).val) : ZMod (q * p))
      simpa only [Pi.add_apply] using coord_add (z.1 i) (z.2 i) (u i)
    have heq : (∑ u : ι → ZMod p,
        f (b + fun i => ((q * (u i).val : ℕ) : ZMod (q * p))) *
          ∏ i, (((u i).val : ℕ) : L) ^ r i) =
        ∑ u : ι → ZMod p, g (z.2 + u) *
          ∏ i, (((u i).val : ℕ) : L) ^ r i := by
      apply Fintype.sum_congr
      intro u
      rw [hcoord]
    rw [heq]
    exact htranslated

end SIC
