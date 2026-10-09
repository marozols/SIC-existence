/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Lagrange

/-!
# Functions on the prime field with vanishing low moments

A function `g : 𝔽_p → k` into a field of characteristic `p` whose moments `∑_u g(u)u^r` vanish for
`2r < p - 1` is zero or nonzero at more than half the points; if `g` and `1/g` both have this
property, `g` is constant; and if `A(u₁)B(u₂)` and `A⁻¹(u₁)B⁻¹(u₂)` have vanishing moments of total
degree below `p - 1`, then `A` or `B` is constant.

This module carries the last step of the proof of [RW26b, Radchenko, Wheeler (2026b), Section 4,
Lemma 1](i)–(iii), after the reduction of a Fourier-integral function to a coset of `H[p]`,
where (14) says that the residues have vanishing moments of total degree below `d(p - 1)/2`. The
statements are about functions on `𝔽_p = ZMod p`; the weight `u^r` is `(u.val : k)^r`.

## The argument

Represent a function `g : 𝔽_p → k` by its interpolation polynomial `A` of degree at most `p - 1`
(Lagrange interpolation over the `p` points of `𝔽_p ⊆ k`). For a polynomial `A ≠ 0` of degree
`m ≤ p - 1`, `∑_{t ∈ 𝔽_p} t^{p-1-m} A(t) = -lc(A)`, since `∑_t t^i` is `0` for `i < p - 1`
(`FiniteField.sum_pow_lt_card_sub_one`) and `-1` for `i = p - 1`. Hence vanishing moments of
degree `r` with `2r < p - 1` force `deg A ≤ (p - 1)/2`.

*(i)* A nonzero `A` of degree at most `(p - 1)/2` has fewer than `p/2` roots, so `g` is nonzero at
more than half the points.

*(ii)* If also `1/g` has interpolation polynomial `A'` of degree at most `(p - 1)/2`, then
`AA' - 1` has degree at most `p - 1` and vanishes at all `p` points, so `AA' = 1` as polynomials and
both are constant.

*(iii)* Testing `A(u₁)B(u₂)` against `u₁^{p-1-deg A}u₂^{p-1-deg B}` gives
`deg A + deg B ≤ p - 1`, and likewise for the reciprocals. A nonconstant `A` has
`deg A + deg A⁻¹ ≥ p`, since otherwise `AA⁻¹ - 1` would be a nonzero polynomial of degree below `p`
with `p` roots; so `A` and `B` cannot both be nonconstant.
-/

open Polynomial

namespace SIC

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [CharP k p]

/-! ### One variable

Vanishing moments below `(p - 1)/2` bound the degree of the interpolation polynomial by
`(p - 1)/2`. -/

/-- The Lagrange polynomial representing a function on the prime field.
Used by the three moment results. -/
private noncomputable def interp (g : ZMod p → k) : k[X] :=
  Lagrange.interpolate Finset.univ (fun u : ZMod p => (u.val : k)) g

/-- The prime-field nodes remain distinct in a field of characteristic `p`.
Used by `interp_eval`. -/
private theorem cast_injective : Function.Injective (fun u : ZMod p => (u.val : k)) := by
  intro x y h
  apply ZMod.castHom_injective k
  simpa only [ZMod.castHom_apply, ZMod.cast_eq_val] using h

/-- The interpolation polynomial agrees with the function at each prime-field node.
Used by the three moment results. -/
private theorem interp_eval (g : ZMod p → k) (u : ZMod p) :
    (interp g).eval (u.val : k) = g u := by
  exact Lagrange.eval_interpolate_at_node g ((by intro x _ y _ h; exact cast_injective h))
    (Finset.mem_univ u)

/-- A prime-field interpolant has degree at most `p - 1`. Used by `moment_at_degree`. -/
private theorem interp_natDegree_le (g : ZMod p → k) : (interp g).natDegree ≤ p - 1 := by
  apply Polynomial.natDegree_le_of_degree_le
  simpa only [interp, Finset.card_univ, ZMod.card] using
    (Lagrange.degree_interpolate_le (s := Finset.univ)
      (v := fun u : ZMod p => (u.val : k)) g
      (by intro x _ y _ h; exact cast_injective h))

/-- Prime-field power sums below `p - 1` vanish in `k`. Used by `moment_at_degree`. -/
private theorem cast_sum_pow_lt (i : ℕ) (hi : i < p - 1) :
    ∑ u : ZMod p, (u.val : k) ^ i = 0 := by
  have hz : ∑ u : ZMod p, u ^ i = 0 := by
    apply FiniteField.sum_pow_lt_card_sub_one (ZMod p)
    simpa only [ZMod.card] using hi
  have := congrArg (ZMod.castHom (dvd_refl p) k) hz
  simpa only [map_sum, map_pow, map_zero, ZMod.castHom_apply, ZMod.cast_eq_val] using this

/-- The prime-field power sum at exponent `p - 1` is `-1`. Used by `moment_at_degree`. -/
private theorem cast_sum_pow_top : ∑ u : ZMod p, (u.val : k) ^ (p - 1) = -1 := by
  classical
  have hp : 0 < p - 1 := by have := (Fact.out : Nat.Prime p).one_lt; omega
  calc
    ∑ u : ZMod p, (u.val : k) ^ (p - 1) =
        ∑ u ∈ (Finset.univ.erase (0 : ZMod p)), (1 : k) := by
      rw [← Finset.sum_erase_add Finset.univ (fun u : ZMod p => (u.val : k) ^ (p - 1))
        (Finset.mem_univ 0)]
      simp only [ZMod.val_zero, Nat.cast_zero, zero_pow (Nat.ne_of_gt hp), add_zero]
      apply Finset.sum_congr rfl
      intro u hu
      have hu0 : u ≠ 0 := Finset.ne_of_mem_erase hu
      calc
        (u.val : k) ^ (p - 1) =
            (ZMod.castHom (dvd_refl p) k) (u ^ (p - 1)) := by
          simp only [map_pow, ZMod.castHom_apply, ZMod.cast_eq_val]
        _ = 1 := by rw [ZMod.pow_card_sub_one_eq_one hu0, map_one]
    _ = -1 := by
      simp [Finset.card_erase_of_mem, ZMod.card,
        Nat.cast_sub (show 1 ≤ p from (Fact.out : Nat.Prime p).one_lt.le)]

/-- The critical moment of a polynomial of degree at most `p - 1` is minus
its leading coefficient. Used by the one- and two-variable moment results. -/
private theorem moment_at_degree (F : k[X]) (hd : F.natDegree ≤ p - 1) :
    ∑ u : ZMod p, F.eval (u.val : k) * (u.val : k) ^ (p - 1 - F.natDegree) =
      -F.leadingCoeff := by
  classical
  have hdp : F.natDegree < p := by
    have hp := (Fact.out : Nat.Prime p).one_lt
    omega
  have hterm (i : ℕ) (hi : i ∈ Finset.range p) :
      F.coeff i * (∑ u : ZMod p, (u.val : k) ^ (i + (p - 1 - F.natDegree))) =
        if i = F.natDegree then -F.leadingCoeff else 0 := by
    by_cases hil : i < F.natDegree
    · have he : i + (p - 1 - F.natDegree) < p - 1 := by omega
      rw [cast_sum_pow_lt (p := p) (k := k) _ he, mul_zero]
      simp only [ite_eq_right (Nat.ne_of_lt hil)]
    · by_cases hie : i = F.natDegree
      · subst i
        have he : F.natDegree + (p - 1 - F.natDegree) = p - 1 := by omega
        rw [he, Polynomial.coeff_natDegree, cast_sum_pow_top (p := p) (k := k)]
        simp
      · have hig : F.natDegree < i := by omega
        simp [hie, Polynomial.coeff_eq_zero_of_natDegree_lt hig]
  calc
    ∑ u : ZMod p, F.eval (u.val : k) * (u.val : k) ^ (p - 1 - F.natDegree) =
        ∑ u : ZMod p, ∑ i ∈ Finset.range p,
          F.coeff i * (u.val : k) ^ (i + (p - 1 - F.natDegree)) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Polynomial.eval_eq_sum_range' hdp]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_add]
      ring
    _ = ∑ i ∈ Finset.range p,
          F.coeff i * (∑ u : ZMod p, (u.val : k) ^ (i + (p - 1 - F.natDegree))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = -F.leadingCoeff := by
      rw [Finset.sum_congr rfl hterm]
      simp [hdp]


/-- Vanishing low moments bound the interpolation degree, as used in
`eq_zero_or_lt_two_mul_card_of_moments` and `eq_const_of_moments`. -/
private theorem interp_degree_of_moments (g : ZMod p → k)
    (hg : ∀ r : ℕ, 2 * r < p - 1 → ∑ u, g u * (u.val : k) ^ r = 0) :
    2 * (interp g).natDegree ≤ p - 1 := by
  by_contra h
  have hd := interp_natDegree_le g
  have hr : 2 * (p - 1 - (interp g).natDegree) < p - 1 := by omega
  have hsum : ∑ u : ZMod p,
      (interp g).eval (u.val : k) * (u.val : k) ^ (p - 1 - (interp g).natDegree) = 0 := by
    simpa only [interp_eval] using hg _ hr
  have hlead : -(interp g).leadingCoeff = 0 :=
    (moment_at_degree (interp g) hd).symm.trans hsum
  have hz : interp g = 0 := Polynomial.leadingCoeff_eq_zero.mp (neg_eq_zero.mp hlead)
  simp only [hz, Polynomial.natDegree_zero, mul_zero] at h
  have hp := (Fact.out : Nat.Prime p).one_lt
  omega

open scoped Classical in
/-- **[RW26b, Radchenko, Wheeler (2026b), Section 4, Lemma 1](i), on one coset**: a function
`g : 𝔽_p → k` with `∑_u g(u)u^r = 0` for `2r < p - 1` is zero or nonzero at more than half the
points. -/
theorem eq_zero_or_lt_two_mul_card_of_moments (g : ZMod p → k)
    (hg : ∀ r : ℕ, 2 * r < p - 1 → ∑ u, g u * (u.val : k) ^ r = 0) :
    g = 0 ∨ p < 2 * (Finset.univ.filter fun u => g u ≠ 0).card := by
  classical
  by_cases hF : interp g = 0
  · left
    funext u
    have hu := interp_eval g u
    change g u = 0
    simpa only [hF, Polynomial.eval_zero] using hu.symm
  · right
    let Z : Finset (ZMod p) := Finset.univ.filter fun u => g u = 0
    have hZ : Z.card ≤ (interp g).natDegree := by
      by_contra hn
      have hlt : (interp g).natDegree < Fintype.card Z := by
        simpa only [Fintype.card_coe] using (Nat.lt_of_not_ge hn)
      have hz : interp g = 0 :=
        Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (interp g)
          (f := fun u : Z => ((u.val : ZMod p).val : k))
          (fun a b hab => Subtype.ext (cast_injective hab))
          (fun u => by
            rw [interp_eval]
            exact (Finset.mem_filter.mp u.property).2)
          hlt
      exact hF hz
    have hsum := Finset.card_filter_add_card_filter_not (fun u : ZMod p => g u = 0)
      (s := Finset.univ)
    have htotal : Z.card + (Finset.univ.filter fun u : ZMod p => g u ≠ 0).card = p := by
      simpa only [Z, Finset.card_univ, ZMod.card] using hsum
    have hd := interp_degree_of_moments g hg
    have hp := (Fact.out : Nat.Prime p).one_lt
    omega

/-- A function nonzero at one node has a nonzero interpolant.
Used by the one- and two-variable moment results. -/
private theorem interp_ne_zero (g : ZMod p → k) (u : ZMod p) (hu : g u ≠ 0) :
    interp g ≠ 0 := by
  intro hF
  apply hu
  have he := interp_eval g u
  simpa only [hF, Polynomial.eval_zero] using he.symm

/-- Interpolants of pointwise reciprocal functions multiply to one when their
degrees sum to less than `p`. Used by `constant_of_degree_sum_lt`. -/
private theorem interp_mul_eq_one (g h : ZMod p → k) (hgh : ∀ u, g u * h u = 1)
    (hdegree : (interp g).natDegree + (interp h).natDegree < p) :
    interp g * interp h = 1 := by
  have hprod : (interp g * interp h).natDegree < p :=
    lt_of_le_of_lt Polynomial.natDegree_mul_le hdegree
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ cast_injective
  · intro u
    simpa only [Polynomial.eval_mul, interp_eval, Polynomial.eval_one] using hgh u
  · simpa only [Polynomial.natDegree_one, max_eq_left (Nat.zero_le _), ZMod.card] using hprod

/-- A nonvanishing function is constant if its interpolant and reciprocal
interpolant have combined degree less than `p`. Used by `eq_const_of_moments`
and `forall_eq_or_forall_eq_of_moments`. -/
private theorem constant_of_degree_sum_lt (g : ZMod p → k) (hg0 : ∀ u, g u ≠ 0)
    (hdegree : (interp g).natDegree +
      (interp fun u => (g u)⁻¹).natDegree < p) (u : ZMod p) :
    g u = g 0 := by
  have hprod := interp_mul_eq_one g (fun u => (g u)⁻¹)
    (fun u => mul_inv_cancel₀ (hg0 u)) hdegree
  have hF : interp g ≠ 0 := interp_ne_zero g 0 (hg0 0)
  have hG : interp (fun u => (g u)⁻¹) ≠ 0 :=
    interp_ne_zero _ 0 (inv_ne_zero (hg0 0))
  have hzero : (interp g).natDegree = 0 := by
    have hsum : (interp g).natDegree + (interp fun u => (g u)⁻¹).natDegree = 0 := by
      simpa only [Polynomial.natDegree_mul hF hG, Polynomial.natDegree_one] using
        congrArg Polynomial.natDegree hprod
    exact (Nat.add_eq_zero_iff.mp hsum).1
  have hconst := Polynomial.eq_C_of_natDegree_eq_zero hzero
  calc
    g u = (interp g).eval (u.val : k) := (interp_eval g u).symm
    _ = (interp g).eval ((0 : ZMod p).val : k) := by rw [hconst]; simp
    _ = g 0 := interp_eval g 0

/-- **[RW26b, Radchenko, Wheeler (2026b), Section 4, Lemma 1](ii), on one coset**: if `g` has no
zeros and both `g` and `1/g` have vanishing moments below `(p - 1)/2`, then `g` is constant. -/
theorem eq_const_of_moments (g : ZMod p → k) (hg0 : ∀ u, g u ≠ 0)
    (hg : ∀ r : ℕ, 2 * r < p - 1 → ∑ u, g u * (u.val : k) ^ r = 0)
    (hginv : ∀ r : ℕ, 2 * r < p - 1 → ∑ u, (g u)⁻¹ * (u.val : k) ^ r = 0) (u : ZMod p) :
    g u = g 0 := by
  have hd := interp_degree_of_moments g hg
  have hdi := interp_degree_of_moments (fun u => (g u)⁻¹) hginv
  apply constant_of_degree_sum_lt g hg0
  have hp := (Fact.out : Nat.Prime p).one_lt
  omega

/-! ### Two variables

Products `A(u₁)B(u₂)` whose moments of total degree below `p - 1` vanish, together with those of
their reciprocals. -/

/-- A nonzero interpolation polynomial has a nonzero critical moment.
Used by `degree_add_le_of_product_moments`. -/
private theorem critical_moment_ne_zero (g : ZMod p → k) (hF : interp g ≠ 0) :
    (∑ u, g u * (u.val : k) ^ (p - 1 - (interp g).natDegree)) ≠ 0 := by
  have htest : (∑ u, g u * (u.val : k) ^ (p - 1 - (interp g).natDegree)) =
      -(interp g).leadingCoeff := by
    simpa only [interp_eval] using moment_at_degree (interp g) (interp_natDegree_le g)
  rw [htest]
  exact neg_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hF)

/-- Vanishing product moments force the sum of interpolation degrees to be at
most `p - 1`. Used by `forall_eq_or_forall_eq_of_moments`. -/
private theorem degree_add_le_of_product_moments (A B : ZMod p → k)
    (hA0 : A 0 ≠ 0) (hB0 : B 0 ≠ 0)
    (h : ∀ r₁ r₂ : ℕ, r₁ + r₂ < p - 1 →
      (∑ u, A u * (u.val : k) ^ r₁) * (∑ u, B u * (u.val : k) ^ r₂) = 0) :
    (interp A).natDegree + (interp B).natDegree ≤ p - 1 := by
  by_contra hn
  have hdA := interp_natDegree_le A
  have hdB := interp_natDegree_le B
  have hp := (Fact.out : Nat.Prime p).one_lt
  have hr : (p - 1 - (interp A).natDegree) +
      (p - 1 - (interp B).natDegree) < p - 1 := by omega
  have hzero := h _ _ hr
  exact (mul_ne_zero
    (critical_moment_ne_zero A (interp_ne_zero A 0 hA0))
    (critical_moment_ne_zero B (interp_ne_zero B 0 hB0))) hzero

/-- **[RW26b, Radchenko, Wheeler (2026b), Section 4, Lemma 1](iii), on one coset**: if `A` and
`B` have no zeros, and the moments of `A(u₁)B(u₂)` and of `A(u₁)⁻¹B(u₂)⁻¹` of total degree below
`p - 1` vanish, then `A` or `B` is constant. -/
theorem forall_eq_or_forall_eq_of_moments (A B : ZMod p → k) (hA0 : ∀ u, A u ≠ 0)
    (hB0 : ∀ u, B u ≠ 0)
    (h : ∀ r₁ r₂ : ℕ, r₁ + r₂ < p - 1 →
      (∑ u, A u * (u.val : k) ^ r₁) * (∑ u, B u * (u.val : k) ^ r₂) = 0)
    (hinv : ∀ r₁ r₂ : ℕ, r₁ + r₂ < p - 1 →
      (∑ u, (A u)⁻¹ * (u.val : k) ^ r₁) * (∑ u, (B u)⁻¹ * (u.val : k) ^ r₂) = 0) :
    (∀ u, A u = A 0) ∨ ∀ u, B u = B 0 := by
  have hd := degree_add_le_of_product_moments A B (hA0 0) (hB0 0) h
  have hdi := degree_add_le_of_product_moments
    (fun u => (A u)⁻¹) (fun u => (B u)⁻¹)
    (inv_ne_zero (hA0 0)) (inv_ne_zero (hB0 0)) hinv
  by_contra hn
  have hAn : ¬∀ u, A u = A 0 := fun ha => hn (Or.inl ha)
  have hBn : ¬∀ u, B u = B 0 := fun hb => hn (Or.inr hb)
  have hAm : p ≤ (interp A).natDegree +
      (interp fun u => (A u)⁻¹).natDegree := by
    by_contra hm
    exact hAn (fun u => constant_of_degree_sum_lt A hA0 (Nat.lt_of_not_ge hm) u)
  have hBm : p ≤ (interp B).natDegree +
      (interp fun u => (B u)⁻¹).natDegree := by
    by_contra hm
    exact hBn (fun u => constant_of_degree_sum_lt B hB0 (Nat.lt_of_not_ge hm) u)
  have hp := (Fact.out : Nat.Prime p).one_lt
  omega

end SIC
