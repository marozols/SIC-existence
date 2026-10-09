/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.MetricGroup
import SICs.Source

/-!
# Finite quantum dilogarithms

Functions on a metric group satisfying the reflection law and the product form of the pentagon
relation, their Fourier transform `Ê = λ⟨·⟩E` with `λ³` the Gauss sum, and their construction
from the finite five-term relation.

This module follows [RW26b, Radchenko, Wheeler (2026b), Section 3, Proposition 1, (4)–(6)] and
[RW26, Radchenko, Wheeler (2026), Section 4.2, Theorem 5, `thm:fqdilogbasicproperties`;
Section 4.2, equation (36), `eq:pentagonproduct3`]. A `FiniteQuantumDilog` is the structure that
[RW26b] uses: the reflection law (4) and the product form (6) of the pentagon relation, from
which the value at zero (3) and the Fourier law (5) follow. It is not the definition of
[RW26, Radchenko, Wheeler (2026), Section 4.2] by the pentagon relation with constant
`C ≠ 0`, which no endpoint uses. `FiniteQuantumDilog.ofFiveTerm` builds one from
[RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, (7), `eq:Fgpm.5term`],
the form in which the analytic argument
proves the finite five-term relation.

Theorem 5 in [RW26] assumes `N > 4` for its pentagon definition. Its following remark
allows `N ≤ 4` when `E(0)² = √N E(0) + 1` is imposed. Our reflection field already
includes this normalization, so the conclusions below hold at every group order.

## The argument

Write `N = |G|`, `s = √N`, `δ` for the indicator of `0`, and `Ẽ(x) = ⟨x⟩E(x)`.

**The value at zero and nonvanishing.** Reflection (4) at `0` is `E(0)² = s E(0) + 1`, so
`E(0)(E(0) - s) = 1`; off zero it is `E(x)E(-x) = ⟨x⟩⁻¹ ≠ 0`.

**The Fourier law (5).** Summing (6) over its first argument `x` gives on the left
`s Ê(0) Ẽ̂(-y)`, since `∑_x E(x - t) = s Ê(0)`. On the right, (6) at second argument `0` and
first argument `-y` evaluates `∑_w ⟨w⟩E(-w)E(w - y)` as `s E(0)(1 + (s E(0) - N)δ(y))` by
reflection, and with `E(0)² = s E(0) + 1`, `N = s²` the right side becomes `s E(0)E(y)` for every
`y`. Hence `Ê(0) Ẽ̂(z) = E(0) E(-z)` for all `z`; in particular `Ê(0) ≠ 0`. Transforming once
more with `f̂̂(z) = f(-z)` gives `Ê(0) Ẽ(z) = E(0) Ê(z)`, that is `Ê = λ⟨·⟩E` with
`λ = Ê(0)/E(0)`. This reorganizes the proof of
[RW26, Radchenko, Wheeler (2026), Theorem 5, `thm:fqdilogbasicproperties`](iii), which shows
that `Ẽ ⋆ E`
is constant off zero and hence `Ẽ̂ ∝ E(-·)` off zero; the product form (6) also gives the value
at zero, which replaces the source's appeal to `⟨x⟩E(x)` being nonconstant on `G ∖ {0}`.

**The cube of `λ`.** By (5), `WE = λE` for the Fourier–Weil operator, so
`λ³E = W³E = (s⁻¹ ∑_x ⟨x⟩⁻¹) E` (`MetricGroup.weil_weil_weil`), and `E(0) ≠ 0`.

**From the five-term relation.** Given `E` and `F⁻` with `E(x)F⁻(-x) = ⟨x⟩⁻¹`,
`F⁻(x) = E(x)` off zero and `E(0)² = s E(0) + 1`, the case `v = 0` of (7) of
[RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`]
is character orthogonality: the summand `E(x)/F⁻(x)` is `1` off zero and `E(0)²` at zero. For
`(u, v) ≠ (0, 0)`, the five-term relation at `(u + v, -v)` becomes the product form (36) after
`1/F⁻(-y) = ⟨y⟩E(y)` and the Gaussian law `⟨v - x⟩ = ⟨v⟩⟨x⟩⟨x; v⟩⁻¹`; at `(0, 0)` both sides
of (36) are `E(0) + s`.
-/

namespace SIC

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {k : Type*} [Field k]

/-! ### Finite quantum dilogarithms

The structure, the value at zero, and nonvanishing. -/

/-- **A finite quantum dilogarithm** on a metric group, in the form used by
[RW26b, Radchenko, Wheeler (2026b), Section 3, Proposition 1]: a function `E : G → k` with the
reflection law (4), `E(x)E(-x) = ⟨x⟩⁻¹ + √N E(0)δ(x)`, and the product form (6) of the pentagon
relation, `(1/√N) ∑_t E(t)⟨t⟩E(x - t)⟨t; y⟩ = ⟨x + y⟩E(-x - y)E(x)E(y) - N E(0)δ(x)δ(y)`
([RW26, Radchenko, Wheeler (2026), equation (36), `eq:pentagonproduct3`]). -/
structure FiniteQuantumDilog (M : MetricGroup G k) where
  /-- The values `E(x)`. -/
  toFun : G → k
  /-- The reflection law (4). -/
  reflection (x : G) :
    toFun x * toFun (-x) = (M.gaussian x)⁻¹ + M.sqrtCard * toFun 0 * (if x = 0 then 1 else 0)
  /-- The product form (6) of the pentagon relation. -/
  product (x y : G) :
    M.sqrtCard⁻¹ * ∑ t, toFun t * M.gaussian t * toFun (x - t) * M.bichar t y =
      M.gaussian (x + y) * toFun (-x - y) * toFun x * toFun y -
        (Fintype.card G : k) * toFun 0 * ((if x = 0 then 1 else 0) * (if y = 0 then 1 else 0))

/-- The Gaussian weighted product sum from a reflection law, used in
`product_sum_reflected_zero` and `fiveTerm_product_zero`. -/
private theorem reflection_sum (M : MetricGroup G k) (E : G → k)
    (hrefl : ∀ x, E x * E (-x) = (M.gaussian x)⁻¹ +
      M.sqrtCard * E 0 * (if x = 0 then 1 else 0)) :
    (∑ t, E t * M.gaussian t * E (-t)) =
      (Fintype.card G : k) + M.sqrtCard * E 0 := by
  have hsummand (t : G) : E t * M.gaussian t * E (-t) =
      1 + M.sqrtCard * E 0 * (if t = 0 then 1 else 0) := by
    calc
      _ = M.gaussian t * (E t * E (-t)) := by ring
      _ = M.gaussian t * ((M.gaussian t)⁻¹ +
          M.sqrtCard * E 0 * (if t = 0 then 1 else 0)) := by rw [hrefl]
      _ = _ := by
        by_cases ht : t = 0
        · subst t
          simp [M.gaussian_zero]
        · simp [ht, M.gaussian_ne_zero t]
  simp_rw [hsummand]
  rw [Finset.sum_add_distrib]
  simp

namespace FiniteQuantumDilog

variable {M : MetricGroup G k}

/-- Evaluation of a finite quantum dilogarithm as a function. -/
instance : CoeFun (FiniteQuantumDilog M) (fun _ => G → k) :=
  ⟨toFun⟩

variable (E : FiniteQuantumDilog M)

/-- `E(0)² = √N E(0) + 1`, [RW26, Radchenko, Wheeler (2026), Theorem 5,
`thm:fqdilogbasicproperties`](i); reflection (4) at zero. -/
theorem zero_sq : E 0 ^ 2 = M.sqrtCard * E 0 + 1 := by
  simpa only [neg_zero, M.gaussian_zero, inv_one, ite_true, mul_one, pow_two,
    mul_comm (1 : k) (M.sqrtCard * E 0), add_comm] using E.reflection 0

/-- `E(x)E(-x) = ⟨x⟩⁻¹` for `x ≠ 0`, [RW26, Radchenko, Wheeler (2026), Theorem 5,
`thm:fqdilogbasicproperties`](ii). -/
theorem mul_neg_of_ne_zero {x : G} (hx : x ≠ 0) : E x * E (-x) = (M.gaussian x)⁻¹ := by
  simpa [hx] using E.reflection x

/-- The values never vanish. -/
theorem ne_zero (x : G) : E x ≠ 0 := by
  by_cases hx : x = 0
  · subst x
    intro h
    have hsq := E.zero_sq
    simp [h] at hsq
  · intro h
    have hr := E.mul_neg_of_ne_zero hx
    rw [h, zero_mul] at hr
    exact (inv_ne_zero (M.gaussian_ne_zero x)) hr.symm

/-- **The reciprocal values** `E(x)⁻¹ = ⟨x⟩E(-x) - √N δ(x)`, the reflection law (4) solved for
`E(x)⁻¹` (at `x = 0` by `E(0)(E(0) - √N) = 1`), as used in [RW26b, Radchenko, Wheeler (2026b),
Section 7, proof of Theorem 7] and in the identity (15). -/
theorem inv_eq (x : G) :
    (E x)⁻¹ = M.gaussian x * E (-x) - M.sqrtCard * (if x = 0 then 1 else 0) := by
  by_cases hx : x = 0
  · subst x
    simp only [M.gaussian_zero, one_mul, neg_zero, ite_true, mul_one]
    have h := E.zero_sq
    have he : E 0 * (E 0 - M.sqrtCard) = 1 := by
      calc
        _ = E 0 ^ 2 - M.sqrtCard * E 0 := by ring
        _ = 1 := by rw [h]; ring
    rw [(eq_inv_of_mul_eq_one_right he).symm]
  · have hr := E.mul_neg_of_ne_zero hx
    simp only [ite_eq_right hx, mul_zero, sub_zero]
    apply inv_eq_of_mul_eq_one_right
    calc
      E x * (M.gaussian x * E (-x)) = M.gaussian x * (E x * E (-x)) := by ring
      _ = 1 := by rw [hr, mul_inv_cancel₀ (M.gaussian_ne_zero x)]

/-! ### The Fourier law

`Ê = λ⟨·⟩E` with `λ = Ê(0)/E(0)` and `λ³ = s⁻¹ ∑_x ⟨x⟩⁻¹`. -/

/-- **The multiplier** `λ = Ê(0)/E(0)` of [RW26, Radchenko, Wheeler (2026), Theorem 5,
`thm:fqdilogbasicproperties`](iii); for the values of Faddeev's modular quantum dilogarithm it is
the eta multiplier `μ_γ` ([RW26b, Radchenko, Wheeler (2026b), Proposition 1]). -/
def multiplier : k :=
  M.fourier E 0 / E 0

/-- The sum of the left sides of `FiniteQuantumDilog.product`. -/
private theorem product_sum_left (E : FiniteQuantumDilog M) (y : G) :
    (∑ x, M.sqrtCard⁻¹ *
      ∑ t, E t * M.gaussian t * E (x - t) * M.bichar t y) =
      M.sqrtCard * M.fourier E 0 *
        M.fourier (fun t => M.gaussian t * E t) (-y) := by
  have hinner (t : G) :
      (∑ x, E t * M.gaussian t * E (x - t) * M.bichar t y) =
        (∑ x, E x) * (M.gaussian t * E t * M.bichar t y) := by
    calc
      _ = (M.gaussian t * E t * M.bichar t y) * ∑ x, E (x - t) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by
        rw [show (∑ x, E (x - t)) = ∑ x, E x from by
          apply Fintype.sum_equiv (Equiv.subRight t)
          intro x
          rfl]
        ring
  calc
    _ = M.sqrtCard⁻¹ *
        ∑ x, ∑ t, E t * M.gaussian t * E (x - t) * M.bichar t y := by
          rw [Finset.mul_sum]
    _ = M.sqrtCard⁻¹ *
        ∑ t, ∑ x, E t * M.gaussian t * E (x - t) * M.bichar t y := by
          rw [Finset.sum_comm]
    _ = M.sqrtCard⁻¹ * ((∑ x, E x) *
        ∑ t, M.gaussian t * E t * M.bichar t y) := by
          congr 1
          simp_rw [hinner]
          rw [Finset.mul_sum]
    _ = _ := by
      simp only [MetricGroup.fourier, neg_zero, neg_neg, M.bichar_zero_right, mul_one]
      field_simp [M.sqrtCard_ne_zero]

/-- The reflected product sum for a nonzero argument, from `FiniteQuantumDilog.product` at
`(-y, 0)`. -/
private theorem product_sum_reflected (E : FiniteQuantumDilog M) {y : G} (hy : y ≠ 0) :
    (∑ x, M.gaussian (x + y) * E (-x - y) * E x) = M.sqrtCard * E 0 := by
  have hreindex : (∑ x, M.gaussian (x + y) * E (-x - y) * E x) =
      ∑ t, E t * M.gaussian t * E (-y - t) := by
    apply Fintype.sum_equiv ((Equiv.neg G).trans (Equiv.subRight y))
    intro x
    simp only [Equiv.trans_apply, Equiv.neg_apply, Equiv.subRight_apply]
    rw [show -y - (-x - y) = x by abel,
      show -x - y = -(x + y) by abel, M.gaussian_neg]
    ring
  have hprod : M.sqrtCard⁻¹ *
      ∑ t, E t * M.gaussian t * E (-y - t) = E 0 := by
    have hp := E.product (-y) 0
    have hny : -y ≠ 0 := neg_ne_zero.mpr hy
    simp only [add_zero, sub_zero, M.bichar_zero_right, mul_one,
      ite_true, ite_eq_right hny, mul_zero, sub_zero, M.gaussian_neg] at hp
    calc
      _ = M.gaussian y * E y * E (-y) * E 0 := by simpa only [neg_neg] using hp
      _ = E 0 := by
        rw [show M.gaussian y * E y * E (-y) * E 0 =
          M.gaussian y * (E y * E (-y)) * E 0 by ring,
          E.mul_neg_of_ne_zero hy, mul_inv_cancel₀ (M.gaussian_ne_zero y), one_mul]
  calc
    _ = M.sqrtCard * (M.sqrtCard⁻¹ *
        ∑ x, M.gaussian (x + y) * E (-x - y) * E x) := by
          field_simp [M.sqrtCard_ne_zero]
    _ = M.sqrtCard * E 0 := by rw [hreindex, hprod]

/-- The reflected product sum at zero, from `FiniteQuantumDilog.reflection`. -/
private theorem product_sum_reflected_zero (E : FiniteQuantumDilog M) :
    (∑ x, M.gaussian x * E (-x) * E x) =
      (Fintype.card G : k) + M.sqrtCard * E 0 := by
  calc
    _ = ∑ x, E x * M.gaussian x * E (-x) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := reflection_sum M E E.reflection

/-- Summing the right sides of `FiniteQuantumDilog.product`. -/
private theorem product_sum_right (E : FiniteQuantumDilog M) (y : G) :
    (∑ x, (M.gaussian (x + y) * E (-x - y) * E x * E y -
      (Fintype.card G : k) * E 0 *
        ((if x = 0 then 1 else 0) * (if y = 0 then 1 else 0)))) =
      M.sqrtCard * E 0 * E y := by
  have hdelta : (∑ x : G, (Fintype.card G : k) * E 0 *
      ((if x = 0 then 1 else 0) * (if y = 0 then 1 else 0))) =
      (Fintype.card G : k) * E 0 * (if y = 0 then 1 else 0) := by
    by_cases hy : y = 0 <;> simp [hy]
  have hsum : (∑ x, (M.gaussian (x + y) * E (-x - y) * E x * E y -
      (Fintype.card G : k) * E 0 *
        ((if x = 0 then 1 else 0) * (if y = 0 then 1 else 0)))) =
      (∑ x, M.gaussian (x + y) * E (-x - y) * E x) * E y -
        (Fintype.card G : k) * E 0 * (if y = 0 then 1 else 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_mul, hdelta]
  by_cases hy : y = 0
  · subst y
    simp only [add_zero, sub_zero, ite_true, mul_one] at hsum ⊢
    rw [hsum, product_sum_reflected_zero E]
    ring
  · rw [hsum, ite_eq_right hy, mul_zero, sub_zero, product_sum_reflected E hy]

/-- The two summed product identities give the Fourier relation before inversion. -/
private theorem product_fourier_pair (E : FiniteQuantumDilog M) (z : G) :
    M.fourier E 0 * M.fourier (fun t => M.gaussian t * E t) z =
      E 0 * E (-z) := by
  have hsum (y : G) :
      M.sqrtCard * M.fourier E 0 *
          M.fourier (fun t => M.gaussian t * E t) (-y) =
        M.sqrtCard * E 0 * E y := by
    calc
      _ = ∑ x, M.sqrtCard⁻¹ *
          ∑ t, E t * M.gaussian t * E (x - t) * M.bichar t y :=
        (product_sum_left E y).symm
      _ = ∑ x, (M.gaussian (x + y) * E (-x - y) * E x * E y -
          (Fintype.card G : k) * E 0 *
            ((if x = 0 then 1 else 0) * (if y = 0 then 1 else 0))) := by
        apply Finset.sum_congr rfl
        intro x _
        exact E.product x y
      _ = _ := product_sum_right E y
  have hc := mul_left_cancel₀ M.sqrtCard_ne_zero (show
      M.sqrtCard * (M.fourier E 0 *
        M.fourier (fun t => M.gaussian t * E t) z) =
      M.sqrtCard * (E 0 * E (-z)) from by
        simpa only [neg_neg, mul_assoc] using hsum (-z))
  exact hc

/-- **The Fourier law (5)** `Ê(x) = λ⟨x⟩E(x)`
[RW26b, Radchenko, Wheeler (2026b), Proposition 1, (5)];
[RW26, Radchenko, Wheeler (2026), Theorem 5, `thm:fqdilogbasicproperties`](iii). Stated for an
abstract finite quantum dilogarithm on a metric group, of which `E_{I,ε}` is an instance
(`pseudolatticeDilog_eq_finiteDilogE`). -/
@[source "RW26b, Proposition 1, p. 4 (equation (5), abstract form)"]
theorem fourier_eq (x : G) : M.fourier E x = E.multiplier * M.gaussian x * E x := by
  let F : G → k := fun t => M.gaussian t * E t
  have hpair : (fun z => M.fourier E 0 * M.fourier F z) =
      (fun z => E 0 * E (-z)) := by
    funext z
    exact E.product_fourier_pair z
  have htransform (z : G) :
      M.fourier E 0 * F z = E 0 * M.fourier E z := by
    have h := congrArg (fun f : G → k => M.fourier f (-z)) hpair
    rw [M.fourier_const_mul, M.fourier_const_mul,
      M.fourier_fourier, M.fourier_comp_neg] at h
    simpa only [neg_neg] using h
  apply mul_left_cancel₀ (E.ne_zero 0)
  calc
    E 0 * M.fourier E x = M.fourier E 0 * F x := (htransform x).symm
    _ = E 0 * (E.multiplier * M.gaussian x * E x) := by
      simp only [multiplier, F]
      field_simp [E.ne_zero 0]

/-- `λ³ = ∫_G ⟨x⟩⁻¹ dx`, [RW26, Radchenko, Wheeler (2026), Theorem 5,
`thm:fqdilogbasicproperties`](iii); [RW26b, Radchenko, Wheeler (2026b), Proposition 1]. -/
theorem multiplier_pow_three : E.multiplier ^ 3 = M.gaussSum := by
  have hW1 : M.weil E = fun x => E.multiplier * E x := by
    funext x
    rw [MetricGroup.weil, E.fourier_eq x]
    field_simp [M.gaussian_ne_zero x]
  have hW2 : M.weil (M.weil E) = fun x => E.multiplier ^ 2 * E x := by
    funext x
    rw [hW1, M.weil_const_mul, hW1]
    ring
  have hW3 : M.weil (M.weil (M.weil E)) 0 = E.multiplier ^ 3 * E 0 := by
    rw [hW2, M.weil_const_mul, hW1]
    ring
  apply mul_right_cancel₀ (E.ne_zero 0)
  calc
    E.multiplier ^ 3 * E 0 = M.weil (M.weil (M.weil E)) 0 := hW3.symm
    _ = M.gaussSum * E 0 := M.weil_weil_weil E 0

end FiniteQuantumDilog

/-! ### From the finite five-term relation

The case `v = 0` of [RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`](7) by
orthogonality, and a finite quantum dilogarithm from
the cases `v ≠ 0`. -/

omit [DecidableEq G] in
/-- Nonvanishing of the five-term data, used by `fiveTerm_ratio` and `ofFiveTerm`. -/
private theorem fiveTerm_E_ne_zero (M : MetricGroup G k) {E Fm : G → k}
    (hrefl : ∀ x, E x * Fm (-x) = (M.gaussian x)⁻¹) (x : G) : E x ≠ 0 := by
  intro h
  have hr := hrefl x
  rw [h, zero_mul] at hr
  exact (inv_ne_zero (M.gaussian_ne_zero x)) hr.symm

omit [DecidableEq G] in
/-- The reciprocal reflection identity used by `fiveTerm_ratio` and `ofFiveTerm`. -/
private theorem fiveTerm_inv_Fm_neg (M : MetricGroup G k) {E Fm : G → k}
    (hrefl : ∀ x, E x * Fm (-x) = (M.gaussian x)⁻¹) (x : G) :
    (Fm (-x))⁻¹ = M.gaussian x * E x := by
  apply inv_eq_of_mul_eq_one_right
  calc
    Fm (-x) * (M.gaussian x * E x) = M.gaussian x * (E x * Fm (-x)) := by ring
    _ = 1 := by rw [hrefl, mul_inv_cancel₀ (M.gaussian_ne_zero x)]

/-- The quotient in the zero-right five-term relation is one away from zero. -/
private theorem fiveTerm_ratio (M : MetricGroup G k) {E Fm : G → k}
    (hrefl : ∀ x, E x * Fm (-x) = (M.gaussian x)⁻¹)
    (hFm : ∀ x, x ≠ 0 → Fm x = E x) (x : G) :
    E x / Fm x = if x = 0 then E 0 ^ 2 else 1 := by
  by_cases hx : x = 0
  · subst x
    simp only [ite_true]
    have hi := fiveTerm_inv_Fm_neg M hrefl (0 : G)
    simp only [neg_zero, M.gaussian_zero, one_mul] at hi
    rw [div_eq_mul_inv, hi]
    ring
  · rw [ite_eq_right hx, hFm x hx, div_self (fiveTerm_E_ne_zero M hrefl x)]

omit [DecidableEq G] in
/-- The case `v = 0` of the finite five-term relation
[RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, (7), `eq:Fgpm.5term`]:
`(1/√N) ∑_x ⟨x; u⟩E(x)/F⁻(x) = E(u)/(F⁻(u)F⁻(0))` for `u ≠ 0`, from reflection
`E(x)F⁻(-x) = ⟨x⟩⁻¹`, `F⁻ = E` off zero, `E(0)² = √N E(0) + 1`, and orthogonality. -/
theorem MetricGroup.fiveTerm_zero_right (M : MetricGroup G k) {E Fm : G → k}
    (hrefl : ∀ x, E x * Fm (-x) = (M.gaussian x)⁻¹) (hFm : ∀ x, x ≠ 0 → Fm x = E x)
    (hzero : E 0 ^ 2 = M.sqrtCard * E 0 + 1) {u : G} (hu : u ≠ 0) :
    M.sqrtCard⁻¹ * ∑ x, M.bichar x u * (E x / Fm x) = E u / (Fm u * Fm 0) := by
  classical
  have hsum : (∑ x, M.bichar x u * (E x / Fm x)) = E 0 ^ 2 - 1 := by
    calc
      _ = ∑ x : G, (M.bichar x u + if x = 0 then E 0 ^ 2 - 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [fiveTerm_ratio M hrefl hFm x]
        by_cases hx : x = 0
        · subst x
          simp [M.bichar_zero_left]
        · simp [hx]
      _ = (∑ x : G, M.bichar x u) + (E 0 ^ 2 - 1) := by
        rw [Finset.sum_add_distrib]
        simp
      _ = _ := by
        have hchar := M.sum_bichar u
        rw [ite_eq_right hu] at hchar
        have hcomm : (∑ x : G, M.bichar x u) = ∑ x : G, M.bichar u x := by
          apply Finset.sum_congr rfl
          intro x _
          exact M.bichar_comm x u
        rw [hcomm, hchar]
        simp
  have hi := fiveTerm_inv_Fm_neg M hrefl (0 : G)
  simp only [neg_zero, M.gaussian_zero, one_mul] at hi
  calc
    _ = E 0 := by
      rw [hsum, hzero]
      field_simp [M.sqrtCard_ne_zero]
      ring
    _ = E u / (Fm u * Fm 0) := by
      rw [hFm u hu, div_mul_eq_div_mul_one_div,
        div_self (fiveTerm_E_ne_zero M hrefl u), one_mul]
      simpa only [one_div] using hi.symm

/-- The reflection field of `FiniteQuantumDilog.ofFiveTerm`. -/
private theorem fiveTerm_reflection (M : MetricGroup G k) {E Fm : G → k}
    (hrefl : ∀ x, E x * Fm (-x) = (M.gaussian x)⁻¹)
    (hFm : ∀ x, x ≠ 0 → Fm x = E x)
    (hzero : E 0 ^ 2 = M.sqrtCard * E 0 + 1) (x : G) :
    E x * E (-x) = (M.gaussian x)⁻¹ +
      M.sqrtCard * E 0 * (if x = 0 then 1 else 0) := by
  by_cases hx : x = 0
  · subst x
    simpa [M.gaussian_zero, pow_two, add_comm] using hzero
  · have hneg : -x ≠ 0 := neg_ne_zero.mpr hx
    simpa [hx, hFm (-x) hneg] using hrefl x

omit [DecidableEq G] in
/-- The summand of the `product` field of `FiniteQuantumDilog.ofFiveTerm` after reflection. -/
private theorem fiveTerm_product_summand (M : MetricGroup G k) {E Fm : G → k}
    (hrefl : ∀ x, E x * Fm (-x) = (M.gaussian x)⁻¹)
    (x y t : G) :
    M.bichar t (x + y) * (E t / Fm (t + -y)) =
      M.gaussian y * (E t * M.gaussian t * E (y - t) * M.bichar t x) := by
  have ht : t + -y = -(y - t) := by abel
  have hg : M.gaussian (y - t) =
      M.gaussian y * M.gaussian t * (M.bichar t y)⁻¹ := by
    rw [show y - t = y + -t by abel, M.gaussian_add y (-t),
      M.gaussian_neg t, M.bichar_neg_right y t, M.bichar_comm y t]
  rw [ht, div_eq_mul_inv, fiveTerm_inv_Fm_neg M hrefl (y - t), hg,
    M.bichar_add_right t x y]
  field_simp [M.bichar_ne_zero t y]

omit [DecidableEq G] in
/-- The quotient of the `product` field of `FiniteQuantumDilog.ofFiveTerm` after reflection. -/
private theorem fiveTerm_product_quotient (M : MetricGroup G k) {E Fm : G → k}
    (hrefl : ∀ x, E x * Fm (-x) = (M.gaussian x)⁻¹)
    (x y : G) :
    E x / (Fm (x + y) * Fm (-y)) =
      M.gaussian y * (M.gaussian (x + y) * E (-x - y) * E x * E y) := by
  have hsum : (Fm (x + y))⁻¹ = M.gaussian (x + y) * E (-x - y) := by
    have h := fiveTerm_inv_Fm_neg M hrefl (-(x + y))
    simp only [neg_neg, M.gaussian_neg] at h
    convert h using 1
    abel_nf
  have hy := fiveTerm_inv_Fm_neg M hrefl y
  rw [div_eq_mul_inv, mul_inv_rev, hsum, hy]
  ring

omit [DecidableEq G] in
/-- The five-term relation for every pair except `(0, 0)`, used by `ofFiveTerm`. -/
private theorem fiveTerm_nonzero_pair (M : MetricGroup G k) {E Fm : G → k}
    (hrefl : ∀ x, E x * Fm (-x) = (M.gaussian x)⁻¹)
    (hFm : ∀ x, x ≠ 0 → Fm x = E x)
    (hzero : E 0 ^ 2 = M.sqrtCard * E 0 + 1)
    (hfive : ∀ u v, v ≠ 0 →
      M.sqrtCard⁻¹ * ∑ x, M.bichar x u * (E x / Fm (x + v)) = E (u + v) / (Fm u * Fm v))
    {u v : G} (hpair : (u, v) ≠ (0, 0)) :
    M.sqrtCard⁻¹ * ∑ x, M.bichar x u * (E x / Fm (x + v)) =
      E (u + v) / (Fm u * Fm v) := by
  by_cases hv : v = 0
  · subst v
    have hu : u ≠ 0 := by
      intro h
      exact hpair (by simp [h])
    simpa using M.fiveTerm_zero_right hrefl hFm hzero hu
  · exact hfive u v hv

omit [DecidableEq G] in
/-- Away from `(0, 0)`, the `product` field of `FiniteQuantumDilog.ofFiveTerm` is the reflected
five-term relation. -/
private theorem fiveTerm_product_nonzero (M : MetricGroup G k) {E Fm : G → k}
    (hrefl : ∀ x, E x * Fm (-x) = (M.gaussian x)⁻¹)
    (hFm : ∀ x, x ≠ 0 → Fm x = E x)
    (hzero : E 0 ^ 2 = M.sqrtCard * E 0 + 1)
    (hfive : ∀ u v, v ≠ 0 →
      M.sqrtCard⁻¹ * ∑ x, M.bichar x u * (E x / Fm (x + v)) = E (u + v) / (Fm u * Fm v))
    {x y : G} (hpair : (x, y) ≠ (0, 0)) :
    M.sqrtCard⁻¹ * ∑ t, E t * M.gaussian t * E (x - t) * M.bichar t y =
      M.gaussian (x + y) * E (-x - y) * E x * E y := by
  have hpair' : (x + y, -x) ≠ (0, 0) := by
    intro h
    have hx : x = 0 := neg_eq_zero.mp (congrArg Prod.snd h)
    have hy : y = 0 := by simpa [hx] using congrArg Prod.fst h
    exact hpair (by simp [hx, hy])
  have h := fiveTerm_nonzero_pair M hrefl hFm hzero hfive hpair'
  have hsum : (∑ t, M.bichar t (x + y) * (E t / Fm (t + -x))) =
      M.gaussian x * ∑ t, E t * M.gaussian t * E (x - t) * M.bichar t y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun t _ => by
      simpa only [add_comm y x] using fiveTerm_product_summand M hrefl y x t)
  have hq : E y / (Fm (x + y) * Fm (-x)) =
      M.gaussian x * (M.gaussian (x + y) * E (-x - y) * E x * E y) := by
    calc
      _ = E y / (Fm (y + x) * Fm (-x)) := by rw [add_comm x y]
      _ = M.gaussian x * (M.gaussian (y + x) * E (-y - x) * E y * E x) :=
        fiveTerm_product_quotient M hrefl y x
      _ = _ := by
        rw [add_comm y x, show -y - x = -x - y by abel]
        ring
  rw [show x + y + -x = y by abel, hsum, hq] at h
  apply mul_left_cancel₀ (M.gaussian_ne_zero x)
  calc
    M.gaussian x * (M.sqrtCard⁻¹ *
        ∑ t, E t * M.gaussian t * E (x - t) * M.bichar t y) =
      M.sqrtCard⁻¹ * (M.gaussian x *
        ∑ t, E t * M.gaussian t * E (x - t) * M.bichar t y) := by ring
    _ = _ := h

omit [DecidableEq G] in
/-- At `(0, 0)`, the `product` field of `FiniteQuantumDilog.ofFiveTerm` follows from reflection
and the zero value. -/
private theorem fiveTerm_product_zero (M : MetricGroup G k) {E Fm : G → k}
    (hrefl : ∀ x, E x * Fm (-x) = (M.gaussian x)⁻¹)
    (hFm : ∀ x, x ≠ 0 → Fm x = E x)
    (hzero : E 0 ^ 2 = M.sqrtCard * E 0 + 1) :
    M.sqrtCard⁻¹ * ∑ t, E t * M.gaussian t * E (-t) * M.bichar t 0 =
      E 0 ^ 3 - (Fintype.card G : k) * E 0 := by
  classical
  have hsum : (∑ t, E t * M.gaussian t * E (-t) * M.bichar t 0) =
      (Fintype.card G : k) + M.sqrtCard * E 0 := by
    simp only [M.bichar_zero_right, mul_one]
    exact reflection_sum M E (fiveTerm_reflection M hrefl hFm hzero)
  have hright : E 0 ^ 3 - (Fintype.card G : k) * E 0 = E 0 + M.sqrtCard := by
    rw [← M.sqrtCard_sq]
    calc
      E 0 ^ 3 - M.sqrtCard ^ 2 * E 0 =
          (E 0 + M.sqrtCard) * (E 0 ^ 2 - M.sqrtCard * E 0 - 1) +
            E 0 + M.sqrtCard := by ring
      _ = _ := by rw [hzero]; ring
  rw [hsum, hright, ← M.sqrtCard_sq]
  field_simp [M.sqrtCard_ne_zero]
  ring

/-- **A finite quantum dilogarithm from the finite five-term relation**: `E` with
`E(x)F⁻(-x) = ⟨x⟩⁻¹`, `F⁻ = E` off zero, `E(0)² = √N E(0) + 1`, and
`(1/√N) ∑_x ⟨x; u⟩E(x)/F⁻(x + v) = E(u + v)/(F⁻(u)F⁻(v))` for `v ≠ 0`
([RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, (4), (5), (7)]) satisfies the
product form (36), by the derivation of [RW26, Radchenko, Wheeler (2026), Section 4.2]. -/
def FiniteQuantumDilog.ofFiveTerm (M : MetricGroup G k) (E Fm : G → k)
    (hrefl : ∀ x, E x * Fm (-x) = (M.gaussian x)⁻¹) (hFm : ∀ x, x ≠ 0 → Fm x = E x)
    (hzero : E 0 ^ 2 = M.sqrtCard * E 0 + 1)
    (hfive : ∀ u v, v ≠ 0 →
      M.sqrtCard⁻¹ * ∑ x, M.bichar x u * (E x / Fm (x + v)) = E (u + v) / (Fm u * Fm v)) :
    FiniteQuantumDilog M where
  toFun := E
  reflection := fiveTerm_reflection M hrefl hFm hzero
  product := by
    intro x y
    by_cases hpair : (x, y) = (0, 0)
    · have hx : x = 0 := congrArg Prod.fst hpair
      have hy : y = 0 := congrArg Prod.snd hpair
      subst x
      subst y
      simpa only [zero_add, zero_sub, neg_zero, M.gaussian_zero, one_mul,
        ite_true, mul_one, pow_three'] using fiveTerm_product_zero M hrefl hFm hzero
    · have hdelta : (if x = 0 then (1 : k) else 0) *
          (if y = 0 then 1 else 0) = 0 := by
        by_cases hx : x = 0
        · have hy : y ≠ 0 := by
            intro hy
            exact hpair (by simp [hx, hy])
          simp [hx, hy]
        · simp [hx]
      simpa only [hdelta, mul_zero, sub_zero] using
        fiveTerm_product_nonzero M hrefl hFm hzero hfive hpair

end SIC
