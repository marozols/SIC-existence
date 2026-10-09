/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.QPochhammer.Infinite
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The q-binomial theorem

The convergent q-binomial series and its expression as a quotient of infinite products.

This module proves [RW26, Radchenko, Wheeler (2026), equation (58),
`eq:q-binomial-series`], the summation used in Appendix A.2's residue calculation.
The proof follows Heine's functional equation as presented in George Gasper,
*Lecture notes for an introductory minicourse on q-series* (1995), Section 1.2,
equations (1.2.12)–(1.2.13), arXiv:math/9509223v1,
[doi:10.48550/arXiv.math/9509223](https://doi.org/10.48550/arXiv.math/9509223).

## The argument

The coefficient products converge, and their denominators have nonzero limit for
`‖q‖ < 1`. The coefficients are therefore bounded, which gives absolute convergence
of the series for `‖x‖ < 1`. Their recurrence gives
`(1-x) f(a,x) = (1-ax) f(a,qx)`. Iterating and taking `qⁿx → 0` identifies the
sum with `(ax;q)∞/(x;q)∞`. No restriction on `a` is imposed: a vanishing numerator
factor simply terminates the series. The exponential-variable corollary connects
this standard form to the project's finite and infinite symbols. Appendix A.2 also
uses backward finite factors based at `y-nτ`. Reversing their order and applying
`(1-e(y-u))/(1-e(-u)) = e(y)(1-e(u-y))/(1-e(u))` at `u = kτ`
changes the coefficient to `e(y)ⁿ ϖₙ(τ-y,τ)/ϖₙ(τ,τ)`. The forward theorem at
`(τ-y,y+z,τ)` then sums the backward series.
-/

noncomputable section

open Complex Real

namespace SIC

/-! ### Summing the q-binomial series

Heine's recurrence and continuity at zero determine the sum on the open unit disk.
-/

/-- The finite product `(b;q)ₙ` used in `hasSum_qBinomial`. -/
private def qBinomialProd (b q : ℂ) (n : ℕ) : ℂ :=
  ∏ j ∈ Finset.range n, (1 - b * q ^ j)

/-- The coefficients `(a;q)ₙ/(q;q)ₙ` of `hasSum_qBinomial`. -/
private def qBinomialCoeff (a q : ℂ) (n : ℕ) : ℂ :=
  qBinomialProd a q n / qBinomialProd q q n

/-- The series in `hasSum_qBinomial`, evaluated by `tsum`. -/
private def qBinomialSeries (a q x : ℂ) : ℂ :=
  ∑' n : ℕ, qBinomialCoeff a q n * x ^ n

/-- The finite products for `hasSum_qBinomial` converge when `‖q‖ < 1`. -/
private lemma qBinomialProd_tendsto (b q : ℂ) (hq : ‖q‖ < 1) :
    Filter.Tendsto (qBinomialProd b q) Filter.atTop
      (nhds (∏' j : ℕ, (1 - b * q ^ j))) := by
  have hs : Summable (fun j : ℕ => -(b * q ^ j)) :=
    ((summable_geometric_of_norm_lt_one hq).mul_left b).neg
  have hm : Multipliable (fun j : ℕ => 1 - b * q ^ j) := by
    simpa only [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable hs
  change Filter.Tendsto (fun n => ∏ i ∈ Finset.range n, (1 - b * q ^ i))
    Filter.atTop (nhds (∏' i : ℕ, (1 - b * q ^ i)))
  exact hm.tendsto_prod_tprod_nat

/-- The factor `1-bqʲ` stays nonzero if `‖b‖, ‖q‖ < 1`, as needed by
`hasSum_qBinomial`. -/
private lemma qBinomial_factor_ne_zero (b q : ℂ) (hq : ‖q‖ < 1)
    (hb : ‖b‖ < 1) (j : ℕ) : 1 - b * q ^ j ≠ 0 := by
  have hqpow : ‖q‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) hq.le
  have hsmall : ‖b * q ^ j‖ < 1 := by
    calc
      ‖b * q ^ j‖ = ‖b‖ * ‖q‖ ^ j := by rw [norm_mul, norm_pow]
      _ ≤ ‖b‖ := by nlinarith [norm_nonneg b]
      _ < 1 := hb
  intro h
  have heq : b * q ^ j = 1 := (sub_eq_zero.mp h).symm
  rw [heq, norm_one] at hsmall
  exact (lt_irrefl (1 : ℝ)) hsmall

/-- The infinite denominator `(b;q)∞` of `hasSum_qBinomial` is nonzero
for `‖b‖,‖q‖ < 1`. -/
private lemma qBinomial_tprod_ne_zero (b q : ℂ) (hq : ‖q‖ < 1)
    (hb : ‖b‖ < 1) : (∏' j : ℕ, (1 - b * q ^ j)) ≠ 0 := by
  have hs : Summable (fun j : ℕ => ‖-(b * q ^ j)‖) := by
    simpa only [norm_neg, norm_mul, norm_pow] using
      ((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_left ‖b‖)
  simpa only [sub_eq_add_neg] using
    tprod_one_add_ne_zero_of_summable
      (f := fun j : ℕ => -(b * q ^ j))
      (fun j => by simpa only [sub_eq_add_neg] using qBinomial_factor_ne_zero b q hq hb j)
      hs

/-- The q-binomial coefficients are bounded for `‖q‖ < 1`, including when
`(a;q)ₙ` terminates. This is the majorant used by `hasSum_qBinomial`. -/
private lemma qBinomialCoeff_bounded (a q : ℂ) (hq : ‖q‖ < 1) :
    ∃ C : ℝ, ∀ n : ℕ, ‖qBinomialCoeff a q n‖ ≤ C := by
  have ht : Filter.Tendsto (qBinomialCoeff a q) Filter.atTop
      (nhds ((∏' j : ℕ, (1 - a * q ^ j)) /
        (∏' j : ℕ, (1 - q * q ^ j)))) := by
    change Filter.Tendsto
      (fun n => qBinomialProd a q n / qBinomialProd q q n) Filter.atTop _
    exact (qBinomialProd_tendsto a q hq).div
      (qBinomialProd_tendsto q q hq) (qBinomial_tprod_ne_zero q q hq hq)
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ ht).exists_norm_le
  exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩

/-- The q-binomial series converges absolutely for `‖x‖ < 1`; used by
`hasSum_qBinomial` and Heine's functional equation. -/
private lemma qBinomialSeries_summable (a q x : ℂ) (hq : ‖q‖ < 1)
    (hx : ‖x‖ < 1) : Summable (fun n : ℕ => qBinomialCoeff a q n * x ^ n) := by
  obtain ⟨C, hC⟩ := qBinomialCoeff_bounded a q hq
  apply ((summable_geometric_of_lt_one (norm_nonneg _) hx).mul_left C).of_norm_bounded
  intro n
  calc
    ‖qBinomialCoeff a q n * x ^ n‖ = ‖qBinomialCoeff a q n‖ * ‖x‖ ^ n :=
      by rw [norm_mul, norm_pow]
    _ ≤ C * ‖x‖ ^ n := mul_le_mul_of_nonneg_right (hC n) (pow_nonneg (norm_nonneg _) _)

/-- Appending the factor at index `n` to `(b;q)ₙ`, for `hasSum_qBinomial`. -/
private lemma qBinomialProd_succ (b q : ℂ) (n : ℕ) :
    qBinomialProd b q (n + 1) = qBinomialProd b q n * (1 - b * q ^ n) := by
  simp [qBinomialProd, Finset.prod_range_succ]

/-- The coefficient recurrence used to derive Heine's equation in
`hasSum_qBinomial`. -/
private lemma qBinomialCoeff_succ (a q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) :
    qBinomialCoeff a q (n + 1) * (1 - q * q ^ n) =
      qBinomialCoeff a q n * (1 - a * q ^ n) := by
  have hf := qBinomial_factor_ne_zero q q hq hq n
  simp only [qBinomialCoeff, qBinomialProd_succ]
  rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hf]
  ring

/-- The shifted series terms agree after the coefficient recurrence; this
termwise identity is summed in `qBinomialSeries_heine`. -/
private lemma qBinomialSeries_heine_term (a q x : ℂ) (hq : ‖q‖ < 1) (n : ℕ) :
    qBinomialCoeff a q (n + 1) * x ^ (n + 1) -
      qBinomialCoeff a q (n + 1) * (q * x) ^ (n + 1) =
    x * (qBinomialCoeff a q n * x ^ n -
      a * (qBinomialCoeff a q n * (q * x) ^ n)) := by
  calc
    _ = (qBinomialCoeff a q (n + 1) * (1 - q * q ^ n)) * x ^ (n + 1) := by
      rw [mul_pow, pow_succ]
      ring
    _ = (qBinomialCoeff a q n * (1 - a * q ^ n)) * x ^ (n + 1) := by
      rw [qBinomialCoeff_succ a q hq n]
    _ = _ := by rw [mul_pow, pow_succ]; ring

/-- Heine's functional equation `(1-x)f(a,x)=(1-ax)f(a,qx)` for the
convergent series used by `hasSum_qBinomial`; see Gasper (1995), (1.2.12). -/
private lemma qBinomialSeries_heine (a q x : ℂ) (hq : ‖q‖ < 1)
    (hx : ‖x‖ < 1) :
    (1 - x) * qBinomialSeries a q x =
      (1 - a * x) * qBinomialSeries a q (q * x) := by
  have hqx : ‖q * x‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg x]
  have hsx := qBinomialSeries_summable a q x hq hx
  have hsqx := qBinomialSeries_summable a q (q * x) hq hqx
  have hshift :
      (∑' n : ℕ, (qBinomialCoeff a q n * x ^ n -
        qBinomialCoeff a q n * (q * x) ^ n)) =
      ∑' n : ℕ, (qBinomialCoeff a q (n + 1) * x ^ (n + 1) -
        qBinomialCoeff a q (n + 1) * (q * x) ^ (n + 1)) := by
    simpa using (hsx.sub hsqx).tsum_eq_zero_add
  have hdiff := hsx.sub (hsqx.mul_left a)
  have hseries : qBinomialSeries a q x - qBinomialSeries a q (q * x) =
      x * (qBinomialSeries a q x - a * qBinomialSeries a q (q * x)) := by
    change (∑' n, qBinomialCoeff a q n * x ^ n) -
      (∑' n, qBinomialCoeff a q n * (q * x) ^ n) =
      x * ((∑' n, qBinomialCoeff a q n * x ^ n) -
        a * (∑' n, qBinomialCoeff a q n * (q * x) ^ n))
    calc
      _ = ∑' n, (qBinomialCoeff a q n * x ^ n -
          qBinomialCoeff a q n * (q * x) ^ n) := (hsx.tsum_sub hsqx).symm
      _ = ∑' n, (qBinomialCoeff a q (n + 1) * x ^ (n + 1) -
          qBinomialCoeff a q (n + 1) * (q * x) ^ (n + 1)) := hshift
      _ = ∑' n, x * (qBinomialCoeff a q n * x ^ n -
          a * (qBinomialCoeff a q n * (q * x) ^ n)) :=
            tsum_congr (qBinomialSeries_heine_term a q x hq)
      _ = _ := by rw [hdiff.tsum_mul_left, hsx.tsum_sub (hsqx.mul_left a),
          hsqx.tsum_mul_left]
  linear_combination hseries

/-- The constant term of the series in `hasSum_qBinomial` is one. -/
private lemma qBinomialSeries_zero (a q : ℂ) (hq : ‖q‖ < 1) :
    qBinomialSeries a q 0 = 1 := by
  have hs := qBinomialSeries_summable a q 0 hq (by simp)
  unfold qBinomialSeries
  rw [hs.tsum_eq_zero_add]
  simp [qBinomialCoeff, qBinomialProd]

/-- A geometric majorant makes the series in `hasSum_qBinomial`
continuous at zero, with limit one. -/
private lemma qBinomialSeries_tendsto_zero (a q : ℂ) (hq : ‖q‖ < 1) :
    Filter.Tendsto (qBinomialSeries a q) (nhds 0) (nhds 1) := by
  obtain ⟨C, hC⟩ := qBinomialCoeff_bounded a q hq
  have hmajor : Summable (fun n : ℕ => C * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
  have hterm (n : ℕ) : Filter.Tendsto
      (fun y : ℂ => qBinomialCoeff a q n * y ^ n) (nhds 0)
      (nhds (qBinomialCoeff a q n * (0 : ℂ) ^ n)) := by
    exact ((continuous_const.mul (continuous_id.pow n)).tendsto 0)
  have hsmall : ∀ᶠ y : ℂ in nhds 0, ‖y‖ ≤ (1 / 2 : ℝ) := by
    have h := (continuous_norm.tendsto (0 : ℂ)).eventually
      (eventually_lt_nhds (by norm_num : ‖(0 : ℂ)‖ < (1 / 2 : ℝ)))
    exact h.mono (fun y hy => hy.le)
  have hbound : ∀ᶠ y : ℂ in nhds 0, ∀ n : ℕ,
      ‖qBinomialCoeff a q n * y ^ n‖ ≤ C * (1 / 2 : ℝ) ^ n := by
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    filter_upwards [hsmall] with y hy n
    rw [norm_mul, norm_pow]
    exact mul_le_mul (hC n) (pow_le_pow_left₀ (norm_nonneg _) hy n)
      (pow_nonneg (by norm_num) n) hC0
  have ht := tendsto_tsum_of_dominated_convergence hmajor hterm hbound
  change Filter.Tendsto (qBinomialSeries a q) (nhds (0 : ℂ))
    (nhds (qBinomialSeries a q 0)) at ht
  rwa [qBinomialSeries_zero a q hq] at ht

/-- Iterating Heine's equation gives the finite-product identity (1.2.13)
of Gasper (1995), the decisive step in `hasSum_qBinomial`. -/
private lemma qBinomialSeries_finite_identity (a q x : ℂ) (hq : ‖q‖ < 1)
    (hx : ‖x‖ < 1) (n : ℕ) :
    qBinomialProd x q n * qBinomialSeries a q x =
      qBinomialProd (a * x) q n * qBinomialSeries a q (q ^ n * x) := by
  induction n with
  | zero => simp [qBinomialProd]
  | succ n ih =>
    have hpow : ‖q‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hq.le
    have hqx : ‖q ^ n * x‖ < 1 := by
      rw [norm_mul, norm_pow]
      nlinarith [norm_nonneg x]
    have hheine := qBinomialSeries_heine a q (q ^ n * x) hq hqx
    have harg : q * (q ^ n * x) = q ^ (n + 1) * x := by rw [pow_succ]; ring
    rw [harg] at hheine
    calc
      qBinomialProd x q (n + 1) * qBinomialSeries a q x =
          (qBinomialProd x q n * qBinomialSeries a q x) * (1 - x * q ^ n) := by
            rw [qBinomialProd_succ]; ring
      _ = (qBinomialProd (a * x) q n * qBinomialSeries a q (q ^ n * x)) *
            (1 - x * q ^ n) := by rw [ih]
      _ = qBinomialProd (a * x) q n *
            ((1 - q ^ n * x) * qBinomialSeries a q (q ^ n * x)) := by ring
      _ = qBinomialProd (a * x) q n *
            ((1 - a * (q ^ n * x)) * qBinomialSeries a q (q ^ (n + 1) * x)) := by
              rw [hheine]
      _ = qBinomialProd (a * x) q (n + 1) *
            qBinomialSeries a q (q ^ (n + 1) * x) := by
              rw [qBinomialProd_succ]
              ring

/-- The q-binomial theorem `∑ₙ (a;q)ₙ xⁿ/(q;q)ₙ = (ax;q)∞/(x;q)∞`, with
convergence, for `|q| < 1` and `|x| < 1`.
[RW26, Radchenko, Wheeler (2026), equation (58), `eq:q-binomial-series`]. -/
@[source "RW26, equation (58), p. 28, eq:q-binomial-series"]
theorem hasSum_qBinomial (a q x : ℂ) (hq : ‖q‖ < 1) (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ =>
      (∏ j ∈ Finset.range n, (1 - a * q ^ j)) /
        (∏ j ∈ Finset.range n, (1 - q * q ^ j)) * x ^ n)
      ((∏' j : ℕ, (1 - (a * x) * q ^ j)) /
        (∏' j : ℕ, (1 - x * q ^ j))) := by
  have hpow : Filter.Tendsto (fun n : ℕ => q ^ n * x) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).mul_const x
  have hseries : Filter.Tendsto
      (fun n : ℕ => qBinomialSeries a q (q ^ n * x)) Filter.atTop (nhds 1) :=
    (qBinomialSeries_tendsto_zero a q hq).comp hpow
  have hleft := (qBinomialProd_tendsto x q hq).mul_const (qBinomialSeries a q x)
  have hright := (qBinomialProd_tendsto (a * x) q hq).mul hseries
  have hlim : (∏' j : ℕ, (1 - x * q ^ j)) * qBinomialSeries a q x =
      (∏' j : ℕ, (1 - (a * x) * q ^ j)) * 1 := by
    apply tendsto_nhds_unique ?_ hright
    exact hleft.congr' (Filter.Eventually.of_forall fun n =>
      qBinomialSeries_finite_identity a q x hq hx n)
  have hvalue : qBinomialSeries a q x =
      (∏' j : ℕ, (1 - (a * x) * q ^ j)) /
        (∏' j : ℕ, (1 - x * q ^ j)) := by
    apply (eq_div_iff (qBinomial_tprod_ne_zero x q hq hx)).mpr
    simpa [mul_comm] using hlim
  rw [← hvalue]
  exact qBinomialSeries_summable a q x hq hx |>.hasSum

/-- The finite additive symbol becomes `(e(w);e(τ))ₙ` in
`hasSum_qPochhammerFin_div`. -/
private lemma qBinomial_exp_finite (n : ℕ) (w τ : ℂ) :
    qPochhammerFin (n : ℤ) w τ =
      qBinomialProd (Complex.exp (2 * π * I * w))
        (Complex.exp (2 * π * I * τ)) n := by
  rw [qPochhammerFin_natCast]
  unfold qBinomialProd
  apply Finset.prod_congr rfl
  intro j _
  rw [qPochhammer_exp_add_nat_mul]

/-- The infinite additive symbol becomes `(e(w);e(τ))∞` in
`hasSum_qPochhammerFin_div`. -/
private lemma qBinomial_exp_infinite (w τ : ℂ) :
    qPochhammer w τ =
      ∏' j : ℕ, (1 - Complex.exp (2 * π * I * w) *
        Complex.exp (2 * π * I * τ) ^ j) := by
  unfold qPochhammer
  exact tprod_congr (fun j => by rw [qPochhammer_exp_add_nat_mul])

/-- The exponential-variable form of `hasSum_qBinomial`:
`∑ₙ ϖₙ(a,τ)e(z)ⁿ/ϖₙ(τ,τ) = ϖ(a+z,τ)/ϖ(z,τ)` for `Im τ, Im z > 0`.
This bridges the standard q-binomial theorem to the symbols used in the modular
five-term integral of [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem hasSum_qPochhammerFin_div (a z τ : ℂ) (hτ : 0 < τ.im) (hz : 0 < z.im) :
    HasSum (fun n : ℕ => qPochhammerFin (n : ℤ) a τ /
      qPochhammerFin (n : ℤ) τ τ * Complex.exp (2 * π * I * z) ^ n)
      (qPochhammer (a + z) τ / qPochhammer z τ) := by
  have heaz : Complex.exp (2 * π * I * (a + z)) =
      Complex.exp (2 * π * I * a) * Complex.exp (2 * π * I * z) := by
    rw [show (2 : ℂ) * π * I * (a + z) =
      2 * π * I * a + 2 * π * I * z by ring, Complex.exp_add]
  have h := hasSum_qBinomial
    (Complex.exp (2 * π * I * a)) (Complex.exp (2 * π * I * τ))
    (Complex.exp (2 * π * I * z))
    (qPochhammer_exp_period_norm_lt_one τ hτ)
    (qPochhammer_exp_period_norm_lt_one z hz)
  have hprod :
      (∏' j : ℕ, (1 - (Complex.exp (2 * π * I * a) *
        Complex.exp (2 * π * I * z)) * Complex.exp (2 * π * I * τ) ^ j)) /
        (∏' j : ℕ, (1 - Complex.exp (2 * π * I * z) *
          Complex.exp (2 * π * I * τ) ^ j)) =
      qPochhammer (a + z) τ / qPochhammer z τ := by
    rw [qBinomial_exp_infinite (a + z) τ, qBinomial_exp_infinite z τ, heaz]
  rw [hprod] at h
  exact h.congr_fun (fun n => by
    rw [qBinomial_exp_finite n a τ, qBinomial_exp_finite n τ τ]
    rfl)

/-! ### The backward-factor q-binomial series

The finite base inversion used in
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`] converts each
factor at a negative multiple of `τ` into a forward factor and one copy of `e(y)`.
The ordinary convergent q-binomial theorem then gives the backward series.
-/

/-- The algebraic factor inversion
`(1-A/B)/(1-B⁻¹) = A(1-B/A)/(1-B)` used by
`qBinomial_backward_factor_exp`. -/
private lemma qBinomial_backward_div_algebra (A B : ℂ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hB1 : B ≠ 1) :
    (1 - A / B) / (1 - B⁻¹) = A * ((1 - B / A) / (1 - B)) := by
  field_simp
  ring

/-- The exponential form of the one-factor base inversion at `u`, where `Im u > 0`;
used by `qBinomial_backward_factor_div`. -/
private lemma qBinomial_backward_factor_exp (y u : ℂ) (hu : 0 < u.im) :
    (1 - Complex.exp (2 * π * I * (y - u))) /
      (1 - Complex.exp (2 * π * I * (-u))) =
    Complex.exp (2 * π * I * y) *
      ((1 - Complex.exp (2 * π * I * (u - y))) /
        (1 - Complex.exp (2 * π * I * u))) := by
  let A : ℂ := Complex.exp (2 * π * I * y)
  let B : ℂ := Complex.exp (2 * π * I * u)
  have hA : A ≠ 0 := Complex.exp_ne_zero _
  have hB : B ≠ 0 := Complex.exp_ne_zero _
  have hBsmall : ‖B‖ < 1 := qPochhammer_exp_period_norm_lt_one u hu
  have hB1 : B ≠ 1 := by
    intro h
    rw [h, norm_one] at hBsmall
    exact (lt_irrefl (1 : ℝ)) hBsmall
  rw [show (2 : ℂ) * π * I * (y - u) =
      2 * π * I * y - 2 * π * I * u by ring,
    show (2 : ℂ) * π * I * (-u) = -(2 * π * I * u) by ring,
    show (2 : ℂ) * π * I * (u - y) =
      2 * π * I * u - 2 * π * I * y by ring]
  simp only [Complex.exp_sub, Complex.exp_neg]
  exact qBinomial_backward_div_algebra A B hA hB hB1

/-- The one-factor inversion at `u = (k+1)τ`; used by
`qBinomial_backward_coefficient`. -/
private lemma qBinomial_backward_factor_div (y τ : ℂ) (hτ : 0 < τ.im) (k : ℕ) :
    (1 - Complex.exp (2 * π * I * (y - ((k + 1 : ℕ) : ℂ) * τ))) /
      (1 - Complex.exp (2 * π * I * (-((k + 1 : ℕ) : ℂ) * τ))) =
    Complex.exp (2 * π * I * y) *
      ((1 - Complex.exp (2 * π * I * (τ - y + (k : ℂ) * τ))) /
        (1 - Complex.exp (2 * π * I * (τ + (k : ℂ) * τ)))) := by
  have him : 0 < (τ + (k : ℂ) * τ).im := by
    simp only [Complex.add_im, Complex.mul_im]
    simp
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have harg : (((k + 1 : ℕ) : ℂ) * τ) = τ + (k : ℂ) * τ := by
    push_cast
    ring
  have harg1 : y - ((k + 1 : ℕ) : ℂ) * τ = y - (τ + (k : ℂ) * τ) := by
    rw [harg]
  have harg2 : -((k + 1 : ℕ) : ℂ) * τ = -(τ + (k : ℂ) * τ) := by
    rw [neg_mul, harg]
  have harg3 : τ - y + (k : ℂ) * τ = (τ + (k : ℂ) * τ) - y := by ring
  rw [harg1, harg2, harg3]
  exact qBinomial_backward_factor_exp y (τ + (k : ℂ) * τ) him

/-- Prepending the factor at `w-(n+1)τ` to `ϖₙ(w-nτ,τ)`; used by
`qBinomial_backward_coefficient`. -/
private lemma qPochhammerFin_backward_succ (n : ℕ) (w τ : ℂ) :
    qPochhammerFin ((n + 1 : ℕ) : ℤ) (w - ((n + 1 : ℕ) : ℂ) * τ) τ =
      (1 - Complex.exp (2 * π * I * (w - ((n + 1 : ℕ) : ℂ) * τ))) *
        qPochhammerFin (n : ℤ) (w - (n : ℂ) * τ) τ := by
  rw [qPochhammerFin_natCast, qPochhammerFin_natCast, Finset.prod_range_succ']
  have hprod :
      (∏ j ∈ Finset.range n, (1 - Complex.exp
        (2 * π * I * (w - ((n + 1 : ℕ) : ℂ) * τ + (j + 1 : ℕ) * τ)))) =
      ∏ j ∈ Finset.range n, (1 - Complex.exp
        (2 * π * I * (w - (n : ℂ) * τ + (j : ℂ) * τ))) := by
    apply Finset.prod_congr rfl
    intro j _
    congr 1
    congr 1
    push_cast
    ring
  rw [hprod]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  exact mul_comm _ _

/-- Finite base inversion gives
`ϖₙ(y-nτ,τ)/ϖₙ(-nτ,τ) = e(y)ⁿ ϖₙ(τ-y,τ)/ϖₙ(τ,τ)`;
the coefficient identity used by `hasSum_qPochhammerFin_backward_div`.
See [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
private lemma qBinomial_backward_coefficient (y τ : ℂ) (hτ : 0 < τ.im) (n : ℕ) :
    qPochhammerFin (n : ℤ) (y - (n : ℂ) * τ) τ /
      qPochhammerFin (n : ℤ) (-(n : ℂ) * τ) τ =
    Complex.exp (2 * π * I * y) ^ n *
      (qPochhammerFin (n : ℤ) (τ - y) τ / qPochhammerFin (n : ℤ) τ τ) := by
  induction n with
  | zero => simp [qPochhammerFin]
  | succ n ih =>
    have hden :
        qPochhammerFin ((n + 1 : ℕ) : ℤ) (-((n + 1 : ℕ) : ℂ) * τ) τ =
          (1 - Complex.exp (2 * π * I * (-((n + 1 : ℕ) : ℂ) * τ))) *
            qPochhammerFin (n : ℤ) (-(n : ℂ) * τ) τ := by
      simpa only [zero_sub, neg_mul] using (qPochhammerFin_backward_succ n 0 τ)
    have hforward (w : ℂ) :
        qPochhammerFin ((n + 1 : ℕ) : ℤ) w τ =
          qPochhammerFin (n : ℤ) w τ *
            (1 - Complex.exp (2 * π * I * (w + (n : ℂ) * τ))) := by
      simpa only [Nat.cast_add, Nat.cast_one, Int.cast_natCast] using
        (qPochhammerFin_add_one (n : ℤ) w τ (by omega))
    rw [qPochhammerFin_backward_succ n y τ, hden,
      hforward (τ - y), hforward τ, pow_succ]
    calc
      _ = (qPochhammerFin (n : ℤ) (y - (n : ℂ) * τ) τ /
            qPochhammerFin (n : ℤ) (-(n : ℂ) * τ) τ) *
          ((1 - Complex.exp (2 * π * I * (y - ((n + 1 : ℕ) : ℂ) * τ))) /
            (1 - Complex.exp (2 * π * I * (-((n + 1 : ℕ) : ℂ) * τ)))) := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
      _ = _ := by
          rw [ih, qBinomial_backward_factor_div y τ hτ n]
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring

/-- The backward-factor q-binomial sum
`∑ₙ ϖₙ(y-nτ,τ)e(z)ⁿ/ϖₙ(-nτ,τ) = ϖ(τ+z,τ)/ϖ(y+z,τ)`
for `Im τ > 0` and `Im(y+z) > 0`. This is the inverse-base series in
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`], obtained from
`hasSum_qPochhammerFin_div` by finite base inversion. -/
theorem hasSum_qPochhammerFin_backward_div (y z τ : ℂ) (hτ : 0 < τ.im)
    (hyz : 0 < (y + z).im) :
    HasSum (fun n : ℕ => qPochhammerFin (n : ℤ) (y - (n : ℂ) * τ) τ /
      qPochhammerFin (n : ℤ) (-(n : ℂ) * τ) τ * Complex.exp (2 * π * I * z) ^ n)
      (qPochhammer (τ + z) τ / qPochhammer (y + z) τ) := by
  have hsum := hasSum_qPochhammerFin_div (τ - y) (y + z) τ hτ hyz
  have harg : (τ - y) + (y + z) = τ + z := by ring
  rw [harg] at hsum
  have heyz : Complex.exp (2 * π * I * (y + z)) =
      Complex.exp (2 * π * I * y) * Complex.exp (2 * π * I * z) := by
    rw [show (2 : ℂ) * π * I * (y + z) =
      2 * π * I * y + 2 * π * I * z by ring, Complex.exp_add]
  exact hsum.congr_fun (fun n => by
    rw [qBinomial_backward_coefficient y τ hτ n, heyz, mul_pow]
    ring)

end SIC
