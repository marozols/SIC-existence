/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.ElementForms
import Mathlib.Order.OrderIsoNat

/-!
# Reaching a reduced quadratic irrational

The eventual-reducedness conclusion of Katok's Theorem 1.3: the Hirzebruch–Jung expansion of a real
quadratic irrational `x` with conjugate `y` reaches `0 < y_N < 1 < x_N`, by the growth of `|x_n -
y_n|` inside a unit interval against the integrality of `a·j(x)j(y)`; hence every pair of conjugate
real quadratic irrationals, and every irrational `β ∈ K`, is carried by some `R ∈ SL₂(ℤ)` with `j_R
> 0` to a reduced pair; Möbius images of the two roots of a rational quadratic are the two roots of
another, and a matrix fixing one root fixes the other with `j(x)j(y) = 1`.

This file proves that the Hirzebruch--Jung expansion of a real quadratic irrational `x` with
conjugate `y` eventually reaches a reduced number: for some `N ≥ 1` the conjugate `y_N` lies in
`(0,1)`, so that `0 < y_N < 1 < x_N`. This is the eventual-reducedness step in
the proof of [68, Katok (2003), Theorem 1.3] (eventual periodicity of the minus continued fraction).
It supplies the reduction ingredient in [72, Kopp (2024), Proposition 3.17, `prop:reduced`],
that every class has a reduced representative. Pure periodicity from a reduced start is in
`SICs.Quadratic.ReducedForms`. The reducing matrix `R ∈ SL₂(ℤ)` has `j_R(x) > 0`
(`exists_flt_reduced_of_sq_eq`), and the file adds the two facts a reduction of a fixed-point
datum needs: `R·x`, `R·y` are again the roots of a rational quadratic
(`exists_sq_eq_flt_of_sq_eq`), and a matrix of `SL₂(ℤ)` fixing `x` fixes `y` with
`j(x)j(y) = 1` (`flt_eq_self_of_flt_eq_self_of_sq_eq`,
`fltDenominator_mul_fltDenominator_eq_one_of_sq_eq`).

The setting is a pair of real numbers `x ≠ y`, both roots of `X² - tX + n` with `t, n ∈ ℚ`, and
`x` irrational: the two real values of an element of a real quadratic field
(`map_sq_eq_trace_mul_sub_norm`). The rotated numbers are `x_n = hjPeriod x n`, the conjugates
are the companion sequence `y_n = hjCompanion x y n`, `y_{n+1} = 1/(b_n - y_n)`,
`b_n = ⌈x_n⌉`.

## Mathematical argument

For `n ≥ 1` the rotated number satisfies `x_n > 1`, so `b_n ≥ 2`. If `y_n < b_n - 1` then
`b_n - y_n > 1` and `y_{n+1} = 1/(b_n - y_n) ∈ (0,1)`. If `y_n > b_n` then `y_{n+1} < 0`, and
one more step gives `y_{n+2} = 1/(b_{n+1} - y_{n+1}) ∈ (0, 1/2)`. Since `y_n` is irrational, the
only remaining case is `b_n - 1 < y_n < b_n`, when `y_n` lies in the same unit interval as `x_n`.
In that case both `b_n - x_n` and `b_n - y_n` lie in `(0,1)`, and

$$
x_{n+1} - y_{n+1} = \frac{1}{b_n - x_n} - \frac{1}{b_n - y_n}
= \frac{x_n - y_n}{(b_n - x_n)(b_n - y_n)},
$$

so `|x_{n+1} - y_{n+1}| > |x_n - y_n|`. On the other hand `x_n = A⁻¹·x`, `y_n = A⁻¹·y` for the
cycle matrix `A = A_{0,n}`, so by the difference formula `flt_sub_flt`

$$
x_n - y_n = \frac{x - y}{j(x)\,j(y)},\qquad j(x)j(y) = c^2 n + cd\,t + d^2
$$

with `(c, d)` the bottom row of `A⁻¹`, and `a·j(x)j(y)` is the integer `Q(d, -c)` for the form
`Q = ⟨a, -at, an⟩` of `X² - tX + n` (`BinaryQF.ofTraceNorm`). Hence `|x_n - y_n|` takes values in
the discrete set `{a|x - y|/m : m ∈ ℕ, m ≥ 1}`, and cannot increase strictly forever. So some
`n` falls outside the remaining case, and `y_{n+1}` or `y_{n+2}` lies in `(0,1)`.

This is an alternative proof of Katok's eventual-reducedness conclusion. Katok proves it from
convergence of the continued-fraction convergents and uses coefficient bounds only afterward,
to obtain eventual periodicity. The proof here instead uses growth of the gap and the strictly
decreasing positive integers supplied by `Q(d, -c)`.

## References

- [68, Katok (2003), Theorem 1.3], the eventual-reducedness conclusion in its proof.
- [72, Kopp (2024), Proposition 3.17, `prop:reduced`], which cites it.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The difference `x_n - y_n` along the cycle

`x_n - y_n = (x - y)/(j(x)j(y))` for the Jacobi denominators `j` of `A_{0,n}⁻¹`, and `j(x)j(y)`
is a rational number with denominator dividing `a`, the leading coefficient of the form
`⟨a, -at, an⟩`. -/

/-- **The difference of the rotated number and its conjugate**:
`x_n - y_n = (x - y)/(j_{A⁻¹}(x) j_{A⁻¹}(y))` with `A = A_{0,n}`, from `flt_sub_flt`
(determinant one), `IsHJCompanion.flt_hjCycleMatrix_inv` at the rotated numbers
(`isHJCompanion_hjPeriod`) and `hjCompanion_eq_flt_inv`; the denominators
are nonzero by `fltDenominator_ne_zero_of_irrational`. -/
theorem hjPeriod_sub_hjCompanion {x y : ℝ} (hx : Irrational x) (hy : Irrational y) (n : ℕ) :
    hjPeriod x n - hjCompanion x y n =
      (x - y) /
        (fltDenominator (((hjCycleMatrix x n)⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) x *
          fltDenominator (((hjCycleMatrix x n)⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
            y) := by
  let A := (hjCycleMatrix x n)⁻¹
  let M : Mat(2, ℤ) := (A : SL(2, ℤ))
  have hdet : M.det = 1 := Matrix.SpecialLinearGroup.det_coe A
  have hxden := fltDenominator_ne_zero_of_irrational hx A
  have hyden := fltDenominator_ne_zero_of_irrational hy A
  rw [← (isHJCompanion_hjPeriod hx).flt_hjCycleMatrix_inv n,
    hjPeriod_zero, hjCompanion_eq_flt_inv hy]
  rw [flt_sub_flt M x y hxden hyden, hdet]
  norm_num
  rfl

/-- **The product of the two Jacobi denominators is a value of `X² - tX + n`'s coefficients**:
`(cx + d)(cy + d) = c²·xy + cd·(x + y) + d² = c² n + cd t + d²` when `x + y = t` and `xy = n`. -/
theorem fltDenominator_mul_fltDenominator (M : Mat(2, ℤ)) {x y t n : ℝ}
    (hsum : x + y = t) (hprod : x * y = n) :
    fltDenominator M x * fltDenominator M y =
      (M 1 0 : ℝ) ^ 2 * n + (M 1 0 : ℝ) * (M 1 1 : ℝ) * t + (M 1 1 : ℝ) ^ 2 := by
  unfold fltDenominator
  rw [← hsum, ← hprod]
  ring

/-- **Clearing the denominator of `j(x)j(y)`**: `a·j_M(x)j_M(y) = Q(M₁₁, -M₁₀)` for the form
`Q = ⟨a, -at, an⟩ = BinaryQF.ofTraceNorm t n`, since `Q(d, -c) = ad² + at·cd + an·c²`
(`BinaryQF.eval`, `BinaryQF.b_ofTraceNorm_cast`, `BinaryQF.c_ofTraceNorm_cast`). -/
theorem a_mul_fltDenominator_mul_fltDenominator (M : Mat(2, ℤ))
    {t n : ℚ} {x y : ℝ} (hsum : x + y = t) (hprod : x * y = n) :
    ((BinaryQF.ofTraceNorm t n).a : ℝ) * (fltDenominator M x * fltDenominator M y) =
      ((BinaryQF.ofTraceNorm t n).eval (M 1 1) (-(M 1 0)) : ℝ) := by
  let Q := BinaryQF.ofTraceNorm t n
  have hb : ((Q.b : ℤ) : ℝ) = -((Q.a : ℤ) : ℝ) * (t : ℝ) := by
    exact_mod_cast BinaryQF.b_ofTraceNorm_cast t n
  have hc : ((Q.c : ℤ) : ℝ) = ((Q.a : ℤ) : ℝ) * (n : ℝ) := by
    exact_mod_cast BinaryQF.c_ofTraceNorm_cast t n
  rw [fltDenominator_mul_fltDenominator M hsum hprod]
  change (Q.a : ℝ) * ((M 1 0 : ℝ) ^ 2 * (n : ℝ) +
      (M 1 0 : ℝ) * (M 1 1 : ℝ) * (t : ℝ) + (M 1 1 : ℝ) ^ 2) = _
  rw [BinaryQF.eval]
  push_cast
  rw [hb, hc]
  ring

/-- **The gap `|x_n - y_n|` lies in a discrete set**: `|x_n - y_n|·m = a|x - y|` for a positive
integer `m`, namely `m = |Q(d, -c)|` for the bottom row `(c, d)` of `A_{0,n}⁻¹`
(`hjPeriod_sub_hjCompanion`, `a_mul_fltDenominator_mul_fltDenominator`, Vieta
`BinaryQF.add_eq_and_mul_eq_of_sq_eq`); `m ≠ 0` because `x_n ≠ y_n`. -/
theorem exists_abs_hjPeriod_sub_hjCompanion_mul_eq {x y : ℝ} {t n : ℚ} (hx : x ^ 2 = t * x - n)
    (hy : y ^ 2 = t * y - n) (hxy : x ≠ y) (hirr : Irrational x) (k : ℕ) :
    ∃ m : ℕ, 0 < m ∧ |hjPeriod x k - hjCompanion x y k| * m =
      ((BinaryQF.ofTraceNorm t n).a : ℝ) * |x - y| := by
  let A := (hjCycleMatrix x k)⁻¹
  let M : Mat(2, ℤ) := (A : SL(2, ℤ))
  let Q := BinaryQF.ofTraceNorm t n
  let q := Q.eval (M 1 1) (-(M 1 0))
  obtain ⟨hsum, hprod⟩ := BinaryQF.add_eq_and_mul_eq_of_sq_eq hxy hx hy
  have hyirr : Irrational y := by
    rw [show y = (t : ℝ) - x by linarith, irrational_ratCast_sub_iff]
    exact hirr
  have hdet : M.det = 1 := Matrix.SpecialLinearGroup.det_coe A
  have hD : fltDenominator M x * fltDenominator M y ≠ 0 :=
    mul_ne_zero (fltDenominator_ne_zero_of_irrational hirr A)
      (fltDenominator_ne_zero_of_irrational hyirr A)
  have haq : (Q.a : ℝ) * (fltDenominator M x * fltDenominator M y) = (q : ℝ) :=
    a_mul_fltDenominator_mul_fltDenominator M hsum hprod
  have ha : 0 < (Q.a : ℝ) := by exact_mod_cast BinaryQF.a_ofTraceNorm_pos t n
  have hgap : hjPeriod x k - hjCompanion x y k =
      (x - y) / (fltDenominator M x * fltDenominator M y) := by
    simpa [M, A] using hjPeriod_sub_hjCompanion hirr hyirr k
  have hq : q ≠ 0 := by
    intro hq
    rw [hq, Int.cast_zero] at haq
    rcases mul_eq_zero.mp haq with h | h
    · exact ha.ne' h
    · exact hD h
  refine ⟨q.natAbs, Int.natAbs_pos.mpr hq, ?_⟩
  rw [hgap, Nat.cast_natAbs, Int.cast_abs,
    ← haq, abs_div, abs_mul (Q.a : ℝ), abs_of_pos ha]
  field_simp [abs_ne_zero.mpr hD]
  simp [Q]

/-! ### The case analysis of one step

If `y_n` is not in the unit interval `(b_n - 1, b_n)` of `x_n`, a conjugate in `(0,1)` appears
within two steps; if it is, the gap `|x_n - y_n|` grows. -/

/-- **Leaving the unit interval of `x_n` produces a conjugate in `(0,1)`**: if `y_n < b_n - 1`
then `b_n - y_n > 1` and `y_{n+1} ∈ (0,1)`; if `y_n > b_n` then `y_{n+1} < 0`, and since
`x_{n+1} > 1` gives `b_{n+1} ≥ 2` (`one_lt_hjPeriod_succ`, `two_le_hjLetter`),
`y_{n+2} = 1/(b_{n+1} - y_{n+1}) ∈ (0, 1/2)`. The irrational `y_n` is neither `b_n - 1` nor
`b_n` (`Irrational.ne_int`). -/
theorem hjCompanion_mem_Ioo_of_not_mem_Ioo {x y : ℝ} (hx : Irrational x) (hy : Irrational y)
    {n : ℕ}
    (h : hjCompanion x y n ∉
      Set.Ioo ((hjLetter (hjPeriod x n) : ℝ) - 1) (hjLetter (hjPeriod x n) : ℝ)) :
    hjCompanion x y (n + 1) ∈ Set.Ioo 0 1 ∨ hjCompanion x y (n + 2) ∈ Set.Ioo 0 1 := by
  have hyn := irrational_hjCompanion (β := x) hy n
  have hneUpper : hjCompanion x y n ≠ (hjLetter (hjPeriod x n) : ℝ) :=
    hyn.ne_int _
  have hneLower : hjCompanion x y n ≠ (hjLetter (hjPeriod x n) : ℝ) - 1 := by
    simpa using hyn.ne_int (hjLetter (hjPeriod x n) - 1)
  simp only [Set.mem_Ioo, not_and_or, not_lt] at h
  rcases h with hlow | hupp
  · left
    rw [hjCompanion_succ]
    have hden : 1 < (hjLetter (hjPeriod x n) : ℝ) - hjCompanion x y n := by
      have := lt_of_le_of_ne hlow hneLower
      linarith
    exact ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ hden⟩
  · right
    have hy1neg : hjCompanion x y (n + 1) < 0 := by
      rw [hjCompanion_succ]
      exact inv_neg''.mpr (sub_neg.mpr (lt_of_le_of_ne hupp hneUpper.symm))
    rw [show n + 2 = (n + 1) + 1 by omega, hjCompanion_succ]
    have hb : (2 : ℝ) ≤ hjLetter (hjPeriod x (n + 1)) := by
      exact_mod_cast two_le_hjLetter (one_lt_hjPeriod_succ hx n)
    have hden : 1 < (hjLetter (hjPeriod x (n + 1)) : ℝ) -
        hjCompanion x y (n + 1) := by linarith
    exact ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ hden⟩

/-- **Inside the unit interval of `x_n` the gap grows**: if `b_n - 1 < y_n < b_n` and
`x_n ≠ y_n`, then `|x_n - y_n| < |x_{n+1} - y_{n+1}|`, since
`x_{n+1} - y_{n+1} = (x_n - y_n)/((b_n - x_n)(b_n - y_n))` with both factors in `(0,1)`
(`hjLetter_sub_pos`, `hjLetter_sub_lt_one`). -/
theorem abs_hjPeriod_sub_hjCompanion_lt_succ {x y : ℝ} (hx : Irrational x) {n : ℕ}
    (hne : hjPeriod x n ≠ hjCompanion x y n)
    (h : hjCompanion x y n ∈
      Set.Ioo ((hjLetter (hjPeriod x n) : ℝ) - 1) (hjLetter (hjPeriod x n) : ℝ)) :
    |hjPeriod x n - hjCompanion x y n| < |hjPeriod x (n + 1) - hjCompanion x y (n + 1)| := by
  let a := (hjLetter (hjPeriod x n) : ℝ) - hjPeriod x n
  let c := (hjLetter (hjPeriod x n) : ℝ) - hjCompanion x y n
  have ha : a ∈ Set.Ioo 0 1 := ⟨hjLetter_sub_pos (irrational_hjPeriod hx n),
    hjLetter_sub_lt_one (hjPeriod x n)⟩
  have hc : c ∈ Set.Ioo 0 1 := by exact ⟨by linarith [h.2], by linarith [h.1]⟩
  have hac : 0 < a * c := mul_pos ha.1 hc.1
  have hac1 : a * c < 1 := by
    have : a * c < a * 1 := mul_lt_mul_of_pos_left hc.2 ha.1
    nlinarith [ha.2]
  have heq : a⁻¹ - c⁻¹ =
      (hjPeriod x n - hjCompanion x y n) / (a * c) := by
    field_simp [ha.1.ne', hc.1.ne']
    dsimp [a, c]
    ring
  rw [hjPeriod_succ, hjRotate, hjCompanion_succ]
  change |hjPeriod x n - hjCompanion x y n| < |a⁻¹ - c⁻¹|
  rw [heq, abs_div, abs_of_pos hac]
  rw [lt_div_iff₀ hac]
  nlinarith [abs_pos.mpr (sub_ne_zero.mpr hne)]

/-! ### Eventual reducedness -/

/-- Positive integer multipliers of a fixed positive real constant decrease when their nonnegative
real factors strictly increase. This is the order step used in `exists_hjCompanion_mem_Ioo`. -/
private theorem nat_lt_of_mul_eq_of_lt {a b C : ℝ} {m n : ℕ} (ha : 0 ≤ a) (hab : a < b)
    (hn : 0 < n) (hm : a * m = C) (hne : b * n = C) : n < m := by
  by_contra hnot
  have hmn : m ≤ n := Nat.le_of_not_gt hnot
  have hle : a * (m : ℝ) ≤ a * (n : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hmn) ha
  have hlt : a * (n : ℝ) < b * (n : ℝ) :=
    mul_lt_mul_of_pos_right hab (by exact_mod_cast hn)
  nlinarith

/-- There is no infinite sequence of natural numbers that strictly decreases at every step. -/
private theorem false_of_nat_succ_lt (m : ℕ → ℕ) (hdec : ∀ k, m (k + 1) < m k) : False :=
  not_strictAnti_of_wellFoundedLT m (strictAnti_nat_of_succ_lt hdec)

/-- **The eventual-reducedness conclusion in [68, Katok (2003), Theorem 1.3]**: for a real quadratic
irrational `x` with conjugate `y` (both roots of `X² - tX + n`, `t, n ∈ ℚ`, `x ≠ y`), some
conjugate `y_N` with `N ≥ 1` lies in `(0,1)`. If none did, `hjCompanion_mem_Ioo_of_not_mem_Ioo`
would put every `y_n` in the unit interval of `x_n`, so by
`abs_hjPeriod_sub_hjCompanion_lt_succ` the gaps `|x_n - y_n|` would increase strictly, and
by `exists_abs_hjPeriod_sub_hjCompanion_mul_eq` the positive integers `m_n` with
`|x_n - y_n|·m_n = a|x - y|` would decrease strictly, which is impossible. This alternative
gap-descent argument differs from Katok's proof by convergence of convergents, as explained
in the module docstring. The conclusion is the reduction step behind [72, Kopp (2024),
Proposition 3.17, `prop:reduced`]; Katok's theorem itself asserts eventual periodicity, of which
this is the reduction step. -/
@[source "68, Theorem 1.3, p. 4 (eventual reducedness)"]
theorem exists_hjCompanion_mem_Ioo {x y : ℝ} {t n : ℚ} (hx : x ^ 2 = t * x - n)
    (hy : y ^ 2 = t * y - n) (hxy : x ≠ y) (hirr : Irrational x) :
    ∃ N : ℕ, 0 < N ∧ hjCompanion x y N ∈ Set.Ioo 0 1 := by
  by_contra hnone
  have hyirr : Irrational y := by
    obtain ⟨hsum, _⟩ := BinaryQF.add_eq_and_mul_eq_of_sq_eq hxy hx hy
    rw [show y = (t : ℝ) - x by linarith, irrational_ratCast_sub_iff]
    exact hirr
  choose m hmpos hmeq using fun k =>
    exists_abs_hjPeriod_sub_hjCompanion_mul_eq hx hy hxy hirr k
  have hne (k : ℕ) : hjPeriod x k ≠ hjCompanion x y k := by
    intro heq
    have heq' := hmeq k
    rw [heq, sub_self, abs_zero, zero_mul] at heq'
    have ha : 0 < ((BinaryQF.ofTraceNorm t n).a : ℝ) := by
      exact_mod_cast BinaryQF.a_ofTraceNorm_pos t n
    have hxyabs : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    nlinarith
  have hinterval (k : ℕ) : hjCompanion x y k ∈
      Set.Ioo ((hjLetter (hjPeriod x k) : ℝ) - 1) (hjLetter (hjPeriod x k) : ℝ) := by
    by_contra hk
    rcases hjCompanion_mem_Ioo_of_not_mem_Ioo hirr hyirr hk with h1 | h2
    · exact hnone ⟨k + 1, by omega, h1⟩
    · exact hnone ⟨k + 2, by omega, h2⟩
  have hmdec (k : ℕ) : m (k + 1) < m k := by
    apply nat_lt_of_mul_eq_of_lt (abs_nonneg _)
      (abs_hjPeriod_sub_hjCompanion_lt_succ hirr (hne k) (hinterval k)) (hmpos (k + 1))
      (hmeq k) (hmeq (k + 1))
  exact false_of_nat_succ_lt m hmdec

/-! ### Reduction of a real quadratic irrational

The two roots `x ≠ y` of `X² - tX + n` with `x` irrational, without a field around them. The
matrix `R = A_{0,N}⁻¹` for the `N ≥ 1` of `exists_hjCompanion_mem_Ioo` carries `x` to
`x_N > 1` and `y` to `y_N ∈ (0,1)`, with `j_R(x) > 0`. Möbius images of the two roots are again
the two roots of a rational quadratic, and a matrix of `SL₂(ℤ)` fixing one root fixes the other
with reciprocal Jacobi denominators. -/


/-- **Every real quadratic irrational is carried by some `R ∈ SL₂(ℤ)` with positive Jacobi
denominator to a reduced one**: for `x ≠ y` roots of `X² - tX + n` with `t, n ∈ ℚ` and `x`
irrational, there is `R ∈ SL₂(ℤ)` with `1 < R·x`, `0 < R·y < 1` and `j_R(x) > 0`.
This is the quadratic-irrational reduction ingredient in [72, Kopp (2024), Proposition 3.17,
`prop:reduced`], whose full statement concerns finitely many reduced ray-class representatives.
Take `R = A_{0,N}⁻¹` for the `N ≥ 1` of
`exists_hjCompanion_mem_Ioo`: then `R·x = x_N > 1` (`IsHJCompanion.flt_hjCycleMatrix_inv` at
`hjPeriod`, `one_lt_hjPeriod_succ`), `R·y = y_N ∈ (0,1)` (`hjCompanion_eq_flt_inv`, with `y`
irrational since `y = t - x`), and `j_R(x) = (x_1⋯x_N)⁻¹ > 0`
(`IsHJCompanion.fltDenominator_hjCycleMatrix_inv`). -/
@[source "72, Proposition 3.17, p. 31, prop:reduced (quadratic irrational reduction)"]
theorem exists_flt_reduced_of_sq_eq {x y : ℝ} {t n : ℚ} (hx : x ^ 2 = t * x - n)
    (hy : y ^ 2 = t * y - n) (hxy : x ≠ y) (hirr : Irrational x) :
    ∃ R : SL(2, ℤ), 1 < flt (R : Mat(2, ℤ)) x ∧
      flt (R : Mat(2, ℤ)) y ∈ Set.Ioo 0 1 ∧
      0 < fltDenominator (R : Mat(2, ℤ)) x := by
  have hyirr : Irrational y := by
    obtain ⟨hsum, _⟩ := BinaryQF.add_eq_and_mul_eq_of_sq_eq hxy hx hy
    rw [show y = (t : ℝ) - x by linarith, irrational_ratCast_sub_iff]
    exact hirr
  obtain ⟨N, hN, hmem⟩ := exists_hjCompanion_mem_Ioo hx hy hxy hirr
  let R : SL(2, ℤ) := (hjCycleMatrix x N)⁻¹
  have hRx : flt (R : Mat(2, ℤ)) x = hjPeriod x N := by
    simpa only [R, hjPeriod_zero] using
      (isHJCompanion_hjPeriod hirr).flt_hjCycleMatrix_inv N
  have hRy : flt (R : Mat(2, ℤ)) y = hjCompanion x y N := by
    exact (hjCompanion_eq_flt_inv hyirr N).symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.ne_of_gt hN)
  refine ⟨R, ?_, ?_, ?_⟩
  · rw [hRx]
    exact one_lt_hjPeriod_succ hirr k
  · rw [hRy]
    exact hmem
  · simpa only [R] using fltDenominator_hjCycleMatrix_inv_pos hirr (k + 1)

/-- `j_R(x)j_R(y) = c²n + cdt + d²` as the cast of a rational number, for `x + y = t`, `xy = n`
(`fltDenominator_mul_fltDenominator`); the common denominator in `exists_sq_eq_flt_of_sq_eq`. -/
private lemma fltDenominator_mul_fltDenominator_eq_ratCast {x y : ℝ} {t n : ℚ}
    (hsum : x + y = t) (hprod : x * y = n) (R : Mat(2, ℤ)) :
    fltDenominator R x * fltDenominator R y =
      (((R 1 0 : ℚ) ^ 2 * n + R 1 0 * R 1 1 * t + R 1 1 ^ 2 : ℚ) : ℝ) := by
  rw [fltDenominator_mul_fltDenominator R hsum hprod]
  push_cast
  ring

/-- **Vieta for the Möbius images, sum**: `R·x + R·y = (2acn + (ad + bc)t + 2bd)/D` with
`D = c²n + cdt + d² = j_R(x)j_R(y)`, for `x + y = t`, `xy = n`, `R = [[a,b],[c,d]]`. -/
private lemma flt_add_flt_of_add_eq {x y : ℝ} {t n : ℚ} (hsum : x + y = t) (hprod : x * y = n)
    (R : Mat(2, ℤ)) (hjx : fltDenominator R x ≠ 0)
    (hjy : fltDenominator R y ≠ 0) :
    flt R x + flt R y = (((2 * R 0 0 * R 1 0 * n + (R 0 0 * R 1 1 + R 0 1 * R 1 0) * t +
      2 * R 0 1 * R 1 1) / ((R 1 0 : ℚ) ^ 2 * n + R 1 0 * R 1 1 * t + R 1 1 ^ 2) : ℚ) : ℝ) := by
  have hD := fltDenominator_mul_fltDenominator_eq_ratCast hsum hprod R
  have hD0 : (((R 1 0 : ℚ) ^ 2 * n + R 1 0 * R 1 1 * t + R 1 1 ^ 2 : ℚ) : ℝ) ≠ 0 :=
    hD ▸ mul_ne_zero hjx hjy
  unfold fltDenominator at hjx hjy hD
  rw [Rat.cast_div, eq_div_iff hD0, ← hD]
  unfold flt
  rw [div_add_div _ _ hjx hjy, div_mul_cancel₀ _ (mul_ne_zero hjx hjy)]
  push_cast
  linear_combination (2 * (R 0 0 : ℝ) * R 1 0) * hprod +
    ((R 0 0 : ℝ) * R 1 1 + R 0 1 * R 1 0) * hsum

/-- **Vieta for the Möbius images, product**: `R·x · R·y = (a²n + abt + b²)/D` with
`D = c²n + cdt + d² = j_R(x)j_R(y)`, for `x + y = t`, `xy = n`, `R = [[a,b],[c,d]]`. -/
private lemma flt_mul_flt_of_add_eq {x y : ℝ} {t n : ℚ} (hsum : x + y = t) (hprod : x * y = n)
    (R : Mat(2, ℤ)) (hjx : fltDenominator R x ≠ 0)
    (hjy : fltDenominator R y ≠ 0) :
    flt R x * flt R y = ((((R 0 0 : ℚ) ^ 2 * n + R 0 0 * R 0 1 * t + R 0 1 ^ 2) /
      ((R 1 0 : ℚ) ^ 2 * n + R 1 0 * R 1 1 * t + R 1 1 ^ 2) : ℚ) : ℝ) := by
  have hD := fltDenominator_mul_fltDenominator_eq_ratCast hsum hprod R
  have hD0 : (((R 1 0 : ℚ) ^ 2 * n + R 1 0 * R 1 1 * t + R 1 1 ^ 2 : ℚ) : ℝ) ≠ 0 :=
    hD ▸ mul_ne_zero hjx hjy
  unfold fltDenominator at hjx hjy hD
  rw [Rat.cast_div, eq_div_iff hD0, ← hD]
  unfold flt
  rw [div_mul_div_comm, div_mul_cancel₀ _ (mul_ne_zero hjx hjy)]
  push_cast
  linear_combination ((R 0 0 : ℝ) ^ 2) * hprod + ((R 0 0 : ℝ) * R 0 1) * hsum

/-- **The Möbius images of the two roots of a rational quadratic are the two roots of another**:
for `x ≠ y` roots of `X² - tX + n` with `t, n ∈ ℚ` and an integer matrix `R = [[a,b],[c,d]]` with
`j_R(x), j_R(y) ≠ 0`, the numbers `R·x`, `R·y` are roots of `X² - t'X + n'` with
`t' = (2acn + (ad + bc)t + 2bd)/D` and `n' = (a²n + abt + b²)/D`, `D = c²n + cdt + d²`: these are
`R·x + R·y` and `R·x · R·y` by Vieta (`BinaryQF.add_eq_and_mul_eq_of_sq_eq`), and
`D = j_R(x)j_R(y) ≠ 0` (`fltDenominator_mul_fltDenominator`). -/
theorem exists_sq_eq_flt_of_sq_eq {x y : ℝ} {t n : ℚ} (hx : x ^ 2 = t * x - n)
    (hy : y ^ 2 = t * y - n) (hxy : x ≠ y) (R : Mat(2, ℤ))
    (hjx : fltDenominator R x ≠ 0) (hjy : fltDenominator R y ≠ 0) :
    ∃ t' n' : ℚ, flt R x ^ 2 = t' * flt R x - n' ∧ flt R y ^ 2 = t' * flt R y - n' := by
  obtain ⟨hsum, hprod⟩ := BinaryQF.add_eq_and_mul_eq_of_sq_eq hxy hx hy
  obtain ⟨t', ht'⟩ : ∃ t' : ℚ, flt R x + flt R y = t' :=
    ⟨_, flt_add_flt_of_add_eq hsum hprod R hjx hjy⟩
  obtain ⟨n', hn'⟩ : ∃ n' : ℚ, flt R x * flt R y = n' :=
    ⟨_, flt_mul_flt_of_add_eq hsum hprod R hjx hjy⟩
  exact ⟨t', n', by rw [← ht', ← hn']; ring, by rw [← ht', ← hn']; ring⟩

/-- The fixed-point equation at an irrational root gives the rational entry relations used by
`flt_eq_self_of_flt_eq_self_of_sq_eq` and its Jacobi-denominator counterpart. -/
private lemma entry_relations_of_flt_eq_self_of_sq_eq {x : ℝ} {t n : ℚ}
    (hx : x ^ 2 = t * x - n) (hirr : Irrational x) {M : SL(2, ℤ)}
    (hM : flt (M : Mat(2, ℤ)) x = x) :
    (M 1 0 : ℚ) * t + M 1 1 - M 0 0 = 0 ∧ (M 1 0 : ℚ) * n + M 0 1 = 0 := by
  have hden : fltDenominator (M : Mat(2, ℤ)) x ≠ 0 :=
    fltDenominator_ne_zero_of_irrational hirr M
  change (M 1 0 : ℝ) * x + (M 1 1 : ℝ) ≠ 0 at hden
  rw [flt, div_eq_iff hden] at hM
  have hrel :
      (((M 1 0 : ℚ) * t + M 1 1 - M 0 0 : ℚ) : ℝ) * x =
        (((M 1 0 : ℚ) * n + M 0 1 : ℚ) : ℝ) := by
    push_cast
    linear_combination -hM - (M 1 0 : ℝ) * hx
  exact ratCast_eq_zero_of_irrational_mul hirr hrel

/-- **A matrix of `SL₂(ℤ)` fixing one root of a rational quadratic fixes the other**: for `x ≠ y`
roots of `X² - tX + n` with `x` irrational and `M = [[a,b],[c,d]]` with `M·x = x`, the relation
`cx² + (d - a)x - b = 0` becomes `(ct + d - a)x = cn + b` after `x² = tx - n`, so both sides
vanish (`x` irrational, `ratCast_eq_zero_of_irrational_mul`), and then `y` satisfies the same
relation; `j_M(y) ≠ 0` as `y = t - x` is irrational (`fltDenominator_ne_zero_of_irrational`). -/
theorem flt_eq_self_of_flt_eq_self_of_sq_eq {x y : ℝ} {t n : ℚ} (hx : x ^ 2 = t * x - n)
    (hy : y ^ 2 = t * y - n) (hxy : x ≠ y) (hirr : Irrational x) {M : SL(2, ℤ)}
    (hM : flt (M : Mat(2, ℤ)) x = x) :
    flt (M : Mat(2, ℤ)) y = y := by
  obtain ⟨hsum, _⟩ := BinaryQF.add_eq_and_mul_eq_of_sq_eq hxy hx hy
  have hyirr : Irrational y := by
    rw [show y = (t : ℝ) - x by linarith, irrational_ratCast_sub_iff]
    exact hirr
  have hden : fltDenominator (M : Mat(2, ℤ)) y ≠ 0 :=
    fltDenominator_ne_zero_of_irrational hyirr M
  have hden' : (M 1 0 : ℝ) * y + M 1 1 ≠ 0 := by
    simpa only [fltDenominator] using hden
  obtain ⟨hcoeff, hconst⟩ := entry_relations_of_flt_eq_self_of_sq_eq hx hirr hM
  have hcoeffR : (M 1 0 : ℝ) * t + M 1 1 - M 0 0 = 0 := by
    exact_mod_cast hcoeff
  have hconstR : (M 1 0 : ℝ) * n + M 0 1 = 0 := by
    exact_mod_cast hconst
  change ((M 0 0 : ℝ) * y + M 0 1) / ((M 1 0 : ℝ) * y + M 1 1) = y
  rw [div_eq_iff hden']
  linear_combination -(M 1 0 : ℝ) * hy - y * hcoeffR + hconstR

/-- **The Jacobi denominators of a matrix fixing both roots are reciprocal**: under the hypotheses
of `flt_eq_self_of_flt_eq_self_of_sq_eq`, `j_M(x)j_M(y) = c²n + cdt + d² = ad - bc = 1`
(`fltDenominator_mul_fltDenominator`), using `ct = a - d` and `cn = -b` from the entry
relations. -/
theorem fltDenominator_mul_fltDenominator_eq_one_of_sq_eq {x y : ℝ} {t n : ℚ}
    (hx : x ^ 2 = t * x - n) (hy : y ^ 2 = t * y - n) (hxy : x ≠ y) (hirr : Irrational x)
    {M : SL(2, ℤ)} (hM : flt (M : Mat(2, ℤ)) x = x) :
    fltDenominator (M : Mat(2, ℤ)) x *
      fltDenominator (M : Mat(2, ℤ)) y = 1 := by
  obtain ⟨hsum, hprod⟩ := BinaryQF.add_eq_and_mul_eq_of_sq_eq hxy hx hy
  obtain ⟨hcoeff, hconst⟩ := entry_relations_of_flt_eq_self_of_sq_eq hx hirr hM
  have hcoeffR : (M 1 0 : ℝ) * t + M 1 1 - M 0 0 = 0 := by
    exact_mod_cast hcoeff
  have hconstR : (M 1 0 : ℝ) * n + M 0 1 = 0 := by
    exact_mod_cast hconst
  rw [fltDenominator_mul_fltDenominator (M : Mat(2, ℤ)) hsum hprod]
  have hdet : (M 0 0 : ℝ) * M 1 1 - (M 0 1 : ℝ) * M 1 0 = 1 :=
    det_fin_two_cast_eq_one M
  linear_combination (M 1 0 : ℝ) * hconstR + (M 1 1 : ℝ) * hcoeffR + hdet

/-! ### Reduction of an element of a real quadratic field

Kopp's remark "every `SL₂(ℤ)`-orbit in `F_quad` contains a `β` with `0 < β' < 1 < β`"
[72, Kopp (2024), Theorem 3.14, `thm:correspondence`, proof; Proposition 3.17, `prop:reduced`],
for an element `β ∈ K` read at the two real places, with the reducing matrix `R = A_{0,N}⁻¹`
taken from the expansion of `ρ₁(β)` so that `j_R(ρ₁(β)) = (β_1⋯β_N)⁻¹ > 0`. -/

section Element

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

/-- **Every irrational element of a real quadratic field is carried by some `R ∈ SL₂(ℤ)` with
positive Jacobi denominator to a reduced one**: for `β ∈ K` with `ρ₂(β) ≠ ρ₁(β)` there is
`R ∈ SL₂(ℤ)` with `1 < ρ₁(R·β)`, `0 < ρ₂(R·β) < 1` and `j_R(ρ₁(β)) > 0`
[72, Kopp (2024), Proposition 3.17, `prop:reduced`]. This is
`exists_flt_reduced_of_sq_eq` read at the two real places: both values are roots of
`X² - Tr(β)X + N(β)` (`RealQuadraticFieldData.finrank_eq_two`,
`map_sq_eq_trace_mul_sub_norm`), and the values of `R·β` are the corresponding fractional linear
transforms (`map_flt`). -/
theorem RealQuadraticFieldData.exists_flt_reduced (F : RealQuadraticFieldData K) {β : K}
    (hβ : realEmbeddingAt K F.otherPlace β ≠ realEmbeddingAt K F.place β) :
    ∃ R : SL(2, ℤ), 1 < realEmbeddingAt K F.place (flt (R : Mat(2, ℤ)) β) ∧
      realEmbeddingAt K F.otherPlace (flt (R : Mat(2, ℤ)) β) ∈ Set.Ioo 0 1 ∧
      0 < fltDenominator (R : Mat(2, ℤ)) (realEmbeddingAt K F.place β) := by
  obtain ⟨R, hRx, hRy, hj⟩ := exists_flt_reduced_of_sq_eq
    (map_sq_eq_trace_mul_sub_norm F.finrank_eq_two (realEmbeddingAt K F.place) β)
    (map_sq_eq_trace_mul_sub_norm F.finrank_eq_two (realEmbeddingAt K F.otherPlace) β)
    hβ.symm (irrational_realEmbeddingAt_of_ne hβ.symm)
  refine ⟨R, ?_, ?_, hj⟩
  · simpa only [map_flt] using hRx
  · simpa only [map_flt] using hRy

end Element

end SIC

end
