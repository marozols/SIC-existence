/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.ReducedForms
import SICs.Quadratic.RealFields

/-!
# The form of an element of a real quadratic field

The integral form `⟨a, -a Tr β, a N β⟩` of an element `β` of a quadratic field, with roots its two
real values, and Kopp's Proposition 7.2 for `β ∈ K`: `0 < ρ₂(β) < 1 < ρ₁(β)` makes `ρ₁(β)` purely
periodic.

This file attaches to an element `β` of a quadratic field `K` an integral binary quadratic form
whose two real roots are the two real values `ρ₁(β)`, `ρ₂(β)` of `β`, and uses it to carry the
pure periodicity theorem of `SICs.Quadratic.ReducedForms`, stated there for the root
`ρ_{Q,+}` of a reduced form, over to the field: an element with `0 < ρ₂(β) < 1 < ρ₁(β)` has a
purely periodic Hirzebruch--Jung expansion at `ρ₁`. This is [72, Kopp (2024), Proposition 7.2,
`prop:quadhj`] in the form in which the cycle data of [72, Kopp (2024), Definition 7.4,
`defn:cycledata`] use it, for `β ∈ K` rather than for a root of a form.

## Mathematical argument

By Cayley--Hamilton in the degree-two algebra `K/ℚ` (`SICs.Quadratic.DegreeTwoAlgebras`),
every `β ∈ K` satisfies

$$
\beta^2 = t\beta - n,\qquad t = \operatorname{Tr}_{K/\mathbb Q}(\beta),\quad
n = \operatorname{N}_{K/\mathbb Q}(\beta),
$$

so both real values `x = ρ₁(β)`, `y = ρ₂(β)` are roots of `X² - tX + n`. Clearing the
denominators of `t` and `n` with `a = den(t)·den(n)` gives the integral form

$$
Q = \langle a,\,-at,\,an\rangle,
$$

`BinaryQF.ofTraceNorm t n`. When `x ≠ y`, Vieta's relations `x + y = t`, `xy = n` follow from
the two equations, so `Δ(Q) = a²(t² - 4n) = a²(x - y)²` and, for `y < x`, `√Δ = a(x - y)`. Hence
`ρ_{Q,+} = (at + a(x-y))/(2a) = x` and `ρ_{Q,-} = y`. If `x` is irrational, `Δ` is not a
square (a square discriminant makes `ρ_{Q,+}` rational), so `Q` is irreducible, and
`0 < y < 1 < x` makes `Q` reduced (`isHJReduced_iff_roots`). The pure periodicity of `x` is
then `exists_hjPeriod_rootPlus_eq`.

The form `ofTraceNorm t n` need not be primitive; nothing here needs it to be.

## References

- [72, Kopp (2024), Proposition 7.2, `prop:quadhj`]: the statement for `β ∈ K`.
- `SICs.Quadratic.ReducedForms`: the proof for the root of a reduced form, after
  [68, Katok (2003), Theorem 1.4].
-/

noncomputable section

open NumberField

namespace SIC

namespace BinaryQF

/-! ### The form with prescribed trace and norm

The integral form `⟨a, -at, an⟩` with `a = den(t)·den(n)`, and its coefficients and discriminant
as rational numbers. -/

/-- **The integral form of the polynomial `X² - tX + n`**, `⟨a, -at, an⟩` with
`a = den(t)·den(n)`: `aX² - atX + an = a(X² - tX + n)`, with integer coefficients
`-at = -num(t)·den(n)` and `an = num(n)·den(t)`. Its roots are the roots of `X² - tX + n`
(`rootPlus_ofTraceNorm`, `rootMinus_ofTraceNorm`). -/
def ofTraceNorm (t n : ℚ) : BinaryQF where
  a := t.den * n.den
  b := -(t.num * n.den)
  c := n.num * t.den

/-- `a > 0`. -/
theorem a_ofTraceNorm_pos (t n : ℚ) : 0 < (ofTraceNorm t n).a := by
  change (0 : ℤ) < (t.den : ℤ) * (n.den : ℤ)
  positivity

/-- `b = -at` as rational numbers (`Rat.mul_den_eq_num`). -/
theorem b_ofTraceNorm_cast (t n : ℚ) :
    (((ofTraceNorm t n).b : ℤ) : ℚ) = -(((ofTraceNorm t n).a : ℤ) : ℚ) * t := by
  change ((-(t.num * (n.den : ℤ)) : ℤ) : ℚ) =
    -(((t.den * n.den : ℕ) : ℤ) : ℚ) * t
  push_cast
  rw [← Rat.mul_den_eq_num t]
  ring

/-- `c = an` as rational numbers (`Rat.mul_den_eq_num`). -/
theorem c_ofTraceNorm_cast (t n : ℚ) :
    (((ofTraceNorm t n).c : ℤ) : ℚ) = (((ofTraceNorm t n).a : ℤ) : ℚ) * n := by
  change (((n.num * (t.den : ℤ) : ℤ)) : ℚ) =
    ((((t.den * n.den : ℕ) : ℤ)) : ℚ) * n
  push_cast
  rw [← Rat.mul_den_eq_num n]
  ring

/-- `Δ = a²(t² - 4n)` as rational numbers (`disc_eq_coefficients`). -/
theorem disc_ofTraceNorm_cast (t n : ℚ) :
    (((ofTraceNorm t n).disc : ℤ) : ℚ) = (((ofTraceNorm t n).a : ℤ) : ℚ) ^ 2 * (t ^ 2 - 4 * n) := by
  rw [disc_eq_coefficients]
  push_cast
  rw [b_ofTraceNorm_cast, c_ofTraceNorm_cast]
  ring

/-! ### Vieta's relations and the roots

Two distinct roots `x ≠ y` of `X² - tX + n` have `x + y = t` and `xy = n`; the discriminant of
`ofTraceNorm t n` is then `a²(x-y)²`, and its roots are `x` and `y`. -/

/-- **Vieta's relations for two distinct roots**: if `x² = tx - n`, `y² = ty - n` and `x ≠ y`,
then `x + y = t` and `xy = n`. Subtracting the equations gives `(x - y)(x + y - t) = 0`; then
`n = tx - x² = x(t - x) = xy`. -/
theorem add_eq_and_mul_eq_of_sq_eq {x y t n : ℝ} (hxy : x ≠ y) (hx : x ^ 2 = t * x - n)
    (hy : y ^ 2 = t * y - n) : x + y = t ∧ x * y = n := by
  have hprod : (x - y) * (x + y - t) = 0 := by
    nlinarith [hx, hy]
  have hsum : x + y = t := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd (sub_eq_zero.mp h) hxy
    · linarith
  have hy' : y = t - x := by linarith
  refine ⟨hsum, ?_⟩
  rw [hy']
  nlinarith [hx]

/-- `√Δ = a(x - y)` for the roots `y < x` of `X² - tX + n`: `Δ = a²(t² - 4n) = a²(x-y)²` by
Vieta (`add_eq_and_mul_eq_of_sq_eq`, `disc_ofTraceNorm_cast`), and `a(x - y) > 0`
(`Real.sqrt_sq`). -/
theorem sqrt_disc_ofTraceNorm {t n : ℚ} {x y : ℝ} (hxy : y < x) (hx : x ^ 2 = t * x - n)
    (hy : y ^ 2 = t * y - n) :
    Real.sqrt (((ofTraceNorm t n).disc : ℤ) : ℝ) = (((ofTraceNorm t n).a : ℤ) : ℝ) * (x - y) := by
  have hv := add_eq_and_mul_eq_of_sq_eq (ne_of_gt hxy) hx hy
  have hdisc : (((ofTraceNorm t n).disc : ℤ) : ℝ) =
      (((ofTraceNorm t n).a : ℤ) : ℝ) ^ 2 * ((t : ℝ) ^ 2 - 4 * (n : ℝ)) := by
    exact_mod_cast disc_ofTraceNorm_cast t n
  have hsquare : (((ofTraceNorm t n).a : ℤ) : ℝ) ^ 2 *
      ((t : ℝ) ^ 2 - 4 * (n : ℝ)) =
        ((((ofTraceNorm t n).a : ℤ) : ℝ) * (x - y)) ^ 2 := by
    rw [← hv.1, ← hv.2]
    ring
  rw [hdisc, hsquare, Real.sqrt_sq]
  exact mul_nonneg (by exact_mod_cast (a_ofTraceNorm_pos t n).le) (sub_nonneg.mpr hxy.le)

/-- **The root `ρ_{Q,+}` of `ofTraceNorm t n` is the larger root `x`** of `X² - tX + n`:
`(-b + √Δ)/(2a) = (at + a(x - y))/(2a) = x` by `sqrt_disc_ofTraceNorm` and Vieta. -/
theorem rootPlus_ofTraceNorm {t n : ℚ} {x y : ℝ} (hxy : y < x) (hx : x ^ 2 = t * x - n)
    (hy : y ^ 2 = t * y - n) : (ofTraceNorm t n).rootPlus = x := by
  have hv := add_eq_and_mul_eq_of_sq_eq (ne_of_gt hxy) hx hy
  have hb : (((ofTraceNorm t n).b : ℤ) : ℝ) =
      -(((ofTraceNorm t n).a : ℤ) : ℝ) * (t : ℝ) := by
    exact_mod_cast b_ofTraceNorm_cast t n
  have ha : (((ofTraceNorm t n).a : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast (a_ofTraceNorm_pos t n).ne'
  unfold rootPlus
  rw [sqrt_disc_ofTraceNorm hxy hx hy, hb, ← hv.1]
  field_simp
  ring

/-- **The root `ρ_{Q,-}` of `ofTraceNorm t n` is the smaller root `y`** of `X² - tX + n`:
`(-b - √Δ)/(2a) = (at - a(x - y))/(2a) = y`. -/
theorem rootMinus_ofTraceNorm {t n : ℚ} {x y : ℝ} (hxy : y < x) (hx : x ^ 2 = t * x - n)
    (hy : y ^ 2 = t * y - n) : (ofTraceNorm t n).rootMinus = y := by
  have hv := add_eq_and_mul_eq_of_sq_eq (ne_of_gt hxy) hx hy
  have hb : (((ofTraceNorm t n).b : ℤ) : ℝ) =
      -(((ofTraceNorm t n).a : ℤ) : ℝ) * (t : ℝ) := by
    exact_mod_cast b_ofTraceNorm_cast t n
  have ha : (((ofTraceNorm t n).a : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast (a_ofTraceNorm_pos t n).ne'
  unfold rootMinus
  rw [sqrt_disc_ofTraceNorm hxy hx hy, hb, ← hv.1]
  field_simp
  ring

/-- Solving a nondegenerate linear equation with integral coefficients gives a rational real. -/
private lemma mem_range_ratCast_of_two_mul_mul_add_eq {a b k : ℤ} {x : ℝ}
    (ha : a ≠ 0) (h : 2 * (a : ℝ) * x + (b : ℝ) = (k : ℝ)) :
    x ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨(((k - b : ℤ) : ℚ) / ((2 * a : ℤ) : ℚ)), ?_⟩
  push_cast
  field_simp
  nlinarith [h]

/-- **An irrational root makes the form irreducible**: if `x² = tx - n` with `x` irrational then
`Δ` is not a square. Completing the square, `(2ax + b)² = Δ` (`b_ofTraceNorm_cast`,
`disc_ofTraceNorm_cast`); if `Δ = k²` then `2ax + b = ±k` (`sq_eq_sq_iff_eq_or_eq_neg`) and
`x = (±k - b)/(2a)` is rational. -/
theorem isIrreducible_ofTraceNorm {t n : ℚ} {x : ℝ} (hirr : Irrational x)
    (hx : x ^ 2 = t * x - n) : (ofTraceNorm t n).IsIrreducible := by
  intro hsquare
  apply hirr
  have hb : (((ofTraceNorm t n).b : ℤ) : ℝ) =
      -(((ofTraceNorm t n).a : ℤ) : ℝ) * (t : ℝ) := by
    exact_mod_cast b_ofTraceNorm_cast t n
  have hdisc : (((ofTraceNorm t n).disc : ℤ) : ℝ) =
      (((ofTraceNorm t n).a : ℤ) : ℝ) ^ 2 * ((t : ℝ) ^ 2 - 4 * (n : ℝ)) := by
    exact_mod_cast disc_ofTraceNorm_cast t n
  have hcomplete :
      (2 * (((ofTraceNorm t n).a : ℤ) : ℝ) * x +
        (((ofTraceNorm t n).b : ℤ) : ℝ)) ^ 2 =
          (((ofTraceNorm t n).disc : ℤ) : ℝ) := by
    rw [hdisc, hb]
    nlinarith [hx]
  rcases hsquare with ⟨k, hk⟩
  have hk' : (((ofTraceNorm t n).disc : ℤ) : ℝ) = (k : ℝ) ^ 2 := by
    rw [hk]
    push_cast
    ring
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp (hcomplete.trans hk')) with hlin | hlin
  · exact mem_range_ratCast_of_two_mul_mul_add_eq
      (a_ofTraceNorm_pos t n).ne' hlin
  · apply mem_range_ratCast_of_two_mul_mul_add_eq
      (a_ofTraceNorm_pos t n).ne' (k := -k)
    simpa only [Int.cast_neg] using hlin

/-- **The form of a pair `0 < y < 1 < x` of roots is reduced** (`isHJReduced_iff_roots` with
`rootPlus_ofTraceNorm`, `rootMinus_ofTraceNorm`). -/
theorem isHJReduced_ofTraceNorm {t n : ℚ} {x y : ℝ} (hx1 : 1 < x) (hy : y ∈ Set.Ioo 0 1)
    (hx : x ^ 2 = t * x - n) (hy' : y ^ 2 = t * y - n) : (ofTraceNorm t n).IsHJReduced := by
  have hxy : y < x := lt_trans hy.2 hx1
  apply (isHJReduced_iff_roots (a_ofTraceNorm_pos t n)).2
  rw [rootMinus_ofTraceNorm hxy hx hy', rootPlus_ofTraceNorm hxy hx hy']
  exact ⟨hy.1, hy.2, hx1⟩

end BinaryQF

variable {K : Type*} [Field K] [NumberField K]

/-! ### The form of an element and pure periodicity

The form `⟨a, -a Tr(β), a N(β)⟩` of `β ∈ K`, whose roots are the two real values of `β`, and
[72, Kopp (2024), Proposition 7.2, `prop:quadhj`] for `β ∈ K`. -/

/-- **The integral form of `β ∈ K`**: `ofTraceNorm` at `t = Tr_{K/ℚ}(β)`, `n = N_{K/ℚ}(β)`, the
form `a(X² - Tr(β)X + N(β))` with `a` clearing the denominators. Its roots are the two real
values of `β`; `RealQuadraticFieldData.rootPlus_elementForm` identifies the larger one. -/
def elementForm (β : K) : BinaryQF :=
  BinaryQF.ofTraceNorm (Algebra.trace ℚ K β) (Algebra.norm ℚ β)

namespace RealQuadraticFieldData

variable [NumberField.IsTotallyReal K] (F : RealQuadraticFieldData K)

/-- **`ρ_{Q,+}` of the form of `β` is `ρ₁(β)`** when `ρ₂(β) < ρ₁(β)`, with `ρ₁` at `F.place`
and `ρ₂` at a place `w₂`, necessarily different from `F.place` (`BinaryQF.rootPlus_ofTraceNorm`,
`map_sq_eq_trace_mul_sub_norm`). -/
theorem rootPlus_elementForm {w₂ : InfinitePlace K} {β : K}
    (h : realEmbeddingAt K w₂ β < realEmbeddingAt K F.place β) :
    (elementForm β).rootPlus = realEmbeddingAt K F.place β := by
  apply BinaryQF.rootPlus_ofTraceNorm h
  · exact map_sq_eq_trace_mul_sub_norm F.finrank_eq_two (realEmbeddingAt K F.place) β
  · exact map_sq_eq_trace_mul_sub_norm F.finrank_eq_two (realEmbeddingAt K w₂) β

/-- **The form of `β` is irreducible when `β` has two different real values**
(`irrational_realEmbeddingAt_of_ne`, `BinaryQF.isIrreducible_ofTraceNorm`). -/
theorem isIrreducible_elementForm {w₂ : InfinitePlace K} {β : K}
    (h : realEmbeddingAt K w₂ β ≠ realEmbeddingAt K F.place β) :
    (elementForm β).IsIrreducible := by
  apply BinaryQF.isIrreducible_ofTraceNorm (irrational_realEmbeddingAt_of_ne h.symm)
  exact map_sq_eq_trace_mul_sub_norm F.finrank_eq_two (realEmbeddingAt K F.place) β

/-- **The form of `β` is reduced when `0 < ρ₂(β) < 1 < ρ₁(β)`**
(`BinaryQF.isHJReduced_ofTraceNorm`). -/
theorem isHJReduced_elementForm {w₂ : InfinitePlace K} {β : K}
    (h1 : 1 < realEmbeddingAt K F.place β) (h2 : realEmbeddingAt K w₂ β ∈ Set.Ioo 0 1) :
    (elementForm β).IsHJReduced := by
  apply BinaryQF.isHJReduced_ofTraceNorm h1 h2
  · exact map_sq_eq_trace_mul_sub_norm F.finrank_eq_two (realEmbeddingAt K F.place) β
  · exact map_sq_eq_trace_mul_sub_norm F.finrank_eq_two (realEmbeddingAt K w₂) β

/-- **[72, Kopp (2024), Proposition 7.2, `prop:quadhj`], the direction the cycle data need, for
an element of `K`**: if `0 < ρ₂(β) < 1 < ρ₁(β)`, with `ρ₁` at `F.place` and `ρ₂` at a place
`w₂`, then `ρ₁(β)` is a periodic point of the Hirzebruch--Jung rotation, `β_ℓ = β` for
some `ℓ ≥ 1`. From `BinaryQF.exists_hjPeriod_rootPlus_eq` at `elementForm β`
(`isHJReduced_elementForm`, `isIrreducible_elementForm`, `rootPlus_elementForm`), through
`Function.mem_periodicPts`; `hjPeriod x ℓ` is `hjRotate^[ℓ] x` by definition. -/
theorem mem_periodicPts_hjRotate {w₂ : InfinitePlace K} {β : K}
    (h1 : 1 < realEmbeddingAt K F.place β) (h2 : realEmbeddingAt K w₂ β ∈ Set.Ioo 0 1) :
    realEmbeddingAt K F.place β ∈ Function.periodicPts hjRotate := by
  have hlt : realEmbeddingAt K w₂ β < realEmbeddingAt K F.place β := lt_trans h2.2 h1
  have hred := F.isHJReduced_elementForm h1 h2
  have hirr := F.isIrreducible_elementForm (ne_of_lt hlt)
  obtain ⟨ℓ, hℓ, hperiod⟩ := BinaryQF.exists_hjPeriod_rootPlus_eq hred hirr
  apply Function.mem_periodicPts.mpr
  refine ⟨ℓ, hℓ, ?_⟩
  change hjPeriod (realEmbeddingAt K F.place β) ℓ = realEmbeddingAt K F.place β
  rw [← F.rootPlus_elementForm hlt]
  exact hperiod

end RealQuadraticFieldData

end SIC

end
