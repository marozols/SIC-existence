/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.HJExpansion

/-!
# The stabilizer of a purely periodic Hirzebruch--Jung expansion

The stabilizer elements of a purely periodic expansion with positive Jacobi denominators are the
powers of `P`, by the relative-minima (Klein sail) argument along a companion sequence.

This file proves the group-theoretic half of [72, Kopp (2024), Proposition 7.7,
`prop:betatogamma`] in its positive form: if `β` has a purely periodic Hirzebruch--Jung expansion
of minimal period `ℓ` and `P = A_{0,ℓ}` is its cycle matrix, then every `M ∈ SL₂(ℤ)` fixing `β`
and `β'` with positive Jacobi denominators at both is `P^m`. Kopp's statement covers every `M`
fixing `β`, which is `±P^m`, the sign `-` occurring for negative Jacobi denominators. Kopp states
it for a real quadratic `β` and uses its Galois conjugate `β'`; here the conjugate is replaced by
a companion sequence `x` of the expansion (`SICs.SL2Z.HJExpansion`) with values in `(0,1)`, of
which the sequence of conjugates `β'_n` is the instance the quadratic layer supplies
(`SICs.Quadratic.CycleUnit`). The two forms are equivalent for quadratic `β`, and this one needs
no field.

## The argument

Kopp's proof is by discreteness of the stabilizer in `SL₂(ℝ)`, but its last step ("`e^v - e^{-v}
= (β - β')m` is only possible if `v ∈ (log ε)ℤ`") assumes that `ε = β_0⋯β_{ℓ-1}` generates the
totally positive units, which is his Lemma 7.6, whose proof in turn relies on this proposition.
The argument here is instead the classical one through the relative minima of a lattice, the
vertices of Klein's sail, which needs nothing beyond the expansion itself. No reference in
`References` proves it in this form, so it is carried out in full.

Write `φ(r, s) = rβ + s` and `φ'(r, s) = rβ' + s` for the two linear forms on `ℤ²`, where
`β' = x_0`; both are the Jacobi denominator `j_N(·)` of any matrix `N` with bottom row `(r, s)`.
A matrix `N ∈ SL₂(ℤ)` fixing `β` and `β'` acts on row vectors by `v ↦ vN`, and
`φ(vN) = j_N(β) φ(v)`, `φ'(vN) = j_N(β') φ'(v)`: right multiplication by `N` scales the two forms
by the two eigenvalues. The bottom rows `v_n` of the inverse cycle matrices `A_{n,0} = A_{0,n}⁻¹`,
the *sail vertices* below, have values `φ(v_n) = 1/(β_1⋯β_n)`, strictly decreasing, and
`φ'(v_n) = 1/(β'_1⋯β'_n)`, strictly increasing since `0 < β'_i < 1`; consecutive `v_n, v_{n+1}`
are the two rows of the determinant-one matrix `A_{n+1,0}`, hence a basis of `ℤ²`.

* **The sail bounds the lattice from below.** If `w ∈ ℤ²` has `φ(v_{n+1}) ≤ φ(w) < φ(v_n)` and
  `φ'(w) > 0`, then `φ'(w) ≥ φ'(v_{n+1})`. Writing `w = p v_n + q v_{n+1}`, the bound
  `φ'(w) < φ'(v_{n+1})` would force `p ≥ 1`, then `q ≤ -1`, and then the integer `-q` would lie
  strictly between `(p-1)β_{n+1} ≥ p-1` and `pβ'_{n+1} < p`.
* **`(0,1)` is a relative minimum.** No `w ≠ (0,1)` has `0 < φ(w) ≤ 1` and `0 < φ'(w) ≤ 1`:
  with `w = (r, s)` and `r ≥ 1` the integer `s` would lie in `(-r, 1-r)`, with `r ≤ -1` in
  `(|r|, |r|+1)`. This uses exactly `0 < β' < 1 < β`.
* **Transport.** Hence for `N` fixing `β` and `β'` with positive Jacobi denominators, the bottom
  row `w = (0,1)N` is a relative minimum too: anything below it is carried by `N⁻¹` below `(0,1)`.
* **Conclusion.** If `1/(β_1⋯β_ℓ) < j_N(β) ≤ 1`, either `j_N(β) = 1` and `w = (0,1)` outright, or
  there is `n < ℓ` with `φ(v_{n+1}) ≤ φ(w) < φ(v_n)`, and the bullets give `w = v_{n+1}`. Then
  `N = T^k A_{0,n+1}⁻¹`, so `β = N·β = β_{n+1} + k`; as the rotation ignores integer shifts,
  `β_{n+1} = β`, which contradicts minimality of `ℓ` unless `n + 1 = ℓ`, where
  `φ(w) = 1/(β_1⋯β_ℓ)` contradicts the strict lower bound. So in every case `N = T^k` with
  `β + k = β`, that is `N = I`. A general `M` with positive Jacobi denominators is reduced to this
  by dividing out the power of `P` with `ε^m < j_M(β) ≤ ε^{m+1}`.

## References

- [72, Kopp (2024), Proposition 7.7, `prop:betatogamma`]: the statement, in its purely periodic
  case; Kopp attributes the unit identification to Hirzebruch, *Hilbert modular surfaces*,
  Enseign. Math. 19 (1973), p. 215.
- [68, Katok (2003), Lemma 4.32]: the discreteness argument Kopp's proof follows, not used here.
-/

open scoped MatrixGroups

namespace SIC

/-! ### Values of row vectors

The bottom row `(r, s)` of a matrix determines its Jacobi denominator `rτ + s`. Treating the
row as a vector of its own lets the lattice `ℤ²` be compared under the two forms `φ`, `φ'`
without naming matrices. -/

/-- The value `rτ + s` of the row vector `(r, s)` at `τ`: the Jacobi denominator of any matrix
whose bottom row is `(r, s)`. -/
def rowValue (v : Fin 2 → ℤ) (τ : ℝ) : ℝ := (v 0 : ℝ) * τ + (v 1 : ℝ)

/-- The value of `(0, 1)` is `1`. -/
@[simp] theorem rowValue_zero_one (τ : ℝ) : rowValue ![0, 1] τ = 1 := by
  simp [rowValue]

/-- **Linearity under right multiplication**: the value of `vM` is the combination
`v_0·(value of row 0 of M) + v_1·(value of row 1 of M)`. -/
theorem rowValue_vecMul (v : Fin 2 → ℤ) (M : Mat(2, ℤ)) (τ : ℝ) :
    rowValue (Matrix.vecMul v M) τ =
      (v 0 : ℝ) * rowValue (M 0) τ + (v 1 : ℝ) * rowValue (M 1) τ := by
  simp only [rowValue, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  push_cast
  ring

/-- **Right multiplication by a matrix fixing `τ` scales the value by the Jacobi denominator**:
`φ_τ(vM) = j_M(τ) φ_τ(v)` when `M·τ = τ` and `j_M(τ) ≠ 0`, because `M(τ, 1)ᵀ = j_M(τ)(τ, 1)ᵀ`. -/
theorem rowValue_vecMul_of_flt_eq_self (v : Fin 2 → ℤ) {M : Mat(2, ℤ)}
    {τ : ℝ} (hden : fltDenominator M τ ≠ 0) (hfix : flt M τ = τ) :
    rowValue (Matrix.vecMul v M) τ = fltDenominator M τ * rowValue v τ := by
  have hnum : (M 0 0 : ℝ) * τ + (M 0 1 : ℝ) = fltDenominator M τ * τ := by
    have h := (div_eq_iff hden).mp hfix
    simpa [flt, mul_comm] using h
  simp only [rowValue, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  push_cast
  unfold fltDenominator at hnum ⊢
  linear_combination (v 0 : ℝ) * hnum

/-- **At an irrational point the value determines the row**: `rτ + s = r'τ + s'` forces
`(r, s) = (r', s')`, by `ratCast_eq_zero_of_irrational_mul`. -/
theorem rowValue_injective {τ : ℝ} (hτ : Irrational τ) :
    Function.Injective (fun v : Fin 2 → ℤ ↦ rowValue v τ) := by
  intro v w h
  have hrel : ((((v 0 - w 0 : ℤ) : ℚ) : ℝ) * τ) =
      (((w 1 - v 1 : ℤ) : ℚ) : ℝ) := by
    unfold rowValue at h
    push_cast at h ⊢
    linarith
  obtain ⟨h0, h1⟩ := ratCast_eq_zero_of_irrational_mul hτ hrel
  have hvw0 : v 0 = w 0 := by
    have : v 0 - w 0 = 0 := by exact_mod_cast h0
    omega
  have hvw1 : v 1 = w 1 := by
    have : w 1 - v 1 = 0 := by exact_mod_cast h1
    omega
  funext i
  fin_cases i
  · exact hvw0
  · exact hvw1

/-! ### The sail vertices

The bottom rows of the inverse cycle matrices. Their values under `φ` and `φ'` are the reciprocal
partial products of `β_n` and of the companion sequence, so the former decrease while the latter
stay positive, and consecutive ones form a basis of `ℤ²`. -/

/-- The `n`-th **sail vertex** of the expansion of `β`: the bottom row of `A_{n,0} = A_{0,n}⁻¹`.
Under the two forms `φ`, `φ'` these are the vertices of Klein's sail, the boundary of the convex
hull of the lattice points in the positive quadrant; the name is used here only for this row
vector, and none of the convexity is needed. -/
noncomputable def sailVertex (β : ℝ) (n : ℕ) : Fin 2 → ℤ :=
  (((hjCycleMatrix β n)⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) 1

/-- The zeroth vertex is `(0, 1)`, the bottom row of the identity. -/
@[simp] theorem sailVertex_zero (β : ℝ) : sailVertex β 0 = ![0, 1] := by
  funext i
  fin_cases i <;> simp [sailVertex, hjCycleMatrix_zero]

/-- **Consecutive vertices are the two rows of `A_{0,n+1}⁻¹`**: its top row is the `n`-th vertex
(`hjCycleMatrix_inv_succ_apply_zero`) and its bottom row the `(n+1)`-st. -/
theorem hjCycleMatrix_inv_succ_apply (β : ℝ) (n : ℕ) :
    (((hjCycleMatrix β (n + 1))⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) 0 = sailVertex β n ∧
      (((hjCycleMatrix β (n + 1))⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) 1 =
        sailVertex β (n + 1) := by
  constructor
  · funext j
    exact hjCycleMatrix_inv_succ_apply_zero β n j
  · rfl

/-- **The value of a vertex along a companion sequence**: `φ'(v_n) = (x_1⋯x_n)⁻¹`, which is
`IsHJCompanion.fltDenominator_hjCycleMatrix_inv` read on the bottom row. -/
theorem rowValue_sailVertex {β : ℝ} {x : ℕ → ℝ} (hx : IsHJCompanion β x) (n : ℕ) :
    rowValue (sailVertex β n) (x 0) = (∏ i ∈ Finset.range n, x (i + 1))⁻¹ := by
  exact hx.fltDenominator_hjCycleMatrix_inv n

/-- **The vertices decrease under `φ`**: `φ(v_{n+1}) = φ(v_n)/β_{n+1}` with `β_{n+1} > 1`. -/
theorem rowValue_sailVertex_succ {β : ℝ} (hβ : Irrational β) (n : ℕ) :
    rowValue (sailVertex β (n + 1)) β = rowValue (sailVertex β n) β / hjPeriod β (n + 1) := by
  have hs := rowValue_sailVertex (isHJCompanion_hjPeriod hβ) (n + 1)
  have hn := rowValue_sailVertex (isHJCompanion_hjPeriod hβ) n
  simp only [hjPeriod_zero, Finset.prod_range_succ] at hs hn
  rw [hs, hn]
  simp only [mul_inv_rev, div_eq_mul_inv]
  ring

/-- **The vertices move along a companion sequence by its terms**: `φ'(v_{n+1}) = φ'(v_n)/x_{n+1}`.
-/
theorem rowValue_sailVertex_succ_of_isHJCompanion {β : ℝ} {x : ℕ → ℝ} (hx : IsHJCompanion β x)
    (n : ℕ) :
    rowValue (sailVertex β (n + 1)) (x 0) = rowValue (sailVertex β n) (x 0) / x (n + 1) := by
  rw [rowValue_sailVertex hx, rowValue_sailVertex hx, Finset.prod_range_succ]
  simp only [mul_inv_rev, div_eq_mul_inv]
  ring

/-- The values `φ(v_n)` are positive. -/
theorem rowValue_sailVertex_pos {β : ℝ} (hβ : Irrational β) (n : ℕ) :
    0 < rowValue (sailVertex β n) β := by
  have hn := rowValue_sailVertex (isHJCompanion_hjPeriod hβ) n
  simp only [hjPeriod_zero] at hn
  rw [hn]
  exact inv_pos.mpr
    (Finset.prod_pos fun i _ ↦ lt_trans zero_lt_one (one_lt_hjPeriod_succ hβ i))

/-- Along a companion sequence with values in `(0, 1)`, the values `φ'(v_n)` are positive. -/
theorem rowValue_sailVertex_pos_of_isHJCompanion {β : ℝ} {x : ℕ → ℝ} (hx : IsHJCompanion β x)
    (hx01 : ∀ n, 0 < x n ∧ x n < 1) (n : ℕ) :
    0 < rowValue (sailVertex β n) (x 0) := by
  rw [rowValue_sailVertex hx]
  exact inv_pos.mpr (Finset.prod_pos fun i _ ↦ (hx01 (i + 1)).1)

/-! ### The sail bounds the lattice from below

A lattice point whose `φ`-value lies between two consecutive vertices has `φ'`-value at least
that of the lower vertex: the coordinate argument of the file docstring. -/

/-- **Coordinates in the basis of two consecutive vertices**: every `w ∈ ℤ²` is
`p v_n + q v_{n+1}` with `p, q ∈ ℤ` (namely `(p, q) = w A_{0,n+1}`, since `v_n, v_{n+1}` are the
rows of `A_{0,n+1}⁻¹`), so its value at every `τ` is `p φ_τ(v_n) + q φ_τ(v_{n+1})`. -/
theorem exists_rowValue_eq_sailVertex (β : ℝ) (w : Fin 2 → ℤ) (n : ℕ) :
    ∃ p q : ℤ, ∀ τ : ℝ, rowValue w τ =
      p * rowValue (sailVertex β n) τ + q * rowValue (sailVertex β (n + 1)) τ := by
  let A : SL(2, ℤ) := hjCycleMatrix β (n + 1)
  let u : Fin 2 → ℤ := Matrix.vecMul w (A : Mat(2, ℤ))
  have hw : w = Matrix.vecMul u ((A⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) := by
    rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  refine ⟨u 0, u 1, fun τ ↦ ?_⟩
  rw [hw, rowValue_vecMul, (hjCycleMatrix_inv_succ_apply β n).1,
    (hjCycleMatrix_inv_succ_apply β n).2]

/-- The real-arithmetic core of `rowValue_sailVertex_le_of_isHJCompanion`: with `a = bt` and
`c = dy` for `b, d > 0`, `t > 1` and `y < 1`, no integers `p, q` satisfy both
`b ≤ pa + qb < a` and `0 < pc + qd < d`. The first pair forces `p ≥ 1` and then `q ≤ -1`, and
then the integer `-q` lies strictly between `(p-1)t ≥ p-1` and `py < p`. -/
private theorem not_lt_of_coords {a b c d t y : ℝ} (p q : ℤ) (hb : 0 < b) (hd : 0 < d)
    (hbt : b * t = a) (hdy : d * y = c) (ht : 1 < t) (hy1 : y < 1)
    (h₁ : b ≤ p * a + q * b) (h₂ : p * a + q * b < a) (h₃ : 0 < p * c + q * d)
    (h₄ : p * c + q * d < d) : False := by
  have ha : 0 < a := hbt ▸ mul_pos hb (zero_lt_one.trans ht)
  have hbracket : 0 < a * d - b * c := by
    calc
      0 < b * d * (t - y) := mul_pos (mul_pos hb hd) (sub_pos.mpr (lt_trans hy1 ht))
      _ = a * d - b * c := by rw [← hbt, ← hdy]; ring
  have hp : 0 < (p : ℝ) := by
    apply pos_of_mul_pos_left _ hbracket.le
    nlinarith [mul_le_mul_of_nonneg_right h₁ hd.le, mul_lt_mul_of_pos_right h₄ hb]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 0 < p by exact_mod_cast hp)
  have hq : q ≤ -1 := by
    by_contra hq
    have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast (show 0 ≤ q by omega)
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1) ha.le, mul_nonneg hq0 hb.le]
  have hleft : (p : ℝ) - 1 < -(q : ℝ) := by
    have haux : ((p : ℝ) - 1) * t < -(q : ℝ) := by
      apply lt_of_mul_lt_mul_left _ hb.le
      calc
        b * (((p : ℝ) - 1) * t) = ((p : ℝ) - 1) * a := by rw [← hbt]; ring
        _ < -(q : ℝ) * b := by linarith
        _ = b * -(q : ℝ) := by ring
    have hle : (p : ℝ) - 1 ≤ ((p : ℝ) - 1) * t := by
      simpa using mul_le_mul_of_nonneg_left ht.le (sub_nonneg.mpr hp1)
    exact lt_of_le_of_lt hle haux
  have hright : -(q : ℝ) < p := by
    have haux : -(q : ℝ) < (p : ℝ) * y := by
      apply lt_of_mul_lt_mul_left _ hd.le
      calc
        d * -(q : ℝ) < (p : ℝ) * c := by nlinarith
        _ = d * ((p : ℝ) * y) := by rw [← hdy]; ring
    exact lt_trans haux (mul_lt_of_lt_one_right hp hy1)
  have hleftInt : p - 1 < -q := by exact_mod_cast hleft
  have hrightInt : -q < p := by exact_mod_cast hright
  omega

/-- **The sail bounds the lattice from below.** If `w ∈ ℤ²` satisfies
`φ(v_{n+1}) ≤ φ(w) < φ(v_n)` and `φ'(w) > 0`, then `φ'(v_{n+1}) ≤ φ'(w)`. In the basis
`v_n, v_{n+1}` of `ℤ²`, write `w = p v_n + q v_{n+1}`: were `φ'(w) < φ'(v_{n+1})`, the bounds
would give `p ≥ 1`, then `q ≤ -1`, and then `(p-1)β_{n+1} < -q < pβ'_{n+1}`, impossible for the
integer `-q` since `β_{n+1} > 1 > β'_{n+1} > 0`. -/
theorem rowValue_sailVertex_le_of_isHJCompanion {β : ℝ} (hβ : Irrational β) {x : ℕ → ℝ}
    (hx : IsHJCompanion β x) (hx01 : ∀ n, 0 < x n ∧ x n < 1) (w : Fin 2 → ℤ) (n : ℕ)
    (h₁ : rowValue (sailVertex β (n + 1)) β ≤ rowValue w β)
    (h₂ : rowValue w β < rowValue (sailVertex β n) β) (h₃ : 0 < rowValue w (x 0)) :
    rowValue (sailVertex β (n + 1)) (x 0) ≤ rowValue w (x 0) := by
  obtain ⟨p, q, hpq⟩ := exists_rowValue_eq_sailVertex β w n
  rw [hpq] at h₁ h₂ h₃ ⊢
  by_contra hnot
  have hbt : rowValue (sailVertex β (n + 1)) β * hjPeriod β (n + 1) =
      rowValue (sailVertex β n) β := by
    rw [rowValue_sailVertex_succ hβ n]
    exact div_mul_cancel₀ _ (zero_lt_one.trans (one_lt_hjPeriod_succ hβ n)).ne'
  have hdy : rowValue (sailVertex β (n + 1)) (x 0) * x (n + 1) =
      rowValue (sailVertex β n) (x 0) := by
    rw [rowValue_sailVertex_succ_of_isHJCompanion hx n]
    exact div_mul_cancel₀ _ (hx01 (n + 1)).1.ne'
  exact not_lt_of_coords p q (rowValue_sailVertex_pos hβ (n + 1))
    (rowValue_sailVertex_pos_of_isHJCompanion hx hx01 (n + 1)) hbt hdy
    (one_lt_hjPeriod_succ hβ n) (hx01 (n + 1)).2 h₁ h₂ h₃ (lt_of_not_ge hnot)

/-! ### Relative minima

The vector `(0,1)` is a relative minimum of `ℤ²` for the pair of forms `(φ, φ')`, and right
multiplication by a stabilizing matrix with positive Jacobi denominators carries relative minima
to relative minima. -/

/-- **`(0,1)` is a relative minimum**: if `0 < rβ + s ≤ 1` and `0 < rβ' + s ≤ 1` with `β > 1` and
`0 < β' < 1`, then `(r, s) = (0, 1)`. For `r ≥ 1` the integer `s` would lie in `(-r, 1-r)`, for
`r ≤ -1` in `(-r, 1-r)` again read as `(|r|, |r|+1)`. -/
theorem eq_zero_one_of_rowValue_le_one {β β' : ℝ} (hβ : 1 < β) (hβ'0 : 0 < β') (hβ'1 : β' < 1)
    (w : Fin 2 → ℤ) (h₁ : 0 < rowValue w β) (h₂ : rowValue w β ≤ 1) (h₃ : 0 < rowValue w β')
    (h₄ : rowValue w β' ≤ 1) : w = ![0, 1] := by
  let r := w 0
  let s := w 1
  have hr_cases : r = 0 ∨ 0 < r ∨ r < 0 := by omega
  rcases hr_cases with hr | hr | hr
  · have hs0 : (0 : ℝ) < s := by simpa [rowValue, r, s, hr] using h₁
    have hs1 : (s : ℝ) ≤ 1 := by simpa [rowValue, r, s, hr] using h₂
    have hs : s = 1 := by
      have hs0' : 0 < s := by exact_mod_cast hs0
      have hs1' : s ≤ 1 := by exact_mod_cast hs1
      omega
    funext i
    fin_cases i
    · simpa [r] using hr
    · simpa [s] using hs
  · have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have hlow : -(r : ℝ) < s := by
      dsimp only [rowValue] at h₃
      nlinarith [mul_lt_mul_of_pos_left hβ'1 hr0]
    have hhigh : (s : ℝ) < 1 - r := by
      dsimp only [rowValue] at h₂
      nlinarith [mul_lt_mul_of_pos_left hβ hr0]
    have hlow' : -r < s := by exact_mod_cast hlow
    have hhigh' : s < 1 - r := by exact_mod_cast hhigh
    omega
  · have hr0 : (r : ℝ) < 0 := by exact_mod_cast hr
    have hlow : -(r : ℝ) < s := by
      dsimp only [rowValue] at h₁
      nlinarith [mul_lt_mul_of_neg_left hβ hr0]
    have hhigh : (s : ℝ) < 1 - r := by
      dsimp only [rowValue] at h₄
      have hprodneg : (r : ℝ) * β' < 0 := mul_neg_of_neg_of_pos hr0 hβ'0
      have hprodgt : (r : ℝ) < (r : ℝ) * β' := by
        simpa using mul_lt_mul_of_neg_left hβ'1 hr0
      nlinarith
    have hlow' : -r < s := by exact_mod_cast hlow
    have hhigh' : s < 1 - r := by exact_mod_cast hhigh
    omega

/-- **Transport of the relative minimum**: if `N ∈ SL₂(ℤ)` fixes `β` and `β'` with positive
Jacobi denominators, then no lattice point other than `N`'s bottom row `w` has
`0 < φ(u) ≤ φ(w)` and `0 < φ'(u) ≤ φ'(w)`. The vector `uN⁻¹` would violate
`eq_zero_one_of_rowValue_le_one`. -/
theorem eq_row_one_of_rowValue_le {β β' : ℝ} (hβ : 1 < β) (hβ'0 : 0 < β') (hβ'1 : β' < 1)
    {N : SL(2, ℤ)} (hfix : flt (N : Mat(2, ℤ)) β = β)
    (hfix' : flt (N : Mat(2, ℤ)) β' = β')
    (hden : 0 < fltDenominator (N : Mat(2, ℤ)) β)
    (hden' : 0 < fltDenominator (N : Mat(2, ℤ)) β') (u : Fin 2 → ℤ)
    (h₁ : 0 < rowValue u β)
    (h₂ : rowValue u β ≤ fltDenominator (N : Mat(2, ℤ)) β)
    (h₃ : 0 < rowValue u β')
    (h₄ : rowValue u β' ≤ fltDenominator (N : Mat(2, ℤ)) β') :
    u = (N : Mat(2, ℤ)) 1 := by
  let u' := Matrix.vecMul u ((N⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
  have hden0 : fltDenominator (N : Mat(2, ℤ)) β ≠ 0 := ne_of_gt hden
  have hden0' : fltDenominator (N : Mat(2, ℤ)) β' ≠ 0 := ne_of_gt hden'
  have hinvfix := flt_inv_of_flt_eq_self hden0 hfix
  have hinvfix' := flt_inv_of_flt_eq_self hden0' hfix'
  have hmul := fltDenominator_inv_mul_self_of_flt_eq_self hden0 hfix
  have hmul' := fltDenominator_inv_mul_self_of_flt_eq_self hden0' hfix'
  have hinvden : 0 < fltDenominator
      ((N⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) β := by
    nlinarith
  have hinvden' : 0 < fltDenominator
      ((N⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) β' := by
    nlinarith
  have huβ := rowValue_vecMul_of_flt_eq_self u (ne_of_gt hinvden) hinvfix
  have huβ' := rowValue_vecMul_of_flt_eq_self u (ne_of_gt hinvden') hinvfix'
  change rowValue u' β = _ at huβ
  change rowValue u' β' = _ at huβ'
  have hu' : u' = ![0, 1] := by
    apply eq_zero_one_of_rowValue_le_one hβ hβ'0 hβ'1
    · rw [huβ]
      exact mul_pos hinvden h₁
    · rw [huβ]
      nlinarith [mul_le_mul_of_nonneg_left h₂ hinvden.le]
    · rw [huβ']
      exact mul_pos hinvden' h₃
    · rw [huβ']
      nlinarith [mul_le_mul_of_nonneg_left h₄ hinvden'.le]
  have hu : u = Matrix.vecMul u' (N : Mat(2, ℤ)) := by
    calc
      u = Matrix.vecMul u (1 : Mat(2, ℤ)) := (Matrix.vecMul_one u).symm
      _ = Matrix.vecMul u (((N⁻¹ * N : SL(2, ℤ)) : SL(2, ℤ)) :
          Mat(2, ℤ)) := by rw [inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
      _ = Matrix.vecMul u (((N⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) *
          (N : Mat(2, ℤ))) := by rw [Matrix.SpecialLinearGroup.coe_mul]
      _ = Matrix.vecMul u' (N : Mat(2, ℤ)) := by
        rw [Matrix.vecMul_vecMul]
  rw [hu, hu']
  funext j
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-! ### The stabilizer

The relative-minimum property pins the bottom row of a stabilizing matrix to a sail vertex, and
the fixed-point equation then forces the vertex to be the trivial one. -/

/-- **A stabilizing matrix with `T`-shaped bottom row is trivial**: if `N ∈ SL₂(ℤ)` has bottom row
`(0, 1)` and fixes `β`, then `N = I`, because `N = T^k` and `β + k = β`. -/
theorem eq_one_of_row_one_eq_zero_one_of_flt_eq_self {β : ℝ} {N : SL(2, ℤ)}
    (hrow : (N : Mat(2, ℤ)) 1 = ![0, 1])
    (hfix : flt (N : Mat(2, ℤ)) β = β) : N = 1 := by
  have h10 : N 1 0 = 0 := congrFun hrow 0
  have h11 : N 1 1 = 1 := congrFun hrow 1
  have h00 : N 0 0 = 1 := by
    have hdet := N.2
    rw [Matrix.det_fin_two, h10, h11, mul_one, mul_zero, sub_zero] at hdet
    exact hdet
  have hN := eq_T_zpow_of_lowerLeft_eq_zero N h10 (by omega)
  have hk : N 0 1 = 0 := by
    rw [hN, flt_T_zpow] at hfix
    exact_mod_cast (by linarith : (N 0 1 : ℝ) = 0)
  rw [hN, hk, zpow_zero]

/-- **Locating a value between consecutive vertices**: if `φ(v_ℓ) < θ < φ(v_0)`, there is
`n < ℓ` with `φ(v_{n+1}) ≤ θ < φ(v_n)`. Take the least `m` with `φ(v_m) ≤ θ`; it lies in
`[1, ℓ]`. -/
theorem exists_rowValue_sailVertex_le_of_lt {β : ℝ} {ℓ : ℕ} {θ : ℝ}
    (hlow : rowValue (sailVertex β ℓ) β < θ) (hhigh : θ < rowValue (sailVertex β 0) β) :
    ∃ n < ℓ, rowValue (sailVertex β (n + 1)) β ≤ θ ∧ θ < rowValue (sailVertex β n) β := by
  let p : ℕ → Prop := fun m ↦ rowValue (sailVertex β m) β ≤ θ
  have H : ∃ m, p m := ⟨ℓ, hlow.le⟩
  let m := Nat.find H
  have hmpos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    have := Nat.find_spec H
    change p m at this
    rw [hm0] at this
    exact (not_le_of_gt hhigh) this
  have hmle : m ≤ ℓ := Nat.find_min' H hlow.le
  have hpred : m - 1 < m := by omega
  refine ⟨m - 1, lt_of_lt_of_le hpred hmle, ?_, ?_⟩
  · have hspec : p m := by exact Nat.find_spec H
    simpa [p, show m - 1 + 1 = m by omega] using hspec
  · exact lt_of_not_ge (Nat.find_min H hpred)

/-- **A period of the expansion determines a period of the rotation from an integer shift**: if
`β = β_n + k` with `k ∈ ℤ` and `β_ℓ = β`, then `β_n = β`. Rotating both sides once removes the
shift (`hjRotate_add_intCast`), so `β_{n+1} = β_1`, and `ℓ - 1` further rotations give
`β_{n+ℓ} = β_ℓ = β`, while periodicity gives `β_{n+ℓ} = β_n`. -/
theorem hjPeriod_eq_self_of_eq_add_intCast {β : ℝ} {ℓ : ℕ} (hℓpos : 0 < ℓ)
    (hℓ : hjPeriod β ℓ = β) {n : ℕ} {k : ℤ} (h : β = hjPeriod β n + k) : hjPeriod β n = β := by
  have hs : hjPeriod β (n + 1) = hjPeriod β 1 := by
    calc
      hjPeriod β (n + 1) = hjRotate (hjPeriod β n) := hjPeriod_succ β n
      _ = hjRotate (hjPeriod β n + k) := (hjRotate_add_intCast _ _).symm
      _ = hjRotate β := congrArg hjRotate h.symm
      _ = hjPeriod β 1 := by rw [hjPeriod_succ]; simp
  have hperiod := hjPeriod_add_of_hjPeriod_eq hℓ n
  calc
    hjPeriod β n = hjPeriod β (ℓ + n) := hperiod.symm
    _ = hjPeriod β ((n + 1) + (ℓ - 1)) := by
      rw [show ℓ + n = (n + 1) + (ℓ - 1) by omega]
    _ = hjPeriod (hjPeriod β (n + 1)) (ℓ - 1) := hjPeriod_add β _ _
    _ = hjPeriod (hjPeriod β 1) (ℓ - 1) := by rw [hs]
    _ = hjPeriod β (1 + (ℓ - 1)) := (hjPeriod_add β _ _).symm
    _ = hjPeriod β ℓ := by rw [show 1 + (ℓ - 1) = ℓ by omega]
    _ = β := hℓ

/-- **A vertex as bottom row forces a period**: if `N ∈ SL₂(ℤ)` fixes `β`, whose expansion has
period `ℓ ≥ 1`, and the bottom row of `N` is the vertex `v_{n+1}`, then `β_{n+1} = β`. Indeed
`N = T^k A_{0,n+1}⁻¹` (`exists_T_zpow_mul_eq_of_row_one_eq`), so `β = N·β = β_{n+1} + k`, and
`hjPeriod_eq_self_of_eq_add_intCast` removes the shift. -/
theorem hjPeriod_eq_self_of_row_one_eq_sailVertex {β : ℝ} (hβ : Irrational β) {ℓ : ℕ}
    (hℓpos : 0 < ℓ) (hℓ : hjPeriod β ℓ = β) {N : SL(2, ℤ)}
    (hfix : flt (N : Mat(2, ℤ)) β = β) {n : ℕ}
    (hrow : (N : Mat(2, ℤ)) 1 = sailVertex β (n + 1)) :
    hjPeriod β (n + 1) = β := by
  let A : SL(2, ℤ) := (hjCycleMatrix β (n + 1))⁻¹
  obtain ⟨k, hNk⟩ := exists_T_zpow_mul_eq_of_row_one_eq (M := N) (N := A) hrow
  have hAfix : flt (A : Mat(2, ℤ)) β = hjPeriod β (n + 1) := by
    simpa only [A, hjPeriod_zero] using
      (isHJCompanion_hjPeriod hβ).flt_hjCycleMatrix_inv (n + 1)
  refine hjPeriod_eq_self_of_eq_add_intCast hℓpos hℓ (k := k) ?_
  calc
    β = flt (N : Mat(2, ℤ)) β := hfix.symm
    _ = hjPeriod β (n + 1) + k := by
      rw [hNk, Matrix.SpecialLinearGroup.coe_mul,
        flt_mul _ _ β (fltDenominator_ne_zero_of_irrational hβ A),
        hAfix, flt_T_zpow]

/-- **The core of [72, Kopp (2024), Proposition 7.7, `prop:betatogamma`]**: let `β > 1` be
irrational with purely periodic expansion of minimal period `ℓ = minimalPeriod ℛ β`, and let `x`
be a companion sequence with values in `(0, 1)`. If `N ∈ SL₂(ℤ)` fixes `β` and `x_0`, with
`j_N(x_0) > 0` and `1/(β_1⋯β_ℓ) < j_N(β) ≤ 1`, then `N = I`. This is the relative-minima
argument of the file docstring; `1/(β_1⋯β_ℓ) = j_{P⁻¹}(β)` is `φ(v_ℓ)`. -/
theorem eq_one_of_flt_eq_self_of_isHJCompanion {β : ℝ} (hβ : Irrational β) (hβ1 : 1 < β)
    {x : ℕ → ℝ} (hx : IsHJCompanion β x) (hx01 : ∀ n, 0 < x n ∧ x n < 1)
    (hper : β ∈ Function.periodicPts hjRotate) {N : SL(2, ℤ)}
    (hfix : flt (N : Mat(2, ℤ)) β = β)
    (hfix' : flt (N : Mat(2, ℤ)) (x 0) = x 0)
    (hden' : 0 < fltDenominator (N : Mat(2, ℤ)) (x 0))
    (hlow : rowValue (sailVertex β (Function.minimalPeriod hjRotate β)) β <
      fltDenominator (N : Mat(2, ℤ)) β)
    (hhigh : fltDenominator (N : Mat(2, ℤ)) β ≤ 1) : N = 1 := by
  set ℓ := Function.minimalPeriod hjRotate β with hℓdef
  have hℓpos : 0 < ℓ := Function.minimalPeriod_pos_of_mem_periodicPts hper
  have hden : 0 < fltDenominator (N : Mat(2, ℤ)) β :=
    lt_trans (rowValue_sailVertex_pos hβ ℓ) hlow
  rcases hhigh.eq_or_lt with hone | hlt
  · -- `j_N(β) = 1 = φ(0, 1)`, so the bottom row of `N` is `(0, 1)`.
    apply eq_one_of_row_one_eq_zero_one_of_flt_eq_self _ hfix
    apply rowValue_injective hβ
    change fltDenominator (N : Mat(2, ℤ)) β = rowValue ![0, 1] β
    rw [rowValue_zero_one, hone]
  · -- Otherwise the bottom row is a vertex `v_{n+1}` with `n + 1 < ℓ`, contradicting minimality.
    obtain ⟨n, hnℓ, hnlow, hnhigh⟩ := exists_rowValue_sailVertex_le_of_lt hlow
      (by simpa using hlt)
    have hrow : (N : Mat(2, ℤ)) 1 = sailVertex β (n + 1) := by
      refine (eq_row_one_of_rowValue_le hβ1 (hx01 0).1 (hx01 0).2 hfix hfix' hden hden' _
        (rowValue_sailVertex_pos hβ (n + 1)) hnlow
        (rowValue_sailVertex_pos_of_isHJCompanion hx hx01 (n + 1)) ?_).symm
      exact rowValue_sailVertex_le_of_isHJCompanion hβ hx hx01 _ n hnlow hnhigh hden'
    have hper' : Function.IsPeriodicPt hjRotate (n + 1) β :=
      hjPeriod_eq_self_of_row_one_eq_sailVertex hβ hℓpos (hjPeriod_minimalPeriod β) hfix hrow
    have hnℓeq : n + 1 = ℓ := le_antisymm (by omega) (hper'.minimalPeriod_le (Nat.succ_pos n))
    have hvalue : rowValue (sailVertex β ℓ) β =
        fltDenominator (N : Mat(2, ℤ)) β := by
      rw [← hnℓeq, ← hrow]
      rfl
    exact absurd hvalue (ne_of_lt hlow)

/-- **`P` fixes the first term of a periodic companion sequence with positive Jacobi
denominator**: if `x_ℓ = x_0` then `A_{0,ℓ}·x_0 = x_0` and `j_{A_{0,ℓ}}(x_0) = x_1⋯x_ℓ > 0`. -/
theorem flt_hjCycleMatrix_apply_zero_of_isHJCompanion {β : ℝ} {x : ℕ → ℝ}
    (hx : IsHJCompanion β x) (hx01 : ∀ n, 0 < x n ∧ x n < 1) {ℓ : ℕ} (hxℓ : x ℓ = x 0) :
    flt (hjCycleMatrix β ℓ : SL(2, ℤ)) (x 0) = x 0 ∧
      0 < fltDenominator (hjCycleMatrix β ℓ : SL(2, ℤ)) (x 0) := by
  constructor
  · calc
      flt (hjCycleMatrix β ℓ : SL(2, ℤ)) (x 0) =
          flt (hjCycleMatrix β ℓ : SL(2, ℤ)) (x ℓ) := by
            rw [hxℓ]
      _ = x 0 := hx.flt_hjCycleMatrix ℓ
  · rw [← hxℓ, hx.fltDenominator_hjCycleMatrix]
    exact Finset.prod_pos fun i _ ↦ (hx01 (i + 1)).1

/-- **The unit product exceeds `1`**: `j_P(β) = β_0⋯β_{ℓ-1} > 1` for `ℓ ≥ 1`, every factor
exceeding `1`. -/
theorem one_lt_fltDenominator_hjCycleMatrix_of_hjPeriod_eq {β : ℝ} (hβ : Irrational β)
    (hβ1 : 1 < β) {ℓ : ℕ} (hℓpos : 0 < ℓ) (hℓ : hjPeriod β ℓ = β) :
    1 < fltDenominator (hjCycleMatrix β ℓ : SL(2, ℤ)) β := by
  rw [fltDenominator_hjCycleMatrix_of_hjPeriod_eq hβ hℓ]
  simpa only [Finset.prod_const_one] using
    Finset.prod_lt_prod_of_nonempty₀ (fun _ _ => (zero_lt_one : (0 : ℝ) < 1))
      (fun i _ => one_lt_hjPeriod hβ hβ1 i) (Finset.nonempty_range_iff.mpr hℓpos.ne')

/-- **The lowest vertex of a period is the reciprocal unit**: `φ(v_ℓ) = j_P(β)⁻¹` when
`β_ℓ = β`, since `φ(v_ℓ) = 1/(β_1⋯β_ℓ)` and `β_ℓ = β_0`. -/
theorem rowValue_sailVertex_of_hjPeriod_eq {β : ℝ} (hβ : Irrational β) {ℓ : ℕ}
    (hℓ : hjPeriod β ℓ = β) :
    rowValue (sailVertex β ℓ) β =
      (fltDenominator (hjCycleMatrix β ℓ : SL(2, ℤ)) β)⁻¹ := by
  have hv := rowValue_sailVertex (isHJCompanion_hjPeriod hβ) ℓ
  have hprod := fltDenominator_hjCycleMatrix hβ ℓ
  rw [hjPeriod_zero] at hv
  rw [hℓ] at hprod
  rw [hv, hprod]

/-- **[72, Kopp (2024), Proposition 7.7, `prop:betatogamma`], positive half, purely periodic
case**: with `β`, `x`, `ℓ` as in `eq_one_of_flt_eq_self_of_isHJCompanion` and `x_ℓ = x_0`,
every `M ∈ SL₂(ℤ)` fixing `β` and `x_0` with positive Jacobi denominators at both is an integer
power of the cycle matrix `P = A_{0,ℓ}`. Choose `m` with `ε^m < j_M(β) ≤ ε^{m+1}` for
`ε = j_P(β)`; then `M P^{-(m+1)}` satisfies the hypotheses of the core theorem. -/
theorem exists_zpow_eq_of_flt_eq_self_of_isHJCompanion {β : ℝ} (hβ : Irrational β)
    (hβ1 : 1 < β) {x : ℕ → ℝ} (hx : IsHJCompanion β x) (hx01 : ∀ n, 0 < x n ∧ x n < 1)
    (hper : β ∈ Function.periodicPts hjRotate)
    (hxℓ : x (Function.minimalPeriod hjRotate β) = x 0) {M : SL(2, ℤ)}
    (hfix : flt (M : Mat(2, ℤ)) β = β)
    (hfix' : flt (M : Mat(2, ℤ)) (x 0) = x 0)
    (hden : 0 < fltDenominator (M : Mat(2, ℤ)) β)
    (hden' : 0 < fltDenominator (M : Mat(2, ℤ)) (x 0)) :
    ∃ m : ℤ, M = hjCycleMatrix β (Function.minimalPeriod hjRotate β) ^ m := by
  set ℓ := Function.minimalPeriod hjRotate β with hℓdef
  set P : SL(2, ℤ) := hjCycleMatrix β ℓ with hPdef
  set ε := fltDenominator (P : Mat(2, ℤ)) β with hεdef
  have hℓ : hjPeriod β ℓ = β := hjPeriod_minimalPeriod β
  have hPfix : flt (P : Mat(2, ℤ)) β = β :=
    flt_hjCycleMatrix_of_hjPeriod_eq hβ hℓ
  obtain ⟨hPfix', hPden'⟩ := flt_hjCycleMatrix_apply_zero_of_isHJCompanion hx hx01 hxℓ
  have hε : 1 < ε := one_lt_fltDenominator_hjCycleMatrix_of_hjPeriod_eq hβ hβ1
    (Function.minimalPeriod_pos_of_mem_periodicPts hper) hℓ
  have hε0 : 0 < ε := zero_lt_one.trans hε
  obtain ⟨m, hm⟩ := exists_mem_Ioc_zpow hden hε
  -- The matrix `N = M P^{-(m+1)}` fixes `β` and `x_0`, with `j_N(β) = j_M(β) ε^{-(m+1)}`.
  have hpowden := fltDenominator_zpow_of_flt_eq_self hε0.ne' hPfix (-(m + 1))
  have hpowden' := fltDenominator_zpow_of_flt_eq_self hPden'.ne' hPfix' (-(m + 1))
  have hpowfix := flt_zpow_of_flt_eq_self hε0.ne' hPfix (-(m + 1))
  have hpowfix' := flt_zpow_of_flt_eq_self hPden'.ne' hPfix' (-(m + 1))
  have hpowden0 := hpowden ▸ zpow_ne_zero (-(m + 1)) hε0.ne'
  have hpowden0' := hpowden' ▸ zpow_ne_zero (-(m + 1)) hPden'.ne'
  have hNden : fltDenominator ((M * P ^ (-(m + 1)) : SL(2, ℤ)) : Mat(2, ℤ)) β =
      fltDenominator (M : Mat(2, ℤ)) β / ε ^ (m + 1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul,
      fltDenominator_mul_of_flt_eq_self hpowfix hpowden0, hpowden, zpow_neg,
      div_eq_mul_inv]
  have hpowpos : 0 < ε ^ (m + 1) := zpow_pos hε0 _
  have hNone : M * P ^ (-(m + 1)) = 1 := by
    refine eq_one_of_flt_eq_self_of_isHJCompanion hβ hβ1 hx hx01 hper ?_ ?_ ?_ ?_ ?_
    · rw [Matrix.SpecialLinearGroup.coe_mul]
      exact flt_mul_of_flt_eq_self hfix hpowfix hpowden0
    · rw [Matrix.SpecialLinearGroup.coe_mul]
      exact flt_mul_of_flt_eq_self hfix' hpowfix' hpowden0'
    · rw [Matrix.SpecialLinearGroup.coe_mul,
        fltDenominator_mul_of_flt_eq_self hpowfix' hpowden0', hpowden']
      exact mul_pos hden' (zpow_pos hPden' _)
    · rw [rowValue_sailVertex_of_hjPeriod_eq hβ hℓ, hNden, lt_div_iff₀ hpowpos, ← hεdef,
        ← zpow_neg_one, ← zpow_add₀ hε0.ne', show -1 + (m + 1) = m by ring]
      exact hm.1
    · rw [hNden, div_le_one hpowpos]
      exact hm.2
  rw [zpow_neg] at hNone
  exact ⟨m + 1, mul_inv_eq_one.mp hNone⟩

end SIC
