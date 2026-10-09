/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.FormActions

/-!
# Integral Coordinates of Form Stabilizers

The integral doubled decomposition `2M = Tr(M)I + n(2SQ)` of the matrices commuting with `SQ`.

This file follows the decomposition clause of [AFK25, Theorem 4.37, `tm:sqchar`]. For a
primitive integral form `Q = ⟨a,b,c⟩`, every matrix commuting with `SQ` has an expression
`M = (t/2)I + nSQ` with integral `t,n`. We use the doubled equation to avoid rational matrices.

Writing `M = [[A,B],[C,D]]`, commutation gives
`aB + cC = 0`, `bC = a(D-A)`, and `bB = c(A-D)`. A Bézout relation
`xa + yb + zc = 1` then gives the integral coefficient `n = xC + y(D-A) - zB`.
Thus `C = na`, `D-A = nb`, and `B = -nc`. This is the coefficientwise version of the source's
linear-combination argument and its use of primitivity. The trace determines `t`. Conversely,
every integral combination of `I` and `SQ` commutes with `SQ`. No irreducibility or
indefiniteness is needed in this section of the source.

The proof of Theorem 4.37(2) says its scalar coefficient is nonzero; it must allow zero when
`M = ±I`. The coefficient equations used here include these cases.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC.BinaryQF

/-! ### Primitive coefficients and commutation

The integral Bézout relation is the only arithmetic input to the source's decomposition. -/

/-- A primitive form has a Bézout relation `xa + yb + zc = 1` among its coefficients. -/
lemma IsPrimitive.exists_linear_combination {Q : BinaryQF} (hQ : Q.IsPrimitive) :
    ∃ x y z : ℤ, x * Q.a + y * Q.b + z * Q.c = 1 := by
  have hab := Int.gcd_eq_gcd_ab Q.a Q.b
  have habc := Int.gcd_eq_gcd_ab (Int.gcd Q.a Q.b) Q.c
  rw [show Int.gcd (Int.gcd Q.a Q.b) Q.c = 1 from hQ] at habc
  refine ⟨Int.gcdA (Int.gcd Q.a Q.b) Q.c * Int.gcdA Q.a Q.b,
    Int.gcdA (Int.gcd Q.a Q.b) Q.c * Int.gcdB Q.a Q.b,
    Int.gcdB (Int.gcd Q.a Q.b) Q.c, ?_⟩
  nth_rw 1 [hab] at habc
  norm_num only [Int.natCast_one] at habc
  linear_combination -habc

/-- The coefficient equations of `Commute Q.twiceSQ M`, used to construct the integral
coordinate in `IsPrimitive.exists_stabilizer_coordinates`. -/
private lemma commute_twiceSQ_entries {Q : BinaryQF}
    {M : Mat(2, ℤ)} (hM : Commute Q.twiceSQ M) :
    Q.a * M 0 1 + Q.c * M 1 0 = 0 ∧
      Q.b * M 1 0 = Q.a * (M 1 1 - M 0 0) ∧
      Q.b * M 0 1 = Q.c * (M 0 0 - M 1 1) := by
  have h00 := congrArg (fun A : Mat(2, ℤ) ↦ A 0 0) hM.eq
  have h10 := congrArg (fun A : Mat(2, ℤ) ↦ A 1 0) hM.eq
  have h01 := congrArg (fun A : Mat(2, ℤ) ↦ A 0 1) hM.eq
  simp [twiceSQ, Matrix.mul_apply, Fin.sum_univ_two] at h00 h10 h01
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Integral coordinates `C = na`, `D-A = nb`, and `B = -nc` for a matrix commuting with `SQ`.
This is the coefficient step in `IsPrimitive.commute_twiceSQ_iff`. -/
private lemma IsPrimitive.exists_stabilizer_coordinates {Q : BinaryQF}
    (hQ : Q.IsPrimitive) {M : Mat(2, ℤ)} (hM : Commute Q.twiceSQ M) :
    ∃ n : ℤ, M 1 0 = n * Q.a ∧ M 1 1 - M 0 0 = n * Q.b ∧ M 0 1 = -n * Q.c := by
  obtain ⟨x, y, z, hxyz⟩ := hQ.exists_linear_combination
  obtain ⟨h1, h2, h3⟩ := commute_twiceSQ_entries hM
  refine ⟨x * M 1 0 + y * (M 1 1 - M 0 0) - z * M 0 1, ?_, ?_, ?_⟩
  · linear_combination -M 1 0 * hxyz + z * h1 + y * h2
  · linear_combination -(M 1 1 - M 0 0) * hxyz - x * h2 + z * h3
  · linear_combination -M 0 1 * hxyz + x * h1 + y * h3

/-! ### The doubled decomposition

The decomposition uses the trace as its first coordinate. Its converse follows by commuting
scalar matrices and `SQ`, and is valid even for matrices with zero determinant. -/

/-- For a primitive form, a matrix commutes with `SQ` exactly when it has an integral doubled
expression `2M = Tr(M)I + n(2SQ)`. This is the integral normalization of
[AFK25, Theorem 4.37(3), `tm:sqchar`], without the unnecessary invertibility hypothesis, together
with its converse. -/
lemma IsPrimitive.commute_twiceSQ_iff {Q : BinaryQF} (hQ : Q.IsPrimitive)
    {M : Mat(2, ℤ)} :
    Commute Q.twiceSQ M ↔
      ∃ n : ℤ, (2 : ℤ) • M = Matrix.trace M • (1 : Mat(2, ℤ)) +
        n • Q.twiceSQ := by
  constructor
  · intro hM
    obtain ⟨n, ha, hb, hc⟩ := hQ.exists_stabilizer_coordinates hM
    refine ⟨n, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;>
      simp [twiceSQ, Matrix.trace_fin_two] <;> nlinarith
  · rintro ⟨n, hn⟩
    have hc : Q.twiceSQ * ((2 : ℤ) • M) = ((2 : ℤ) • M) * Q.twiceSQ := by
      rw [hn]
      simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul]
    apply smul_right_injective _ (two_ne_zero : (2 : ℤ) ≠ 0)
    simpa only [Matrix.mul_smul, Matrix.smul_mul] using hc

/-- The trace coordinate in `2M = tI + n(2SQ)` is necessarily `t = Tr(M)`. -/
lemma trace_eq_of_twice_eq {Q : BinaryQF} {M : Mat(2, ℤ)} {t n : ℤ}
    (hM : (2 : ℤ) • M = t • (1 : Mat(2, ℤ)) + n • Q.twiceSQ) :
    Matrix.trace M = t := by
  have h00 := congrArg (fun A : Mat(2, ℤ) ↦ A 0 0) hM
  have h11 := congrArg (fun A : Mat(2, ℤ) ↦ A 1 1) hM
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h00 h11
  simp [twiceSQ] at h00 h11
  rw [Matrix.trace_fin_two]
  omega

end SIC.BinaryQF

end
