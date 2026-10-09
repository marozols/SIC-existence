/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import SICs.MatrixNotation

/-!
# Elementary integer matrices and the modular group

Elementary `SL₂(ℤ)` matrix identities, translations, congruence subgroups, and trace recurrences.

These are the matrix-algebra ingredients used by the modular cocycle and quadratic stabilizers.
A determinant-one matrix with positive top-left entry and zero lower-left entry is a translation;
two matrices with the same bottom row differ by a translation. Cayley--Hamilton expresses all
powers through the trace recurrence. Membership in a principal congruence subgroup is an
entrywise congruence condition.

The translation case is the base case in [AFK25, Appendix C, Theorem C.4, `thm:tsaltexpn`].
The Möbius action and its Jacobi denominator are developed separately in
`SICs.SL2Z.FractionalLinear`.
-/

open ModularGroup
open scoped MatrixGroups

namespace SIC

/-! ### Determinants and translations

The determinant condition controls the diagonal of a triangular matrix. Applying this to
`M N⁻¹` identifies matrices with the same bottom row up to left translation. -/

/-- The determinant identity `M₀₀M₁₁ - M₀₁M₁₀ = 1` of a determinant-one matrix, cast into a
ring `R`. It clears denominators in the Möbius identities below. -/
theorem det_fin_two_cast_eq_one {R : Type*} [Ring R] (M : SL(2, ℤ)) :
    (M 0 0 : R) * M 1 1 - M 0 1 * M 1 0 = 1 := by
  have h := congrArg (Int.cast : ℤ → R) M.2
  rw [Matrix.det_fin_two] at h
  push_cast at h
  exact h

/-- Every element of `GL₂(ℤ)` has determinant `1` or `-1` as an integer matrix. -/
theorem gl_det_eq_one_or_neg_one (M : GL (Fin 2) ℤ) :
    (M : Mat(2, ℤ)).det = 1 ∨
      (M : Mat(2, ℤ)).det = -1 :=
  Int.isUnit_iff.mp (Matrix.GeneralLinearGroup.det M).isUnit

/-- A matrix with lower-left entry `0` is a pure power of `T`, provided its top-left entry is
positive (ruling out the other unit root `-1`, which would instead give `-T^k`). This is
[AFK25]'s own `c = 0` case. -/
theorem eq_T_zpow_of_lowerLeft_eq_zero (M : SL(2, ℤ)) (h0 : M 1 0 = 0) (ha : 0 < M 0 0) :
    M = T ^ (M 0 1) := by
  have hdet : (M : Mat(2, ℤ)).det = 1 := M.2
  rw [Matrix.det_fin_two, h0, mul_zero, sub_zero] at hdet
  have h1 : M 0 0 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h
    · exact h
    · omega
  have h11 : M 1 1 = 1 := by rw [h1] at hdet; linarith
  ext i j
  simp only [coe_T_zpow]
  fin_cases i <;> fin_cases j <;> simp_all

/-- The bottom row of `M N⁻¹` is `(0, 1)` when `M` and `N` have the same bottom row. -/
private theorem mul_inv_bottom_row_of_row_one_eq {M N : SL(2, ℤ)} (h : M 1 = N 1) :
    (M * N⁻¹) 1 0 = 0 ∧ (M * N⁻¹) 1 1 = 1 := by
  have h10 : M 1 0 = N 1 0 := congrFun h 0
  have h11 : M 1 1 = N 1 1 := congrFun h 1
  have hinv00 : (N⁻¹) 0 0 = N 1 1 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    rfl
  have hinv10 : (N⁻¹) 1 0 = -N 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    rfl
  have hinv01 : (N⁻¹) 0 1 = -N 0 1 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    rfl
  have hinv11 : (N⁻¹) 1 1 = N 0 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    rfl
  constructor
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      hinv00, hinv10, h10, h11]
    ring
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      hinv01, hinv11, h10, h11]
    have hdet := Matrix.SpecialLinearGroup.det_coe N
    rw [Matrix.det_fin_two] at hdet
    nlinarith

/-- **Two determinant-one matrices with the same bottom row differ by a power of `T` on the
left**: `M = T^k N` with `k = (M N⁻¹) 0 1`. The product `M N⁻¹` has bottom row `(0, 1)`, so
`eq_T_zpow_of_lowerLeft_eq_zero` applies to it. Used to recover a stabilizing matrix from its
bottom row in `SICs.SL2Z.HJStabilizer`. -/
theorem exists_T_zpow_mul_eq_of_row_one_eq {M N : SL(2, ℤ)} (h : M 1 = N 1) :
    ∃ k : ℤ, M = T ^ k * N := by
  obtain ⟨hP10, hP11⟩ := mul_inv_bottom_row_of_row_one_eq h
  have hP00 : (M * N⁻¹) 0 0 = 1 := by
    have hdet := Matrix.SpecialLinearGroup.det_coe (M * N⁻¹)
    rw [Matrix.det_fin_two, hP10, hP11] at hdet
    simpa using hdet
  let k : ℤ := (M * N⁻¹) 0 1
  have hP : M * N⁻¹ = T ^ k :=
    eq_T_zpow_of_lowerLeft_eq_zero (M * N⁻¹) hP10 (by rw [hP00]; decide)
  exact ⟨k, eq_mul_of_mul_inv_eq hP⟩

namespace SL2Z

/-! ### The principal congruence subgroup

Mathlib defines the subgroup through reduction to `SL(2, ZMod d)`. The following entrywise form is
the interface used by the stability-group developments.
-/

/-- Mathlib uses `CongruenceSubgroup.Gamma d` for the determinant-one integer matrices that look
like the identity matrix when their entries are considered modulo `d`.  This lemma spells out that
membership condition using integer congruences: `M 0 0` and `M 1 1` must be congruent to `1`, while
`M 0 1` and `M 1 0` must be congruent to `0`, all modulo `d`.  The identity matrix on the right-hand
side packages these four conditions into one entrywise statement. -/
lemma gamma_mem_iff_modEq {d : ℕ} {M : SL(2, ℤ)} :
    M ∈ CongruenceSubgroup.Gamma d ↔
      ∀ i j, M i j ≡ (1 : Mat(2, ℤ)) i j [ZMOD (d : ℤ)] := by
  rw [CongruenceSubgroup.Gamma_mem', Matrix.SpecialLinearGroup.ext_iff]
  constructor
  · intro h i j
    apply (ZMod.intCast_eq_intCast_iff (M i j)
      ((1 : Mat(2, ℤ)) i j) d).mp
    simpa [SL_reduction_mod_hom_val, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply] using h i j
  · intro h i j
    have hij := (ZMod.intCast_eq_intCast_iff (M i j)
      ((1 : Mat(2, ℤ)) i j) d).mpr (h i j)
    simpa [SL_reduction_mod_hom_val, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply] using hij

/-! ### Inversion

For determinant-one `2 × 2` matrices, the adjugate formula gives the inverse explicitly; in
particular inversion negates the lower-left entry.
-/

/-- Inversion negates the lower-left entry of a determinant-one matrix. -/
@[simp]
lemma lowerLeft_inv (M : SL(2, ℤ)) :
    (M⁻¹) 1 0 = -M 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  rfl

/-! ### Powers and the trace recursion

In two dimensions the Cayley--Hamilton theorem reads `M² = (Tr M) M - (det M) I`, so on
`SL(2, ℤ)` every power of `M` is an integer combination of `M` and `I`.  The coefficients are the
values of the three-term recursion `r_{n+2} = (Tr M) r_{n+1} - r_n` started at `r₀ = 0`, `r₁ = 1`.
That sequence is a parameter of `pow_succ_eq_smul_sub_smul` below, so a caller may supply a
sequence already built for other reasons; the rank grid `r_{j,m}` of
`SICs.Quadratic.DimensionGrids` is one such sequence.
-/

/-- **Cayley--Hamilton on `SL(2, ℤ)`:** `M² = (Tr M) M - I`.

This specializes Mathlib's `Matrix.aeval_self_charpoly` using `Matrix.charpoly_fin_two`
and `det M = 1`. -/
lemma sq_eq_trace_smul_sub_one (M : SL(2, ℤ)) :
    (M : Mat(2, ℤ)) ^ 2 =
      Matrix.trace (M : Mat(2, ℤ)) • (M : Mat(2, ℤ)) - 1 := by
  have h := Matrix.aeval_self_charpoly (M : Mat(2, ℤ))
  rw [Matrix.charpoly_fin_two, M.2] at h
  simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
    Matrix.one_mul, one_smul] at h
  rw [sub_add_eq_add_sub, sub_eq_zero] at h
  exact eq_sub_of_add_eq h

/-- For a determinant-one matrix, `M⁻¹ = (Tr M) I - M`. This is the inverse form of
`sq_eq_trace_smul_sub_one`. -/
lemma inv_eq_trace_smul_sub (M : SL(2, ℤ)) :
    ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) =
      Matrix.trace (M : Mat(2, ℤ)) • (1 : Mat(2, ℤ)) - (M : Mat(2, ℤ)) := by
  change (M : Mat(2, ℤ)).adjugate = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.intCast_apply,
      Matrix.sub_apply]

/-- **The powers of a matrix in `SL(2, ℤ)` along its trace recursion:**
`Mⁿ⁺¹ = r_{n+1} M - r_n I`, for any sequence `r` with `r₀ = 0`, `r₁ = 1` and
`r_{n+2} = (Tr M) r_{n+1} - r_n`.

The induction step needs only `sq_eq_trace_smul_sub_one`, since `Mⁿ⁺² = (r_{n+1} M - r_n I) M`
replaces `M²` by its Cayley--Hamilton value. -/
lemma pow_succ_eq_smul_sub_smul (M : SL(2, ℤ)) {r : ℕ → ℤ} (h0 : r 0 = 0) (h1 : r 1 = 1)
    (hrec : ∀ n, r (n + 2) =
      Matrix.trace (M : Mat(2, ℤ)) * r (n + 1) - r n) (n : ℕ) :
    (M : Mat(2, ℤ)) ^ (n + 1) =
      r (n + 1) • (M : Mat(2, ℤ)) - r n • 1 := by
  induction n with
  | zero => simp [h0, h1]
  | succ n ih =>
      rw [pow_succ, ih, sub_mul, smul_mul_assoc, smul_mul_assoc, Matrix.one_mul, ← pow_two,
        sq_eq_trace_smul_sub_one, hrec n]
      module

end SL2Z
end SIC
