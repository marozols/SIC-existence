/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Quadratic.Forms
import SICs.Quadratic.FormActions
import SICs.SL2Z.DedekindReciprocity

/-!
# Explicit Stabilizers for the Principal Rank-One Forms

`U_d`, `A_d = U_d³`, their congruences, and the Jacobi factor `j_{A_d}(ρ_d) = ρ_d³`.

For the principal form `Q_d = ⟨1, 1 - d, 1⟩`, this file studies the explicit matrix

`U_d = [[d - 1, -1], [1, 0]] = T^(d - 1) S`

and its cube `A_d = U_d³`.  We prove directly that both matrices fix the positive root `ρ_d` of
`Q_d`, that the Jacobi factor of `A_d` at `ρ_d` is `ρ_d³`, that `A_d` lies in the principal
congruence subgroup `Γ(d)`, and we evaluate the Rademacher invariant of `A_d`.

These elementary results do not assert that `U_d` generates the stability group modulo `{±I}`,
or that `A_d` is the distinguished generator of the level stability group.

## Main definitions

- `principalU`: the determinant-one matrix `[[d - 1, -1], [1, 0]]`.
- `principalA`: the cube `principalU d ^ 3`.
- `principalA_eq_T_zpow_mul_S_word`: `A_d` as the six-letter modular word
  `T^(d-1) S T^(d-1) S T^(d-1) S`.
- `flt_principalU_principalRoot` and `flt_principalU_sq_principalRoot`: `U_d` and `U_d²` fix `ρ_d`.
- `fltDenominator_principalU_principalRoot` and `fltDenominator_principalU_sq_principalRoot`:
  `j_{U_d}(ρ_d) = ρ_d` and `j_{U_d²}(ρ_d) = ρ_d²`.
- `principalJacobiFactor`: the Jacobi factor `j_{A_d}(ρ_d) = d(d - 2)ρ_d + (1 - d) = ρ_d³`, with
  `principalJacobiFactor_add_inv`, `j + j⁻¹ = Tr(A_d)`.
- `principalUMod`: reduction of `principalU` modulo `d`.

## References

- [AFK25, Definition 1.28, `dfn:AssociatedStabilizers`] for the associated stabilizers
- [AFK25, Theorem 4.50, `tm:symgp`] for their arithmetic description and congruences
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The positive stabilizer

The matrix `U_d = [[d-1,-1],[1,0]]` is the explicit positive determinant-one stabilizer of
`Q_d`. This section records its entries and square, its modular-group word, and the
fixed-point and Jacobi-denominator identities for `U_d` and `U_d²`.
-/

/-- The explicit determinant-one matrix `U_d = [[d - 1, -1], [1, 0]]` attached to the
principal form.  No generator claim is part of this definition. -/
def principalU (d : ℕ) : SL(2, ℤ) :=
  ⟨!![(d : ℤ) - 1, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

/-- The underlying integer matrix of `principalU`. -/
@[simp]
lemma coe_principalU (d : ℕ) :
    (principalU d : Mat(2, ℤ)) =
      !![(d : ℤ) - 1, -1; 1, 0] :=
  rfl

/-- The underlying matrix of `U_d²`, the first intermediate matrix of the word walk. Not marked
`@[simp]`: `Matrix.SpecialLinearGroup.coe_pow` is already simp, so tagging this would leave two
competing normal forms for the same matrix. -/
lemma coe_principalU_sq (d : ℕ) :
    ((principalU d ^ 2 : SL(2, ℤ)) : Mat(2, ℤ)) =
      !![(d : ℤ) ^ 2 - 2 * d, 1 - (d : ℤ); (d : ℤ) - 1, -1] := by
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_principalU]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg, mul_comm]
  ring

/-- The principal matrix is the two-factor modular word `T^(d - 1) S`. -/
lemma principalU_eq_T_zpow_mul_S (d : ℕ) :
    principalU d = ModularGroup.T ^ ((d : ℤ) - 1) * ModularGroup.S := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [principalU, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]

/-- The Möbius expression for `principalU d` fixes the principal root. -/
lemma principalU_fixes_principalRoot (d : ℕ) (hd : d > 3) :
    (((d : ℝ) - 1) * principalRoot d - 1) / principalRoot d = principalRoot d := by
  have hroot : principalRoot d ≠ 0 := ne_of_gt
    (lt_trans Real.zero_lt_one (one_lt_principalRoot d hd))
  field_simp
  nlinarith [principalRoot_satisfies_quadratic d hd]

/-- The principal stabilizer's Jacobi denominator at the principal root is the root itself:
`U_d`'s lower row `(1, 0)` gives `j_{U_d}(ρ_d) = 1 · ρ_d + 0`. -/
theorem fltDenominator_principalU_principalRoot (d : ℕ) :
    fltDenominator (principalU d : Mat(2, ℤ)) (principalRoot d) =
      principalRoot d := by
  simp [fltDenominator, coe_principalU]

/-- The Jacobi denominator of `U_d` is positive at `ρ_d`; used by
`SICs.Principal.Dilogarithm.Values`. -/
lemma fltDenominator_principalU_principalRoot_pos (d : ℕ) (hd : 3 < d) :
    0 < fltDenominator (principalU d : Mat(2, ℤ)) (principalRoot d) := by
  rw [fltDenominator_principalU_principalRoot]
  exact principalRoot_pos d hd

/-- `j_{U_d²}(ρ_d) = ρ_d²`, by the defining quadratic `ρ_d² = (d-1)ρ_d - 1`. -/
lemma fltDenominator_principalU_sq_principalRoot (d : ℕ) (hd : 3 < d) :
    fltDenominator ((principalU d ^ 2 : SL(2, ℤ)) : Mat(2, ℤ))
      (principalRoot d) = principalRoot d ^ 2 := by
  have hq := principalRoot_satisfies_quadratic d hd
  rw [fltDenominator, coe_principalU_sq]
  norm_num
  linarith

/-- `U_d·ρ_d = ρ_d`, the defining fixed-point property, in `flt` form. -/
lemma flt_principalU_principalRoot (d : ℕ) (hd : 3 < d) :
    flt ((principalU d : SL(2, ℤ)) : Mat(2, ℤ)) (principalRoot d) =
      principalRoot d := by
  simpa [flt, coe_principalU, sub_eq_add_neg] using principalU_fixes_principalRoot d hd

/-- The complex embedding of the fixed-point identity `U_d·ρ_d=ρ_d`; used by the
principal-root and boundary-continuity bridges. -/
lemma flt_principalU_principalRoot_complex (d : ℕ) (hd : 3 < d) :
    flt (principalU d : Mat(2, ℤ)) (principalRoot d : ℂ) = principalRoot d := by
  rw [← ofReal_flt]
  exact_mod_cast flt_principalU_principalRoot d hd

/-- `U_d²·ρ_d = ρ_d`: `U_d` fixes `ρ_d`, hence so does its square. -/
lemma flt_principalU_sq_principalRoot (d : ℕ) (hd : 3 < d) :
    flt ((principalU d ^ 2 : SL(2, ℤ)) : Mat(2, ℤ)) (principalRoot d) =
      principalRoot d := by
  apply flt_pow_of_flt_eq_self ?_ (flt_principalU_principalRoot d hd)
  rw [fltDenominator_principalU_principalRoot]
  exact (principalRoot_pos d hd).ne'

/-! ### The level matrix

The associated level generator is the cube `A_d = U_d³`, as prescribed in rank one. Its explicit
entries and word decomposition drive the cocycle and congruence calculations downstream.
-/

/-- The explicit level-stabilizer candidate `A_d = U_d³`.  This definition makes no claim that
it is the distinguished generator of the level stability group. -/
def principalA (d : ℕ) : SL(2, ℤ) :=
  principalU d ^ 3

/-- `U_d` commutes with `A_d = U_d³`, in conjugation form; used by
`SICs.Principal.Dilogarithm.Values`. -/
lemma principalU_mul_principalA_mul_inv (d : ℕ) :
    principalU d * principalA d * (principalU d)⁻¹ = principalA d := by
  change principalU d * principalU d ^ 3 * (principalU d)⁻¹ = principalU d ^ 3
  group

/-- The underlying matrix of `A_d` has the explicit polynomial formula from the
principal-family calculation. -/
@[simp]
lemma coe_principalA (d : ℕ) :
    (principalA d : Mat(2, ℤ)) =
      !![((d : ℤ) - 1) * ((d : ℤ) ^ 2 - 2 * d - 1),
          -(d : ℤ) * ((d : ℤ) - 2);
        (d : ℤ) * ((d : ℤ) - 2), 1 - (d : ℤ)] := by
  rw [principalA, Matrix.SpecialLinearGroup.coe_pow, coe_principalU]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- The lower-left entry `d(d-2)` of the principal matrix `A_d` is strictly positive for
`d > 3`. -/
lemma principalA_lowerLeft_pos (d : ℕ) (hd : 3 < d) : 0 < (principalA d) 1 0 := by
  have hd4 : (4 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  rw [show (principalA d) 1 0 = (d : ℤ) * ((d : ℤ) - 2) from by simp [coe_principalA]]
  nlinarith

/-- The lower-left entry `d(d-2)` of the principal matrix `A_d` is nonnegative for `d > 3`. -/
lemma principalA_lowerLeft_nonneg (d : ℕ) (hd : 3 < d) : 0 ≤ (principalA d) 1 0 :=
  (principalA_lowerLeft_pos d hd).le

/-- The cube `A_d` is the six-letter modular word `T^(d-1) S T^(d-1) S T^(d-1) S`, obtained by
substituting `principalU_eq_T_zpow_mul_S` into each of the three factors of `U_d³` and clearing
parentheses. This is the three-factor word decomposition of `A_{t_d}`: it exposes `A_d`
as a product of the elementary generators `T` and `S`, ready for cocycle relations to be applied
one letter at a time. -/
lemma principalA_eq_T_zpow_mul_S_word (d : ℕ) :
    principalA d =
      ModularGroup.T ^ ((d : ℤ) - 1) * ModularGroup.S *
        (ModularGroup.T ^ ((d : ℤ) - 1) * ModularGroup.S) *
        (ModularGroup.T ^ ((d : ℤ) - 1) * ModularGroup.S) := by
  rw [principalA, principalU_eq_T_zpow_mul_S, pow_succ, pow_two]

/-- The determinant of the underlying matrix of `principalA` is one. -/
lemma det_principalA (d : ℕ) :
    (principalA d : Mat(2, ℤ)).det = 1 :=
  (principalA d).property

/-- The trace of `principalA d` is `d²(d - 3) + 2`. -/
lemma trace_principalA (d : ℕ) :
    Matrix.trace (principalA d : Mat(2, ℤ)) =
      (d : ℤ) ^ 2 * ((d : ℤ) - 3) + 2 := by
  rw [coe_principalA, Matrix.trace_fin_two]
  simp
  ring

/-- The order `N = d²(d - 3)` of the group `G_d`: `N + 2 = tr A_d`, in the notation of
[RW26, Radchenko, Wheeler (2026), Section 1]. -/
def principalDilogOrder (d : ℕ) : ℕ :=
  d ^ 2 * (d - 3)

/-- `det(A_d - I) = -N` for `N = d²(d - 3)`. -/
lemma det_principalA_sub_one (d : ℕ) (hd : 3 < d) :
    ((principalA d : Mat(2, ℤ)) - 1).det = -(principalDilogOrder d : ℤ) := by
  unfold principalDilogOrder
  simp only [Matrix.det_fin_two, Matrix.sub_apply, Matrix.one_apply]
  simp only [Fin.isValue, coe_principalA, neg_mul, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
    ↓reduceIte, Matrix.cons_val_one, sub_sub_cancel_left, mul_neg,
    zero_ne_one, sub_zero, one_ne_zero, sub_neg_eq_add,
    Nat.cast_mul, Nat.cast_pow]
  rw [Nat.cast_sub (by omega : 3 ≤ d)]
  ring

/-- The trace of `principalA d` is positive when `d > 3`. -/
lemma zero_lt_trace_principalA (d : ℕ) (hd : d > 3) :
    0 < Matrix.trace (principalA d : Mat(2, ℤ)) := by
  rw [trace_principalA]
  have hd3 : 0 ≤ (d : ℤ) - 3 := by omega
  have hnonneg : 0 ≤ (d : ℤ) ^ 2 * ((d : ℤ) - 3) :=
    mul_nonneg (sq_nonneg _) hd3
  omega

/-! ### The Jacobi factor at the fixed point

The principal root is fixed by `A_d`, and the corresponding Jacobi denominator is `ρ_d³`.
These identities specialize the inverse-cocycle relation at the quadratic fixed point.
-/

/-- The Jacobi factor `j_{A_d}(ρ_d) = d(d - 2)ρ_d + (1 - d)` of the level matrix `A_d = U_d³` at
its fixed point `ρ_d`, written out from the lower row of `coe_principalA`. -/
def principalJacobiFactor (d : ℕ) : ℝ :=
  (d : ℝ) * ((d : ℝ) - 2) * principalRoot d + (1 - (d : ℝ))

/-- `j_{A_d}(ρ_d) = d(d-2)ρ_d + (1-d)`: the explicit formula agrees with the general Jacobi
denominator `fltDenominator` at `M = A_d`, `τ = ρ_d`. -/
lemma fltDenominator_principalA_principalRoot (d : ℕ) :
    fltDenominator (principalA d : Mat(2, ℤ)) (principalRoot d) =
      principalJacobiFactor d := by
  rw [fltDenominator, coe_principalA, principalJacobiFactor]
  simp

/-- The Jacobi factor exceeds one in every dimension `d > 3`: it is at least
`d(d - 2) - (d - 1) = d² - 3d + 1 ≥ 5`, since `ρ_d > 1`. -/
lemma one_lt_principalJacobiFactor (d : ℕ) (hd : 3 < d) : 1 < principalJacobiFactor d := by
  have hroot : 1 < principalRoot d := one_lt_principalRoot d hd
  have hdreal : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hfac : 0 < (d : ℝ) * ((d : ℝ) - 2) := by nlinarith
  rw [principalJacobiFactor]
  nlinarith

/-- The Jacobi factor is positive. -/
lemma principalJacobiFactor_pos (d : ℕ) (hd : 3 < d) : 0 < principalJacobiFactor d :=
  lt_trans zero_lt_one (one_lt_principalJacobiFactor d hd)

/-- The Jacobi denominator of `A_d` is positive at `ρ_d`; used by
`SICs.Principal.Dilogarithm.Values`. -/
lemma fltDenominator_principalA_principalRoot_pos (d : ℕ) (hd : 3 < d) :
    0 < fltDenominator (principalA d : Mat(2, ℤ)) (principalRoot d) := by
  rw [fltDenominator_principalA_principalRoot]
  exact principalJacobiFactor_pos d hd

/-- The Jacobi factor is nonzero. -/
lemma principalJacobiFactor_ne_zero (d : ℕ) (hd : 3 < d) : principalJacobiFactor d ≠ 0 :=
  ne_of_gt (principalJacobiFactor_pos d hd)

/-- **`j_{A_d}(ρ_d) = ρ_d³`.** The closed form `d(d-2)ρ_d + (1-d)` is the minimal polynomial
`ρ_d² - (d-1)ρ_d + 1 = 0` multiplied by `ρ_d + d - 1`; equivalently, substituting
`ρ_d² = (d-1)ρ_d - 1` twice into `ρ_d³ = ρ_d·ρ_d²` reproduces it exactly. -/
lemma principalJacobiFactor_eq_principalRoot_pow_three (d : ℕ) (hd : 3 < d) :
    principalJacobiFactor d = principalRoot d ^ 3 := by
  have hq := principalRoot_satisfies_quadratic d hd
  rw [principalJacobiFactor]
  linear_combination -(principalRoot d + (d : ℝ) - 1) * hq

/-- The principal unit $\varepsilon=\rho_d^3$ is larger than one. -/
lemma one_lt_principalRoot_pow_three (d : ℕ) (hd : 3 < d) :
    1 < principalRoot d ^ 3 := by
  simpa only [← principalJacobiFactor_eq_principalRoot_pow_three d hd] using
    one_lt_principalJacobiFactor d hd

/-- The principal unit satisfies $\rho_d^3=d(d-2)\rho_d+1-d$. -/
lemma principalRoot_pow_three_eq (d : ℕ) (hd : 3 < d) :
    principalRoot d ^ 3 =
      (d : ℝ) * ((d : ℝ) - 2) * principalRoot d + (1 - (d : ℝ)) := by
  simpa only [principalJacobiFactor] using
    (principalJacobiFactor_eq_principalRoot_pow_three d hd).symm

/-- The principal unit satisfies that $\rho_d^3-1$ is irrational. -/
lemma principalRoot_pow_three_sub_one_irrational (d : ℕ) (hd : 3 < d) :
    Irrational (principalRoot d ^ 3 - 1) := by
  let c : ℤ := (principalA d) 1 0
  have hc : c ≠ 0 := ne_of_gt (principalA_lowerLeft_pos d hd)
  have hρ : Irrational (principalRoot d) := principalRoot_irrational d hd
  have hlin : principalRoot d ^ 3 - 1 = (c : ℝ) * principalRoot d - d := by
    rw [principalRoot_pow_three_eq d hd]
    simp [c, coe_principalA]
    ring
  rw [hlin]
  exact (hρ.intCast_mul hc).sub_intCast d

/-- Over `ℂ`, the principal Jacobi denominator at the positive fixed point is still `ρ_d³`. -/
lemma fltDenominator_principalA_principalRoot_complex (d : ℕ) (hd : 3 < d) :
    fltDenominator (principalA d : Mat(2, ℤ)) (principalRoot d : ℂ) =
      (principalRoot d : ℂ) ^ 3 := by
  exact_mod_cast (calc
    fltDenominator (principalA d : Mat(2, ℤ)) (principalRoot d) =
        principalJacobiFactor d := fltDenominator_principalA_principalRoot d
    _ = principalRoot d ^ 3 := principalJacobiFactor_eq_principalRoot_pow_three d hd)

/-- The complex principal Jacobi denominator at the positive fixed point is nonzero. -/
lemma fltDenominator_principalA_principalRoot_ne_zero (d : ℕ) (hd : 3 < d) :
    fltDenominator (principalA d : Mat(2, ℤ)) (principalRoot d : ℂ) ≠ 0 := by
  rw [fltDenominator_principalA_principalRoot_complex d hd]
  exact pow_ne_zero 3 (ofReal_principalRoot_ne_zero d hd)

/-- **`A_d` fixes `ρ_d`**: the fractional linear action of `A_d` on `ρ_d` returns `ρ_d` itself,
by the quadratic equation of `ρ_d`. The fixed-point input to the cocycle relations at `M = A_d`,
`τ = ρ_d`. -/
lemma flt_principalA_principalRoot (d : ℕ) (hd : 3 < d) :
    flt (principalA d : Mat(2, ℤ)) (principalRoot d) = principalRoot d := by
  have hq := principalRoot_satisfies_quadratic d hd
  have hden : fltDenominator (principalA d : Mat(2, ℤ)) (principalRoot d) ≠ 0 := by
    rw [fltDenominator_principalA_principalRoot]
    exact principalJacobiFactor_ne_zero d hd
  simp only [flt, fltDenominator, coe_principalA] at hden ⊢
  simp only [neg_mul, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one,
    Int.cast_pow, Int.cast_ofNat, Matrix.cons_val_one, Int.cast_neg] at hden ⊢
  rw [div_eq_iff hden]
  linear_combination (-(d : ℝ) * ((d : ℝ) - 2)) * hq

/-- The fixed-point relation for the upper row of $A_d$ is $a\rho_d+b=\rho_d\varepsilon$. -/
lemma principalA_numerator_principalRoot (d : ℕ) (hd : 3 < d) :
    ((principalA d) 0 0 : ℝ) * principalRoot d + ((principalA d) 0 1 : ℝ) =
      principalRoot d * principalRoot d ^ 3 := by
  have hden : ((principalA d) 1 0 : ℝ) * principalRoot d +
      ((principalA d) 1 1 : ℝ) = principalRoot d ^ 3 := by
    simpa [coe_principalA, principalJacobiFactor] using
      principalJacobiFactor_eq_principalRoot_pow_three d hd
  have hfix : (((principalA d) 0 0 : ℝ) * principalRoot d +
      ((principalA d) 0 1 : ℝ)) /
      (((principalA d) 1 0 : ℝ) * principalRoot d +
        ((principalA d) 1 1 : ℝ)) = principalRoot d := by
    simpa only [flt, fltDenominator] using flt_principalA_principalRoot d hd
  have hden0 : (((principalA d) 1 0 : ℝ) * principalRoot d +
      ((principalA d) 1 1 : ℝ)) ≠ 0 := by
    rw [hden]
    exact pow_ne_zero 3 (ne_of_gt (principalRoot_pos d hd))
  simpa only [hden] using (div_eq_iff hden0).mp hfix

/-- `j_{A_d}(ρ_d)` is a root of the characteristic polynomial `x² - Tr(A_d)x + 1` of `A_d`, as it
must be: it is the eigenvalue of `A_d` on the eigenvector `(ρ_d, 1)` fixed by the Möbius action.
The proof is the substitution `ρ_d² = (d - 1)ρ_d - 1`. -/
lemma principalJacobiFactor_quadratic (d : ℕ) (hd : 3 < d) :
    principalJacobiFactor d ^ 2 - ((d : ℝ) ^ 2 * ((d : ℝ) - 3) + 2) * principalJacobiFactor d
        + 1 = 0 := by
  have hq := principalRoot_satisfies_quadratic d hd
  rw [principalJacobiFactor]
  linear_combination ((d : ℝ) * ((d : ℝ) - 2)) ^ 2 * hq

/-- **The Jacobi factor and its inverse sum to the trace.** Together with `trace_principalA` this
is `j + j⁻¹ = Tr(A_d) = d²(d - 3) + 2`. -/
lemma principalJacobiFactor_add_inv (d : ℕ) (hd : 3 < d) :
    principalJacobiFactor d + (principalJacobiFactor d)⁻¹ = (d : ℝ) ^ 2 * ((d : ℝ) - 3) + 2 := by
  have hne := principalJacobiFactor_ne_zero d hd
  have hq := principalJacobiFactor_quadratic d hd
  field_simp
  linear_combination hq

/-! ### Reduction modulo the dimension

Reducing `U_d` modulo `d` removes its dimension-dependent entry and yields the fixed Zauner
matrix. This explains why the induced phase-space action is uniform across the principal family.
-/

/-- Reduction of `principalU d` to `SL₂(ℤ/dℤ)`. -/
def principalUMod (d : ℕ) : SL(2, ZMod d) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod d)) (principalU d)

/-- Entrywise, reduction of `principalU d` modulo `d` is the constant matrix
`[[-1, -1], [1, 0]]`. -/
@[simp]
lemma coe_principalUMod (d : ℕ) :
    (principalUMod d : Mat(2, ZMod d)) = !![-1, -1; 1, 0] := by
  rw [principalUMod, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, coe_principalU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The cube of the reduced principal matrix is the identity. -/
lemma principalUMod_pow_three (d : ℕ) : principalUMod d ^ 3 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((principalUMod d : Mat(2, ZMod d)) ^ 3) i j =
    (1 : Mat(2, ZMod d)) i j
  rw [coe_principalUMod]
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### Congruence properties of the cube

Cubing the principal matrix gives `A_d ≡ I (mod d)`, which places `A_d` in the principal
congruence subgroup `Γ(d)`.
-/

/-- The cube `principalA d` belongs to the principal congruence subgroup `Γ(d)`. -/
lemma principalA_mem_Gamma (d : ℕ) :
    principalA d ∈ CongruenceSubgroup.Gamma d := by
  rw [CongruenceSubgroup.Gamma_mem']
  rw [principalA, map_pow]
  exact principalUMod_pow_three d

/-! ### Rademacher invariant of the level generator

The explicit word for `A_d` allows direct evaluation of the Rademacher invariant appearing in the
SF phase. The resulting closed formula is used in the finite phase cancellation.
-/

/-- The Dedekind sum `s(n, n² - 1)` of a self-inverse residue in the Rademacher
calculation for `A_d`.
Used by `rademacherInvariant_principalA`. -/
private lemma principalA_dedekindSum (d n : ℕ) (hn2 : 2 ≤ n) (hnd1 : n + 1 = d) :
    dedekindSum (n : ℤ) ((d : ℤ) * ((d : ℤ) - 2)) =
      ((n : ℚ) ^ 3 - 3 * (n : ℚ) ^ 2 + 3) /
        (6 * ((d : ℚ) * ((d : ℚ) - 2))) := by
  have haux : n * n = d * (d - 2) + 1 := by
    rw [← hnd1]
    have h2 : n + 1 - 2 = n - 1 := by omega
    rw [h2]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn2
    subst hk
    have hk1 : 2 + k - 1 = k + 1 := by omega
    rw [hk1]
    ring
  have hnn1 : 1 ≤ n * n := by nlinarith [haux]
  have hkey : (((n * n - 1 : ℕ)) : ℤ) = (d : ℤ) * ((d : ℤ) - 2) := by
    rw [Nat.cast_sub hnn1]
    have : ((n * n : ℕ) : ℤ) = ((d * (d - 2) + 1 : ℕ) : ℤ) := by exact_mod_cast haux
    rw [this]
    push_cast [Nat.cast_sub (show 2 ≤ d by omega)]
    ring
  have hkeyQ : (((n * n - 1 : ℕ)) : ℚ) = (d : ℚ) * ((d : ℚ) - 2) := by
    exact_mod_cast hkey
  rw [← hkey, ← hkeyQ]
  exact dedekindSum_self_sq_sub_one n hn2

/-- The Rademacher class invariant of `A_{t_d}`. -/
lemma rademacherInvariant_principalA (d : ℕ) (hd : 3 < d) :
    rademacherInvariant (principalA d) = 3 * (d : ℚ) - 12 := by
  unfold rademacherInvariant
  rw [coe_principalA]
  simp only [neg_mul, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, ne_eq, mul_eq_zero, Int.natCast_eq_zero, not_or,
    Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one, Int.cast_pow,
    Int.cast_ofNat, Int.sign_mul, Int.cast_neg]
  have hcond : ¬d = 0 ∧ ¬((d : ℤ) - 2) = 0 := ⟨by omega, by omega⟩
  rw [ite_eq_left hcond]
  have hd0 : (0 : ℤ) < (d : ℤ) := by omega
  have hd2 : (0 : ℤ) < (d : ℤ) - 2 := by omega
  have htr : (0 : ℤ) < ((d : ℤ) - 1) * ((d : ℤ) ^ 2 - 2 * (d : ℤ) - 1) + (1 - (d : ℤ)) := by
    nlinarith
  rw [Int.sign_eq_one_of_pos hd0, Int.sign_eq_one_of_pos hd2, Int.sign_eq_one_of_pos htr]
  set n := d - 1 with hndef
  clear_value n
  have hn2 : 2 ≤ n := by omega
  have hnd1 : n + 1 = d := by omega
  have hndZ : (n : ℤ) = (d : ℤ) - 1 := by omega
  have hαeq : ((d : ℤ) - 1) * ((d : ℤ) ^ 2 - 2 * (d : ℤ) - 1) =
      -(n : ℤ) + (n : ℤ) * ((d : ℤ) * ((d : ℤ) - 2)) := by rw [hndZ]; ring
  have hfinal := principalA_dedekindSum d n hn2 hnd1
  rw [hαeq, dedekindSum_add_mul_right, dedekindSum_neg_left, hfinal]
  rw [show (n : ℚ) = (d : ℚ) - 1 by exact_mod_cast hndZ]
  have hd2Q : (d : ℚ) - 2 ≠ 0 := by
    exact_mod_cast (show (d : ℤ) - 2 ≠ 0 by omega)
  field_simp
  ring

end SIC

end
