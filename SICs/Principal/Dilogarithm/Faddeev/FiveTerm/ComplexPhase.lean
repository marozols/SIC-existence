/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.ComplexPeriodAsymptotics
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.Kernel

/-!
# Complex-period phases of the principal five-term kernel

The principal five-term phase and its reflected form have uniform exponential bounds near the
positive real period.

This module follows [RW26, Radchenko, Wheeler (2026), equation (13),
`eq:PhiS.reflection`, equation (20), `eq:modulartofaddeevCF`, and equation (23),
`eq:5term.int`] at the principal matrix `A_d=U_d^3`.

## The argument

The three Jacobi denominators along the word multiply to `j_{A_d}(τ)`. Expanding the exact
generator reflection polynomials shows that their common quadratic coefficient is
`(A_d)₁₀/j_{A_d}(τ)`. It cancels between the numerator and denominator, while translation by
`y` leaves the linear contribution `2πi((A_d)₁₀y/j_{A_d}(τ)+p-1)`. Adding the kernel phase gives
the claimed reflected slope. Continuity at the positive principal root then preserves the signs
of the upper and lower slopes and supplies uniform exponential bounds on vertical rays.
-/

noncomputable section

open Complex Filter Topology
open scoped MatrixGroups

namespace SIC

/-! ### Exact phases and denominator product -/

/-- The logarithmic exponential phase in the complex-period principal five-term kernel of
[RW26, Radchenko, Wheeler (2026), equation (23), `eq:5term.int`]. -/
def principalFiveTermPhaseComplex (d : ℕ) (ℓ : ℤ) (w : ℂ) (m : ℤ)
    (z τ : ℂ) : ℂ :=
  2 * Real.pi * I *
    (((((principalA d) 1 0 : ℤ) : ℂ) * z +
          fltDenominator (principalA d : Mat(2, ℤ)) τ * m) * w /
        fltDenominator (principalA d : Mat(2, ℤ)) τ + ℓ * (z + m * τ))

/-- The logarithmic phase after reflecting the numerator and denominator principal products in
the complex-period five-term kernel. -/
def principalFiveTermReflectedPhaseComplex (d : ℕ) (ℓ p m : ℤ) (w y z τ : ℂ) : ℂ :=
  principalFaddeevLowerExponentComplex d (m + 1) 0 z τ -
    principalFaddeevLowerExponentComplex d (m + p) 0 (z + y) τ +
      principalFiveTermPhaseComplex d ℓ w m z τ

/-- The coefficient of `z` in the logarithmic complex-period five-term phase. -/
def principalFiveTermPhaseCoeffComplex (d : ℕ) (ℓ : ℤ) (w τ : ℂ) : ℂ :=
  2 * Real.pi * I *
    ((((principalA d) 1 0 : ℤ) : ℂ) * w /
      fltDenominator (principalA d : Mat(2, ℤ)) τ + ℓ)

/-- The coefficient of `z` in the reflected logarithmic complex-period five-term phase. -/
def principalFiveTermReflectedPhaseCoeffComplex (d : ℕ) (ℓ p : ℤ)
    (w y τ : ℂ) : ℂ :=
  2 * Real.pi * I *
    ((((principalA d) 1 0 : ℤ) : ℂ) * (w + y) /
      fltDenominator (principalA d : Mat(2, ℤ)) τ + ℓ + p - 1)

/-- The reflected coefficient is the upper coefficient at `w+y`, plus the index correction
`2πi(p-1)`. -/
lemma principalFiveTermReflectedPhaseCoeffComplex_eq (d : ℕ) (ℓ p : ℤ)
    (w y τ : ℂ) :
    principalFiveTermReflectedPhaseCoeffComplex d ℓ p w y τ =
      principalFiveTermPhaseCoeffComplex d ℓ (w + y) τ +
        2 * Real.pi * I * (p - 1) := by
  simp only [principalFiveTermReflectedPhaseCoeffComplex,
    principalFiveTermPhaseCoeffComplex]
  ring

/-- The logarithmic kernel phase is affine in `z`, with coefficient
`2πi((A_d)₁₀w/j_{A_d}(τ)+ℓ)`. -/
theorem principalFiveTermPhaseComplex_eq_affine (d : ℕ) (ℓ m : ℤ) (w z τ : ℂ) :
    principalFiveTermPhaseComplex d ℓ w m z τ =
      principalFiveTermPhaseCoeffComplex d ℓ w τ * z +
        principalFiveTermPhaseComplex d ℓ w m 0 τ := by
  simp only [principalFiveTermPhaseComplex, principalFiveTermPhaseCoeffComplex]
  ring

/-- The Jacobi denominator of `A_d=U_d^3` is the product of the three successive principal
periods: `j_{A_d}(τ)=τ(U_dτ)(U_d^2τ)`. -/
lemma fltDenominator_principalA_eq_period_product (d : ℕ) (τ : ℂ)
    (hτ : τ ≠ 0)
    (hτ₁ : flt (principalU d : Mat(2, ℤ)) τ ≠ 0) :
    fltDenominator (principalA d : Mat(2, ℤ)) τ =
      τ * flt (principalU d : Mat(2, ℤ)) τ *
        flt (principalU d : Mat(2, ℤ))
          (flt (principalU d : Mat(2, ℤ)) τ) := by
  let U : Mat(2, ℤ) := principalU d
  have hUden (q : ℂ) : fltDenominator U q = q := by
    simp [U, fltDenominator, coe_principalU]
  have hUUden : fltDenominator (U * U) τ = flt U τ * τ := by
    rw [fltDenominator_mul U U τ (by simpa [hUden] using hτ)]
    simp only [hUden]
  have hUUden_ne : fltDenominator (U * U) τ ≠ 0 := by
    rw [hUUden]
    exact mul_ne_zero hτ₁ hτ
  have hUUact : flt (U * U) τ = flt U (flt U τ) :=
    flt_mul U U τ (by simpa [hUden] using hτ)
  have hA : (principalA d : Mat(2, ℤ)) = U * (U * U) := by
    simp [principalA, U, pow_succ]
    constructor <;> ring
  rw [hA, fltDenominator_mul U (U * U) τ hUUden_ne, hUUden, hUUact, hUden]
  ring

/-- The common quadratic coefficient of the three exact generator reflection polynomials. -/
private def principalFaddeevLowerQuadraticCoeffComplex (d : ℕ) (τ : ℂ) : ℂ :=
  let τ₁ := flt (principalU d : Mat(2, ℤ)) τ
  let τ₂ := flt (principalU d : Mat(2, ℤ)) τ₁
  (1 / τ / τ₁) ^ 2 / τ₂ + (1 / τ) ^ 2 / τ₁ + 1 / τ

/-- One step of the principal word satisfies `τ(U_dτ)=((d-1)τ-1)`. -/
private lemma mul_flt_principalU (d : ℕ) (τ : ℂ) (hτ : τ ≠ 0) :
    τ * flt (principalU d : Mat(2, ℤ)) τ = ((d : ℂ) - 1) * τ - 1 := by
  simp [flt, coe_principalU]
  field_simp [hτ]
  ring

/-- The three-generator quadratic coefficient is `(A_d)₁₀/j_{A_d}(τ)`. -/
private lemma lowerQuadraticCoeffComplex_eq (d : ℕ) (τ : ℂ)
    (hτ : τ ≠ 0)
    (hτ₁ : flt (principalU d : Mat(2, ℤ)) τ ≠ 0)
    (hτ₂ : flt (principalU d : Mat(2, ℤ))
      (flt (principalU d : Mat(2, ℤ)) τ) ≠ 0) :
    principalFaddeevLowerQuadraticCoeffComplex d τ =
      (((principalA d) 1 0 : ℤ) : ℂ) /
        fltDenominator (principalA d : Mat(2, ℤ)) τ := by
  let τ₁ := flt (principalU d : Mat(2, ℤ)) τ
  let τ₂ := flt (principalU d : Mat(2, ℤ)) τ₁
  have hτ₁ne : τ₁ ≠ 0 := by simpa only [τ₁] using hτ₁
  have hτ₂ne : τ₂ ≠ 0 := by simpa only [τ₂, τ₁] using hτ₂
  have hprod := fltDenominator_principalA_eq_period_product d τ hτ hτ₁
  have hprod' : fltDenominator (principalA d : Mat(2, ℤ)) τ = τ * τ₁ * τ₂ := by
    simpa only [τ₁, τ₂] using hprod
  have hc : (((principalA d) 1 0 : ℤ) : ℂ) =
      (d : ℂ) * ((d : ℂ) - 2) := by simp [coe_principalA]
  have hrel₁ : τ * τ₁ = ((d : ℂ) - 1) * τ - 1 := mul_flt_principalU d τ hτ
  have hrel₂ : τ₁ * τ₂ = ((d : ℂ) - 1) * τ₁ - 1 := mul_flt_principalU d τ₁ hτ₁ne
  change (1 / τ / τ₁) ^ 2 / τ₂ + (1 / τ) ^ 2 / τ₁ + 1 / τ =
    (((principalA d) 1 0 : ℤ) : ℂ) /
      fltDenominator (principalA d : Mat(2, ℤ)) τ
  rw [hprod', hc]
  field_simp [hτ, hτ₁ne, hτ₂ne]
  calc
    1 + τ₁ * τ₂ + τ * τ₁ ^ 2 * τ₂ =
        1 + τ₁ * τ₂ + (τ * τ₁) * (τ₁ * τ₂) := by ring
    _ = 1 + (((d : ℂ) - 1) * τ₁ - 1) +
        (((d : ℂ) - 1) * τ - 1) * (((d : ℂ) - 1) * τ₁ - 1) := by
      rw [hrel₁, hrel₂]
    _ = τ * τ₁ * (d : ℂ) * ((d : ℂ) - 2) := by
      linear_combination hrel₁

/-! ### Affine cancellation -/

/-- Subtracting the two exact lower exponents cancels the common quadratic term and leaves
coefficient `2πi(Q(τ)y+p-1)`, where `Q(τ)` is their common quadratic coefficient. -/
private lemma principalFaddeevLowerExponentComplex_sub_eq_affine (d : ℕ) (p m : ℤ)
    (y z τ : ℂ) (hτ : τ ≠ 0)
    (hτ₁ : flt (principalU d : Mat(2, ℤ)) τ ≠ 0)
    (hτ₂ : flt (principalU d : Mat(2, ℤ))
      (flt (principalU d : Mat(2, ℤ)) τ) ≠ 0) :
    principalFaddeevLowerExponentComplex d (m + 1) 0 z τ -
        principalFaddeevLowerExponentComplex d (m + p) 0 (z + y) τ =
      (2 * Real.pi * I *
          (principalFaddeevLowerQuadraticCoeffComplex d τ * y + p - 1)) * z +
        (principalFaddeevLowerExponentComplex d (m + 1) 0 0 τ -
          principalFaddeevLowerExponentComplex d (m + p) 0 y τ) := by
  simp only [principalFaddeevLowerExponentComplex,
    principalFaddeevLowerQuadraticCoeffComplex]
  push_cast
  field_simp [hτ, hτ₁, hτ₂]
  ring

/-- The reflected logarithmic phase is affine in `z`, with coefficient
`2πi((A_d)₁₀(w+y)/j_{A_d}(τ)+ℓ+p-1)`. This is the exact five-term cancellation of the three
quadratic generator reflection polynomials. -/
theorem principalFiveTermReflectedPhaseComplex_eq_affine (d : ℕ) (ℓ p m : ℤ)
    (w y z τ : ℂ) (hτ : τ ≠ 0)
    (hτ₁ : flt (principalU d : Mat(2, ℤ)) τ ≠ 0)
    (hτ₂ : flt (principalU d : Mat(2, ℤ))
      (flt (principalU d : Mat(2, ℤ)) τ) ≠ 0) :
    principalFiveTermReflectedPhaseComplex d ℓ p m w y z τ =
      principalFiveTermReflectedPhaseCoeffComplex d ℓ p w y τ * z +
        principalFiveTermReflectedPhaseComplex d ℓ p m w y 0 τ := by
  rw [principalFiveTermReflectedPhaseComplex,
    principalFaddeevLowerExponentComplex_sub_eq_affine d p m y z τ hτ hτ₁ hτ₂,
    principalFiveTermPhaseComplex_eq_affine,
    lowerQuadraticCoeffComplex_eq d τ hτ hτ₁ hτ₂]
  simp only [principalFiveTermReflectedPhaseCoeffComplex,
    principalFiveTermPhaseCoeffComplex, principalFiveTermReflectedPhaseComplex]
  ring_nf

/-! ### Continuity and values at the principal root -/

/-- At `τ=ρ_d`, the complex-period kernel-phase coefficient is
`2πi·principalFiveTermUpperRate`. -/
theorem principalFiveTermPhaseCoeffComplex_principalRoot (d : ℕ) (hd : 3 < d)
    (ℓ : ℤ) (w : ℝ) :
    principalFiveTermPhaseCoeffComplex d ℓ w (principalRoot d) =
      2 * Real.pi * I * (principalFiveTermUpperRate d ℓ w : ℂ) := by
  rw [principalFiveTermPhaseCoeffComplex, principalFiveTermUpperRate,
    fltDenominator_principalA_principalRoot_complex d hd]
  simp [coe_principalA]

/-- At `τ=ρ_d`, the reflected complex-period phase coefficient is
`2πi·principalFiveTermLowerRate`. -/
theorem principalFiveTermReflectedPhaseCoeffComplex_principalRoot
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ) :
    principalFiveTermReflectedPhaseCoeffComplex d ℓ p w y (principalRoot d) =
      2 * Real.pi * I * (principalFiveTermLowerRate d ℓ p w y : ℂ) := by
  rw [principalFiveTermReflectedPhaseCoeffComplex_eq, ← Complex.ofReal_add,
    principalFiveTermPhaseCoeffComplex_principalRoot d hd ℓ (w + y)]
  simp [principalFiveTermUpperRate, principalFiveTermLowerRate]
  ring

/-- The complex-period kernel-phase coefficient varies continuously at the principal root. -/
theorem continuousAt_principalFiveTermPhaseCoeffComplex (d : ℕ) (hd : 3 < d)
    (ℓ : ℤ) (w : ℂ) :
    ContinuousAt (principalFiveTermPhaseCoeffComplex d ℓ w)
      (principalRoot d : ℂ) := by
  have hJ := fltDenominator_principalA_principalRoot_ne_zero d hd
  unfold principalFiveTermPhaseCoeffComplex fltDenominator at hJ ⊢
  fun_prop

/-- The reflected complex-period phase coefficient varies continuously at the principal root. -/
theorem continuousAt_principalFiveTermReflectedPhaseCoeffComplex
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℂ) :
    ContinuousAt (principalFiveTermReflectedPhaseCoeffComplex d ℓ p w y)
      (principalRoot d : ℂ) := by
  have hconst : ContinuousAt (fun _ : ℂ => 2 * Real.pi * I * (p - 1 : ℂ))
      (principalRoot d : ℂ) := continuousAt_const
  apply ((continuousAt_principalFiveTermPhaseCoeffComplex d hd ℓ (w + y)).add
    hconst).congr
  exact Filter.Eventually.of_forall fun τ =>
    (principalFiveTermReflectedPhaseCoeffComplex_eq d ℓ p w y τ).symm

/-- The value at `z=0` of the logarithmic kernel phase varies continuously at the principal
root. This is its affine intercept. -/
theorem continuousAt_principalFiveTermPhaseComplex_zero (d : ℕ) (hd : 3 < d)
    (ℓ m : ℤ) (w : ℂ) :
    ContinuousAt (fun τ : ℂ => principalFiveTermPhaseComplex d ℓ w m 0 τ)
      (principalRoot d : ℂ) := by
  have hJ := fltDenominator_principalA_principalRoot_ne_zero d hd
  unfold principalFiveTermPhaseComplex fltDenominator at hJ ⊢
  fun_prop

/-- The value at `z=0` of the reflected logarithmic phase varies continuously at the principal
root. This is its affine intercept. -/
theorem continuousAt_principalFiveTermReflectedPhaseComplex_zero
    (d : ℕ) (hd : 3 < d) (ℓ p m : ℤ) (w y : ℂ) :
    ContinuousAt
      (fun τ : ℂ => principalFiveTermReflectedPhaseComplex d ℓ p m w y 0 τ)
      (principalRoot d : ℂ) := by
  apply (((continuousAt_principalFaddeevLowerExponentComplex d hd (m + 1) 0 0).sub
    (continuousAt_principalFaddeevLowerExponentComplex d hd (m + p) 0 y)).add
      (continuousAt_principalFiveTermPhaseComplex_zero d hd ℓ m w)).congr
  exact Filter.Eventually.of_forall fun τ => by
    simp [principalFiveTermReflectedPhaseComplex]

/-! ### Uniform vertical exponential bounds -/

/-- If the real upper rate is positive, the exact complex-period phase exponential decays
uniformly on nearby upper vertical rays. Specializes
`exists_norm_exp_affine_vertical_le`. -/
theorem exists_norm_exp_principalFiveTermPhaseComplex_le
    (d : ℕ) (hd : 3 < d) (ℓ m : ℤ) (w x : ℝ)
    (hRate : 0 < principalFiveTermUpperRate d ℓ w) :
    ∃ ε C κ : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧
      ∀ τ : ℂ, ‖τ - (principalRoot d : ℂ)‖ ≤ ε → ∀ t : ℝ, 0 ≤ t →
        ‖Complex.exp
          (principalFiveTermPhaseComplex d ℓ w m ((x : ℂ) + t * I) τ)‖ ≤
            C * Real.exp (-κ * t) := by
  have hIm : 0 < (principalFiveTermPhaseCoeffComplex d ℓ w
      (principalRoot d : ℂ)).im := by
    rw [principalFiveTermPhaseCoeffComplex_principalRoot d hd]
    simp [Complex.mul_im]
    nlinarith [Real.pi_pos]
  obtain ⟨ε, C, κ, hε, hC, hκ, hbound⟩ :=
    exists_norm_exp_affine_vertical_le
      (continuousAt_principalFiveTermPhaseCoeffComplex d hd ℓ w)
      (continuousAt_principalFiveTermPhaseComplex_zero d hd ℓ m w) hIm x
  refine ⟨ε, C, κ, hε, hC, hκ, fun τ hτ t ht => ?_⟩
  rw [principalFiveTermPhaseComplex_eq_affine]
  exact hbound τ hτ t ht

/-- If the real lower rate is negative, the exact reflected phase exponential decays uniformly
on nearby lower vertical rays. Specializes
`exists_norm_exp_affine_vertical_le_of_im_neg`. -/
theorem exists_norm_exp_principalFiveTermReflectedPhaseComplex_le
    (d : ℕ) (hd : 3 < d) (ℓ p m : ℤ) (w y x : ℝ)
    (hRate : principalFiveTermLowerRate d ℓ p w y < 0) :
    ∃ ε C κ : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧
      ∀ τ : ℂ, ‖τ - (principalRoot d : ℂ)‖ ≤ ε → ∀ t : ℝ, t ≤ 0 →
        ‖Complex.exp
          (principalFiveTermReflectedPhaseComplex d ℓ p m w y
            ((x : ℂ) + t * I) τ)‖ ≤ C * Real.exp (κ * t) := by
  have hIm : (principalFiveTermReflectedPhaseCoeffComplex d ℓ p w y
      (principalRoot d : ℂ)).im < 0 := by
    rw [principalFiveTermReflectedPhaseCoeffComplex_principalRoot d hd]
    simp [Complex.mul_im]
    nlinarith [Real.pi_pos]
  obtain ⟨ε₁, C, κ, hε₁, hC, hκ, hbound⟩ :=
    exists_norm_exp_affine_vertical_le_of_im_neg
      (continuousAt_principalFiveTermReflectedPhaseCoeffComplex d hd ℓ p w y)
      (continuousAt_principalFiveTermReflectedPhaseComplex_zero d hd ℓ p m w y) hIm x
  obtain ⟨ε₂, hε₂, hperiods⟩ := exists_principalU_periods_ne_zero d hd
  refine ⟨min ε₁ ε₂, C, κ, lt_min hε₁ hε₂, hC, hκ, fun τ hτ t ht => ?_⟩
  obtain ⟨hτ₀, hτ₁, hτ₂⟩ := hperiods τ (hτ.trans (min_le_right _ _))
  rw [principalFiveTermReflectedPhaseComplex_eq_affine d ℓ p m w y _ τ hτ₀ hτ₁ hτ₂]
  exact hbound τ (hτ.trans (min_le_left _ _)) t ht

end SIC
