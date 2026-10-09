/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ParameterDomain

/-!
# Finite integer parameters for the principal five-term integral

The lattice arguments attached to integer pairs have exact upper and lower convergence rates.
Their strict convergence is equivalent to `S_d(u)≤d(d-3)` and `0<S_d(u)+S_d(v)`.

This module follows [RW26, Radchenko, Wheeler (2026), equation (2), `eq:fgam.def`, and Section
3.2, especially the parameter substitutions before the finite Fourier and five-term calculations]
at `γ=A_d` and `τ=ρ_d`. The source uses `p=v₁` and `ℓ=u₁+1`; the extra one in `ℓ` is retained
throughout.

## The argument

Put `ε=ρ_d³` and `c=d(d-2)`. The fixed-point identity gives `cρ_d=ε+d-1`, so for the source
argument `z_u=(u₁ρ_d+u₂)/(ε⁻¹-1)` one has
`cz_u/ε+u₁=-(du₁+cu₂)/(ε-1)`. This single equality yields both convergence rates. The unit
identity `ε+ε⁻¹=d²(d-3)+2`, together with `0<ε⁻¹<1`, then turns the strict real inequalities
into exact integer bounds for `u₁+(d-2)u₂`.

These classifications hold for every pair of integers. The downstream `ClassWindow` module
chooses representatives of the finite-group classes whose indices lie in a window of `d(d-3)`
consecutive integers.
-/

noncomputable section

open Complex

namespace SIC

/-! ### Lattice arguments and normalized rates

The integer linear form below is the numerator of the normalized rate after extracting the
positive factor `d`.
-/

/-- The real source argument
`z_u=(u₁ρ_d+u₂)/(ρ_d⁻³-1)` from [RW26, Radchenko, Wheeler (2026), equation (2),
`eq:fgam.def`] at `γ=A_d`. -/
def principalFiveTermLatticeArgument (d : ℕ) (u₁ u₂ : ℤ) : ℝ :=
  ((u₁ : ℝ) * principalRoot d + u₂) / ((principalRoot d ^ 3)⁻¹ - 1)

/-- The integer linear form `S_d(u₁,u₂)=u₁+(d-2)u₂` controlling the finite-parameter rates. -/
def principalFiveTermLatticeIndex (d : ℕ) (u₁ u₂ : ℤ) : ℤ :=
  u₁ + ((d : ℤ) - 2) * u₂

/-- The upper integer threshold `H_d=d(d-3)` for the lattice index. -/
def principalFiveTermUpperIndexBound (d : ℕ) : ℤ :=
  (d : ℤ) * ((d : ℤ) - 3)

/-- The source index threshold $H_d=d(d-3)$ is positive for $d>3$. -/
theorem principalFiveTermUpperIndexBound_pos (d : ℕ) (hd : 3 < d) :
    0 < principalFiveTermUpperIndexBound d := by
  simp only [principalFiveTermUpperIndexBound]
  exact mul_pos (by omega) (by omega)

/-- The normalized lattice rate
`L_u=(du₁+d(d-2)u₂)/(ρ_d³-1)`. -/
def principalFiveTermLatticeRate (d : ℕ) (u₁ u₂ : ℤ) : ℝ :=
  ((d : ℝ) * u₁ + (d : ℝ) * ((d : ℝ) - 2) * u₂) /
    (principalRoot d ^ 3 - 1)

/-- The lattice index is additive in integer pairs. -/
@[simp]
theorem principalFiveTermLatticeIndex_add (d : ℕ) (u₁ u₂ v₁ v₂ : ℤ) :
    principalFiveTermLatticeIndex d (u₁ + v₁) (u₂ + v₂) =
      principalFiveTermLatticeIndex d u₁ u₂ +
        principalFiveTermLatticeIndex d v₁ v₂ := by
  simp only [principalFiveTermLatticeIndex]
  ring

/-- The real lattice rate is `d/(ρ_d³-1)` times the integer lattice index. -/
theorem principalFiveTermLatticeRate_eq_index (d : ℕ) (u₁ u₂ : ℤ) :
    principalFiveTermLatticeRate d u₁ u₂ =
      (d : ℝ) * (principalFiveTermLatticeIndex d u₁ u₂ : ℝ) /
        (principalRoot d ^ 3 - 1) := by
  simp only [principalFiveTermLatticeRate, principalFiveTermLatticeIndex]
  push_cast
  ring

/-- The inverse principal unit lies strictly between zero and one. -/
private lemma principalRoot_pow_three_inv_bounds (d : ℕ) (hd : 3 < d) :
    0 < (principalRoot d ^ 3)⁻¹ ∧ (principalRoot d ^ 3)⁻¹ < 1 := by
  have hε : 1 < principalRoot d ^ 3 := one_lt_principalRoot_pow_three d hd
  exact ⟨inv_pos.mpr (lt_trans zero_lt_one hε),
    (inv_lt_one₀ (lt_trans zero_lt_one hε)).2 hε⟩

/-- The denominator `ρ_d³-1` lies strictly between the consecutive real numbers
`d²(d-3)` and `d²(d-3)+1`. -/
private lemma principalRoot_pow_three_sub_one_bounds (d : ℕ) (hd : 3 < d) :
    (d : ℝ) ^ 2 * ((d : ℝ) - 3) < principalRoot d ^ 3 - 1 ∧
      principalRoot d ^ 3 - 1 < (d : ℝ) ^ 2 * ((d : ℝ) - 3) + 1 := by
  have hsum := principalJacobiFactor_add_inv d hd
  rw [principalJacobiFactor_eq_principalRoot_pow_three d hd] at hsum
  obtain ⟨hinvpos, hinvlt⟩ := principalRoot_pow_three_inv_bounds d hd
  constructor <;> nlinarith

/-- The source lattice argument with its inverse-unit denominator rewritten using `ρ_d³-1`. -/
private lemma principalFiveTermLatticeArgument_eq (d : ℕ) (hd : 3 < d) (u₁ u₂ : ℤ) :
    principalFiveTermLatticeArgument d u₁ u₂ =
      -(principalRoot d ^ 3 * ((u₁ : ℝ) * principalRoot d + u₂)) /
        (principalRoot d ^ 3 - 1) := by
  have hε0 : principalRoot d ^ 3 ≠ 0 :=
    ne_of_gt (lt_trans zero_lt_one (one_lt_principalRoot_pow_three d hd))
  have hε1 : principalRoot d ^ 3 - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (one_lt_principalRoot_pow_three d hd))
  have hinv : (principalRoot d ^ 3)⁻¹ - 1 =
      -(principalRoot d ^ 3 - 1) / principalRoot d ^ 3 := by
    calc
      (principalRoot d ^ 3)⁻¹ - 1 =
          (1 - principalRoot d ^ 3) / (principalRoot d ^ 3 * 1) := by
        simpa using inv_sub_inv hε0 one_ne_zero
      _ = _ := by ring
  simp only [principalFiveTermLatticeArgument]
  rw [hinv]
  field_simp [hε0, hε1]

/-- The basic parameter calculation
`d(d-2)z_u/ρ_d³+u₁=-L_u` behind both finite convergence rates. -/
theorem principalFiveTermLatticeArgument_baseRate
    (d : ℕ) (hd : 3 < d) (u₁ u₂ : ℤ) :
    (d : ℝ) * ((d : ℝ) - 2) * principalFiveTermLatticeArgument d u₁ u₂ /
        principalRoot d ^ 3 + u₁ =
      -principalFiveTermLatticeRate d u₁ u₂ := by
  have hε : 1 < principalRoot d ^ 3 := one_lt_principalRoot_pow_three d hd
  have hρ0 : principalRoot d ≠ 0 := (principalRoot_pos d hd).ne'
  have hε0 : principalRoot d ^ 3 ≠ 0 := ne_of_gt (lt_trans zero_lt_one hε)
  have hε1 : principalRoot d ^ 3 - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hε)
  have hc := principalRoot_pow_three_eq d hd
  rw [principalFiveTermLatticeArgument_eq d hd]
  simp only [principalFiveTermLatticeRate]
  field_simp [hρ0, hε0, hε1]
  linear_combination (u₁ : ℝ) * hc

/-! ### Exact convergence conditions

The source indices are `ℓ=u₁+1` and `p=v₁`. Applying the basic calculation once gives the
upper rate; applying it to both integer pairs gives the lower rate.
-/

/-- At `ℓ=u₁+1` and `w=z_u`, the upper decay rate is exactly `1-L_u`. -/
theorem principalFiveTermUpperRate_latticeArgument
    (d : ℕ) (hd : 3 < d) (u₁ u₂ : ℤ) :
    principalFiveTermUpperRate d (u₁ + 1)
        (principalFiveTermLatticeArgument d u₁ u₂) =
      1 - principalFiveTermLatticeRate d u₁ u₂ := by
  have h := principalFiveTermLatticeArgument_baseRate d hd u₁ u₂
  simp only [principalFiveTermUpperRate]
  push_cast
  linarith

/-- At `ℓ=u₁+1`, `p=v₁`, `w=z_u`, and `y=z_v`, the lower decay rate is exactly
`-(L_u+L_v)`. -/
theorem principalFiveTermLowerRate_latticeArgument
    (d : ℕ) (hd : 3 < d) (u₁ u₂ v₁ v₂ : ℤ) :
    principalFiveTermLowerRate d (u₁ + 1) v₁
        (principalFiveTermLatticeArgument d u₁ u₂)
        (principalFiveTermLatticeArgument d v₁ v₂) =
      -(principalFiveTermLatticeRate d u₁ u₂ +
        principalFiveTermLatticeRate d v₁ v₂) := by
  have hu := principalFiveTermLatticeArgument_baseRate d hd u₁ u₂
  have hv := principalFiveTermLatticeArgument_baseRate d hd v₁ v₂
  simp only [principalFiveTermLowerRate]
  push_cast
  linear_combination hu + hv

/-! ### Integer classification

The interval containing `ρ_d³-1` has consecutive integer endpoints. This makes each strict real
rate inequality equivalent to a weak or strict integer inequality.
-/

/-- The upper inequality `L_u<1` is exactly the integer bound `S_d(u)≤d(d-3)`. -/
theorem principalFiveTermLatticeRate_lt_one_iff
    (d : ℕ) (hd : 3 < d) (u₁ u₂ : ℤ) :
    principalFiveTermLatticeRate d u₁ u₂ < 1 ↔
      principalFiveTermLatticeIndex d u₁ u₂ ≤ principalFiveTermUpperIndexBound d := by
  have hden : 0 < principalRoot d ^ 3 - 1 :=
    sub_pos.mpr (one_lt_principalRoot_pow_three d hd)
  have hdreal : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdthree : (3 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨hlower, hupper⟩ := principalRoot_pow_three_sub_one_bounds d hd
  rw [principalFiveTermLatticeRate_eq_index, div_lt_one hden]
  constructor
  · intro hrate
    by_contra hle
    have hstepInt : principalFiveTermUpperIndexBound d + 1 ≤
        principalFiveTermLatticeIndex d u₁ u₂ := by omega
    have hstep : (principalFiveTermUpperIndexBound d : ℝ) + 1 ≤
        (principalFiveTermLatticeIndex d u₁ u₂ : ℝ) := by exact_mod_cast hstepInt
    have hmul := mul_le_mul_of_nonneg_left hstep hdreal
    simp only [principalFiveTermUpperIndexBound, Int.cast_mul, Int.cast_natCast,
      Int.cast_sub, Int.cast_ofNat] at hmul
    nlinarith
  · intro hindex
    have hindexReal : (principalFiveTermLatticeIndex d u₁ u₂ : ℝ) ≤
        (principalFiveTermUpperIndexBound d : ℝ) := by exact_mod_cast hindex
    have hmul := mul_le_mul_of_nonneg_left hindexReal hdreal
    simp only [principalFiveTermUpperIndexBound, Int.cast_mul, Int.cast_natCast,
      Int.cast_sub, Int.cast_ofNat] at hmul
    nlinarith

/-- The strengthened upper inequality `L_u<1-ρ_d⁻³`, the convergence condition of the residue
kernel at `+i∞`, is exactly the strict integer bound `S_d(u)<d(d-3)`, since
`(ρ_d³-1)² = d²(d-3)ρ_d³` (`principalJacobiFactor_add_inv`). -/
theorem principalFiveTermLatticeRate_lt_one_sub_inv_iff
    (d : ℕ) (hd : 3 < d) (u₁ u₂ : ℤ) :
    principalFiveTermLatticeRate d u₁ u₂ < 1 - (principalRoot d ^ 3)⁻¹ ↔
      principalFiveTermLatticeIndex d u₁ u₂ < principalFiveTermUpperIndexBound d := by
  have hε : 1 < principalRoot d ^ 3 := one_lt_principalRoot_pow_three d hd
  have hε0 : principalRoot d ^ 3 ≠ 0 := ne_of_gt (zero_lt_one.trans hε)
  have hden : 0 < principalRoot d ^ 3 - 1 := sub_pos.mpr hε
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_trans (by norm_num) hd)
  have hsum := principalJacobiFactor_add_inv d hd
  rw [principalJacobiFactor_eq_principalRoot_pow_three d hd] at hsum
  have hfactor : (1 - (principalRoot d ^ 3)⁻¹) * (principalRoot d ^ 3 - 1) =
      (d : ℝ) * (principalFiveTermUpperIndexBound d : ℝ) := by
    have hunit : principalRoot d ^ 3 * (principalRoot d ^ 3)⁻¹ = 1 :=
      mul_inv_cancel₀ hε0
    simp only [principalFiveTermUpperIndexBound, Int.cast_mul, Int.cast_natCast,
      Int.cast_sub, Int.cast_ofNat]
    nlinarith
  rw [principalFiveTermLatticeRate_eq_index, div_lt_iff₀ hden, hfactor]
  constructor
  · intro h
    exact_mod_cast lt_of_mul_lt_mul_left h hdpos.le
  · intro h
    exact mul_lt_mul_of_pos_left (by exact_mod_cast h) hdpos

/-- Positivity of `L_u+L_v` is exactly positivity of the sum of the two integer indices. -/
theorem principalFiveTermLatticeRates_add_pos_iff
    (d : ℕ) (hd : 3 < d) (u₁ u₂ v₁ v₂ : ℤ) :
    0 < principalFiveTermLatticeRate d u₁ u₂ +
        principalFiveTermLatticeRate d v₁ v₂ ↔
      0 < principalFiveTermLatticeIndex d u₁ u₂ +
        principalFiveTermLatticeIndex d v₁ v₂ := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_trans (by norm_num) hd)
  have hden : 0 < principalRoot d ^ 3 - 1 :=
    sub_pos.mpr (one_lt_principalRoot_pow_three d hd)
  have hfactor : 0 < (d : ℝ) / (principalRoot d ^ 3 - 1) := div_pos hdpos hden
  rw [principalFiveTermLatticeRate_eq_index, principalFiveTermLatticeRate_eq_index]
  have heq :
      (d : ℝ) * (principalFiveTermLatticeIndex d u₁ u₂ : ℝ) /
          (principalRoot d ^ 3 - 1) +
        (d : ℝ) * (principalFiveTermLatticeIndex d v₁ v₂ : ℝ) /
          (principalRoot d ^ 3 - 1) =
      ((d : ℝ) / (principalRoot d ^ 3 - 1)) *
        ((principalFiveTermLatticeIndex d u₁ u₂ +
          principalFiveTermLatticeIndex d v₁ v₂ : ℤ) : ℝ) := by
    push_cast
    ring
  rw [heq]
  constructor
  · intro h
    have hcast : 0 < ((principalFiveTermLatticeIndex d u₁ u₂ +
        principalFiveTermLatticeIndex d v₁ v₂ : ℤ) : ℝ) :=
      pos_of_mul_pos_left (by simpa [mul_comm] using h) hfactor.le
    exact_mod_cast hcast
  · intro h
    have hcast : 0 < ((principalFiveTermLatticeIndex d u₁ u₂ +
        principalFiveTermLatticeIndex d v₁ v₂ : ℤ) : ℝ) := by exact_mod_cast h
    exact mul_pos hfactor hcast

/-! ### Source phase identities

The defining denominator gives `z_u/ρ_d³-z_u=u₁ρ_d+u₂`. Integer periodicity of the complex
exponential then proves the phase relation from the `p` parameter assumed in the Section 3.2
calculations of [RW26, Radchenko, Wheeler (2026)].
-/

/-- The elementary source identity `z_u/ρ_d³-z_u=u₁ρ_d+u₂`. -/
theorem principalFiveTermLatticeArgument_div_sub_self
    (d : ℕ) (hd : 3 < d) (u₁ u₂ : ℤ) :
    principalFiveTermLatticeArgument d u₁ u₂ / principalRoot d ^ 3 -
        principalFiveTermLatticeArgument d u₁ u₂ =
      (u₁ : ℝ) * principalRoot d + u₂ := by
  have hε : 1 < principalRoot d ^ 3 := one_lt_principalRoot_pow_three d hd
  have hinv : (principalRoot d ^ 3)⁻¹ < 1 :=
    (inv_lt_one₀ (lt_trans zero_lt_one hε)).2 hε
  have hne : (principalRoot d ^ 3)⁻¹ - 1 ≠ 0 := ne_of_lt (sub_neg.mpr hinv)
  rw [principalFiveTermLatticeArgument, div_eq_mul_inv]
  calc
    (((u₁ : ℝ) * principalRoot d + u₂) / ((principalRoot d ^ 3)⁻¹ - 1)) *
          (principalRoot d ^ 3)⁻¹ -
        ((u₁ : ℝ) * principalRoot d + u₂) / ((principalRoot d ^ 3)⁻¹ - 1) =
        (((u₁ : ℝ) * principalRoot d + u₂) / ((principalRoot d ^ 3)⁻¹ - 1)) *
          ((principalRoot d ^ 3)⁻¹ - 1) := by ring
    _ = _ := div_mul_cancel₀ _ hne

/-- The source relation
`exp(2πi(u₁ρ_d+z_u))=exp(2πi(z_u/ρ_d³))` from the `p` parameter. -/
theorem principalFiveTermLatticeArgument_exp_lower
    (d : ℕ) (hd : 3 < d) (u₁ u₂ : ℤ) :
    Complex.exp (2 * Real.pi * I *
        ((u₁ : ℂ) * (principalRoot d : ℂ) +
          (principalFiveTermLatticeArgument d u₁ u₂ : ℂ))) =
      Complex.exp (2 * Real.pi * I *
        ((principalFiveTermLatticeArgument d u₁ u₂ : ℂ) /
          (principalRoot d : ℂ) ^ 3)) := by
  apply exp_two_pi_I_eq_of_sub_intCast _ _ (-u₂)
  have h := principalFiveTermLatticeArgument_div_sub_self d hd u₁ u₂
  have hc :
      (principalFiveTermLatticeArgument d u₁ u₂ : ℂ) /
          (principalRoot d : ℂ) ^ 3 -
          (principalFiveTermLatticeArgument d u₁ u₂ : ℂ) =
        (u₁ : ℂ) * (principalRoot d : ℂ) + u₂ := by
    exact_mod_cast h
  push_cast
  linear_combination -hc

end SIC
