/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.IntegralIdentity
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ShiftedIdentity
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ResidueStripBounds

/-!
# The shifted principal integral with crossed poles

The common-line difference integral minus its crossed-pole squares equals the continued
finite quotient, including the zero left and zero sum classes.

This module follows [RW26, Radchenko, Wheeler (2026), Section 3.2, proof of Theorem 2,
`thm:fg.equs`], applying the integral identity (23), `eq:5term.int`, on the deformed contours.

## The argument

Write `ε=ρ_d³`, `c=d(d-2)`, `β_v=-(v₁ε/c+z_v)`, and use positive representatives
`0 ≤ S_d(u) < H`, `1 ≤ S_d(v) ≤ H`. The difference kernel is
`(1-q^{v₁}e(z_v))` times the five-term kernel at parameters
`(u₁+1,v₁-a,z_u,z_v+aρ_d+b)`. A common line `β_v < x < ε/c` is right of the shifted left
poles. In common-line coordinates a right pole is `(Nε+j)/c`, with `N,j ≥ 0`, so the poles
left of the line are precisely `j/c`, each belonging to its unique contour index modulo `c`.

Carry the corrected integral identity to the real period and translate its squares to this
common line. Summands regular at a crossed point have zero square integral, so the correction
is the sum of square integrals of the whole difference kernel. The continued shifted closed
form gives `√ε F⁺(u+v)/(F⁻(u)F⁻(v))`. At zero left parameter use the literal origin; at zero
sum choose the source sum `(a-1,b)`, which gives the removable-origin numerator.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology MatrixGroups

namespace SIC

/-! ### Positive representatives and shifted contours

The index bounds give decay at both ends. Shifting the right parameter by `aρ_d+b`
preserves regular crossings and puts the shifted left endpoint at `β_v-mε/c`.
-/

/-- The positive source representatives give the two decay inequalities needed by
`integral_principalFiveTermDifferenceSum_of_crossed`. -/
private theorem principalFiveTerm_crossed_rates (d : ℕ) (hd : 3 < d)
    (u₁ u₂ v₁ v₂ : ℤ)
    (hu : principalFiveTermLatticeIndex d u₁ u₂ < principalFiveTermUpperIndexBound d)
    (huNonneg : 0 ≤ principalFiveTermLatticeIndex d u₁ u₂)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂) :
    0 < principalFiveTermUpperRate d (u₁ + 1)
        (principalFiveTermLatticeArgument d u₁ u₂) ∧
      principalFiveTermLowerRate d (u₁ + 1) v₁
        (principalFiveTermLatticeArgument d u₁ u₂)
        (principalFiveTermLatticeArgument d v₁ v₂) < 0 := by
  constructor
  · rw [principalFiveTermUpperRate_latticeArgument d hd]
    exact sub_pos.mpr ((principalFiveTermLatticeRate_lt_one_iff d hd u₁ u₂).2
      (by omega))
  · rw [principalFiveTermLowerRate_latticeArgument d hd]
    have hsum : 0 < principalFiveTermLatticeIndex d u₁ u₂ +
        principalFiveTermLatticeIndex d v₁ v₂ := by omega
    exact neg_lt_zero.mpr ((principalFiveTermLatticeRates_add_pos_iff d hd u₁ u₂ v₁ v₂).2
      hsum)

/-- Shifting `y` by `aρ_d+b` preserves regularity of a translated contour crossing;
used by `integral_principalFiveTermDifferenceSum_of_crossed`. -/
private theorem principalFiveTerm_crossed_shiftedRegular (d : ℕ) (hd : 3 < d)
    (y x : ℝ)
    (hx : IsRegularPeriodLatticeCrossing (principalRoot d) y x) :
    IsRegularPeriodLatticeCrossing (principalRoot d)
      (principalFiveTermShiftedParameter d y) x := by
  refine ⟨hx.base, ?_⟩
  have h := (isPeriodLatticePoint_add_int_mul_add_int_iff
    (principalRoot d : ℂ) ((x : ℂ) + y) ((principalA d) 0 0) ((principalA d) 0 1)).not.mpr
      hx.shifted
  rw [principalFiveTermShiftedParameter_eq d hd y]
  simpa only [add_assoc] using h

/-- The shifted left endpoint is `β-mε/c` on the common line; used by
`integral_principalFiveTermDifferenceSum_of_crossed`. -/
private theorem principalFiveTerm_crossed_leftBound (d : ℕ) (hd : 3 < d)
    (v₁ m : ℤ) (y x : ℝ)
    (hx : -((v₁ : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) + y) < x) :
    (-((m + (v₁ - (principalA d) 0 0) : ℤ) : ℝ) * principalRoot d ^ 3 - 1) /
        ((principalA d) 1 0 : ℝ) - principalFiveTermShiftedParameter d y <
      x - (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) := by
  have hc : ((principalA d) 1 0 : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (principalA_lowerLeft_pos d hd))
  have hident :
      (-((m + (v₁ - (principalA d) 0 0) : ℤ) : ℝ) * principalRoot d ^ 3 - 1) /
          ((principalA d) 1 0 : ℝ) - principalFiveTermShiftedParameter d y =
        -((v₁ : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) + y) -
          (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) := by
    dsimp [principalFiveTermShiftedParameter]
    push_cast
    field_simp [hc]
    ring
  rw [hident]
  linarith

/-! ### Divisors at the crossed positions

At `j/c`, a shifted denominator can lie on the period lattice only when `S_d(v)=H`.
Its second divisor coordinate is then `-j`, which excludes a denominator zero for `j≥0`.
The numerator has order at least `-1`, and an off-lattice numerator gives a removable germ.
-/

/-- The coefficient of `ρ_d` in the source argument is
`-v₁-S_d(v)/H_d`; used to exclude a denominator zero at a crossed numerator pole in
`integral_principalFiveTermDifferenceSum_of_crossed`. -/
private theorem principalFiveTerm_crossed_latticeCoefficient (d : ℕ) (hd : 3 < d)
    (v₁ v₂ : ℤ) :
    principalFiveTermRationalCharacteristic d v₁ v₂ 1 =
      -(v₁ : ℚ) - (principalFiveTermLatticeIndex d v₁ v₂ : ℚ) /
        (principalFiveTermUpperIndexBound d : ℚ) := by
  have hd3 : (d : ℚ) - 3 ≠ 0 := by
    exact_mod_cast (by omega : (d : ℤ) - 3 ≠ 0)
  simp [principalFiveTermRationalCharacteristic, latticeCharacteristicLift, coe_principalA,
    principalDilogOrder, principalFiveTermLatticeIndex, principalFiveTermUpperIndexBound,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.adjugate_fin_two,
    Nat.cast_sub (by omega : 3 ≤ d)]
  field_simp [hd3]
  ring

/-- The second divisor coordinate of the source characteristic is `S_d(v)/H_d`;
used by `integral_principalFiveTermDifferenceSum_of_crossed`. -/
private theorem principalFiveTerm_crossed_latticeSecond (d : ℕ) (hd : 3 < d)
    (v₁ v₂ : ℤ) :
    -((principalA d) 1 0 : ℚ) * principalFiveTermRationalCharacteristic d v₁ v₂ 0 +
      ((d : ℚ) - 1) * principalFiveTermRationalCharacteristic d v₁ v₂ 1 =
        (principalFiveTermLatticeIndex d v₁ v₂ : ℚ) /
          (principalFiveTermUpperIndexBound d : ℚ) := by
  have hrow := congrFun
    (ratVecAction_rationalCharacteristic_sub d hd v₁ v₂) 1
  simp only [Pi.sub_apply, ratVecAction, Matrix.mulVec_fin_two,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at hrow
  rw [principalFiveTerm_crossed_latticeCoefficient d hd v₁ v₂] at *
  simp [coe_principalA] at hrow ⊢
  linear_combination -hrow

/-- Rational coordinate comparison for a shifted denominator lattice point;
used by `principalFiveTerm_crossed_denominator_coordinates`. -/
private theorem principalFiveTerm_crossed_denominator_rat
    (d : ℕ) (hd : 3 < d) (v₁ v₂ m j k l : ℤ)
    (hpoint : (j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) -
        (m : ℂ) * (principalRoot d : ℂ) ^ 3 / (((principalA d) 1 0 : ℤ) : ℂ) +
          (principalFiveTermShiftedParameter d
            (principalFiveTermLatticeArgument d v₁ v₂) : ℂ) =
        (k : ℂ) * (principalRoot d : ℂ) + l) :
    let A : ℚ := principalFiveTermRationalCharacteristic d v₁ v₂ 1
    let B : ℚ := principalFiveTermRationalCharacteristic d v₁ v₂ 0
    let a : ℤ := (principalA d) 0 0
    let b : ℤ := (principalA d) 0 1
    let c : ℤ := (principalA d) 1 0
    A + a - m - k = 0 ∧
      (l : ℚ) - ((j : ℚ) + m * ((d : ℚ) - 1)) / c + B - b = 0 := by
  dsimp
  let A : ℚ := principalFiveTermRationalCharacteristic d v₁ v₂ 1
  let B : ℚ := principalFiveTermRationalCharacteristic d v₁ v₂ 0
  let a : ℤ := (principalA d) 0 0
  let b : ℤ := (principalA d) 0 1
  let c : ℤ := (principalA d) 1 0
  have hc : (c : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (principalA_lowerLeft_pos d hd))
  have hε : principalRoot d ^ 3 = (c : ℝ) * principalRoot d + (1 - (d : ℝ)) := by
    simpa [c, coe_principalA] using principalRoot_pow_three_eq d hd
  have hy : principalFiveTermLatticeArgument d v₁ v₂ =
      (A : ℝ) * principalRoot d - (B : ℝ) := by
    simpa only [A, B, fracSymplecticFormRat] using
      (fracSymplecticFormRat_rationalCharacteristic d hd v₁ v₂).symm
  have hshift : principalFiveTermShiftedParameter d
      (principalFiveTermLatticeArgument d v₁ v₂) =
        principalFiveTermLatticeArgument d v₁ v₂ +
          (a : ℝ) * principalRoot d + b := by
    have hs := congrArg Complex.re
      (principalFiveTermShiftedParameter_eq d hd
        (principalFiveTermLatticeArgument d v₁ v₂))
    simpa only [a, b, Complex.ofReal_re, Complex.intCast_re, Complex.mul_re,
      Complex.ofReal_im, Complex.intCast_im, mul_zero, sub_zero, zero_mul, add_zero,
      Complex.add_re, add_assoc] using hs
  have hreal : (j : ℝ) / c - (m : ℝ) * principalRoot d ^ 3 / c +
      principalFiveTermShiftedParameter d
        (principalFiveTermLatticeArgument d v₁ v₂) =
        (k : ℝ) * principalRoot d + l := by
    exact_mod_cast hpoint
  have hcoord : (j : ℝ) / c - (m : ℝ) * principalRoot d ^ 3 / c +
      principalFiveTermShiftedParameter d
        (principalFiveTermLatticeArgument d v₁ v₂) =
        ((A + a - m : ℚ) : ℝ) * principalRoot d +
          (((j : ℚ) + m * ((d : ℚ) - 1)) / c - B + b : ℚ) := by
    rw [hshift, hy, hε]
    push_cast
    field_simp [hc]
    ring
  have hrel : (((A + a - m - k : ℚ) : ℝ) * principalRoot d) =
      (((l : ℚ) - ((j : ℚ) + m * ((d : ℚ) - 1)) / c + B - b : ℚ) : ℝ) := by
    have h := hcoord.symm.trans hreal
    push_cast at h ⊢
    linear_combination h
  have hcoeff : (A + a - m - k : ℚ) = 0 := by
    exact (ratCast_eq_zero_of_irrational_mul (principalRoot_irrational d hd) hrel).1
  have hconstant : (l : ℚ) - ((j : ℚ) + m * ((d : ℚ) - 1)) / c + B - b = 0 := by
    exact (ratCast_eq_zero_of_irrational_mul (principalRoot_irrational d hd) hrel).2
  exact ⟨hcoeff, hconstant⟩

/-- At a common-line numerator pole `j/c`, any lattice coordinate of the shifted denominator
has `S_d(v)=H_d` and divisor coordinate `-j`; used by
`integral_principalFiveTermDifferenceSum_of_crossed`. -/
private theorem principalFiveTerm_crossed_denominator_coordinates
    (d : ℕ) (hd : 3 < d) (v₁ v₂ m j k l : ℤ)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d)
    (hpoint : (j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) -
        (m : ℂ) * (principalRoot d : ℂ) ^ 3 / (((principalA d) 1 0 : ℤ) : ℂ) +
          (principalFiveTermShiftedParameter d
            (principalFiveTermLatticeArgument d v₁ v₂) : ℂ) =
        (k : ℂ) * (principalRoot d : ℂ) + l) :
    principalFiveTermLatticeIndex d v₁ v₂ = principalFiveTermUpperIndexBound d ∧
      (1 - (d : ℤ)) * k - (principalA d) 1 0 * l = -j := by
  let A : ℚ := principalFiveTermRationalCharacteristic d v₁ v₂ 1
  let B : ℚ := principalFiveTermRationalCharacteristic d v₁ v₂ 0
  let a : ℤ := (principalA d) 0 0
  let b : ℤ := (principalA d) 0 1
  let c : ℤ := (principalA d) 1 0
  let S : ℤ := principalFiveTermLatticeIndex d v₁ v₂
  let H : ℤ := principalFiveTermUpperIndexBound d
  have hH : 0 < H := principalFiveTermUpperIndexBound_pos d hd
  obtain ⟨hcoeff, hconstant⟩ :=
    principalFiveTerm_crossed_denominator_rat d hd v₁ v₂ m j k l hpoint
  change A + a - m - k = 0 at hcoeff
  change (l : ℚ) - ((j : ℚ) + m * ((d : ℚ) - 1)) / c + B - b = 0 at hconstant
  have hA := principalFiveTerm_crossed_latticeCoefficient d hd v₁ v₂
  have hB := principalFiveTerm_crossed_latticeSecond d hd v₁ v₂
  change A = -(v₁ : ℚ) - (S : ℚ) / H at hA
  change -(c : ℚ) * B + ((d : ℚ) - 1) * A = (S : ℚ) / H at hB
  have hHQ : (0 : ℚ) < H := by exact_mod_cast hH
  have hSQ : (0 : ℚ) < S := by exact_mod_cast hv.1
  have hSleQ : (S : ℚ) ≤ H := by exact_mod_cast hv.2
  have hratio : (S : ℚ) / H = ((a - m - k - v₁ : ℤ) : ℚ) := by
    push_cast
    linear_combination hA - hcoeff
  have hunit : a - m - k - v₁ = 1 := by
    have hpos : (0 : ℚ) < (a - m - k - v₁ : ℤ) := by
      rw [← hratio]
      exact div_pos hSQ hHQ
    have hle : ((a - m - k - v₁ : ℤ) : ℚ) ≤ 1 := by
      rw [← hratio]
      exact (div_le_one hHQ).2 hSleQ
    have hposInt : 0 < a - m - k - v₁ := by exact_mod_cast hpos
    have hleInt : a - m - k - v₁ ≤ 1 := by exact_mod_cast hle
    omega
  have hS : S = H := by
    have hr : (S : ℚ) / H = 1 := by rw [hratio, hunit]; norm_num
    exact_mod_cast (div_eq_one_iff_eq hHQ.ne').mp hr
  have hcQ : (c : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (principalA_lowerLeft_pos d hd))
  have hdet : (a : ℚ) * (1 - (d : ℚ)) - (b : ℚ) * c = 1 := by
    simp [a, b, c, coe_principalA]
    ring
  have hcoordQ : ((1 - (d : ℚ)) * k - (c : ℚ) * l) = -(j : ℚ) := by
    rw [hS] at hB
    have hratio' : (H : ℚ) / H = 1 := by field_simp [hHQ.ne']
    rw [hratio'] at hB
    field_simp [hcQ] at hconstant
    linear_combination -(1 - (d : ℚ)) * hcoeff - hconstant - hB + hdet
  exact ⟨hS, by exact_mod_cast hcoordQ⟩

/-- The shifted denominator has no zero at any crossed numerator position `j/c`, `j≥0`;
used by `integral_principalFiveTermDifferenceSum_of_crossed`. -/
private theorem principalFiveTerm_crossed_denominator_nonpos
    (d : ℕ) (hd : 3 < d) (v₁ v₂ m j : ℤ)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d)
    (hj : 0 ≤ j) :
    meromorphicOrderAt (principalFaddeev d
      (m + v₁ - (principalA d) 0 0) 0)
        ((j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) -
          (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
            (((principalA d) 1 0 : ℤ) : ℂ) +
          (principalFiveTermShiftedParameter d
            (principalFiveTermLatticeArgument d v₁ v₂) : ℂ)) ≤ 0 := by
  let z : ℂ := (j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) -
    (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
      (((principalA d) 1 0 : ℤ) : ℂ) +
    (principalFiveTermShiftedParameter d
      (principalFiveTermLatticeArgument d v₁ v₂) : ℂ)
  by_cases hlat : IsPeriodLatticePoint (principalRoot d : ℂ) z
  · obtain ⟨l, k, hpoint⟩ := hlat
    apply le_of_not_gt
    intro hpos
    have hpos' : 0 < meromorphicOrderAt
        (principalFaddeev d (m + v₁ - (principalA d) 0 0) 0)
        ((k : ℂ) * (principalRoot d : ℂ) + l) := by
      change 0 < meromorphicOrderAt
        (principalFaddeev d (m + v₁ - (principalA d) 0 0) 0) z at hpos
      rw [hpoint] at hpos
      simpa only [add_comm] using hpos
    obtain ⟨_, hdiv⟩ :=
      (meromorphicOrderAt_principalFaddeev_pos_iff d hd
        (m + v₁ - (principalA d) 0 0) 0 k l).mp hpos'
    have hcoords := (principalFiveTerm_crossed_denominator_coordinates
      d hd v₁ v₂ m j k l hv (by simpa only [z, add_comm] using hpoint)).2
    rw [show (principalA d) 1 0 = (d : ℤ) * ((d : ℤ) - 2) by simp [coe_principalA]]
      at hcoords
    omega
  · rw [meromorphicOrderAt_principalFaddeev_eq_zero
      d hd _ _ z hlat]

/-- A lattice coordinate of the translated numerator position `j/c-mε/c` has row index
`-m` and column coordinate `cl=j+m(d-1)`; used by
`integral_principalFiveTermDifferenceSum_of_crossed`. -/
private theorem principalFiveTerm_crossed_numerator_coordinates
    (d : ℕ) (hd : 3 < d) (m j k l : ℤ)
    (hpoint : (j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) -
        (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
          (((principalA d) 1 0 : ℤ) : ℂ) =
        (k : ℂ) * (principalRoot d : ℂ) + l) :
    k = -m ∧ (principalA d) 1 0 * l = j + m * ((d : ℤ) - 1) := by
  let c : ℤ := (principalA d) 1 0
  have hc : (c : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (principalA_lowerLeft_pos d hd))
  have hε : principalRoot d ^ 3 = (c : ℝ) * principalRoot d + (1 - (d : ℝ)) := by
    simpa [c, coe_principalA] using principalRoot_pow_three_eq d hd
  have hreal : (j : ℝ) / c - (m : ℝ) * principalRoot d ^ 3 / c =
      (k : ℝ) * principalRoot d + l := by
    exact_mod_cast hpoint
  have hrel : (((m + k : ℤ) : ℚ) : ℝ) * principalRoot d =
      ((((j + m * ((d : ℤ) - 1) - c * l : ℤ) : ℚ) / c : ℚ) : ℝ) := by
    push_cast at *
    field_simp [hc] at hreal ⊢
    linear_combination -hreal - (m : ℝ) * hε
  obtain ⟨hfirst, hsecond⟩ :=
    ratCast_eq_zero_of_irrational_mul (principalRoot_irrational d hd) hrel
  have hk : k = -m := by
    have h : m + k = 0 := by exact_mod_cast hfirst
    omega
  have hl : c * l = j + m * ((d : ℤ) - 1) := by
    have h : j + m * ((d : ℤ) - 1) - c * l = 0 := by
      have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc
      have hnum : ((j + m * ((d : ℤ) - 1) - c * l : ℤ) : ℚ) = 0 :=
        ((div_eq_zero_iff).mp hsecond).resolve_right hcQ
      exact_mod_cast hnum
    omega
  exact ⟨hk, hl⟩

/-- Every shifted five-term kernel has at most a simple pole at a nonnegative common-line
point `j/c`; used by `integral_principalFiveTermDifferenceSum_of_crossed`. -/
private theorem principalFiveTerm_crossed_kernel_order_ge_neg_one
    (d : ℕ) (hd : 3 < d) (ℓ v₁ v₂ m j : ℤ) (w : ℝ)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d)
    (hj : 0 ≤ j) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (principalFiveTermKernel d ℓ (v₁ - (principalA d) 0 0) w
        (principalFiveTermShiftedParameter d
          (principalFiveTermLatticeArgument d v₁ v₂)) m)
        ((j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) -
          (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
            (((principalA d) 1 0 : ℤ) : ℂ)) := by
  let z : ℂ := (j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) -
    (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
      (((principalA d) 1 0 : ℤ) : ℂ)
  let y' := principalFiveTermShiftedParameter d
    (principalFiveTermLatticeArgument d v₁ v₂)
  rw [meromorphicOrderAt_principalFiveTermKernel d hd]
  have hN := meromorphicOrderAt_principalFaddeev_ge_neg_one d hd (m + 1) 0 z
  have hD := principalFiveTerm_crossed_denominator_nonpos d hd v₁ v₂ m j hv hj
  rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
  have hD' : meromorphicOrderAt
      (principalFaddeev d (m + (v₁ - (principalA d) 0 0)) 0)
        (z + (y' : ℂ)) ≤ 0 := by
    simpa only [z, y', sub_eq_add_neg, add_assoc] using hD
  have hneg : 0 ≤ -(meromorphicOrderAt
      (principalFaddeev d (m + (v₁ - (principalA d) 0 0)) 0)
        (z + (y' : ℂ))) := by
    rcases lt_or_eq_of_le hD' with hlt | heq
    · exact le_of_lt ((LinearOrderedAddCommGroupWithTop.neg_pos).2 (Or.inl hlt))
    · rw [heq]
      simp
  rw [sub_eq_add_neg]
  exact hN.trans (le_add_of_nonneg_right hneg)

/-- A summand whose numerator is off the period lattice is regular at `j/c`; used by
`integral_principalFiveTermDifferenceSum_of_crossed`. -/
private theorem principalFiveTerm_crossed_kernel_order_nonneg
    (d : ℕ) (hd : 3 < d) (ℓ v₁ v₂ m j : ℤ) (w : ℝ)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d)
    (hj : 0 ≤ j)
    (hlat : ¬ IsPeriodLatticePoint (principalRoot d : ℂ)
      ((j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) -
        (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
          (((principalA d) 1 0 : ℤ) : ℂ))) :
    0 ≤ meromorphicOrderAt
      (principalFiveTermKernel d ℓ (v₁ - (principalA d) 0 0) w
        (principalFiveTermShiftedParameter d
          (principalFiveTermLatticeArgument d v₁ v₂)) m)
        ((j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) -
          (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
            (((principalA d) 1 0 : ℤ) : ℂ)) := by
  rw [meromorphicOrderAt_principalFiveTermKernel d hd,
    meromorphicOrderAt_principalFaddeev_eq_zero d hd _ _ _ hlat,
    meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
  have hD := principalFiveTerm_crossed_denominator_nonpos d hd v₁ v₂ m j hv hj
  have hD' : meromorphicOrderAt
      (principalFaddeev d (m + (v₁ - (principalA d) 0 0)) 0)
        ((j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) -
          (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
            (((principalA d) 1 0 : ℤ) : ℂ) +
          (principalFiveTermShiftedParameter d
            (principalFiveTermLatticeArgument d v₁ v₂) : ℂ)) ≤ 0 := by
    simpa only [sub_eq_add_neg, add_assoc] using hD
  have hneg : 0 ≤ -(meromorphicOrderAt
      (principalFaddeev d (m + (v₁ - (principalA d) 0 0)) 0)
        ((j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) -
          (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
            (((principalA d) 1 0 : ℤ) : ℂ) +
          (principalFiveTermShiftedParameter d
            (principalFiveTermLatticeArgument d v₁ v₂) : ℂ))) := by
    rcases lt_or_eq_of_le hD' with hlt | heq
    · exact le_of_lt ((LinearOrderedAddCommGroupWithTop.neg_pos).2 (Or.inl hlt))
    · rw [heq]
      simp
  simpa only [sub_eq_add_neg, zero_add] using hneg

/-! ### Matching the right poles

A right pole in common-line coordinates is `(Nε+j)/c`, with `N,j≥0`. Since `x<ε/c`,
every crossed pole has `N=0`. Irrationality identifies its original lattice coordinates
uniquely, so each column `j/c` has at most one pole for each contour index.
-/

/-- Every lattice numerator point `j/c-mε/c`, `j≥0`, is the real-period right pole with
forward index zero and column index `j`; used by
`integral_principalFiveTermDifferenceSum_of_crossed`. -/
private theorem principalFiveTerm_crossed_rightPole_of_lattice
    (d : ℕ) (hd : 3 < d) (m j : ℤ) (hj : 0 ≤ j)
    (hlat : IsPeriodLatticePoint (principalRoot d : ℂ)
      ((j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) -
        (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
          (((principalA d) 1 0 : ℤ) : ℂ))) :
    ∃ k : ℤ,
      faddeevModularUHPIndex (principalA d) m k j.toNat = 0 ∧
        faddeevModularUHPPole (principalA d) (principalRoot d) k j.toNat =
          (j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) -
            (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
              (((principalA d) 1 0 : ℤ) : ℂ) := by
  obtain ⟨l, K, hp⟩ := hlat
  have hl := (principalFiveTerm_crossed_numerator_coordinates d hd m j K l
    (by simpa only [add_comm] using hp)).2
  let a : ℤ := (principalA d) 0 0
  let b : ℤ := (principalA d) 0 1
  let c : ℤ := (principalA d) 1 0
  let k : ℤ := a * l + b * m
  have hdet : a * (1 - (d : ℤ)) - b * c = 1 := by
    simp [a, b, c, coe_principalA]
    ring
  have hjcast : ((j.toNat : ℕ) : ℤ) = j := by omega
  have hjC : (j.toNat : ℂ) = (j : ℂ) := by exact_mod_cast hjcast
  have hN : faddeevModularUHPIndex (principalA d) m k j.toNat = 0 := by
    simp only [faddeevModularUHPIndex, hjcast, k, a, b]
    linear_combination ((principalA d) 0 0) * hl - m * hdet
  refine ⟨k, hN, ?_⟩
  have hc : (c : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (principalA_lowerLeft_pos d hd))
  have hε : fltDenominator (principalA d : Mat(2, ℤ)) (principalRoot d : ℂ) =
      (principalRoot d : ℂ) ^ 3 :=
    fltDenominator_principalA_principalRoot_complex d hd
  have hlin := faddeevModularUHPPole_linear (principalA d)
    (principalRoot d : ℂ) (by rw [hε]; exact pow_ne_zero _ (ofReal_principalRoot_ne_zero d hd))
    m k j.toNat
  rw [hε, hN] at hlin
  have hlin' : (c : ℂ) *
      faddeevModularUHPPole (principalA d) (principalRoot d) k j.toNat +
        (principalRoot d : ℂ) ^ 3 * m = j := by
    simpa only [c, hjC, Int.cast_zero, mul_zero, zero_add] using hlin
  calc
    _ = ((j : ℂ) - (m : ℂ) * (principalRoot d : ℂ) ^ 3) / (c : ℂ) := by
      apply (eq_div_iff hc).2
      linear_combination hlin'
    _ = _ := by ring

/-- A genuine right pole left of `x<ε/c` has forward index zero and common-line coordinate
`j/c`; used by `integral_principalFiveTermDifferenceSum_of_crossed`. -/
private theorem principalFiveTerm_crossed_rightPole_zeroIndex
    (d : ℕ) (hd : 3 < d) (m k : ℤ) (j : ℕ) (x : ℝ)
    (hx : x < principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ))
    (hN : 0 ≤ faddeevModularUHPIndex (principalA d) m k j)
    (hleft : (faddeevModularUHPPole (principalA d) (principalRoot d) k j).re <
      x - (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ)) :
    faddeevModularUHPIndex (principalA d) m k j = 0 ∧
      faddeevModularUHPPole (principalA d) (principalRoot d) k j +
        (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
          (((principalA d) 1 0 : ℤ) : ℂ) =
        (j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) := by
  let N := faddeevModularUHPIndex (principalA d) m k j
  let c : ℝ := ((principalA d) 1 0 : ℝ)
  let ε := principalRoot d ^ 3
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast principalA_lowerLeft_pos d hd
  have hε : 0 < ε := pow_pos (principalRoot_pos d hd) _
  have hreal := re_faddeevModularUHPPole (principalA d)
    (principalA_lowerLeft_pos d hd) (principalRoot d : ℂ)
    (fltDenominator_principalA_principalRoot_ne_zero d hd) m k j
  have hreal' : (faddeevModularUHPPole (principalA d) (principalRoot d) k j).re =
      (((N : ℝ) - m) * ε + j) / c := by
    simpa only [N, c, ε, fltDenominator_principalA_principalRoot_complex d hd,
      ← Complex.ofReal_pow, Complex.ofReal_re] using hreal
  have hbound : (N : ℝ) * ε + j < c * x := by
    rw [hreal'] at hleft
    change (((N : ℝ) - m) * ε + j) / c < x - (m : ℝ) * ε / c at hleft
    have hmul := (div_lt_iff₀ hc).mp hleft
    have hcan : (m : ℝ) * ε / c * c = (m : ℝ) * ε :=
      div_mul_cancel₀ _ hc.ne'
    nlinarith [hmul]
  have hcx : c * x < ε := by
    simpa only [c, ε, mul_comm] using (lt_div_iff₀ hc).mp hx
  have hN0 : N = 0 := by
    by_contra hne
    have hN1 : (1 : ℤ) ≤ N := by omega
    have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hmul := mul_le_mul_of_nonneg_right hN1r hε.le
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    nlinarith
  refine ⟨hN0, ?_⟩
  have hlin := faddeevModularUHPPole_linear (principalA d)
    (principalRoot d : ℂ) (fltDenominator_principalA_principalRoot_ne_zero d hd)
    m k j
  have hN0' : faddeevModularUHPIndex (principalA d) m k j = 0 := hN0
  rw [fltDenominator_principalA_principalRoot_complex d hd, hN0'] at hlin
  have hcC : ((((principalA d) 1 0 : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (principalA_lowerLeft_pos d hd))
  field_simp [hcC]
  simp only [Int.cast_zero, mul_zero, zero_add] at hlin
  linear_combination hlin

/-- The common-line difference sum is the shifted five-term sum as a meromorphic germ;
used by `integral_principalFiveTermDifferenceSum_of_crossed`. -/
private theorem principalFiveTerm_crossed_differenceSum_germ
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ) (z : ℂ) :
    principalFiveTermDifferenceSum d ℓ p w y =ᶠ[𝓝[≠] z]
      (fun ζ => (1 - Complex.exp (2 * Real.pi * I *
        ((y : ℂ) + p * (principalRoot d : ℂ)))) *
          ∑ m : FiveTermIndex (principalA d),
            principalFiveTermKernel d ℓ (p - (principalA d) 0 0) w
              (principalFiveTermShiftedParameter d y) ((m : ℕ) : ℤ)
              (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
                ((principalA d) 1 0 : ℂ))) := by
  have hEach (m : FiveTermIndex (principalA d)) :
      (fun ζ => principalFiveTermDifferenceKernel d ℓ p w y ((m : ℕ) : ℤ)
        (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
          ((principalA d) 1 0 : ℂ))) =ᶠ[𝓝[≠] z]
      (fun ζ => (1 - Complex.exp (2 * Real.pi * I *
        ((y : ℂ) + p * (principalRoot d : ℂ)))) *
        principalFiveTermKernel d ℓ (p - (principalA d) 0 0) w
          (principalFiveTermShiftedParameter d y) ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
            ((principalA d) 1 0 : ℂ))) := by
    let v : ℂ := ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
      ((principalA d) 1 0 : ℂ)
    have ht : Tendsto (fun ζ : ℂ => ζ - v) (𝓝[≠] z) (𝓝[≠] (z - v)) := by
      simpa only [sub_eq_add_neg] using tendsto_add_const_nhdsNE (-v) z
    simpa only [v, Function.comp_def] using
      (principalFiveTermDifferenceKernel_eventuallyEq d hd ℓ p w y
        ((m : ℕ) : ℤ) (z - v)).comp_tendsto ht
  filter_upwards [Filter.eventually_all.mpr hEach] with ζ hζ
  simp only [principalFiveTermDifferenceSum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => hζ m)

/-- A crossed right pole lies in its zero-index common-line column; used by
`principalFiveTerm_crossed_column_square` and `principalFiveTerm_crossed_squares_eq`. -/
private theorem principalFiveTerm_crossed_Gposition
    (d : ℕ) (hd : 3 < d) (m : FiveTermIndex (principalA d))
    (kj : ℤ × ℕ) (x : ℝ)
    (hx : x < principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ))
    (hG : 0 ≤ faddeevModularUHPIndex (principalA d) ((m : ℕ) : ℤ) kj.1 kj.2 ∧
      (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2).re <
        x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ)) :
    faddeevModularUHPIndex (principalA d) ((m : ℕ) : ℤ) kj.1 kj.2 = 0 ∧
      faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 +
        ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
          (((principalA d) 1 0 : ℤ) : ℂ) =
        (kj.2 : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) :=
  principalFiveTerm_crossed_rightPole_zeroIndex d hd ((m : ℕ) : ℤ)
    kj.1 kj.2 x hx hG.1 hG.2

/-- A right pole with forward index zero and translated real part left of `x` has its
nonnegative column in `F`; used by `principalFiveTerm_crossed_squares_eq`. -/
private theorem principalFiveTerm_crossed_rightPole_mem_F
    (d : ℕ) (x : ℝ) (F : Finset ℤ)
    (hF : ∀ j : ℤ, 0 ≤ j →
      (j : ℝ) / ((principalA d) 1 0 : ℝ) < x → j ∈ F)
    (m : ℤ) (kj : ℤ × ℕ)
    (hpos : faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 +
      (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
        (((principalA d) 1 0 : ℤ) : ℂ) =
      (kj.2 : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ))
    (hleft : (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2).re <
      x - (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ)) :
    (kj.2 : ℤ) ∈ F := by
  let ε := principalRoot d ^ 3
  let c : ℝ := ((principalA d) 1 0 : ℝ)
  have hpos' :
      faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 +
        (((m : ℝ) * ε / c : ℝ) : ℂ) = (((kj.2 : ℝ) / c : ℝ) : ℂ) := by
    simpa only [ε, c, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_intCast, Complex.ofReal_natCast] using hpos
  have hre :
      (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2).re +
        (m : ℝ) * ε / c = (kj.2 : ℝ) / c := by
    simpa only [Complex.add_re, Complex.ofReal_re] using congrArg Complex.re hpos'
  apply hF _ (by exact_mod_cast Nat.zero_le kj.2)
  push_cast
  linarith

/-- Every crossed pole belongs to the unique nonnegative common-line column in `F`;
used by `principalFiveTerm_crossed_squares_eq`. -/
private theorem principalFiveTerm_crossed_Gposition_mem_F
    (d : ℕ) (hd : 3 < d) (x : ℝ) (F : Finset ℤ)
    (hx : x < principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ))
    (hF : ∀ j : ℤ, 0 ≤ j →
      (j : ℝ) / ((principalA d) 1 0 : ℝ) < x → j ∈ F)
    (m : FiveTermIndex (principalA d)) (kj : ℤ × ℕ)
    (hG : 0 ≤ faddeevModularUHPIndex (principalA d) ((m : ℕ) : ℤ) kj.1 kj.2 ∧
      (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2).re <
        x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ)) :
    (kj.2 : ℤ) ∈ F := by
  obtain ⟨_, hpos⟩ := principalFiveTerm_crossed_Gposition d hd m kj x hx hG
  exact principalFiveTerm_crossed_rightPole_mem_F d x F hF
    ((m : ℕ) : ℤ) kj hpos hG.2

/-- The lattice pole at column `j` is left of the shifted contour whenever `j/c<x`;
used by `principalFiveTerm_crossed_column_square`. -/
private theorem principalFiveTerm_crossed_column_left
    (d : ℕ) (m : FiveTermIndex (principalA d))
    (j : ℤ) (x : ℝ)
    (hjx : (j : ℝ) / ((principalA d) 1 0 : ℝ) < x) (k : ℤ)
    (hpole : faddeevModularUHPPole (principalA d) (principalRoot d) k j.toNat =
      (j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) -
        ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
          (((principalA d) 1 0 : ℤ) : ℂ)) :
    (faddeevModularUHPPole (principalA d) (principalRoot d) k j.toNat).re <
      x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) := by
  let ε := principalRoot d ^ 3
  let c : ℝ := ((principalA d) 1 0 : ℝ)
  have hpole' : faddeevModularUHPPole (principalA d) (principalRoot d) k j.toNat =
      (((j : ℝ) / c - ((m : ℕ) : ℝ) * ε / c : ℝ) : ℂ) := by
    simpa only [ε, c, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_intCast,
      Complex.ofReal_natCast, Int.cast_natCast] using hpole
  have hre := congrArg Complex.re hpole'
  simp only [Complex.ofReal_re] at hre
  dsimp [ε, c] at hre
  linarith

/-- A fixed nonnegative column determines the crossed right pole uniquely;
used by `principalFiveTerm_crossed_column_square`. -/
private theorem principalFiveTerm_crossed_column_unique
    (d : ℕ) (hd : 3 < d) (m : FiveTermIndex (principalA d))
    (j : ℤ) (hj : 0 ≤ j) (k : ℤ) (kj : ℤ × ℕ)
    (hpole : faddeevModularUHPPole (principalA d) (principalRoot d) k j.toNat =
      (j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) -
        ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
          (((principalA d) 1 0 : ℤ) : ℂ))
    (hpos : faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 +
        ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
          (((principalA d) 1 0 : ℤ) : ℂ) =
        (kj.2 : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ))
    (hcol : kj.2 = j.toNat) : kj = (k, j.toNat) := by
  have hjcast : (j.toNat : ℂ) = (j : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg hj
  have heq : faddeevModularUHPPole (principalA d) (principalRoot d)
      kj.1 kj.2 =
        faddeevModularUHPPole (principalA d) (principalRoot d) k j.toNat := by
    rw [hcol, hjcast] at hpos
    rw [hcol]
    calc
      _ = (j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) -
          ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
            (((principalA d) 1 0 : ℤ) : ℂ) := by
        linear_combination hpos
      _ = _ := hpole.symm
  exact (faddeevModularUHPPole_ofReal_injective (principalA d)
    (principalRoot d) (principalRoot_irrational d hd)
    (fltDenominator_principalA_principalRoot_ne_zero d hd)) heq

/-! ### The square corrections

Translate each kernel square to the common line. The matching pole contributes its square
integral, while the other summands are removable and contribute zero. The germ identity
for the difference kernel and finite reindexing then give the same correction as (23).
-/

/-- At one common-line column, the translated kernel square equals the square at
its unique crossed right pole when present, and vanishes otherwise; used by
`principalFiveTerm_crossed_squares_eq`. -/
private theorem principalFiveTerm_crossed_column_square
    (d : ℕ) (hd : 3 < d) (ℓ v₁ v₂ : ℤ) (w x : ℝ)
    (G : FiveTermIndex (principalA d) → Finset (ℤ × ℕ))
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d)
    (m : FiveTermIndex (principalA d)) (j : ℤ) (hj : 0 ≤ j) :
    let ε := principalRoot d ^ 3
    let c : ℝ := ((principalA d) 1 0 : ℝ)
    let y' := principalFiveTermShiftedParameter d
      (principalFiveTermLatticeArgument d v₁ v₂)
    let x' : FiveTermIndex (principalA d) → ℝ :=
      fun m => x - ((m : ℕ) : ℝ) * ε / c
    x < ε / c →
    (∀ (m : FiveTermIndex (principalA d)) (kj : ℤ × ℕ),
      kj ∈ G m ↔ 0 ≤ faddeevModularUHPIndex (principalA d) ((m : ℕ) : ℤ) kj.1 kj.2 ∧
        (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2).re < x' m) →
    (j : ℝ) / c < x →
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      rectBoundaryIntegral
        (fun ζ => principalFiveTermKernel d ℓ
          (v₁ - (principalA d) 0 0) w y' ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
            ((principalA d) 1 0 : ℂ)))
        ((j : ℂ) / (c : ℂ) - (r + r * I))
        ((j : ℂ) / (c : ℂ) + (r + r * I)) =
      ∑ kj ∈ G m,
        if kj.2 = j.toNat then
          rectBoundaryIntegral (principalFiveTermKernel d ℓ
            (v₁ - (principalA d) 0 0) w y' ((m : ℕ) : ℤ))
            (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 -
              (r + r * I))
            (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 +
              (r + r * I))
        else 0 := by
  dsimp
  intro hxε hG hjx
  let ε := principalRoot d ^ 3
  let c : ℝ := ((principalA d) 1 0 : ℝ)
  let y' := principalFiveTermShiftedParameter d
    (principalFiveTermLatticeArgument d v₁ v₂)
  let x' : FiveTermIndex (principalA d) → ℝ :=
    fun m => x - ((m : ℕ) : ℝ) * ε / c
  let p : ℂ := (j : ℂ) / (c : ℂ)
  let v : ℂ := ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
    ((principalA d) 1 0 : ℂ)
  let z : ℂ := p - v
  let K : ℂ → ℂ := principalFiveTermKernel d ℓ
    (v₁ - (principalA d) 0 0) w y' ((m : ℕ) : ℤ)
  have hGposition (kj : ℤ × ℕ) (hkj : kj ∈ G m) :=
    (principalFiveTerm_crossed_Gposition d hd m kj x hxε ((hG m kj).mp hkj)).2
  have hMer : MeromorphicAt K z := by
    exact meromorphicAt_principalFiveTermKernel d hd _ _ _ _ _ _
  have hOrd : (-1 : WithTop ℤ) ≤ meromorphicOrderAt K z := by
    convert principalFiveTerm_crossed_kernel_order_ge_neg_one d hd
      ℓ v₁ v₂ ((m : ℕ) : ℤ) j w hv hj using 1
  have hTrans := eventually_rectBoundaryIntegral_square_translate K p v hMer hOrd
  by_cases hlat : IsPeriodLatticePoint (principalRoot d : ℂ) z
  · obtain ⟨k, hN, hpole⟩ := principalFiveTerm_crossed_rightPole_of_lattice
      d hd ((m : ℕ) : ℤ) j hj (by simpa only [z, p, v, c,
        Complex.ofReal_intCast, Int.cast_natCast] using hlat)
    have hmem : (k, j.toNat) ∈ G m := by
      apply (hG m (k, j.toNat)).2
      exact ⟨by simp only [hN, le_refl],
        principalFiveTerm_crossed_column_left d m j x hjx k hpole⟩
    have hUnique (kj : ℤ × ℕ) (hkj : kj ∈ G m)
        (hcol : kj.2 = j.toNat) : kj = (k, j.toNat) :=
      principalFiveTerm_crossed_column_unique d hd m j hj k kj hpole
        (hGposition kj hkj) hcol
    filter_upwards [hTrans] with r htrans
    change rectBoundaryIntegral (fun ζ => K (ζ - v))
      (p - (r + r * I)) (p + (r + r * I)) = _
    rw [htrans]
    have hsum := FiniteFiveTerm.unique_column_sum (G m) j k hmem hUnique
      (fun kj => rectBoundaryIntegral K
        (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 - (r + r * I))
        (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 + (r + r * I)))
    rw [hsum]
    simp only [hpole, p, v, c, Complex.ofReal_intCast, Int.cast_natCast]
  · have hOrd0 : 0 ≤ meromorphicOrderAt K z := by
      apply principalFiveTerm_crossed_kernel_order_nonneg
        d hd ℓ v₁ v₂ ((m : ℕ) : ℤ) j w hv hj
      simpa only [z, p, v, c, Complex.ofReal_intCast, Int.cast_natCast] using hlat
    have hNo (kj : ℤ × ℕ) (hkj : kj ∈ G m) : kj.2 ≠ j.toNat := by
      intro hcol
      have hp := hGposition kj hkj
      have hjcast : (j.toNat : ℂ) = (j : ℂ) := by
        exact_mod_cast Int.toNat_of_nonneg hj
      have hpole :
          faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 = z := by
        rw [hcol, hjcast] at hp
        unfold z p v
        simp only [c, Complex.ofReal_intCast]
        rw [hcol]
        linear_combination hp
      apply hlat
      rw [← hpole]
      exact isPeriodLatticePoint_faddeevModularUHPPole (principalA d)
        (principalRoot d) (fltDenominator_principalA_principalRoot_ne_zero d hd)
        kj.1 kj.2
    filter_upwards [hTrans, eventually_rectBoundaryIntegral_square_eq_zero K z hMer hOrd0]
      with r htrans hzero
    change rectBoundaryIntegral (fun ζ => K (ζ - v))
      (p - (r + r * I)) (p + (r + r * I)) = _
    rw [htrans, hzero]
    symm
    apply Finset.sum_eq_zero
    intro kj hkj
    simp [hNo kj hkj]

/-- At a nonnegative common-line point, the difference sum has the square integral of
the sum of its shifted meromorphic kernel germs; used by
`principalFiveTerm_crossed_squares_eq`. -/
private theorem principalFiveTerm_crossed_local_square
    (d : ℕ) (hd : 3 < d) (ℓ v₁ v₂ : ℤ) (w : ℝ) (j : ℤ)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d)
    (hj : 0 ≤ j) :
    let c : ℝ := ((principalA d) 1 0 : ℝ)
    let y := principalFiveTermLatticeArgument d v₁ v₂
    let y' := principalFiveTermShiftedParameter d y
    let P : ℂ := 1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + v₁ * (principalRoot d : ℂ)))
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      rectBoundaryIntegral (principalFiveTermDifferenceSum d ℓ v₁ w y)
        ((j : ℂ) / (c : ℂ) - (r + r * I))
        ((j : ℂ) / (c : ℂ) + (r + r * I)) =
        P * ∑ m : FiveTermIndex (principalA d),
          rectBoundaryIntegral
            (fun ζ => principalFiveTermKernel d ℓ
              (v₁ - (principalA d) 0 0) w y' ((m : ℕ) : ℤ)
              (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
                ((principalA d) 1 0 : ℂ)))
            ((j : ℂ) / (c : ℂ) - (r + r * I))
            ((j : ℂ) / (c : ℂ) + (r + r * I)) := by
  dsimp
  let c : ℝ := ((principalA d) 1 0 : ℝ)
  let y := principalFiveTermLatticeArgument d v₁ v₂
  let y' := principalFiveTermShiftedParameter d y
  let P : ℂ := 1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + v₁ * (principalRoot d : ℂ)))
  let p : ℂ := (j : ℂ) / (c : ℂ)
  let f : FiveTermIndex (principalA d) → ℂ → ℂ := fun m ζ =>
    principalFiveTermKernel d ℓ (v₁ - (principalA d) 0 0) w y'
      ((m : ℕ) : ℤ)
      (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ))
  have hMer (m : FiveTermIndex (principalA d)) : MeromorphicAt (f m) p := by
    change MeromorphicAt
      ((principalFiveTermKernel d ℓ
        (v₁ - (principalA d) 0 0) w y' ((m : ℕ) : ℤ)) ∘
          (fun ζ : ℂ => ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
            ((principalA d) 1 0 : ℂ))) p
    apply (meromorphicAt_comp_sub_const_iff_meromorphicAt).2
    exact meromorphicAt_principalFiveTermKernel d hd ℓ
      (v₁ - (principalA d) 0 0) ((m : ℕ) : ℤ) w y' _
  have hOrd (m : FiveTermIndex (principalA d)) :
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt (f m) p := by
    rw [meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt]
    convert principalFiveTerm_crossed_kernel_order_ge_neg_one d hd
      ℓ v₁ v₂ ((m : ℕ) : ℤ) j w ⟨hv.1, hv.2⟩ hj using 1
  have hEq : principalFiveTermDifferenceSum d ℓ v₁ w y =ᶠ[𝓝[≠] p]
      (fun ζ => P * ∑ m, f m ζ) := by
    simpa only [P, f, p] using
      principalFiveTerm_crossed_differenceSum_germ d hd ℓ v₁ w y p
  simpa only [p, f, c, y, y', P, Complex.ofReal_intCast] using
    eventually_rectBoundaryIntegral_square_mul_sum
      (principalFiveTermDifferenceSum d ℓ v₁ w y) f P p hEq hMer hOrd

/-- The small-square correction on the common line is the crossed right-pole correction
for the shifted kernels; used by `integral_principalFiveTermDifferenceSum_of_crossed`. -/
private theorem principalFiveTerm_crossed_squares_eq
    (d : ℕ) (hd : 3 < d) (ℓ v₁ v₂ : ℤ) (w x : ℝ)
    (F : Finset ℤ) (G : FiveTermIndex (principalA d) → Finset (ℤ × ℕ))
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d) :
    let ε := principalRoot d ^ 3
    let c : ℝ := ((principalA d) 1 0 : ℝ)
    let y := principalFiveTermLatticeArgument d v₁ v₂
    let y' := principalFiveTermShiftedParameter d y
    let x' : FiveTermIndex (principalA d) → ℝ :=
      fun m => x - ((m : ℕ) : ℝ) * ε / c
    let P : ℂ := 1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + v₁ * (principalRoot d : ℂ)));
    -((v₁ : ℝ) * ε / c + y) < x →
    x < ε / c →
    (∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧ (j : ℝ) / c < -((v₁ : ℝ) * ε / c + y)) →
    (∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / c < x ↔ (j : ℝ) / c < -((v₁ : ℝ) * ε / c + y))) →
    (∀ (m : FiveTermIndex (principalA d)) (kj : ℤ × ℕ),
      kj ∈ G m ↔ 0 ≤ faddeevModularUHPIndex (principalA d) ((m : ℕ) : ℤ) kj.1 kj.2 ∧
        (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2).re < x' m) →
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      (∑ j ∈ F, rectBoundaryIntegral
        (principalFiveTermDifferenceSum d ℓ v₁ w y)
          ((j : ℂ) / (c : ℂ) - (r + r * I))
          ((j : ℂ) / (c : ℂ) + (r + r * I))) =
        P * (∑ m : FiveTermIndex (principalA d), ∑ kj ∈ G m,
          rectBoundaryIntegral (principalFiveTermKernel d ℓ
            (v₁ - (principalA d) 0 0) w y' ((m : ℕ) : ℤ))
            (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 -
              (r + r * I))
            (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 +
              (r + r * I))) := by
  dsimp
  intro hxβ hxε hF hxF hG
  let ε := principalRoot d ^ 3
  let c : ℝ := ((principalA d) 1 0 : ℝ)
  let y := principalFiveTermLatticeArgument d v₁ v₂
  let y' := principalFiveTermShiftedParameter d y
  let x' : FiveTermIndex (principalA d) → ℝ :=
    fun m => x - ((m : ℕ) : ℝ) * ε / c
  let P : ℂ := 1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + v₁ * (principalRoot d : ℂ)))
  have hLocal (j : ℤ) (hjF : j ∈ F) :=
    principalFiveTerm_crossed_local_square d hd ℓ v₁ v₂ w j hv ((hF j).mp hjF).1
  have hLocalAll := (F.eventually_all).2 (fun j hj => hLocal j hj)
  have hColumn (m : FiveTermIndex (principalA d)) (j : ℤ) (hjF : j ∈ F) :=
    principalFiveTerm_crossed_column_square d hd ℓ v₁ v₂ w x G hv m j
      ((hF j).mp hjF).1 hxε hG (lt_trans ((hF j).mp hjF).2 hxβ)
  let A (r : ℝ) (j : ℤ) (m : FiveTermIndex (principalA d)) : ℂ :=
    rectBoundaryIntegral
      (fun ζ => principalFiveTermKernel d ℓ
        (v₁ - (principalA d) 0 0) w y' ((m : ℕ) : ℤ)
        (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
          ((principalA d) 1 0 : ℂ)))
      ((j : ℂ) / (c : ℂ) - (r + r * I))
      ((j : ℂ) / (c : ℂ) + (r + r * I))
  let B (r : ℝ) (m : FiveTermIndex (principalA d)) (kj : ℤ × ℕ) : ℂ :=
    rectBoundaryIntegral (principalFiveTermKernel d ℓ
      (v₁ - (principalA d) 0 0) w y' ((m : ℕ) : ℤ))
      (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 -
        (r + r * I))
      (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 +
        (r + r * I))
  have hColumnAll := (F.eventually_all).2 (fun j hj =>
    Filter.eventually_all.mpr (fun m => hColumn m j hj))
  filter_upwards [hLocalAll, hColumnAll] with r hlocal hcolumn
  have hReorder : ∑ j ∈ F, ∑ m : FiveTermIndex (principalA d), A r j m =
      ∑ m : FiveTermIndex (principalA d), ∑ kj ∈ G m, B r m kj := by
    classical
    have hFnonneg : ∀ j ∈ F, 0 ≤ j := fun j hj => ((hF j).mp hj).1
    have hFpole : ∀ (m : FiveTermIndex (principalA d)) (kj : ℤ × ℕ),
        kj ∈ G m → (kj.2 : ℤ) ∈ F :=
      fun m kj hkj => (principalFiveTerm_crossed_Gposition_mem_F d hd x F hxε
        (fun j hj hjx => (hF j).2 ⟨hj, (hxF j hj).mp hjx⟩)
        m kj ((hG m kj).mp hkj))
    calc
      _ = ∑ j ∈ F, ∑ m : FiveTermIndex (principalA d), ∑ kj ∈ G m,
            if kj.2 = j.toNat then B r m kj else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro m _
        simpa only [A, B] using hcolumn j hj m
      _ = _ := FiniteFiveTerm.column_sum F G (B r) hFnonneg hFpole
  calc
    _ = ∑ j ∈ F, P * ∑ m : FiveTermIndex (principalA d), A r j m := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hlocal j hj
    _ = P * ∑ j ∈ F, ∑ m : FiveTermIndex (principalA d), A r j m := by
      rw [Finset.mul_sum]
    _ = P * ∑ m : FiveTermIndex (principalA d), ∑ kj ∈ G m, B r m kj := by
      rw [hReorder]
    _ = _ := rfl

/-! ### The continued finite quotient

Apply the real-period crossed-contour identity with the established shifted closed-form
limit, including its zero-class cases. The common-line square identity cancels the correction;
the nonzero prefactor cancels from the integral and the continued quotient.
-/

/-- The shifted integral identity for the deformed contours of
[RW26, Radchenko, Wheeler (2026), Section 3.2, proof of Theorem 2, `thm:fg.equs`]. The
crossed squares of `J` are subtracted from its straight-line integral, leaving
`√ε F⁺(u+v)/(F⁻(u)F⁻(v))`, also at the two zero-class cases. -/
theorem integral_principalFiveTermDifferenceSum_of_crossed
    (d : ℕ) (hd : 3 < d) (u₁ u₂ v₁ v₂ : ℤ)
    (hu : 0 ≤ principalFiveTermLatticeIndex d u₁ u₂ ∧
      principalFiveTermLatticeIndex d u₁ u₂ < principalFiveTermUpperIndexBound d)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d)
    (hv0 : principalFiveTermCharacteristicResidue d v₁ v₂ ≠ 0)
    (huZero : principalFiveTermCharacteristicResidue d u₁ u₂ = 0 → u₁ = 0 ∧ u₂ = 0)
    (huvZero : principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂) = 0 →
      u₁ + v₁ = (principalA d) 0 0 - 1 ∧ u₂ + v₂ = (principalA d) 0 1) :
    let ε := principalRoot d ^ 3
    let c : ℝ := ((principalA d) 1 0 : ℝ)
    let w := principalFiveTermLatticeArgument d u₁ u₂
    let y := principalFiveTermLatticeArgument d v₁ v₂
    let β := -((v₁ : ℝ) * ε / c + y)
    let J := principalFiveTermDifferenceSum d (u₁ + 1) v₁ w y
    ∀ (x : ℝ) (F : Finset ℤ),
      β < x → x < ε / c →
      (∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧ (j : ℝ) / c < β) →
      (∀ j : ℤ, 0 ≤ j → ((j : ℝ) / c < x ↔ (j : ℝ) / c < β)) →
      (∀ m : FiveTermIndex (principalA d),
        IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ) y
          (x - ((m : ℕ) : ℝ) * ε / c)) →
      ∀ᶠ r : ℝ in 𝓝[>] 0,
        IsRegularPeriodLatticeCrossing (principalRoot d) (principalFiveTermShiftedParameter d y) r →
        IsRegularPeriodLatticeCrossing (principalRoot d) (principalFiveTermShiftedParameter d y)
          (-r) →
        (∫ t : ℝ, J ((x : ℂ) + t * I) * I) -
          (∑ j ∈ F, rectBoundaryIntegral J
            ((j : ℂ) / (c : ℂ) - (r + r * I))
            ((j : ℂ) / (c : ℂ) + (r + r * I))) =
        (Real.sqrt ε : ℂ) *
          principalDilogE d (principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂)) /
            (principalDilogEMinus d (principalFiveTermCharacteristicResidue d u₁ u₂) *
              principalDilogEMinus d (principalFiveTermCharacteristicResidue d v₁ v₂)) := by
  dsimp
  intro x F hxβ hxε hF hxF hreg
  let ε := principalRoot d ^ 3
  let c : ℝ := ((principalA d) 1 0 : ℝ)
  let w := principalFiveTermLatticeArgument d u₁ u₂
  let y := principalFiveTermLatticeArgument d v₁ v₂
  let y' := principalFiveTermShiftedParameter d y
  let x' : FiveTermIndex (principalA d) → ℝ :=
    fun m => x - ((m : ℕ) : ℝ) * ε / c
  let P : ℂ := 1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + v₁ * (principalRoot d : ℂ)))
  let Q : ℂ := (Real.sqrt ε : ℂ) *
    principalDilogE d (principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂)) /
      (principalDilogEMinus d (principalFiveTermCharacteristicResidue d u₁ u₂) *
        principalDilogEMinus d (principalFiveTermCharacteristicResidue d v₁ v₂))
  have hP : P ≠ 0 := principalFiveTerm_shifted_factor_ne_zero d hd v₁ v₂ hv0
  obtain ⟨hupper, hlower⟩ := principalFiveTerm_crossed_rates d hd u₁ u₂ v₁ v₂
    hu.2 hu.1 hv.1
  have hlower' := principalFiveTermLowerRate_shifted_neg d hd (u₁ + 1) v₁ w y hlower
  have hreg' (m : FiveTermIndex (principalA d)) :
      IsRegularPeriodLatticeCrossing (principalRoot d) y' (x' m) :=
    principalFiveTerm_crossed_shiftedRegular d hd y (x' m) (hreg m).lattice
  have hleft (m : FiveTermIndex (principalA d)) :
      (-((((m : ℕ) : ℤ) + (v₁ - (principalA d) 0 0) : ℤ) : ℝ) * ε - 1) / c - y' <
        x' m :=
    principalFiveTerm_crossed_leftBound d hd v₁ ((m : ℕ) : ℤ) y x hxβ
  have hInt (m : FiveTermIndex (principalA d)) :
      Integrable (fun t : ℝ =>
        principalFiveTermKernel d (u₁ + 1) (v₁ - (principalA d) 0 0) w y'
          ((m : ℕ) : ℤ) ((x' m : ℂ) + t * I)) :=
    integrable_principalFiveTermKernel d hd (u₁ + 1)
      (v₁ - (principalA d) 0 0) ((m : ℕ) : ℤ) w y' (x' m)
      (hreg' m).base (hreg' m).shifted hupper hlower'
  have he : 0 < (fltDenominator (principalA d : Mat(2, ℤ)) (principalRoot d : ℂ)).re := by
    simpa only [fltDenominator_principalA_principalRoot_complex d hd,
      ← Complex.ofReal_pow, Complex.ofReal_re] using pow_pos (principalRoot_pos d hd) 3
  choose G hG using (fun m : FiveTermIndex (principalA d) =>
    exists_finset_fiveTermPoles_re_lt (principalA d)
      (principalA_lowerLeft_pos d hd) ((m : ℕ) : ℤ) (principalRoot d : ℂ)
      he (x' m))
  have hcross := principalFiveTermIntegralSum_eq_of_tendsto
    d hd (u₁ + 1) (v₁ - (principalA d) 0 0) w y'
    (not_isPeriodLatticePoint_shiftedParameter d hd v₁ v₂ hv0) (Q / P)
    (tendsto_closedFormUHPContinued_principalA_shifted
      d hd u₁ u₂ v₁ v₂ hv0 huZero huvZero)
    x' hleft hreg' hupper hlower' G hG
  have hIntegral :
      (∫ t : ℝ, principalFiveTermDifferenceSum d (u₁ + 1) v₁ w y
        ((x : ℂ) + t * I) * I) =
        P * principalFiveTermIntegralSum d (u₁ + 1)
          (v₁ - (principalA d) 0 0) w y' x' := by
    simpa only [P, x', ε, c, y', y, w] using
      integral_principalFiveTermDifferenceSum_eq d hd (u₁ + 1) v₁ w y x hInt
  have hSquares := principalFiveTerm_crossed_squares_eq d hd (u₁ + 1) v₁ v₂
    w x F G hv hxβ hxε hF hxF hG
  filter_upwards [hcross, hSquares] with r hcrossR hSquaresR hrpos hrneg
  have hsum := hcrossR hrpos hrneg
  have hSquaresR' :
      (∑ j ∈ F, rectBoundaryIntegral
        (principalFiveTermDifferenceSum d (u₁ + 1) v₁ w y)
          ((j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) - (r + r * I))
          ((j : ℂ) / (((principalA d) 1 0 : ℤ) : ℂ) + (r + r * I))) =
        P * (∑ m : FiveTermIndex (principalA d), ∑ kj ∈ G m,
          rectBoundaryIntegral (principalFiveTermKernel d (u₁ + 1)
            (v₁ - (principalA d) 0 0) w y' ((m : ℕ) : ℤ))
            (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 -
              (r + r * I))
            (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 +
              (r + r * I))) := by
    simpa only [c, Complex.ofReal_intCast] using hSquaresR
  simp only [w, y] at hSquaresR'
  rw [hIntegral, hsum, mul_add, hSquaresR']
  change P * (Q / P) + _ - _ = Q
  field_simp [hP]
  ring

end SIC

end
