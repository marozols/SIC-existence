/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.FiveTerm.Shifted
import SICs.SpecialFunctions.Faddeev.WordFiveTerm.Identity

/-!
# The shifted integral of a letter word with crossed poles

The common-line difference integral of a letter word minus its crossed-pole squares equals the
continued finite quotient `√ε E(u+v)/(F⁻(u)F⁻(v))`, including the zero left and zero sum
classes.

This module follows [RW26, Radchenko, Wheeler (2026), Section 3.2, proof of Theorem 2,
`thm:fg.equs`], applying the integral identity (23), `eq:5term.int`, on the deformed contours,
for `γ = ∏_j T^{b_j}S = (a b; c d)` at an attractive fixed point `τ`. The principal word is
treated directly in `SICs.Principal.Dilogarithm.Faddeev.FiveTerm.CrossedIdentity`.

## The argument

Write `ε = j_γ(τ)`, `β_v = -(v₁ε/c+z_v)`, and use positive representatives `0 ≤ S(u) < N`,
`1 ≤ S(v) ≤ N`. The difference kernel is `1 - q^{v₁}e(z_v)` times the five-term kernel at
parameters `(u₁+1, v₁-a, z_u, z_v+aτ+b)`. A common line `β_v < x < ε/c` is right of the shifted
left poles. In common-line coordinates a right pole is `(Mε+j)/c` with `M, j ≥ 0`, so the poles
left of the line are precisely `j/c`, each belonging to its unique contour index modulo `c`.

Carry the crossed-contour integral identity to the real period
(`fiveTermWordIntegralSum_eq_of_tendsto`) and translate its squares to this common line.
Summands regular at a crossed point have zero square integral, so the correction is the sum of
square integrals of the whole difference kernel. The continued shifted closed form gives
`√ε E(u+v)/(F⁻(u)F⁻(v))` (`tendsto_closedFormUHPContinued_letterWord_shifted`), and the nonzero
prefactor cancels.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology MatrixGroups

namespace SIC

/-! ### Positive representatives and shifted contours

The lattice window gives strict decay at both ends. The parameter shift preserves regular
crossings and places every shifted left endpoint to the left of the common line.
-/

/-- The parameter shift preserves regular period-lattice crossings; used by
`integral_fiveTermWordDifferenceSum_of_crossed`. -/
private theorem fiveTermWord_crossed_shiftedRegular (γ : SL(2, ℤ)) (τ y x : ℝ)
    (hx : IsRegularPeriodLatticeCrossing τ y x) :
    IsRegularPeriodLatticeCrossing τ (fiveTermShiftedParameter γ τ y) x := by
  refine ⟨hx.base, ?_⟩
  have h := (isPeriodLatticePoint_add_int_mul_add_int_iff
    (τ : ℂ) ((x : ℂ) + y) (γ 0 0) (γ 0 1)).not.mpr hx.shifted
  dsimp [fiveTermShiftedParameter]
  simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast,
    add_assoc] using h

/-- The shifted left endpoint lies left of the translated common line; used by
`integral_fiveTermWordDifferenceSum_of_crossed`. -/
private theorem fiveTermWord_crossed_leftBound {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (v₁ m : ℤ) (y x : ℝ)
    (hx : -((v₁ : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) + y) < x) :
    (-((m + (v₁ - γ 0 0) : ℤ) : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ - 1) /
        (γ 1 0 : ℝ) - fiveTermShiftedParameter γ τ y <
      x - (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) := by
  have hc : (γ 1 0 : ℝ) ≠ 0 := by exact_mod_cast h.lowerLeft_pos.ne'
  have hdetZ : (γ : Mat(2, ℤ)).det = 1 := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdetZ
  have hdet : (γ 0 0 : ℝ) * γ 1 1 - (γ 0 1 : ℝ) * γ 1 0 = 1 := by
    exact_mod_cast hdetZ
  have hident :
      (-((m + (v₁ - γ 0 0) : ℤ) : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ - 1) /
          (γ 1 0 : ℝ) - fiveTermShiftedParameter γ τ y =
        -((v₁ : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) + y) -
          (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) := by
    dsimp [fiveTermShiftedParameter, fltDenominator]
    push_cast
    field_simp [hc]
    linear_combination hdet
  rw [hident]
  linarith

/-! ### Divisors at crossed positions

At a common-line point `j/c`, a shifted denominator can lie on the period lattice only at the
upper edge of the positive lattice window. Its divisor coordinate is then `-j`, so the
denominator has no zero there. The word numerator has at most a simple pole.
-/

/-- Rational coordinate comparison for a shifted denominator lattice point; used by
`fiveTermWord_crossed_denominator_coordinates`. -/
private theorem fiveTermWord_crossed_denominator_rat {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (v₁ v₂ m j k l : ℤ)
    (hpoint : (j : ℂ) / (γ 1 0 : ℂ) -
        (m : ℂ) * (fltDenominator (γ : Mat(2, ℤ)) τ : ℂ) / (γ 1 0 : ℂ) +
          (fiveTermShiftedParameter γ τ (fiveTermLatticeArgument γ τ v₁ v₂) : ℂ) =
        (k : ℂ) * (τ : ℂ) + l) :
    let A : ℚ := fiveTermRationalCharacteristic γ v₁ v₂ 1
    let B : ℚ := fiveTermRationalCharacteristic γ v₁ v₂ 0
    let a : ℤ := γ 0 0
    let b : ℤ := γ 0 1
    let c : ℤ := γ 1 0
    A + a - m - k = 0 ∧
      (l : ℚ) - ((j : ℚ) - m * (γ 1 1 : ℚ)) / c + B - b = 0 := by
  dsimp
  let A : ℚ := fiveTermRationalCharacteristic γ v₁ v₂ 1
  let B : ℚ := fiveTermRationalCharacteristic γ v₁ v₂ 0
  let a : ℤ := γ 0 0
  let b : ℤ := γ 0 1
  let c : ℤ := γ 1 0
  have hc : (c : ℝ) ≠ 0 := by exact_mod_cast h.lowerLeft_pos.ne'
  have hε : fltDenominator (γ : Mat(2, ℤ)) τ = (c : ℝ) * τ + γ 1 1 := rfl
  have hy : fiveTermLatticeArgument γ τ v₁ v₂ = (A : ℝ) * τ - (B : ℝ) := by
    simpa only [A, B, fracSymplecticFormRat] using
      (fracSymplecticFormRat_fiveTermRationalCharacteristic h v₁ v₂).symm
  have hshift : fiveTermShiftedParameter γ τ
      (fiveTermLatticeArgument γ τ v₁ v₂) =
        fiveTermLatticeArgument γ τ v₁ v₂ + (a : ℝ) * τ + b := by
    simp only [fiveTermShiftedParameter, a, b]
    ring
  have hreal : (j : ℝ) / c - (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / c +
      fiveTermShiftedParameter γ τ (fiveTermLatticeArgument γ τ v₁ v₂) =
        (k : ℝ) * τ + l := by
    exact_mod_cast hpoint
  have hcoord : (j : ℝ) / c - (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / c +
      fiveTermShiftedParameter γ τ (fiveTermLatticeArgument γ τ v₁ v₂) =
        ((A + a - m : ℚ) : ℝ) * τ +
          (((j : ℚ) - m * (γ 1 1 : ℚ)) / c - B + b : ℚ) := by
    rw [hshift, hy, hε]
    push_cast
    field_simp [hc]
    ring
  have hrel : (((A + a - m - k : ℚ) : ℝ) * τ) =
      (((l : ℚ) - ((j : ℚ) - m * (γ 1 1 : ℚ)) / c + B - b : ℚ) : ℝ) := by
    have h' := hcoord.symm.trans hreal
    push_cast at h' ⊢
    linear_combination h'
  exact ratCast_eq_zero_of_irrational_mul h.irrational hrel

/-- At a common-line numerator point `j/c`, a lattice coordinate of the shifted denominator
forces `S(v)=N` and has divisor coordinate `-j`; used by
`fiveTermWord_crossed_denominator_nonpos`. -/
private theorem fiveTermWord_crossed_denominator_coordinates {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (v₁ v₂ m j k l : ℤ)
    (hv : 1 ≤ fiveTermLatticeIndex γ v₁ v₂ ∧
      fiveTermLatticeIndex γ v₁ v₂ ≤ finiteDilogOrder γ)
    (hpoint : (j : ℂ) / (γ 1 0 : ℂ) -
        (m : ℂ) * (fltDenominator (γ : Mat(2, ℤ)) τ : ℂ) / (γ 1 0 : ℂ) +
          (fiveTermShiftedParameter γ τ (fiveTermLatticeArgument γ τ v₁ v₂) : ℂ) =
        (k : ℂ) * (τ : ℂ) + l) :
    fiveTermLatticeIndex γ v₁ v₂ = finiteDilogOrder γ ∧
      γ 1 1 * k - γ 1 0 * l = -j := by
  let A : ℚ := fiveTermRationalCharacteristic γ v₁ v₂ 1
  let B : ℚ := fiveTermRationalCharacteristic γ v₁ v₂ 0
  let a : ℤ := γ 0 0
  let b : ℤ := γ 0 1
  let c : ℤ := γ 1 0
  let d : ℤ := γ 1 1
  let S : ℤ := fiveTermLatticeIndex γ v₁ v₂
  let N : ℤ := finiteDilogOrder γ
  have hN : 0 < N := by dsimp [N]; exact_mod_cast finiteDilogOrder_pos h
  obtain ⟨hcoeff, hconstant⟩ :=
    fiveTermWord_crossed_denominator_rat h v₁ v₂ m j k l hpoint
  change A + a - m - k = 0 at hcoeff
  change (l : ℚ) - ((j : ℚ) - m * (d : ℚ)) / c + B - b = 0 at hconstant
  have hA := fiveTermRationalCharacteristic_snd_eq h v₁ v₂
  have hB := fiveTermRationalCharacteristic_row_eq h v₁ v₂
  change A = -(v₁ : ℚ) - (S : ℚ) / N at hA
  change -(c : ℚ) * B - (d : ℚ) * A = (S : ℚ) / N at hB
  have hNQ : (0 : ℚ) < N := by exact_mod_cast hN
  have hSQ : (0 : ℚ) < S := by exact_mod_cast hv.1
  have hSleQ : (S : ℚ) ≤ N := by exact_mod_cast hv.2
  have hratio : (S : ℚ) / N = ((a - m - k - v₁ : ℤ) : ℚ) := by
    push_cast
    linear_combination hA - hcoeff
  have hunit : a - m - k - v₁ = 1 := by
    have hpos : (0 : ℚ) < (a - m - k - v₁ : ℤ) := by
      rw [← hratio]
      exact div_pos hSQ hNQ
    have hle : ((a - m - k - v₁ : ℤ) : ℚ) ≤ 1 := by
      rw [← hratio]
      exact (div_le_one hNQ).2 hSleQ
    have hposInt : 0 < a - m - k - v₁ := by exact_mod_cast hpos
    have hleInt : a - m - k - v₁ ≤ 1 := by exact_mod_cast hle
    omega
  have hS : S = N := by
    have hr : (S : ℚ) / N = 1 := by rw [hratio, hunit]; norm_num
    exact_mod_cast (div_eq_one_iff_eq hNQ.ne').mp hr
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast h.lowerLeft_pos.ne'
  have hdetZ : (γ : Mat(2, ℤ)).det = 1 := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdetZ
  have hdet : (a : ℚ) * d - (b : ℚ) * c = 1 := by exact_mod_cast hdetZ
  have hcoordQ : ((d : ℚ) * k - (c : ℚ) * l) = -(j : ℚ) := by
    rw [hS] at hB
    have hratio' : (N : ℚ) / N = 1 := by field_simp [hNQ.ne']
    rw [hratio'] at hB
    field_simp [hcQ] at hconstant
    linear_combination -(d : ℚ) * hcoeff - hconstant - hB + hdet
  exact ⟨hS, by exact_mod_cast hcoordQ⟩

/-- The shifted denominator has no zero at a nonnegative crossed numerator column; used by
`fiveTermWord_crossed_kernel_order_ge_neg_one`. -/
private theorem fiveTermWord_crossed_denominator_nonpos {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (v₁ v₂ m j : ℤ)
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂ ∧
      fiveTermLatticeIndex (letterWord bs) v₁ v₂ ≤ finiteDilogOrder (letterWord bs))
    (hj : 0 ≤ j) :
    meromorphicOrderAt (fun ζ => faddeevWord bs
      (m + v₁ - letterWord bs 0 0) 0 ζ τ)
        ((j : ℂ) / (letterWord bs 1 0 : ℂ) -
          (m : ℂ) * (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) /
            (letterWord bs 1 0 : ℂ) +
          (fiveTermShiftedParameter (letterWord bs) τ
            (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) : ℂ)) ≤ 0 := by
  let z : ℂ := (j : ℂ) / (letterWord bs 1 0 : ℂ) -
    (m : ℂ) * (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) /
      (letterWord bs 1 0 : ℂ) +
    (fiveTermShiftedParameter (letterWord bs) τ
      (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) : ℂ)
  by_cases hlat : IsPeriodLatticePoint (τ : ℂ) z
  · obtain ⟨l, k, hpoint⟩ := hlat
    apply le_of_not_gt
    intro hpos
    have hpos' : 0 < meromorphicOrderAt
        (fun ζ => faddeevWord bs (m + v₁ - letterWord bs 0 0) 0 ζ τ)
        ((k : ℂ) * τ + l) := by
      change 0 < meromorphicOrderAt
        (fun ζ => faddeevWord bs (m + v₁ - letterWord bs 0 0) 0 ζ τ) z at hpos
      rw [hpoint] at hpos
      simpa only [add_comm] using hpos
    obtain ⟨_, hdiv⟩ := (meromorphicOrderAt_faddeevWord_pos_iff bs h.ne_nil
      (m + v₁ - letterWord bs 0 0) 0 k l h.fixedPoint.irrational
      (fun w hw => (h.periodsPos w hw).2)).mp hpos'
    have hcoords := (fiveTermWord_crossed_denominator_coordinates h.fixedPoint
      v₁ v₂ m j k l hv (by simpa only [z, add_comm] using hpoint)).2
    omega
  · rw [meromorphicOrderAt_faddeevWord_eq_zero bs _ _ h.periodsPos.slitPlane hlat]

/-- A translated numerator lattice point has row coordinate `-m` and column equation
`cl=j-md`; used by `fiveTermWord_crossed_rightPole_of_lattice`. -/
private theorem fiveTermWord_crossed_numerator_coordinates {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m j k l : ℤ)
    (hpoint : (j : ℂ) / (γ 1 0 : ℂ) -
        (m : ℂ) * (fltDenominator (γ : Mat(2, ℤ)) τ : ℂ) / (γ 1 0 : ℂ) =
        (k : ℂ) * (τ : ℂ) + l) :
    k = -m ∧ γ 1 0 * l = j - m * γ 1 1 := by
  let c : ℤ := γ 1 0
  let d : ℤ := γ 1 1
  have hc : (c : ℝ) ≠ 0 := by exact_mod_cast h.lowerLeft_pos.ne'
  have hε : fltDenominator (γ : Mat(2, ℤ)) τ = (c : ℝ) * τ + d := rfl
  have hreal : (j : ℝ) / c - (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / c =
      (k : ℝ) * τ + l := by exact_mod_cast hpoint
  have hrel : (((m + k : ℤ) : ℚ) : ℝ) * τ =
      ((((j - m * d - c * l : ℤ) : ℚ) / c : ℚ) : ℝ) := by
    push_cast at *
    field_simp [hc] at hreal ⊢
    linear_combination -hreal - (m : ℝ) * hε
  obtain ⟨hfirst, hsecond⟩ := ratCast_eq_zero_of_irrational_mul h.irrational hrel
  have hk : k = -m := by
    have h' : m + k = 0 := by exact_mod_cast hfirst
    omega
  have hl : c * l = j - m * d := by
    have h' : j - m * d - c * l = 0 := by
      have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc
      have hnum : ((j - m * d - c * l : ℤ) : ℚ) = 0 :=
        ((div_eq_zero_iff).mp hsecond).resolve_right hcQ
      exact_mod_cast hnum
    omega
  exact ⟨hk, hl⟩

/-- Every shifted word kernel has at most a simple pole at a nonnegative common-line column;
used by `fiveTermWord_crossed_column_square`. -/
private theorem fiveTermWord_crossed_kernel_order_ge_neg_one {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ m j : ℤ) (w : ℝ)
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂ ∧
      fiveTermLatticeIndex (letterWord bs) v₁ v₂ ≤ finiteDilogOrder (letterWord bs))
    (hj : 0 ≤ j) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (fiveTermWordKernel bs ℓ (v₁ - letterWord bs 0 0) w
        (fiveTermShiftedParameter (letterWord bs) τ
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)) τ m)
        ((j : ℂ) / (letterWord bs 1 0 : ℂ) -
          (m : ℂ) * (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) /
            (letterWord bs 1 0 : ℂ)) := by
  let z : ℂ := (j : ℂ) / (letterWord bs 1 0 : ℂ) -
    (m : ℂ) * (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) /
      (letterWord bs 1 0 : ℂ)
  let y' := fiveTermShiftedParameter (letterWord bs) τ
    (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)
  rw [meromorphicOrderAt_fiveTermWordKernel bs ℓ (v₁ - letterWord bs 0 0) m
    h.periodsPos.slitPlane]
  have hN := meromorphicOrderAt_faddeevWord_ge_neg_one bs h.ne_nil (m + 1) 0
    h.fixedPoint.irrational (fun a ha => (h.periodsPos a ha).2) z
  have hD := fiveTermWord_crossed_denominator_nonpos h v₁ v₂ m j hv hj
  have hshiftOrd : meromorphicOrderAt
      (fun ζ => faddeevWord bs (m + (v₁ - letterWord bs 0 0)) 0 (ζ + (y' : ℂ)) τ) z =
      meromorphicOrderAt
        (fun ζ => faddeevWord bs (m + (v₁ - letterWord bs 0 0)) 0 ζ τ)
          (z + (y' : ℂ)) :=
    meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt
      (f := fun ζ : ℂ => faddeevWord bs (m + (v₁ - letterWord bs 0 0)) 0 ζ τ)
      (x := z) (c := (y' : ℂ))
  rw [hshiftOrd]
  have hD' : meromorphicOrderAt
      (fun ζ => faddeevWord bs (m + (v₁ - letterWord bs 0 0)) 0 ζ τ)
        (z + (y' : ℂ)) ≤ 0 := by
    simpa only [z, y', sub_eq_add_neg, add_assoc] using hD
  have hneg : 0 ≤ -(meromorphicOrderAt
      (fun ζ => faddeevWord bs (m + (v₁ - letterWord bs 0 0)) 0 ζ τ)
        (z + (y' : ℂ))) := by
    rcases lt_or_eq_of_le hD' with hlt | heq
    · exact le_of_lt ((LinearOrderedAddCommGroupWithTop.neg_pos).2 (Or.inl hlt))
    · rw [heq]
      simp
  rw [sub_eq_add_neg]
  exact hN.trans (le_add_of_nonneg_right hneg)

/-- A shifted word kernel is regular at a crossed column when its numerator is off the period
lattice; used by `fiveTermWord_crossed_column_square`. -/
private theorem fiveTermWord_crossed_kernel_order_nonneg {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ m j : ℤ) (w : ℝ)
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂ ∧
      fiveTermLatticeIndex (letterWord bs) v₁ v₂ ≤ finiteDilogOrder (letterWord bs))
    (hj : 0 ≤ j)
    (hlat : ¬ IsPeriodLatticePoint (τ : ℂ)
      ((j : ℂ) / (letterWord bs 1 0 : ℂ) -
        (m : ℂ) * (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) /
          (letterWord bs 1 0 : ℂ))) :
    0 ≤ meromorphicOrderAt
      (fiveTermWordKernel bs ℓ (v₁ - letterWord bs 0 0) w
        (fiveTermShiftedParameter (letterWord bs) τ
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)) τ m)
        ((j : ℂ) / (letterWord bs 1 0 : ℂ) -
          (m : ℂ) * (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) /
            (letterWord bs 1 0 : ℂ)) := by
  rw [meromorphicOrderAt_fiveTermWordKernel bs ℓ (v₁ - letterWord bs 0 0) m
    h.periodsPos.slitPlane,
    meromorphicOrderAt_faddeevWord_eq_zero bs (m + 1) 0 h.periodsPos.slitPlane hlat]
  have hshiftOrd : meromorphicOrderAt
      (fun ζ => faddeevWord bs (m + (v₁ - letterWord bs 0 0)) 0
        (ζ + (fiveTermShiftedParameter (letterWord bs) τ
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) : ℂ)) τ)
        ((j : ℂ) / (letterWord bs 1 0 : ℂ) -
          (m : ℂ) * (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) /
            (letterWord bs 1 0 : ℂ)) =
      meromorphicOrderAt
        (fun ζ => faddeevWord bs (m + (v₁ - letterWord bs 0 0)) 0 ζ τ)
        ((j : ℂ) / (letterWord bs 1 0 : ℂ) -
          (m : ℂ) * (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) /
            (letterWord bs 1 0 : ℂ) +
          (fiveTermShiftedParameter (letterWord bs) τ
            (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) : ℂ)) :=
    meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt
      (f := fun ζ : ℂ => faddeevWord bs (m + (v₁ - letterWord bs 0 0)) 0 ζ τ)
      (x := (j : ℂ) / (letterWord bs 1 0 : ℂ) -
        (m : ℂ) * (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) /
          (letterWord bs 1 0 : ℂ))
      (c := (fiveTermShiftedParameter (letterWord bs) τ
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) : ℂ))
  rw [hshiftOrd]
  have hD := fiveTermWord_crossed_denominator_nonpos h v₁ v₂ m j hv hj
  have hD' : meromorphicOrderAt
      (fun ζ => faddeevWord bs (m + (v₁ - letterWord bs 0 0)) 0 ζ τ)
        ((j : ℂ) / (letterWord bs 1 0 : ℂ) -
          (m : ℂ) * (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) /
            (letterWord bs 1 0 : ℂ) +
          (fiveTermShiftedParameter (letterWord bs) τ
            (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) : ℂ)) ≤ 0 := by
    simpa only [sub_eq_add_neg, add_assoc] using hD
  have hneg : 0 ≤ -(meromorphicOrderAt
      (fun ζ => faddeevWord bs (m + (v₁ - letterWord bs 0 0)) 0 ζ τ)
        ((j : ℂ) / (letterWord bs 1 0 : ℂ) -
          (m : ℂ) * (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) /
            (letterWord bs 1 0 : ℂ) +
          (fiveTermShiftedParameter (letterWord bs) τ
            (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) : ℂ))) := by
    rcases lt_or_eq_of_le hD' with hlt | heq
    · exact le_of_lt ((LinearOrderedAddCommGroupWithTop.neg_pos).2 (Or.inl hlt))
    · rw [heq]
      simp
  simpa only [sub_eq_add_neg, zero_add] using hneg

/-! ### Matching the right poles

In common-line coordinates a right pole is `(Mε+j)/c` for nonnegative `M,j`. Since the common
line is left of `ε/c`, every crossed pole has `M=0`.
-/

/-- A numerator lattice point `j/c-mε/c`, `j≥0`, is a right pole with forward index zero;
used by `fiveTermWord_crossed_column_square`. -/
private theorem fiveTermWord_crossed_rightPole_of_lattice {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m j : ℤ) (hj : 0 ≤ j)
    (hlat : IsPeriodLatticePoint (τ : ℂ)
      ((j : ℂ) / (γ 1 0 : ℂ) -
        (m : ℂ) * (fltDenominator (γ : Mat(2, ℤ)) τ : ℂ) / (γ 1 0 : ℂ))) :
    ∃ k : ℤ,
      faddeevModularUHPIndex γ m k j.toNat = 0 ∧
        faddeevModularUHPPole γ (τ : ℂ) k j.toNat =
          (j : ℂ) / (γ 1 0 : ℂ) -
            (m : ℂ) * (fltDenominator (γ : Mat(2, ℤ)) τ : ℂ) / (γ 1 0 : ℂ) := by
  obtain ⟨l, K, hp⟩ := hlat
  have hl := (fiveTermWord_crossed_numerator_coordinates h m j K l
    (by simpa only [add_comm] using hp)).2
  let a : ℤ := γ 0 0
  let b : ℤ := γ 0 1
  let c : ℤ := γ 1 0
  let d : ℤ := γ 1 1
  let k : ℤ := a * l + b * m
  have hdetZ : (γ : Mat(2, ℤ)).det = 1 := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdetZ
  have hdet : a * d - b * c = 1 := by simpa only [a, b, c, d] using hdetZ
  have hjcast : ((j.toNat : ℕ) : ℤ) = j := by omega
  have hjC : (j.toNat : ℂ) = (j : ℂ) := by exact_mod_cast hjcast
  have hN : faddeevModularUHPIndex γ m k j.toNat = 0 := by
    simp only [faddeevModularUHPIndex, hjcast, k, a, b]
    linear_combination (γ 0 0) * hl - m * hdet
  refine ⟨k, hN, ?_⟩
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast h.lowerLeft_pos.ne'
  have hε : fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ) ≠ 0 := by
    rw [← ofReal_fltDenominator]
    exact_mod_cast h.fltDenominator_pos.ne'
  have hlin := faddeevModularUHPPole_linear γ (τ : ℂ) hε m k j.toNat
  rw [hN] at hlin
  have hlin' : (c : ℂ) * faddeevModularUHPPole γ (τ : ℂ) k j.toNat +
      (fltDenominator (γ : Mat(2, ℤ)) τ : ℂ) * m = j := by
    simpa only [c, hjC, Int.cast_zero, mul_zero, zero_add,
      ← ofReal_fltDenominator] using hlin
  calc
    _ = ((j : ℂ) - (m : ℂ) * (fltDenominator (γ : Mat(2, ℤ)) τ : ℂ)) /
        (c : ℂ) := by
      apply (eq_div_iff hc).2
      linear_combination hlin'
    _ = _ := by ring

/-- A right pole left of the common line has forward index zero and position `j/c` after
translation; used by `fiveTermWord_crossed_squares_eq`. -/
private theorem fiveTermWord_crossed_rightPole_zeroIndex {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m k : ℤ) (j : ℕ) (x : ℝ)
    (hx : x < fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ))
    (hN : 0 ≤ faddeevModularUHPIndex γ m k j)
    (hleft : (faddeevModularUHPPole γ (τ : ℂ) k j).re <
      x - (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ)) :
    faddeevModularUHPIndex γ m k j = 0 ∧
      faddeevModularUHPPole γ (τ : ℂ) k j +
        (m : ℂ) * (fltDenominator (γ : Mat(2, ℤ)) τ : ℂ) / (γ 1 0 : ℂ) =
        (j : ℂ) / (γ 1 0 : ℂ) := by
  let N := faddeevModularUHPIndex γ m k j
  let c : ℝ := (γ 1 0 : ℝ)
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  have hc : 0 < c := by
    change 0 < (γ 1 0 : ℝ)
    exact_mod_cast h.lowerLeft_pos
  have hε : 0 < ε := h.fltDenominator_pos
  have hεC : fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ) ≠ 0 := by
    rw [← ofReal_fltDenominator]
    exact_mod_cast hε.ne'
  have hreal := re_faddeevModularUHPPole γ h.lowerLeft_pos
    (τ : ℂ) hεC m k j
  have hreal' : (faddeevModularUHPPole γ (τ : ℂ) k j).re =
      (((N : ℝ) - m) * ε + j) / c := by
    simpa only [N, c, ε, ← ofReal_fltDenominator, Complex.ofReal_re] using hreal
  have hbound : (N : ℝ) * ε + j < c * x := by
    rw [hreal'] at hleft
    change (((N : ℝ) - m) * ε + j) / c < x - (m : ℝ) * ε / c at hleft
    have hmul := (div_lt_iff₀ hc).mp hleft
    have hcan : (m : ℝ) * ε / c * c = (m : ℝ) * ε := div_mul_cancel₀ _ hc.ne'
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
  have hlin := faddeevModularUHPPole_linear γ (τ : ℂ) hεC m k j
  change faddeevModularUHPIndex γ m k j = 0 at hN0
  rw [hN0] at hlin
  have hcC : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast h.lowerLeft_pos.ne'
  rw [← ofReal_fltDenominator]
  field_simp [hcC]
  simp only [Int.cast_zero, mul_zero, zero_add, ← ofReal_fltDenominator] at hlin
  linear_combination hlin

/-- The difference sum is the shifted word-kernel sum as a meromorphic germ; used by
`fiveTermWord_crossed_local_square`. -/
private theorem fiveTermWord_crossed_differenceSum_germ {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y : ℝ) (z : ℂ) :
    fiveTermWordDifferenceSum bs ℓ p w y τ =ᶠ[𝓝[≠] z]
      (fun ζ => (1 - Complex.exp (2 * Real.pi * I *
        ((y : ℂ) + p * (τ : ℂ)))) *
          ∑ m : FiveTermIndex (letterWord bs),
            fiveTermWordKernel bs ℓ (p - letterWord bs 0 0) w
              (fiveTermShiftedParameter (letterWord bs) τ y) τ ((m : ℕ) : ℤ)
              (ζ - ((m : ℕ) : ℂ) *
                fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
                (letterWord bs 1 0 : ℂ))) := by
  have hEach (m : FiveTermIndex (letterWord bs)) :
      (fun ζ => fiveTermWordDifferenceKernel bs ℓ p w y τ ((m : ℕ) : ℤ)
        (ζ - ((m : ℕ) : ℂ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ))) =ᶠ[𝓝[≠] z]
      (fun ζ => (1 - Complex.exp (2 * Real.pi * I *
        ((y : ℂ) + p * (τ : ℂ)))) *
        fiveTermWordKernel bs ℓ (p - letterWord bs 0 0) w
          (fiveTermShiftedParameter (letterWord bs) τ y) τ ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) *
            fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
            (letterWord bs 1 0 : ℂ))) := by
    let v : ℂ := ((m : ℕ) : ℂ) *
      fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (letterWord bs 1 0 : ℂ)
    have ht : Tendsto (fun ζ : ℂ => ζ - v) (𝓝[≠] z) (𝓝[≠] (z - v)) := by
      simpa only [sub_eq_add_neg] using tendsto_add_const_nhdsNE (-v) z
    simpa only [v, Function.comp_def] using
      (fiveTermWordDifferenceKernel_eventuallyEq h ℓ p w y
        ((m : ℕ) : ℤ) (z - v)).comp_tendsto ht
  filter_upwards [Filter.eventually_all.mpr hEach] with ζ hζ
  simp only [fiveTermWordDifferenceSum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => hζ m)

/-- A crossed right pole lies in its zero-index common-line column; used by
`fiveTermWord_crossed_column_square` and `fiveTermWord_crossed_squares_eq`. -/
private theorem fiveTermWord_crossed_Gposition {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m : FiveTermIndex (letterWord bs))
    (kj : ℤ × ℕ) (x : ℝ)
    (hx : x < fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ))
    (hG : 0 ≤ faddeevModularUHPIndex (letterWord bs) ((m : ℕ) : ℤ) kj.1 kj.2 ∧
      (faddeevModularUHPPole (letterWord bs) (τ : ℂ) kj.1 kj.2).re <
        x - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
          (letterWord bs 1 0 : ℝ)) :
    faddeevModularUHPIndex (letterWord bs) ((m : ℕ) : ℤ) kj.1 kj.2 = 0 ∧
      faddeevModularUHPPole (letterWord bs) (τ : ℂ) kj.1 kj.2 +
        ((m : ℕ) : ℂ) * (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) /
          (letterWord bs 1 0 : ℂ) =
        (kj.2 : ℂ) / (letterWord bs 1 0 : ℂ) :=
  fiveTermWord_crossed_rightPole_zeroIndex h.fixedPoint ((m : ℕ) : ℤ)
    kj.1 kj.2 x hx hG.1 hG.2

/-- A translated right pole left of the common line has its column in `F`; used by
`fiveTermWord_crossed_squares_eq`. -/
private theorem fiveTermWord_crossed_rightPole_mem_F {γ : SL(2, ℤ)} {τ : ℝ}
    (x : ℝ) (F : Finset ℤ)
    (hF : ∀ j : ℤ, 0 ≤ j → (j : ℝ) / (γ 1 0 : ℝ) < x → j ∈ F)
    (m : ℤ) (kj : ℤ × ℕ)
    (hpos : faddeevModularUHPPole γ (τ : ℂ) kj.1 kj.2 +
      (m : ℂ) * (fltDenominator (γ : Mat(2, ℤ)) τ : ℂ) / (γ 1 0 : ℂ) =
      (kj.2 : ℂ) / (γ 1 0 : ℂ))
    (hleft : (faddeevModularUHPPole γ (τ : ℂ) kj.1 kj.2).re <
      x - (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ)) :
    (kj.2 : ℤ) ∈ F := by
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let c : ℝ := (γ 1 0 : ℝ)
  have hpos' : faddeevModularUHPPole γ (τ : ℂ) kj.1 kj.2 +
      (((m : ℝ) * ε / c : ℝ) : ℂ) = (((kj.2 : ℝ) / c : ℝ) : ℂ) := by
    simpa only [ε, c, ofReal_fltDenominator, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_intCast, Complex.ofReal_natCast] using hpos
  have hre : (faddeevModularUHPPole γ (τ : ℂ) kj.1 kj.2).re +
      (m : ℝ) * ε / c = (kj.2 : ℝ) / c := by
    simpa only [Complex.add_re, Complex.ofReal_re] using congrArg Complex.re hpos'
  apply hF _ (by exact_mod_cast Nat.zero_le kj.2)
  push_cast
  linarith

/-- Every crossed pole belongs to its nonnegative common-line column in `F`; used by
`fiveTermWord_crossed_squares_eq`. -/
private theorem fiveTermWord_crossed_Gposition_mem_F {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (x : ℝ) (F : Finset ℤ)
    (hx : x < fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ))
    (hF : ∀ j : ℤ, 0 ≤ j → (j : ℝ) / (letterWord bs 1 0 : ℝ) < x → j ∈ F)
    (m : FiveTermIndex (letterWord bs)) (kj : ℤ × ℕ)
    (hG : 0 ≤ faddeevModularUHPIndex (letterWord bs) ((m : ℕ) : ℤ) kj.1 kj.2 ∧
      (faddeevModularUHPPole (letterWord bs) (τ : ℂ) kj.1 kj.2).re <
        x - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
          (letterWord bs 1 0 : ℝ)) :
    (kj.2 : ℤ) ∈ F := by
  obtain ⟨_, hpos⟩ := fiveTermWord_crossed_Gposition h m kj x hx hG
  exact fiveTermWord_crossed_rightPole_mem_F x F hF
    ((m : ℕ) : ℤ) kj hpos hG.2

/-- A lattice pole at column `j` lies left of the shifted contour when `j/c<x`; used by
`fiveTermWord_crossed_column_square`. -/
private theorem fiveTermWord_crossed_column_left {γ : SL(2, ℤ)} {τ : ℝ}
    (m : FiveTermIndex γ)
    (j : ℤ) (x : ℝ)
    (hjx : (j : ℝ) / (γ 1 0 : ℝ) < x) (k : ℤ)
    (hpole : faddeevModularUHPPole γ (τ : ℂ) k j.toNat =
      (j : ℂ) / (γ 1 0 : ℂ) -
        ((m : ℕ) : ℂ) * (fltDenominator (γ : Mat(2, ℤ)) τ : ℂ) /
          (γ 1 0 : ℂ)) :
    (faddeevModularUHPPole γ (τ : ℂ) k j.toNat).re <
      x - ((m : ℕ) : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) := by
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let c : ℝ := (γ 1 0 : ℝ)
  have hpole' : faddeevModularUHPPole γ (τ : ℂ) k j.toNat =
      (((j : ℝ) / c - ((m : ℕ) : ℝ) * ε / c : ℝ) : ℂ) := by
    simpa only [ε, c, ofReal_fltDenominator, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_intCast,
      Complex.ofReal_natCast, Int.cast_natCast] using hpole
  have hre := congrArg Complex.re hpole'
  simp only [Complex.ofReal_re] at hre
  dsimp [ε, c] at hre
  linarith

/-- A fixed nonnegative column determines its crossed right pole uniquely; used by
`fiveTermWord_crossed_column_square`. -/
private theorem fiveTermWord_crossed_column_unique {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m : FiveTermIndex γ)
    (j : ℤ) (hj : 0 ≤ j) (k : ℤ) (kj : ℤ × ℕ)
    (hpole : faddeevModularUHPPole γ (τ : ℂ) k j.toNat =
      (j : ℂ) / (γ 1 0 : ℂ) -
        ((m : ℕ) : ℂ) * (fltDenominator (γ : Mat(2, ℤ)) τ : ℂ) /
          (γ 1 0 : ℂ))
    (hpos : faddeevModularUHPPole γ (τ : ℂ) kj.1 kj.2 +
        ((m : ℕ) : ℂ) * (fltDenominator (γ : Mat(2, ℤ)) τ : ℂ) /
          (γ 1 0 : ℂ) =
        (kj.2 : ℂ) / (γ 1 0 : ℂ))
    (hcol : kj.2 = j.toNat) : kj = (k, j.toNat) := by
  have hjcast : (j.toNat : ℂ) = (j : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg hj
  have heq : faddeevModularUHPPole γ (τ : ℂ) kj.1 kj.2 =
      faddeevModularUHPPole γ (τ : ℂ) k j.toNat := by
    rw [hcol, hjcast] at hpos
    rw [hcol]
    calc
      _ = (j : ℂ) / (γ 1 0 : ℂ) -
          ((m : ℕ) : ℂ) * (fltDenominator (γ : Mat(2, ℤ)) τ : ℂ) /
            (γ 1 0 : ℂ) := by
        linear_combination hpos
      _ = _ := hpole.symm
  have hε : fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ) ≠ 0 := by
    rw [← ofReal_fltDenominator]
    exact_mod_cast h.fltDenominator_pos.ne'
  exact (faddeevModularUHPPole_ofReal_injective γ τ h.irrational hε) heq

/-! ### Square corrections

Translate each kernel square to the common line. A crossed pole contributes exactly one square;
all other summands have removable germs there.
-/

/-- At one common-line column, the translated kernel square equals the unique crossed-pole
square when present and vanishes otherwise; used by `fiveTermWord_crossed_squares_eq`. -/
private theorem fiveTermWord_crossed_column_square {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w x : ℝ)
    (G : FiveTermIndex (letterWord bs) → Finset (ℤ × ℕ))
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂ ∧
      fiveTermLatticeIndex (letterWord bs) v₁ v₂ ≤ finiteDilogOrder (letterWord bs))
    (m : FiveTermIndex (letterWord bs)) (j : ℤ) (hj : 0 ≤ j) :
    let ε := fltDenominator (letterWord bs : Mat(2, ℤ)) τ
    let c : ℝ := (letterWord bs 1 0 : ℝ)
    let y' := fiveTermShiftedParameter (letterWord bs) τ
      (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)
    let x' : FiveTermIndex (letterWord bs) → ℝ :=
      fun m => x - ((m : ℕ) : ℝ) * ε / c
    x < ε / c →
    (∀ (m : FiveTermIndex (letterWord bs)) (kj : ℤ × ℕ),
      kj ∈ G m ↔ 0 ≤ faddeevModularUHPIndex (letterWord bs) ((m : ℕ) : ℤ) kj.1 kj.2 ∧
        (faddeevModularUHPPole (letterWord bs) (τ : ℂ) kj.1 kj.2).re < x' m) →
    (j : ℝ) / c < x →
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      rectBoundaryIntegral
        (fun ζ => fiveTermWordKernel bs ℓ (v₁ - letterWord bs 0 0) w y' τ
          ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) *
            fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
              (letterWord bs 1 0 : ℂ)))
        ((j : ℂ) / (c : ℂ) - (r + r * I))
        ((j : ℂ) / (c : ℂ) + (r + r * I)) =
      ∑ kj ∈ G m,
        if kj.2 = j.toNat then
          rectBoundaryIntegral (fiveTermWordKernel bs ℓ
            (v₁ - letterWord bs 0 0) w y' τ ((m : ℕ) : ℤ))
            (faddeevModularUHPPole (letterWord bs) (τ : ℂ) kj.1 kj.2 - (r + r * I))
            (faddeevModularUHPPole (letterWord bs) (τ : ℂ) kj.1 kj.2 + (r + r * I))
        else 0 := by
  dsimp
  intro hxε hG hjx
  let ε := fltDenominator (letterWord bs : Mat(2, ℤ)) τ
  let c : ℝ := (letterWord bs 1 0 : ℝ)
  let y' := fiveTermShiftedParameter (letterWord bs) τ
    (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)
  let x' : FiveTermIndex (letterWord bs) → ℝ :=
    fun m => x - ((m : ℕ) : ℝ) * ε / c
  let p : ℂ := (j : ℂ) / (c : ℂ)
  let v : ℂ := ((m : ℕ) : ℂ) *
    fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
      (letterWord bs 1 0 : ℂ)
  let z : ℂ := p - v
  let K : ℂ → ℂ := fiveTermWordKernel bs ℓ
    (v₁ - letterWord bs 0 0) w y' τ ((m : ℕ) : ℤ)
  have hGposition (kj : ℤ × ℕ) (hkj : kj ∈ G m) :=
    (fiveTermWord_crossed_Gposition h m kj x hxε ((hG m kj).mp hkj)).2
  have hMer : MeromorphicAt K z := by
    exact meromorphicAt_fiveTermWordKernel bs ℓ
      (v₁ - letterWord bs 0 0) ((m : ℕ) : ℤ) h.periodsPos.slitPlane z
  have hOrd : (-1 : WithTop ℤ) ≤ meromorphicOrderAt K z := by
    convert fiveTermWord_crossed_kernel_order_ge_neg_one h
      ℓ v₁ v₂ ((m : ℕ) : ℤ) j w hv hj using 1
  have hTrans := eventually_rectBoundaryIntegral_square_translate K p v hMer hOrd
  by_cases hlat : IsPeriodLatticePoint (τ : ℂ) z
  · obtain ⟨k, hN, hpole⟩ := fiveTermWord_crossed_rightPole_of_lattice
      h.fixedPoint ((m : ℕ) : ℤ) j hj (by
        simpa only [z, p, v, c, ofReal_fltDenominator, Complex.ofReal_intCast,
          Int.cast_natCast] using hlat)
    have hmem : (k, j.toNat) ∈ G m := by
      apply (hG m (k, j.toNat)).2
      exact ⟨by simp only [hN, le_refl],
        fiveTermWord_crossed_column_left m j x hjx k hpole⟩
    have hUnique (kj : ℤ × ℕ) (hkj : kj ∈ G m)
        (hcol : kj.2 = j.toNat) : kj = (k, j.toNat) :=
      fiveTermWord_crossed_column_unique h.fixedPoint m j hj k kj hpole
        (hGposition kj hkj) hcol
    filter_upwards [hTrans] with r htrans
    change rectBoundaryIntegral (fun ζ => K (ζ - v))
      (p - (r + r * I)) (p + (r + r * I)) = _
    rw [htrans]
    have hsum := FiniteFiveTerm.unique_column_sum (G m) j k hmem hUnique
      (fun kj => rectBoundaryIntegral K
        (faddeevModularUHPPole (letterWord bs) (τ : ℂ) kj.1 kj.2 - (r + r * I))
        (faddeevModularUHPPole (letterWord bs) (τ : ℂ) kj.1 kj.2 + (r + r * I)))
    rw [hsum]
    simp only [hpole, p, v, c,
      Complex.ofReal_intCast, Int.cast_natCast]
  · have hOrd0 : 0 ≤ meromorphicOrderAt K z := by
      apply fiveTermWord_crossed_kernel_order_nonneg h
        ℓ v₁ v₂ ((m : ℕ) : ℤ) j w hv hj
      simpa only [z, p, v, c, ofReal_fltDenominator,
        Complex.ofReal_intCast, Int.cast_natCast] using hlat
    have hNo (kj : ℤ × ℕ) (hkj : kj ∈ G m) : kj.2 ≠ j.toNat := by
      intro hcol
      have hp := hGposition kj hkj
      have hjcast : (j.toNat : ℂ) = (j : ℂ) := by
        exact_mod_cast Int.toNat_of_nonneg hj
      have hpole : faddeevModularUHPPole (letterWord bs) (τ : ℂ) kj.1 kj.2 = z := by
        rw [hcol, hjcast] at hp
        unfold z p v
        simp only [c, Complex.ofReal_intCast]
        rw [hcol]
        linear_combination hp
      apply hlat
      rw [← hpole]
      have hε : fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) ≠ 0 := by
        rw [← ofReal_fltDenominator]
        exact_mod_cast h.fixedPoint.fltDenominator_pos.ne'
      exact isPeriodLatticePoint_faddeevModularUHPPole (letterWord bs)
        (τ : ℂ) hε kj.1 kj.2
    filter_upwards [hTrans, eventually_rectBoundaryIntegral_square_eq_zero K z hMer hOrd0]
      with r htrans hzero
    change rectBoundaryIntegral (fun ζ => K (ζ - v))
      (p - (r + r * I)) (p + (r + r * I)) = _
    rw [htrans, hzero]
    symm
    apply Finset.sum_eq_zero
    intro kj hkj
    simp [hNo kj hkj]

/-- The square integral of the difference sum is the sum of its shifted meromorphic kernel
germs; used by `fiveTermWord_crossed_squares_eq`. -/
private theorem fiveTermWord_crossed_local_square {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w : ℝ) (j : ℤ)
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂ ∧
      fiveTermLatticeIndex (letterWord bs) v₁ v₂ ≤ finiteDilogOrder (letterWord bs))
    (hj : 0 ≤ j) :
    let c : ℝ := (letterWord bs 1 0 : ℝ)
    let y := fiveTermLatticeArgument (letterWord bs) τ v₁ v₂
    let y' := fiveTermShiftedParameter (letterWord bs) τ y
    let P : ℂ := 1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + v₁ * (τ : ℂ)));
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      rectBoundaryIntegral (fiveTermWordDifferenceSum bs ℓ v₁ w y τ)
        ((j : ℂ) / (c : ℂ) - (r + r * I))
        ((j : ℂ) / (c : ℂ) + (r + r * I)) =
        P * ∑ m : FiveTermIndex (letterWord bs),
          rectBoundaryIntegral
            (fun ζ => fiveTermWordKernel bs ℓ (v₁ - letterWord bs 0 0) w y' τ
              ((m : ℕ) : ℤ)
              (ζ - ((m : ℕ) : ℂ) *
                fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
                  (letterWord bs 1 0 : ℂ)))
            ((j : ℂ) / (c : ℂ) - (r + r * I))
            ((j : ℂ) / (c : ℂ) + (r + r * I)) := by
  dsimp
  let c : ℝ := (letterWord bs 1 0 : ℝ)
  let y := fiveTermLatticeArgument (letterWord bs) τ v₁ v₂
  let y' := fiveTermShiftedParameter (letterWord bs) τ y
  let P : ℂ := 1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + v₁ * (τ : ℂ)))
  let p : ℂ := (j : ℂ) / (c : ℂ)
  let f : FiveTermIndex (letterWord bs) → ℂ → ℂ := fun m ζ =>
    fiveTermWordKernel bs ℓ (v₁ - letterWord bs 0 0) w y' τ ((m : ℕ) : ℤ)
      (ζ - ((m : ℕ) : ℂ) *
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ))
  have hMer (m : FiveTermIndex (letterWord bs)) : MeromorphicAt (f m) p := by
    change MeromorphicAt
      ((fiveTermWordKernel bs ℓ (v₁ - letterWord bs 0 0) w y' τ ((m : ℕ) : ℤ)) ∘
        (fun ζ : ℂ => ζ - ((m : ℕ) : ℂ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
            (letterWord bs 1 0 : ℂ))) p
    apply (meromorphicAt_comp_sub_const_iff_meromorphicAt).2
    exact meromorphicAt_fiveTermWordKernel bs ℓ (v₁ - letterWord bs 0 0)
      ((m : ℕ) : ℤ) h.periodsPos.slitPlane _
  have hOrd (m : FiveTermIndex (letterWord bs)) :
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt (f m) p := by
    rw [meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt]
    convert fiveTermWord_crossed_kernel_order_ge_neg_one h
      ℓ v₁ v₂ ((m : ℕ) : ℤ) j w hv hj using 1
  have hEq : fiveTermWordDifferenceSum bs ℓ v₁ w y τ =ᶠ[𝓝[≠] p]
      (fun ζ => P * ∑ m, f m ζ) := by
    simpa only [P, f, p] using
      fiveTermWord_crossed_differenceSum_germ h ℓ v₁ w y p
  simpa only [p, f, c, y, y', P, Complex.ofReal_intCast] using
    eventually_rectBoundaryIntegral_square_mul_sum
      (fiveTermWordDifferenceSum bs ℓ v₁ w y τ) f P p hEq hMer hOrd

/-- The small-square correction on the common line equals the crossed right-pole correction
for the shifted kernels; used by `integral_fiveTermWordDifferenceSum_of_crossed`. -/
private theorem fiveTermWord_crossed_squares_eq {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w x : ℝ)
    (F : Finset ℤ) (G : FiveTermIndex (letterWord bs) → Finset (ℤ × ℕ))
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂ ∧
      fiveTermLatticeIndex (letterWord bs) v₁ v₂ ≤ finiteDilogOrder (letterWord bs)) :
    let ε := fltDenominator (letterWord bs : Mat(2, ℤ)) τ
    let c : ℝ := (letterWord bs 1 0 : ℝ)
    let y := fiveTermLatticeArgument (letterWord bs) τ v₁ v₂
    let y' := fiveTermShiftedParameter (letterWord bs) τ y
    let x' : FiveTermIndex (letterWord bs) → ℝ :=
      fun m => x - ((m : ℕ) : ℝ) * ε / c
    let P : ℂ := 1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + v₁ * (τ : ℂ)));
    -((v₁ : ℝ) * ε / c + y) < x →
    x < ε / c →
    (∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧ (j : ℝ) / c < -((v₁ : ℝ) * ε / c + y)) →
    (∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / c < x ↔ (j : ℝ) / c < -((v₁ : ℝ) * ε / c + y))) →
    (∀ (m : FiveTermIndex (letterWord bs)) (kj : ℤ × ℕ),
      kj ∈ G m ↔ 0 ≤ faddeevModularUHPIndex (letterWord bs) ((m : ℕ) : ℤ) kj.1 kj.2 ∧
        (faddeevModularUHPPole (letterWord bs) (τ : ℂ) kj.1 kj.2).re < x' m) →
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      (∑ j ∈ F, rectBoundaryIntegral
        (fiveTermWordDifferenceSum bs ℓ v₁ w y τ)
          ((j : ℂ) / (c : ℂ) - (r + r * I))
          ((j : ℂ) / (c : ℂ) + (r + r * I))) =
        P * (∑ m : FiveTermIndex (letterWord bs), ∑ kj ∈ G m,
          rectBoundaryIntegral (fiveTermWordKernel bs ℓ
            (v₁ - letterWord bs 0 0) w y' τ ((m : ℕ) : ℤ))
            (faddeevModularUHPPole (letterWord bs) (τ : ℂ) kj.1 kj.2 - (r + r * I))
            (faddeevModularUHPPole (letterWord bs) (τ : ℂ) kj.1 kj.2 + (r + r * I))) := by
  dsimp
  intro hxβ hxε hF hxF hG
  let ε := fltDenominator (letterWord bs : Mat(2, ℤ)) τ
  let c : ℝ := (letterWord bs 1 0 : ℝ)
  let y := fiveTermLatticeArgument (letterWord bs) τ v₁ v₂
  let y' := fiveTermShiftedParameter (letterWord bs) τ y
  let x' : FiveTermIndex (letterWord bs) → ℝ :=
    fun m => x - ((m : ℕ) : ℝ) * ε / c
  let P : ℂ := 1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + v₁ * (τ : ℂ)))
  have hLocal (j : ℤ) (hjF : j ∈ F) :=
    fiveTermWord_crossed_local_square h ℓ v₁ v₂ w j hv ((hF j).mp hjF).1
  have hLocalAll := (F.eventually_all).2 (fun j hj => hLocal j hj)
  have hColumn (m : FiveTermIndex (letterWord bs)) (j : ℤ) (hjF : j ∈ F) :=
    fiveTermWord_crossed_column_square h ℓ v₁ v₂ w x G hv m j
      ((hF j).mp hjF).1 hxε hG (lt_trans ((hF j).mp hjF).2 hxβ)
  let A (r : ℝ) (j : ℤ) (m : FiveTermIndex (letterWord bs)) : ℂ :=
    rectBoundaryIntegral
      (fun ζ => fiveTermWordKernel bs ℓ (v₁ - letterWord bs 0 0) w y' τ
        ((m : ℕ) : ℤ)
        (ζ - ((m : ℕ) : ℂ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
            (letterWord bs 1 0 : ℂ)))
      ((j : ℂ) / (c : ℂ) - (r + r * I))
      ((j : ℂ) / (c : ℂ) + (r + r * I))
  let B (r : ℝ) (m : FiveTermIndex (letterWord bs)) (kj : ℤ × ℕ) : ℂ :=
    rectBoundaryIntegral (fiveTermWordKernel bs ℓ
      (v₁ - letterWord bs 0 0) w y' τ ((m : ℕ) : ℤ))
      (faddeevModularUHPPole (letterWord bs) (τ : ℂ) kj.1 kj.2 - (r + r * I))
      (faddeevModularUHPPole (letterWord bs) (τ : ℂ) kj.1 kj.2 + (r + r * I))
  have hColumnAll := (F.eventually_all).2 (fun j hj =>
    Filter.eventually_all.mpr (fun m => hColumn m j hj))
  filter_upwards [hLocalAll, hColumnAll] with r hlocal hcolumn
  have hFnonneg : ∀ j ∈ F, 0 ≤ j := fun j hj => ((hF j).mp hj).1
  have hFpole : ∀ (m : FiveTermIndex (letterWord bs)) (kj : ℤ × ℕ),
      kj ∈ G m → (kj.2 : ℤ) ∈ F :=
    fun m kj hkj => (fiveTermWord_crossed_Gposition_mem_F h x F hxε
      (fun j hj hjx => (hF j).2 ⟨hj, (hxF j hj).mp hjx⟩)
      m kj ((hG m kj).mp hkj))
  have hReorder : ∑ j ∈ F, ∑ m : FiveTermIndex (letterWord bs), A r j m =
      ∑ m : FiveTermIndex (letterWord bs), ∑ kj ∈ G m, B r m kj := by
    calc
      _ = ∑ j ∈ F, ∑ m : FiveTermIndex (letterWord bs), ∑ kj ∈ G m,
            if kj.2 = j.toNat then B r m kj else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro m _
        simpa only [A, B] using hcolumn j hj m
      _ = _ := FiniteFiveTerm.column_sum F G (B r) hFnonneg hFpole
  calc
    _ = ∑ j ∈ F, P * ∑ m : FiveTermIndex (letterWord bs), A r j m := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hlocal j hj
    _ = P * ∑ j ∈ F, ∑ m : FiveTermIndex (letterWord bs), A r j m := by
      rw [Finset.mul_sum]
    _ = P * ∑ m : FiveTermIndex (letterWord bs), ∑ kj ∈ G m, B r m kj := by
      rw [hReorder]
    _ = _ := rfl

/-- **The crossed shifted integral.** For positive source representatives `0 ≤ S(u) < N`,
`1 ≤ S(v) ≤ N` with `v` off the zero class, the literal origin representing a zero `u`, and
`(a-1,b)` representing a zero `u+v`, the integral of the difference sum `J` along a common line
`β_v < x < ε/c` through regular residue crossings, minus the boundary integrals of `J` over the
small squares around the crossed points `j/c`, `0 ≤ j < cβ_v`, is `√ε E(u+v)/(F⁻(u)F⁻(v))`. This
is the evaluation of the telescoped integral in the proof of [RW26, Radchenko, Wheeler (2026),
Theorem 2, `thm:fg.equs`, Section 3.2] on straight contours deformed around the crossed poles. -/
theorem integral_fiveTermWordDifferenceSum_of_crossed {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (u₁ u₂ v₁ v₂ : ℤ)
    (hu : 0 ≤ fiveTermLatticeIndex (letterWord bs) u₁ u₂ ∧
      fiveTermLatticeIndex (letterWord bs) u₁ u₂ < finiteDilogOrder (letterWord bs))
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂ ∧
      fiveTermLatticeIndex (letterWord bs) v₁ v₂ ≤ finiteDilogOrder (letterWord bs))
    (hv0 : fiveTermCharacteristicResidue (letterWord bs) v₁ v₂ ≠ 0)
    (huZero : fiveTermCharacteristicResidue (letterWord bs) u₁ u₂ = 0 → u₁ = 0 ∧ u₂ = 0)
    (huvZero : fiveTermCharacteristicResidue (letterWord bs) (u₁ + v₁) (u₂ + v₂) = 0 →
      u₁ + v₁ = letterWord bs 0 0 - 1 ∧ u₂ + v₂ = letterWord bs 0 1) :
    let ε := fltDenominator (letterWord bs : Mat(2, ℤ)) τ
    let c : ℝ := (letterWord bs 1 0 : ℝ)
    let w := fiveTermLatticeArgument (letterWord bs) τ u₁ u₂
    let y := fiveTermLatticeArgument (letterWord bs) τ v₁ v₂
    let β := -((v₁ : ℝ) * ε / c + y)
    let J := fiveTermWordDifferenceSum bs (u₁ + 1) v₁ w y τ
    ∀ (x : ℝ) (F : Finset ℤ),
      β < x → x < ε / c →
      (∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧ (j : ℝ) / c < β) →
      (∀ j : ℤ, 0 ≤ j → ((j : ℝ) / c < x ↔ (j : ℝ) / c < β)) →
      (∀ m : FiveTermIndex (letterWord bs),
        IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ) y
          (x - ((m : ℕ) : ℝ) * ε / c)) →
      ∀ᶠ r : ℝ in 𝓝[>] 0,
        IsRegularPeriodLatticeCrossing τ (fiveTermShiftedParameter (letterWord bs) τ y) r →
        IsRegularPeriodLatticeCrossing τ (fiveTermShiftedParameter (letterWord bs) τ y) (-r) →
        (∫ t : ℝ, J ((x : ℂ) + t * I) * I) -
          (∑ j ∈ F, rectBoundaryIntegral J
            ((j : ℂ) / (c : ℂ) - (r + r * I)) ((j : ℂ) / (c : ℂ) + (r + r * I))) =
        (Real.sqrt ε : ℂ) *
          finiteDilogE (letterWord bs) τ
            (fiveTermCharacteristicResidue (letterWord bs) (u₁ + v₁) (u₂ + v₂)) /
          (finiteDilogEMinus (letterWord bs) τ
              (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
            finiteDilogEMinus (letterWord bs) τ
              (fiveTermCharacteristicResidue (letterWord bs) v₁ v₂)) := by
  dsimp
  intro x F hxβ hxε hF hxF hreg
  let γ := letterWord bs
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let c : ℝ := (γ 1 0 : ℝ)
  let w := fiveTermLatticeArgument γ τ u₁ u₂
  let y := fiveTermLatticeArgument γ τ v₁ v₂
  let y' := fiveTermShiftedParameter γ τ y
  let x' : FiveTermIndex γ → ℝ :=
    fun m => x - ((m : ℕ) : ℝ) * ε / c
  let P : ℂ := 1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + v₁ * (τ : ℂ)))
  let Q : ℂ := (Real.sqrt ε : ℂ) *
    finiteDilogE γ τ (fiveTermCharacteristicResidue γ (u₁ + v₁) (u₂ + v₂)) /
      (finiteDilogEMinus γ τ (fiveTermCharacteristicResidue γ u₁ u₂) *
        finiteDilogEMinus γ τ (fiveTermCharacteristicResidue γ v₁ v₂))
  have hP : P ≠ 0 := fiveTerm_shifted_factor_ne_zero h.fixedPoint v₁ v₂ hv0
  have hsum : 0 < fiveTermLatticeIndex (letterWord bs) u₁ u₂ +
      fiveTermLatticeIndex (letterWord bs) v₁ v₂ := by omega
  obtain ⟨hupper', hlower⟩ := fiveTermLatticeArgument_source_rates h.fixedPoint
    u₁ u₂ v₁ v₂ hu.2 hsum
  have hupper : 0 < fiveTermUpperRate (letterWord bs) (u₁ + 1)
      (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂) τ :=
    lt_trans (inv_pos.mpr h.fixedPoint.fltDenominator_pos) hupper'
  have hlower' := fiveTermLowerRate_shifted_neg h (u₁ + 1) v₁ w y hlower
  have hreg' (m : FiveTermIndex γ) :
      IsRegularPeriodLatticeCrossing τ y' (x' m) :=
    fiveTermWord_crossed_shiftedRegular γ τ y (x' m) (hreg m).lattice
  have hleft (m : FiveTermIndex γ) :
      (-((((m : ℕ) : ℤ) + (v₁ - γ 0 0) : ℤ) : ℝ) * ε - 1) / c - y' < x' m :=
    fiveTermWord_crossed_leftBound h.fixedPoint v₁ ((m : ℕ) : ℤ) y x hxβ
  have hInt (m : FiveTermIndex γ) :
      Integrable (fun t : ℝ =>
        fiveTermWordKernel bs (u₁ + 1) (v₁ - γ 0 0) w y' τ
          ((m : ℕ) : ℤ) ((x' m : ℂ) + t * I)) :=
    integrable_fiveTermWordKernel bs h.ne_nil h.periodsPos (u₁ + 1)
      (v₁ - γ 0 0) ((m : ℕ) : ℤ) w y' (x' m)
      (hreg' m) hupper hlower'
  have he : 0 < (fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ)).re := by
    simpa only [← ofReal_fltDenominator, Complex.ofReal_re] using
      h.fixedPoint.fltDenominator_pos
  choose G hG using (fun m : FiveTermIndex γ =>
    exists_finset_fiveTermPoles_re_lt γ h.fixedPoint.lowerLeft_pos
      ((m : ℕ) : ℤ) (τ : ℂ) he (x' m))
  have hcross := fiveTermWordIntegralSum_eq_of_tendsto bs
    h.fixedPoint.lowerLeft_pos h.fixedPoint.irrational h.periodsPos
    (u₁ + 1) (v₁ - γ 0 0) w y'
    (not_isPeriodLatticePoint_fiveTermShiftedParameter h.fixedPoint v₁ v₂ hv0)
    (Q / P)
    (tendsto_closedFormUHPContinued_letterWord_shifted h
      u₁ u₂ v₁ v₂ hv0 huZero huvZero)
    x' hleft hreg' hupper hlower' G hG
  have hIntegral :
      (∫ t : ℝ, fiveTermWordDifferenceSum bs (u₁ + 1) v₁ w y τ
        ((x : ℂ) + t * I) * I) =
        P * fiveTermWordIntegralSum bs (u₁ + 1)
          (v₁ - γ 0 0) w y' τ x' := by
    simpa only [P, x', ε, c, y', y, w, γ] using
      integral_fiveTermWordDifferenceSum_eq h (u₁ + 1) v₁ w y x hInt
  have hSquares := fiveTermWord_crossed_squares_eq h (u₁ + 1) v₁ v₂
    w x F G hv hxβ hxε hF hxF hG
  filter_upwards [hcross, hSquares] with r hcrossR hSquaresR hrpos hrneg
  have hsum := hcrossR hrpos hrneg
  have hSquaresR' :
      (∑ j ∈ F, rectBoundaryIntegral
        (fiveTermWordDifferenceSum bs (u₁ + 1) v₁ w y τ)
          ((j : ℂ) / (γ 1 0 : ℂ) - (r + r * I))
          ((j : ℂ) / (γ 1 0 : ℂ) + (r + r * I))) =
        P * (∑ m : FiveTermIndex γ, ∑ kj ∈ G m,
          rectBoundaryIntegral (fiveTermWordKernel bs (u₁ + 1)
            (v₁ - γ 0 0) w y' τ ((m : ℕ) : ℤ))
            (faddeevModularUHPPole γ (τ : ℂ) kj.1 kj.2 - (r + r * I))
            (faddeevModularUHPPole γ (τ : ℂ) kj.1 kj.2 + (r + r * I))) := by
    simpa only [c, γ, Complex.ofReal_intCast] using hSquaresR
  simp only [w, y] at hSquaresR'
  rw [hIntegral, hsum, mul_add, hSquaresR']
  change P * (Q / P) + _ - _ = Q
  field_simp [hP]
  ring

end SIC

end
