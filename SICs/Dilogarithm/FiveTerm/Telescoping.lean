/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.FiveTerm.ResidueKernel

/-!
# Telescoping of the residue kernels of a letter word

The sum of the residue kernels of a letter word on a common line, shifted by `(ε-1)/c`,
telescopes to the difference kernel of the five-term identity at shifted parameters.

This module follows [RW26, Radchenko, Wheeler (2026), Section 3.2, the proof of Theorem 2,
`thm:fg.equs`, the computation of equation (7), `eq:Fgpm.5term`] for `γ = ∏_j T^{b_j}S =
(a b; c d)` at an attractive fixed point `τ`, `ε = j_γ(τ)`, `q = e(τ)`, and `n = h = 0`. The
principal word is treated directly in `SICs.Principal.Dilogarithm.Faddeev.FiveTerm.Telescoping`.

## The argument

Move every contour to one line: `L(z) = ∑_{m<c} K̃_m(z - mε/c)`. Translating by `(ε-1)/c` sends
the `m`-th summand to a lattice shift of the `m'`-th, where `m + a - 1 = m' + Mc`, `0 ≤ m' < c`:
`-mε/c + (ε-1)/c = -m'ε/c + (aτ + b) - Mε`, using `aτ + b = ετ` at the fixed point. The word
shift laws `Φ_{m,n}(z + aτ + b) = Φ_{m+a,n+1}(z)` (the simultaneous index shift at the fixed
point) and `Φ_{m,n}(z + ε) = Φ_{m+c,n}(z)` (a lattice shift) change the two products of `K̃_m`
to `Φ_{m'+1,1}(z)/Φ_{m'+p+1,1}(z+y)`; the pole factor becomes `q(e(z/ε) - q^{m'} e(z))` because
`e((aτ + b)/ε) = q` and `e(aτ + b) = q^a`, and the phase gains the factor `q` through the
lattice relation `e(w/ε) = e(w + (ℓ-1)τ)`. Hence
`K̃_m(z - mε/c + (ε-1)/c) = (K̃_{m'} B_{m'})(z - m'ε/c)` with the one-step bracket
`B_{m'}(z) = (1 - e(z/ε))(1 - q^{m'+p}e(z+y)) / ((1 - q^{m'}e(z))(1 - e((z+y)/ε)))`.

Since `m ↦ m'` permutes `ℤ/c`, `L(z) - L(z + (ε-1)/c) = ∑_{m'} (K̃_{m'}(1 - B_{m'}))(z - m'ε/c)`,
and `q^p e(y) = e(y/ε)` makes `K̃_{m'}(1 - B_{m'})` the difference kernel
`J_{m'}(z) = (1 - q^p e(y)) Φ_{m'+1,0}(z)/Φ_{m'+p,1}(z+y) · e(phase)`, which is free of the kernel
poles. All identities are identities of germs at every point; on a vertical line they hold
outside a countable set.
-/

noncomputable section

open Complex Filter MeasureTheory
open scoped Topology MatrixGroups Fin.IntCast

namespace SIC

/-! ### The bracket, the difference kernel, and the line sums -/

/-- The one-step bracket
`B_m(z) = (1 - e(z/ε))(1 - q^{m+p} e(z+y)) / ((1 - q^m e(z))(1 - e((z+y)/ε)))`
of [RW26, Radchenko, Wheeler (2026), Section 3.2], `ε = j_γ(τ)`, `q = e(τ)`. -/
private def fiveTermBracket (γ : SL(2, ℤ)) (τ : ℝ) (p : ℤ) (y : ℂ) (m : ℤ) (z : ℂ) : ℂ :=
  (1 - Complex.exp (2 * Real.pi * I * (z / fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ)))) *
      (1 - Complex.exp (2 * Real.pi * I * (z + y + (m + p) * (τ : ℂ)))) /
    ((1 - Complex.exp (2 * Real.pi * I * (z + m * (τ : ℂ)))) *
      (1 - Complex.exp (2 * Real.pi * I * ((z + y) / fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ)))))

/-- The difference kernel `J_m(z) = (1 - q^p e(y)) Φ_{m+1,0}(z)/Φ_{m+p,1}(z+y) · e(phase_m(z))`
of [RW26, Radchenko, Wheeler (2026), Section 3.2] for a letter word: the integrand of Theorem 3
at the parameters `(ℓ, p - a, w, y + aτ + b)` times `1 - q^p e(y)`. -/
def fiveTermWordDifferenceKernel (bs : List ℤ) (ℓ p : ℤ) (w y : ℂ) (τ : ℝ) (m : ℤ) (z : ℂ) :
    ℂ :=
  (1 - Complex.exp (2 * Real.pi * I * (y + p * (τ : ℂ)))) *
    (faddeevWord bs (m + 1) 0 z τ / faddeevWord bs (m + p) 1 (z + y) τ) *
      Complex.exp (2 * Real.pi * I *
        ((((letterWord bs 1 0 : ℤ) : ℂ) * z +
            fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) * m) * w /
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) + ℓ * (z + m * (τ : ℂ))))

/-- The sum `L(z) = ∑_{m<c} K̃_m(z - mε/c)` of the residue kernels moved to a common line. -/
def fiveTermWordResidueSum (bs : List ℤ) (ℓ p : ℤ) (w y : ℂ) (τ : ℝ) (z : ℂ) : ℂ :=
  ∑ m : FiveTermIndex (letterWord bs),
    fiveTermWordResidueKernel bs ℓ p w y τ ((m : ℕ) : ℤ)
      (z - ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        ((letterWord bs 1 0 : ℤ) : ℂ))

/-- The sum `J(z) = ∑_{m<c} J_m(z - mε/c)` of the difference kernels on the common line. -/
def fiveTermWordDifferenceSum (bs : List ℤ) (ℓ p : ℤ) (w y : ℂ) (τ : ℝ) (z : ℂ) : ℂ :=
  ∑ m : FiveTermIndex (letterWord bs),
    fiveTermWordDifferenceKernel bs ℓ p w y τ ((m : ℕ) : ℤ)
      (z - ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        ((letterWord bs 1 0 : ℤ) : ℂ))

/-! ### The two one-step kernel identities -/

/-- The phase in the word kernel, named locally to state its contour translation. -/
private def wordPhase (bs : List ℤ) (ℓ m : ℤ) (w : ℂ) (τ : ℝ) (z : ℂ) : ℂ :=
  ((((letterWord bs 1 0 : ℤ) : ℂ) * z +
      fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) * m) * w /
    fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) + ℓ * (z + m * (τ : ℂ)))

/-- The two factors in the bracket denominator avoid zero on a punctured germ. -/
private lemma eventually_wordBracket_den_ne {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m : ℤ) (y z : ℂ) :
    ∀ᶠ ζ in 𝓝[≠] z,
      (1 - Complex.exp (2 * Real.pi * I * (ζ + m * (τ : ℂ))) ≠ 0) ∧
      (1 - Complex.exp (2 * Real.pi * I *
        ((ζ + y) / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) ≠ 0) := by
  let ε : ℂ := fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ)
  have hε : ε ≠ 0 := by
    rw [show ε = (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) by
      simp [ε, fltDenominator]]
    exact_mod_cast h.fixedPoint.fltDenominator_pos.ne'
  have hB := eventually_exp_two_pi_I_affine_ne_one_nhdsNE 1
    (m * (τ : ℂ)) z one_ne_zero
  have hF := eventually_exp_two_pi_I_affine_ne_one_nhdsNE ((1 : ℂ) / ε)
    (y / ε) z (div_ne_zero one_ne_zero hε)
  filter_upwards [hB, hF] with ζ hBζ hFζ
  constructor
  · exact sub_ne_zero.mpr (by simpa only [one_mul] using hBζ.symm)
  · apply sub_ne_zero.mpr
    convert hFζ.symm using 2; ring

/-- The pole factor avoids zero on a punctured germ. -/
private lemma eventually_wordPoleFactor_ne_zero {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m : ℤ) (z : ℂ) :
    ∀ᶠ ζ in 𝓝[≠] z, fiveTermPoleFactor (letterWord bs) τ m ζ ≠ 0 := by
  let ε : ℂ := fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ)
  have hεcast : ε = (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) := by
    simp [ε, fltDenominator]
  have hε0 : ε ≠ 0 := by rw [hεcast]; exact_mod_cast h.fixedPoint.fltDenominator_pos.ne'
  have hε1 : ε ≠ 1 := by
    rw [hεcast]
    exact_mod_cast (ne_of_gt h.fixedPoint.one_lt_fltDenominator)
  have hA : (1 : ℂ) / ε - 1 ≠ 0 := by
    intro h'
    exact hε1 (((div_eq_one_iff_eq hε0).mp (sub_eq_zero.mp h')).symm)
  have he := eventually_exp_two_pi_I_affine_ne_one_nhdsNE ((1 : ℂ) / ε - 1)
    (-(m : ℂ) * (τ : ℂ)) z hA
  filter_upwards [he] with ζ hζ
  intro hz
  apply hζ
  have hexp : Complex.exp (2 * Real.pi * I *
      (((1 : ℂ) / ε - 1) * ζ + -(m : ℂ) * (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * (ζ / ε)) /
        Complex.exp (2 * Real.pi * I * (ζ + m * (τ : ℂ))) := by
    rw [← Complex.exp_sub]
    congr 1
    ring
  rw [hexp]
  have heq : Complex.exp (2 * Real.pi * I * (ζ / ε)) =
      Complex.exp (2 * Real.pi * I * (ζ + m * (τ : ℂ))) := sub_eq_zero.mp hz
  rw [heq, div_self (Complex.exp_ne_zero _)]

/-- The two ways to separate the exponential factors in the bracket. -/
private lemma wordBracket_exp_product (bs : List ℤ) (τ : ℝ) (m p : ℤ) (y z : ℂ)
    (hy : Complex.exp (2 * Real.pi * I *
        (y / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * (y + p * (τ : ℂ)))) :
    Complex.exp (2 * Real.pi * I * (z + y + (m + p) * (τ : ℂ))) =
        Complex.exp (2 * Real.pi * I * (z + m * (τ : ℂ))) *
          Complex.exp (2 * Real.pi * I * (y + p * (τ : ℂ))) ∧
      Complex.exp (2 * Real.pi * I *
          ((z + y) / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
        Complex.exp (2 * Real.pi * I *
          (z / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) *
          Complex.exp (2 * Real.pi * I * (y + p * (τ : ℂ))) := by
  constructor
  · rw [← Complex.exp_add]
    congr 1
    ring
  · rw [← hy, ← Complex.exp_add]
    congr 1
    ring

/-- The bracket removes the residue pole and changes the denominator index to `1`. -/
private lemma fiveTermWordResidueKernel_mul_one_sub_bracket {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y : ℂ)
    (hy : Complex.exp (2 * Real.pi * I *
        (y / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * (y + p * (τ : ℂ))))
    (m : ℤ) (z : ℂ) :
    (fun ζ => fiveTermWordResidueKernel bs ℓ p w y τ m ζ *
        (1 - fiveTermBracket (letterWord bs) τ p y m ζ)) =ᶠ[𝓝[≠] z]
      fiveTermWordDifferenceKernel bs ℓ p w y τ m := by
  have hp := (h.periodsPos).slitPlane
  have ht := tendsto_add_const_nhdsNE y z
  have hV := ht.eventually (eventually_faddeevWord_ne_zero bs (m + p) 0 hp (z + y))
  have hW := (faddeevWord_index_add_one_right_eventuallyEq bs h.ne_nil
    (m + p) 0 hp (z + y)).comp_tendsto ht
  have hAB := eventually_wordPoleFactor_ne_zero h m z
  have hden := eventually_wordBracket_den_ne h m y z
  filter_upwards [hV, hW, hAB, hden] with ζ hVζ hWζ hABζ hdenζ
  let ε : ℂ := fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ)
  let A := Complex.exp (2 * Real.pi * I * (ζ / ε))
  let B := Complex.exp (2 * Real.pi * I * (ζ + m * (τ : ℂ)))
  let C := Complex.exp (2 * Real.pi * I * (y + p * (τ : ℂ)))
  let D := Complex.exp (2 * Real.pi * I * (ζ + y + (m + p) * (τ : ℂ)))
  let F := Complex.exp (2 * Real.pi * I * ((ζ + y) / ε))
  let U := faddeevWord bs (m + 1) 0 ζ τ
  let V := faddeevWord bs (m + p) 0 (ζ + y) τ
  let W := faddeevWord bs (m + p) 1 (ζ + y) τ
  let E := Complex.exp (2 * Real.pi * I * wordPhase bs ℓ m w τ ζ)
  change ((U / V * E) * (1 - B) / (A - B)) *
    (1 - ((1 - A) * (1 - D) / ((1 - B) * (1 - F)))) = (1 - C) * (U / W) * E
  obtain ⟨hD, hF⟩ := wordBracket_exp_product bs τ m p y ζ hy
  exact FiniteFiveTerm.bracket_algebra A B C D F U V W E hABζ hdenζ.1 hdenζ.2
    hVζ (by simpa only [Int.cast_zero, zero_mul, add_zero, Function.comp_def,
      zero_add] using hWζ) hD hF

/-- At the fixed point, the numerator of `γ·τ` is `τε`. -/
private lemma wordFixed_numerator {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) :
    ((letterWord bs 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((letterWord bs 0 1 : ℤ) : ℂ) =
      (τ : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) := by
  have hfix : flt (letterWord bs : Mat(2, ℤ)) (τ : ℂ) = (τ : ℂ) := by
    exact_mod_cast h.fixedPoint.flt_eq
  have hε : fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) ≠ 0 := by
    exact_mod_cast h.fixedPoint.fltDenominator_pos.ne'
  exact (div_eq_iff hε).mp hfix

/-- The determinant-one fixed-point identity is `a-cτ=ε⁻¹`. -/
private lemma wordFixed_inverse {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) :
    ((letterWord bs 0 0 : ℤ) : ℂ) -
        ((letterWord bs 1 0 : ℤ) : ℂ) * (τ : ℂ) =
      1 / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) := by
  have hε : fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) ≠ 0 := by
    exact_mod_cast h.fixedPoint.fltDenominator_pos.ne'
  have hi := inv_fltDenominator_eq (letterWord bs) (τ : ℂ) hε
  rw [show flt (letterWord bs : Mat(2, ℤ)) (τ : ℂ) = (τ : ℂ) by
    exact_mod_cast h.fixedPoint.flt_eq] at hi
  simpa only [one_div] using hi.symm

/-- The contour shift `aτ+b-Mε`, with the integer lattice coordinates of `γ`. -/
private def wordContourShift (bs : List ℤ) (τ : ℝ) (M : ℤ) : ℂ :=
  ((letterWord bs 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((letterWord bs 0 1 : ℤ) : ℂ) -
    M * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ)

/-- Translating by `aτ+b-Mε` changes `Φ_{r,0}` to `Φ_{r+a-Mc,1}` as a germ. -/
private lemma wordProduct_add_contourShift_eventuallyEq {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (r M : ℤ) (z : ℂ) :
    (fun ζ => faddeevWord bs r 0 (ζ + wordContourShift bs τ M) τ) =ᶠ[𝓝[≠] z]
      (fun ζ => faddeevWord bs
        (r + letterWord bs 0 0 - M * letterWord bs 1 0) 1 ζ τ) := by
  let γ := letterWord bs
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = (1 : ℤ) := by
    simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe γ
  have hidx : (0 : ℤ) + (γ 0 0 - M * γ 1 0) * γ 1 1 -
      (γ 0 1 - M * γ 1 1) * γ 1 0 = 1 := by
    linear_combination hdet
  have hshift : wordContourShift bs τ M =
      (((γ 0 0 - M * γ 1 0 : ℤ) : ℂ) * (τ : ℂ) +
        ((γ 0 1 - M * γ 1 1 : ℤ) : ℂ)) := by
    simp only [wordContourShift, fltDenominator]
    push_cast
    ring
  have hs := faddeevWord_add_lattice_eventuallyEq bs h.ne_nil r 0
    (γ 0 0 - M * γ 1 0) (γ 0 1 - M * γ 1 1) (h.periodsPos).slitPlane z
  dsimp [γ] at hidx hshift hs
  have hr : r + (letterWord bs 0 0 - M * letterWord bs 1 0) =
      r + letterWord bs 0 0 - M * letterWord bs 1 0 := by omega
  simpa only [hshift, hidx, hr, add_assoc] using hs

/-- The shifted argument divided by `ε` differs from `z/ε+τ` by the integer `-M`. -/
private lemma wordContourShift_div_argument {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (M : ℤ) (z : ℂ) :
    (z + wordContourShift bs τ M) /
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) -
      (z / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) + (τ : ℂ)) =
        -(M : ℂ) := by
  let ε : ℂ := fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ)
  have hε0 : ε ≠ 0 := by
    rw [show ε = (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) by
      simp [ε, fltDenominator]]
    exact_mod_cast h.fixedPoint.fltDenominator_pos.ne'
  have hS : wordContourShift bs τ M = ((τ : ℂ) - M) * ε := by
    dsimp [wordContourShift, ε]
    rw [wordFixed_numerator h]
    ring
  rw [hS]
  change (z + ((τ : ℂ) - M) * ε) / ε - (z / ε + (τ : ℂ)) = -(M : ℂ)
  field_simp [hε0]
  ring

/-- After reindexing, the shifted `z+mτ` differs from `z+(m'+1)τ` by an integer. -/
private lemma wordContourShift_add_argument {bs : List ℤ} {τ : ℝ}
    (_h : IsLetterWordFixedPoint bs τ) (m m' M : ℤ)
    (hm : m + letterWord bs 0 0 - M * letterWord bs 1 0 = m' + 1) (z : ℂ) :
    (z + wordContourShift bs τ M + m * (τ : ℂ)) -
      (z + (m' + 1) * (τ : ℂ)) =
        ((letterWord bs 0 1 - M * letterWord bs 1 1 : ℤ) : ℂ) := by
  have hmC : (m : ℂ) + ((letterWord bs 0 0 : ℤ) : ℂ) -
      M * ((letterWord bs 1 0 : ℤ) : ℂ) = (m' : ℂ) + 1 := by exact_mod_cast hm
  dsimp [wordContourShift, fltDenominator]
  push_cast
  linear_combination (τ : ℂ) * hmC

/-- The coefficient of `w` in the translated phase is `1-ε⁻¹`. -/
private lemma wordContourShift_phase_coefficient {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m m' M : ℤ)
    (hm : m + letterWord bs 0 0 - M * letterWord bs 1 0 = m' + 1) :
    ((letterWord bs 1 0 : ℤ) : ℂ) * wordContourShift bs τ M /
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) + (m : ℂ) - m' =
      1 - 1 / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) := by
  let ε : ℂ := fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ)
  let a : ℂ := letterWord bs 0 0
  let c : ℂ := letterWord bs 1 0
  have hε0 : ε ≠ 0 := by
    rw [show ε = (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ) by
      simp [ε, fltDenominator]]
    exact_mod_cast h.fixedPoint.fltDenominator_pos.ne'
  have hac : a - c * (τ : ℂ) = 1 / ε := wordFixed_inverse h
  have hS : wordContourShift bs τ M = ((τ : ℂ) - M) * ε := by
    dsimp [wordContourShift, ε]
    rw [wordFixed_numerator h]
    ring
  have hmC : (m : ℂ) + a - M * c = (m' : ℂ) + 1 := by
    dsimp [a, c]
    exact_mod_cast hm
  change c * wordContourShift bs τ M / ε + (m : ℂ) - m' = 1 - 1 / ε
  calc
    c * wordContourShift bs τ M / ε + (m : ℂ) - m' =
        c * ((τ : ℂ) - M) + (m : ℂ) - m' := by
      rw [hS, show c * (((τ : ℂ) - M) * ε) = (c * ((τ : ℂ) - M)) * ε by ring,
        mul_div_cancel_right₀ _ hε0]
    _ = 1 - (a - c * (τ : ℂ)) := by linear_combination hmC
    _ = 1 - 1 / ε := by rw [hac]

/-- The `ℓ` part of the translated phase is `τ+b-Md` after reindexing. -/
private lemma wordContourShift_phase_sum {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m m' M : ℤ)
    (hm : m + letterWord bs 0 0 - M * letterWord bs 1 0 = m' + 1) :
    wordContourShift bs τ M + ((m : ℂ) - m') * (τ : ℂ) =
      (τ : ℂ) + ((letterWord bs 0 1 - M * letterWord bs 1 1 : ℤ) : ℂ) := by
  have hs := wordContourShift_add_argument h m m' M hm 0
  linear_combination hs

/-- The difference of two word phases under an argument translation is affine in that shift. -/
private lemma wordPhase_shift_linear {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ m m' : ℤ) (w S z : ℂ) :
    wordPhase bs ℓ m w τ (z + S) - wordPhase bs ℓ m' w τ z =
      (((letterWord bs 1 0 : ℤ) : ℂ) * S /
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) + (m : ℂ) - m') * w +
        ℓ * (S + ((m : ℂ) - m') * (τ : ℂ)) := by
  have hε0 : fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) ≠ 0 := by
    exact_mod_cast h.fixedPoint.fltDenominator_pos.ne'
  simp only [wordPhase]
  field_simp [hε0]
  ring

/-- The word phase acquires the factor `e(τ)` under the contour shift. -/
private lemma wordPhase_exp_add_contourShift {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ m m' M : ℤ) (w : ℂ)
    (hw : Complex.exp (2 * Real.pi * I *
        (w / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * (w + (ℓ - 1) * (τ : ℂ))))
    (hm : m + letterWord bs 0 0 - M * letterWord bs 1 0 = m' + 1)
    (z : ℂ) :
    Complex.exp (2 * Real.pi * I *
      wordPhase bs ℓ m w τ (z + wordContourShift bs τ M)) =
      Complex.exp (2 * Real.pi * I * (τ : ℂ)) *
        Complex.exp (2 * Real.pi * I * wordPhase bs ℓ m' w τ z) := by
  let ε : ℂ := fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ)
  let k : ℤ := letterWord bs 0 1 - M * letterWord bs 1 1
  let S : ℂ := wordContourShift bs τ M
  have hcoeff := wordContourShift_phase_coefficient h m m' M hm
  have hsum := wordContourShift_phase_sum h m m' M hm
  have hlinear := wordPhase_shift_linear h ℓ m m' w S z
  have hphase : wordPhase bs ℓ m w τ (z + S) =
      wordPhase bs ℓ m' w τ z + (w - w / ε + ℓ * ((τ : ℂ) + k)) := by
    dsimp [ε, S, k] at hcoeff hsum ⊢
    rw [hcoeff, hsum] at hlinear
    linear_combination hlinear
  have hbase : Complex.exp (2 * Real.pi * I * (w - w / ε + ℓ * (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * (τ : ℂ)) := by
    have h₁ : Complex.exp (2 * Real.pi * I * (w - w / ε + ℓ * (τ : ℂ))) *
        Complex.exp (2 * Real.pi * I * (w / ε)) =
        Complex.exp (2 * Real.pi * I * (w + ℓ * (τ : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have h₂ : Complex.exp (2 * Real.pi * I * (τ : ℂ)) *
        Complex.exp (2 * Real.pi * I * (w + (ℓ - 1) * (τ : ℂ))) =
        Complex.exp (2 * Real.pi * I * (w + ℓ * (τ : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [hw] at h₁
    exact mul_right_cancel₀ (Complex.exp_ne_zero _) (h₁.trans h₂.symm)
  have hint : Complex.exp (2 * Real.pi * I * (w - w / ε + ℓ * ((τ : ℂ) + k))) =
      Complex.exp (2 * Real.pi * I * (w - w / ε + ℓ * (τ : ℂ))) := by
    apply exp_two_pi_I_eq_of_sub_intCast _ _ (ℓ * k)
    push_cast
    ring
  change Complex.exp (2 * Real.pi * I * wordPhase bs ℓ m w τ (z + S)) = _
  rw [hphase, show 2 * Real.pi * I *
      (wordPhase bs ℓ m' w τ z + (w - w / ε + ℓ * ((τ : ℂ) + k))) =
      2 * Real.pi * I * wordPhase bs ℓ m' w τ z +
        2 * Real.pi * I * (w - w / ε + ℓ * ((τ : ℂ) + k)) by ring,
    Complex.exp_add, hint, hbase]
  ring

/-- The pole factor acquires `e(τ)` under the same contour shift. -/
private lemma wordPoleFactor_add_contourShift {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m m' M : ℤ)
    (hm : m + letterWord bs 0 0 - M * letterWord bs 1 0 = m' + 1) (z : ℂ) :
    fiveTermPoleFactor (letterWord bs) τ m (z + wordContourShift bs τ M) =
      Complex.exp (2 * Real.pi * I * (τ : ℂ)) *
        fiveTermPoleFactor (letterWord bs) τ m' z := by
  let ε : ℂ := fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ)
  let T : ℂ := z + wordContourShift bs τ M
  have he1 : Complex.exp (2 * Real.pi * I * (T / ε)) =
      Complex.exp (2 * Real.pi * I * (z / ε + (τ : ℂ))) :=
    exp_two_pi_I_eq_of_sub_intCast _ _ (-M)
      (by simpa [T, ε] using wordContourShift_div_argument h M z)
  have he2 : Complex.exp (2 * Real.pi * I * (T + m * (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * (z + (m' + 1) * (τ : ℂ))) :=
    exp_two_pi_I_eq_of_sub_intCast _ _
      (letterWord bs 0 1 - M * letterWord bs 1 1)
      (by simpa [T] using wordContourShift_add_argument h m m' M hm z)
  have hmul1 : Complex.exp (2 * Real.pi * I * (z / ε + (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * (τ : ℂ)) *
        Complex.exp (2 * Real.pi * I * (z / ε)) := by
    rw [show 2 * Real.pi * I * (z / ε + (τ : ℂ)) =
      2 * Real.pi * I * (τ : ℂ) + 2 * Real.pi * I * (z / ε) by ring,
      Complex.exp_add]
  have hmul2 : Complex.exp (2 * Real.pi * I * (z + (m' + 1) * (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * (τ : ℂ)) *
        Complex.exp (2 * Real.pi * I * (z + m' * (τ : ℂ))) := by
    rw [show 2 * Real.pi * I * (z + (m' + 1) * (τ : ℂ)) =
      2 * Real.pi * I * (τ : ℂ) + 2 * Real.pi * I * (z + m' * (τ : ℂ)) by ring,
      Complex.exp_add]
  change fiveTermPoleFactor (letterWord bs) τ m T = _
  simp only [fiveTermPoleFactor]
  rw [he1, he2, hmul1, hmul2]
  ring

/-- The translated residue kernel has word-product indices `(m'+1,1)` and `(m'+p+1,1)`. -/
private lemma wordResidueKernel_shift_factor_eventuallyEq {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y : ℂ)
    (hw : Complex.exp (2 * Real.pi * I *
        (w / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * (w + (ℓ - 1) * (τ : ℂ))))
    (m m' M : ℤ) (hm : m + letterWord bs 0 0 - M * letterWord bs 1 0 = m' + 1)
    (z : ℂ) :
    (fun ζ => fiveTermWordResidueKernel bs ℓ p w y τ m
      (ζ + wordContourShift bs τ M)) =ᶠ[𝓝[≠] z]
      (fun ζ => faddeevWord bs (m' + 1) 1 ζ τ /
        faddeevWord bs (m' + p + 1) 1 (ζ + y) τ *
          (Complex.exp (2 * Real.pi * I * (τ : ℂ)) *
            Complex.exp (2 * Real.pi * I * wordPhase bs ℓ m' w τ ζ)) /
            (Complex.exp (2 * Real.pi * I * (τ : ℂ)) *
              fiveTermPoleFactor (letterWord bs) τ m' ζ)) := by
  let S := wordContourShift bs τ M
  have htS := tendsto_add_const_nhdsNE S z
  have htY := tendsto_add_const_nhdsNE y z
  have hK := (fiveTermWordResidueKernel_eventuallyEq h ℓ p w y m (z + S))
    |>.comp_tendsto htS
  have hN := wordProduct_add_contourShift_eventuallyEq h m M z
  have hD := (wordProduct_add_contourShift_eventuallyEq h (m + p) M (z + y))
    |>.comp_tendsto htY
  filter_upwards [hK, hN, hD] with ζ hKζ hNζ hDζ
  simp only [Function.comp_def] at hKζ hDζ
  have hpole := wordPoleFactor_add_contourShift h m m' M hm ζ
  have hphase := wordPhase_exp_add_contourShift h ℓ m m' M w hw hm ζ
  have harg : (ζ + S) + y = (ζ + y) + S := by abel
  change fiveTermWordResidueKernel bs ℓ p w y τ m (ζ + S) = _
  change fiveTermWordResidueKernel bs ℓ p w y τ m (ζ + S) =
    faddeevWord bs m 0 (ζ + S) τ /
      faddeevWord bs (m + p) 0 ((ζ + S) + y) τ *
        Complex.exp (2 * Real.pi * I * wordPhase bs ℓ m w τ (ζ + S)) /
          fiveTermPoleFactor (letterWord bs) τ m (ζ + S) at hKζ
  have hN' : faddeevWord bs m 0 (ζ + S) τ =
      faddeevWord bs (m' + 1) 1 ζ τ := by
    simpa only [S, hm] using hNζ
  have hD' : faddeevWord bs (m + p) 0 ((ζ + S) + y) τ =
      faddeevWord bs (m' + p + 1) 1 (ζ + y) τ := by
    rw [harg]
    simpa only [S, show m + p + letterWord bs 0 0 - M * letterWord bs 1 0 =
      m' + p + 1 by omega] using hDζ
  rw [hKζ, hN', hD', hpole, hphase]

/-- The shifted product fraction equals the residue kernel times its bracket as a germ. -/
private lemma wordShiftedFactor_mul_bracket_eventuallyEq {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y : ℂ) (m : ℤ) (z : ℂ) :
    (fun ζ => faddeevWord bs (m + 1) 1 ζ τ /
      faddeevWord bs (m + p + 1) 1 (ζ + y) τ *
        (Complex.exp (2 * Real.pi * I * (τ : ℂ)) *
          Complex.exp (2 * Real.pi * I * wordPhase bs ℓ m w τ ζ)) /
          (Complex.exp (2 * Real.pi * I * (τ : ℂ)) *
            fiveTermPoleFactor (letterWord bs) τ m ζ)) =ᶠ[𝓝[≠] z]
      (fun ζ => fiveTermWordResidueKernel bs ℓ p w y τ m ζ *
        fiveTermBracket (letterWord bs) τ p y m ζ) := by
  have hp := (h.periodsPos).slitPlane
  have ht := tendsto_add_const_nhdsNE y z
  have hK := fiveTermWordResidueKernel_eventuallyEq h ℓ p w y m z
  have hU := faddeevWord_index_add_one_left_eventuallyEq bs h.ne_nil m 0 hp z
  have hV := (faddeevWord_index_add_one_left_eventuallyEq bs h.ne_nil
    (m + p) 0 hp (z + y)).comp_tendsto ht
  have hU1 := faddeevWord_index_add_one_right_eventuallyEq bs h.ne_nil (m + 1) 0 hp z
  have hV1 := (faddeevWord_index_add_one_right_eventuallyEq bs h.ne_nil
    (m + p + 1) 0 hp (z + y)).comp_tendsto ht
  have hVne := ht.eventually (eventually_faddeevWord_ne_zero bs (m + p) 0 hp (z + y))
  have hAB := eventually_wordPoleFactor_ne_zero h m z
  have hden := eventually_wordBracket_den_ne h m y z
  filter_upwards [hK, hU, hV, hU1, hV1, hVne, hAB, hden]
    with ζ hKζ hUζ hVζ hU1ζ hV1ζ hVneζ hABζ hdenζ
  let ε : ℂ := fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ)
  let A := Complex.exp (2 * Real.pi * I * (ζ / ε))
  let B := Complex.exp (2 * Real.pi * I * (ζ + m * (τ : ℂ)))
  let D := Complex.exp (2 * Real.pi * I * (ζ + y + (m + p) * (τ : ℂ)))
  let F := Complex.exp (2 * Real.pi * I * ((ζ + y) / ε))
  let Q := Complex.exp (2 * Real.pi * I * (τ : ℂ))
  let U := faddeevWord bs m 0 ζ τ
  let V := faddeevWord bs (m + p) 0 (ζ + y) τ
  let U1 := faddeevWord bs (m + 1) 0 ζ τ
  let V1 := faddeevWord bs (m + p + 1) 0 (ζ + y) τ
  let U11 := faddeevWord bs (m + 1) 1 ζ τ
  let V11 := faddeevWord bs (m + p + 1) 1 (ζ + y) τ
  let E := Complex.exp (2 * Real.pi * I * wordPhase bs ℓ m w τ ζ)
  have halg := FiniteFiveTerm.shift_algebra A B D F Q U V U1 V1 U11 V11 E
    (Complex.exp_ne_zero _) hABζ hdenζ.1 hdenζ.2 hVneζ hUζ.symm
    (by simpa only [Function.comp_def, Int.cast_add] using hVζ.symm)
    (by simpa only [Int.cast_zero, zero_mul, add_zero, zero_add] using hU1ζ)
    (by simpa only [Function.comp_def, Int.cast_zero, zero_mul, add_zero, zero_add]
      using hV1ζ)
  change U11 / V11 * (Q * E) / (Q * (A - B)) =
    fiveTermWordResidueKernel bs ℓ p w y τ m ζ *
      fiveTermBracket (letterWord bs) τ p y m ζ
  rw [hKζ]
  exact halg

/-- Reindexing by `m+a-1=m'+Mc` turns the translated residue kernel into `K̃_{m'} B_{m'}`. -/
private lemma wordResidueKernel_shift_eventuallyEq {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y : ℂ)
    (hw : Complex.exp (2 * Real.pi * I *
        (w / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * (w + (ℓ - 1) * (τ : ℂ))))
    (m m' M : ℤ) (hm : m + letterWord bs 0 0 - M * letterWord bs 1 0 = m' + 1)
    (z : ℂ) :
    (fun ζ => fiveTermWordResidueKernel bs ℓ p w y τ m
      (ζ + wordContourShift bs τ M)) =ᶠ[𝓝[≠] z]
      (fun ζ => fiveTermWordResidueKernel bs ℓ p w y τ m' ζ *
        fiveTermBracket (letterWord bs) τ p y m' ζ) :=
  (wordResidueKernel_shift_factor_eventuallyEq h ℓ p w y hw m m' M hm z).trans
    (wordShiftedFactor_mul_bracket_eventuallyEq h ℓ p w y m' z)

/-! ### Reindexing and the finite sum -/

/-- Addition by `a-1` modulo `c` permutes the contour indices. -/
private def wordReindex {bs : List ℤ} {τ : ℝ} (h : IsLetterWordFixedPoint bs τ) :
    FiveTermIndex (letterWord bs) ≃ FiveTermIndex (letterWord bs) :=
  letI : NeZero (letterWord bs 1 0).toNat :=
    ⟨by have := h.fixedPoint.lowerLeft_pos; omega⟩
  Equiv.addRight (((letterWord bs 0 0 - 1 : ℤ) : FiveTermIndex (letterWord bs)))

/-- Every index has a quotient `M` with `m+a-1=m'+Mc`, including when `a-1` is negative. -/
private lemma wordReindex_exists_quotient {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m : FiveTermIndex (letterWord bs)) :
    ∃ M : ℤ, ((m : ℕ) : ℤ) + letterWord bs 0 0 -
        M * letterWord bs 1 0 =
      (((wordReindex h m : FiveTermIndex (letterWord bs)) : ℕ) : ℤ) + 1 := by
  let c : ℕ := (letterWord bs 1 0).toNat
  let a : ℤ := letterWord bs 0 0 - 1
  have hcpos : 0 < letterWord bs 1 0 := h.fixedPoint.lowerLeft_pos
  have hc : (c : ℤ) = letterWord bs 1 0 := by exact Int.toNat_of_nonneg hcpos.le
  have hcne : NeZero c := ⟨by omega⟩
  have heq : (wordReindex h m : Fin c) = @Fin.intCast c hcne ((m.val : ℤ) + a) := by
    change m + @Fin.intCast c hcne a = @Fin.intCast c hcne ((m.val : ℤ) + a)
    apply Fin.ext
    rw [Fin.val_add]
    have haVal : (Fin.intCast a : Fin c).val = (a % (c : ℤ)).toNat :=
      @Fin.val_intCast c hcne a
    have hsumVal : (Fin.intCast ((m.val : ℤ) + a) : Fin c).val =
        (((m.val : ℤ) + a) % (c : ℤ)).toNat :=
      @Fin.val_intCast c hcne ((m.val : ℤ) + a)
    rw [haVal, hsumVal]
    have ha0 : 0 ≤ a % (c : ℤ) := Int.emod_nonneg _ (by omega)
    have hmodZ : (((m.val + (a % (c : ℤ)).toNat) % c : ℕ) : ℤ) =
        ((m.val : ℤ) + a % (c : ℤ)) % (c : ℤ) := by
      rw [Int.natCast_emod]
      congr 1
      simp only [Nat.cast_add, Int.toNat_of_nonneg ha0]
    have hmodA : ((m.val : ℤ) + a % (c : ℤ)) % (c : ℤ) =
        ((m.val : ℤ) + a) % (c : ℤ) := by
      simpa only [add_comm] using Int.emod_add_emod a (c : ℤ) (m.val : ℤ)
    change (m.val + (a % (c : ℤ)).toNat) % c =
      (((m.val : ℤ) + a) % (c : ℤ)).toNat
    omega
  have hmod : (((wordReindex h m).val : ℕ) : ℤ) =
      ((m.val : ℤ) + a) % (c : ℤ) := by
    calc
      _ = ((@Fin.intCast c hcne ((m.val : ℤ) + a)).val : ℤ) :=
        congrArg (fun n : Fin c => (n.val : ℤ)) heq
      _ = ((((m.val : ℤ) + a) % (c : ℤ)).toNat : ℤ) :=
        congrArg (fun n : ℕ => (n : ℤ)) (@Fin.val_intCast c hcne ((m.val : ℤ) + a))
      _ = _ := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  refine ⟨((m.val : ℤ) + a) / (c : ℤ), ?_⟩
  have hdiv := Int.emod_add_mul_ediv ((m.val : ℤ) + a) (c : ℤ)
  have ha : letterWord bs 0 0 = a + 1 := by dsimp [a]; omega
  linear_combination ha + (((m.val : ℤ) + a) / (c : ℤ)) * hc - hdiv - hmod

/-- The common-line translation is the lattice shift of the reindexed summand. -/
private lemma wordContourShift_coordinate {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m m' M : ℤ)
    (hm : m + letterWord bs 0 0 - M * letterWord bs 1 0 = m' + 1)
    (z : ℂ) :
    z + (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) /
        ((letterWord bs 1 0 : ℤ) : ℂ) -
      (m : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        ((letterWord bs 1 0 : ℤ) : ℂ) =
      (z - (m' : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        ((letterWord bs 1 0 : ℤ) : ℂ)) + wordContourShift bs τ M := by
  let γ := letterWord bs
  let ρ : ℂ := τ
  let ε : ℂ := fltDenominator (γ : Mat(2, ℤ)) ρ
  let a : ℂ := γ 0 0
  let b : ℂ := γ 0 1
  let c : ℂ := γ 1 0
  let d : ℂ := γ 1 1
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (ne_of_gt h.fixedPoint.lowerLeft_pos)
  have hε : ε = c * ρ + d := rfl
  have hdetZ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = (1 : ℤ) := by
    simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe γ
  have hdet : a * d - b * c = 1 := by
    dsimp [a, b, c, d]
    exact_mod_cast hdetZ
  have hroot : c * (a * ρ + b) = a * ε - 1 := by
    calc
      c * (a * ρ + b) = a * (c * ρ + d) - (a * d - b * c) := by ring
      _ = a * ε - 1 := by rw [← hε, hdet]
  have hmC : (m : ℂ) + a - M * c = (m' : ℂ) + 1 := by
    dsimp [a, c]
    exact_mod_cast hm
  change z + (ε - 1) / c - m * ε / c =
    (z - m' * ε / c) + (a * ρ + b - M * ε)
  field_simp [hc0]
  linear_combination -hroot - ε * hmC

/-- The residue kernel's summand after moving the `m`-th contour to the common line. -/
private def wordCommonResidue (bs : List ℤ) (ℓ p : ℤ) (w y : ℂ) (τ : ℝ)
    (m : FiveTermIndex (letterWord bs)) (z : ℂ) : ℂ :=
  fiveTermWordResidueKernel bs ℓ p w y τ ((m : ℕ) : ℤ)
    (z - ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
      ((letterWord bs 1 0 : ℤ) : ℂ))

/-- The one-step bracket evaluated at the `m`-th common-line argument. -/
private def wordCommonBracket (bs : List ℤ) (p : ℤ) (y : ℂ) (τ : ℝ)
    (m : FiveTermIndex (letterWord bs)) (z : ℂ) : ℂ :=
  fiveTermBracket (letterWord bs) τ p y ((m : ℕ) : ℤ)
    (z - ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
      ((letterWord bs 1 0 : ℤ) : ℂ))

/-- One shifted common-line summand equals the bracketed summand at its reindexed position. -/
private lemma wordResidueSum_shift_summand_eventuallyEq {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y : ℂ)
    (hw : Complex.exp (2 * Real.pi * I *
        (w / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * (w + (ℓ - 1) * (τ : ℂ))))
    (m : FiveTermIndex (letterWord bs)) (z : ℂ) :
    (fun ζ => wordCommonResidue bs ℓ p w y τ m
      (ζ + (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) /
        ((letterWord bs 1 0 : ℤ) : ℂ))) =ᶠ[𝓝[≠] z]
    (fun ζ => wordCommonResidue bs ℓ p w y τ (wordReindex h m) ζ *
      wordCommonBracket bs p y τ (wordReindex h m) ζ) := by
  dsimp only [wordCommonResidue, wordCommonBracket]
  obtain ⟨M, hm⟩ := wordReindex_exists_quotient h m
  let m' := wordReindex h m
  let v : ℂ := ((m' : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
    ((letterWord bs 1 0 : ℤ) : ℂ)
  have ht : Tendsto (fun ζ : ℂ => ζ - v) (𝓝[≠] z) (𝓝[≠] (z - v)) := by
    simpa only [sub_eq_add_neg] using tendsto_add_const_nhdsNE (-v) z
  have hs := (wordResidueKernel_shift_eventuallyEq h ℓ p w y hw
    ((m : ℕ) : ℤ) ((m' : ℕ) : ℤ) M hm (z - v)).comp_tendsto ht
  filter_upwards [hs] with ζ hζ
  have hcoord := wordContourShift_coordinate h ((m : ℕ) : ℤ) ((m' : ℕ) : ℤ) M hm ζ
  simp only [Int.cast_natCast] at hcoord
  simp only [Function.comp_def] at hζ
  change _ = fiveTermWordResidueKernel bs ℓ p w y τ ((m' : ℕ) : ℤ) (ζ - v) *
    fiveTermBracket (letterWord bs) τ p y ((m' : ℕ) : ℤ) (ζ - v)
  rw [hcoord]
  exact hζ

/-- Bracket cancellation survives translation of each summand to the common line. -/
private lemma wordResidueSum_bracket_summand_eventuallyEq {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y : ℂ)
    (hy : Complex.exp (2 * Real.pi * I *
        (y / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * (y + p * (τ : ℂ))))
    (m : FiveTermIndex (letterWord bs)) (z : ℂ) :
    (fun ζ => fiveTermWordResidueKernel bs ℓ p w y τ ((m : ℕ) : ℤ)
      (ζ - ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        ((letterWord bs 1 0 : ℤ) : ℂ)) *
        (1 - fiveTermBracket (letterWord bs) τ p y ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
            ((letterWord bs 1 0 : ℤ) : ℂ)))) =ᶠ[𝓝[≠] z]
      (fun ζ => fiveTermWordDifferenceKernel bs ℓ p w y τ ((m : ℕ) : ℤ)
        (ζ - ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          ((letterWord bs 1 0 : ℤ) : ℂ))) := by
  let v : ℂ := ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
    ((letterWord bs 1 0 : ℤ) : ℂ)
  have ht : Tendsto (fun ζ : ℂ => ζ - v) (𝓝[≠] z) (𝓝[≠] (z - v)) := by
    simpa only [sub_eq_add_neg] using tendsto_add_const_nhdsNE (-v) z
  simpa only [Function.comp_def] using
    (fiveTermWordResidueKernel_mul_one_sub_bracket h ℓ p w y hy ((m : ℕ) : ℤ)
      (z - v)).comp_tendsto ht

/-! ### Telescoping -/

/-- **Telescoping of the residue sum.** Under the lattice relations `e(w/ε) = e(w + (ℓ-1)τ)` and
`e(y/ε) = e(y + pτ)`, `L(z) - L(z + (ε-1)/c) = J(z)` as germs at every point, as in the proof of
[RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, Section 3.2]. -/
theorem fiveTermWordResidueSum_sub_shift_eventuallyEq {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y : ℂ)
    (hw : Complex.exp (2 * Real.pi * I *
        (w / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * (w + (ℓ - 1) * (τ : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I *
        (y / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * (y + p * (τ : ℂ))))
    (z : ℂ) :
    (fun ζ => fiveTermWordResidueSum bs ℓ p w y τ ζ -
        fiveTermWordResidueSum bs ℓ p w y τ
          (ζ + (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) /
            ((letterWord bs 1 0 : ℤ) : ℂ))) =ᶠ[𝓝[≠] z]
      fiveTermWordDifferenceSum bs ℓ p w y τ := by
  let e := wordReindex h
  have hs := Filter.eventually_all.mpr (fun m : FiveTermIndex (letterWord bs) =>
    wordResidueSum_shift_summand_eventuallyEq h ℓ p w y hw m z)
  have hb := Filter.eventually_all.mpr (fun m : FiveTermIndex (letterWord bs) =>
    wordResidueSum_bracket_summand_eventuallyEq h ℓ p w y hy m z)
  filter_upwards [hs, hb] with ζ hsζ hbζ
  let f : FiveTermIndex (letterWord bs) → ℂ := fun m =>
    fiveTermWordResidueKernel bs ℓ p w y τ ((m : ℕ) : ℤ)
      (ζ - ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        ((letterWord bs 1 0 : ℤ) : ℂ))
  let b : FiveTermIndex (letterWord bs) → ℂ := fun m =>
    fiveTermBracket (letterWord bs) τ p y ((m : ℕ) : ℤ)
      (ζ - ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        ((letterWord bs 1 0 : ℤ) : ℂ))
  let g : FiveTermIndex (letterWord bs) → ℂ := fun m =>
    fiveTermWordDifferenceKernel bs ℓ p w y τ ((m : ℕ) : ℤ)
      (ζ - ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        ((letterWord bs 1 0 : ℤ) : ℂ))
  have hsum : (∑ m : FiveTermIndex (letterWord bs),
      fiveTermWordResidueKernel bs ℓ p w y τ ((m : ℕ) : ℤ)
        (ζ + (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) /
          ((letterWord bs 1 0 : ℤ) : ℂ) -
          ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
            ((letterWord bs 1 0 : ℤ) : ℂ))) =
      ∑ m, f (e m) * b (e m) := by
    exact Finset.sum_congr rfl (fun m hm => hsζ m)
  change (∑ m, f m) - (∑ m : FiveTermIndex (letterWord bs),
    fiveTermWordResidueKernel bs ℓ p w y τ ((m : ℕ) : ℤ)
      (ζ + (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) /
        ((letterWord bs 1 0 : ℤ) : ℂ) -
        ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          ((letterWord bs 1 0 : ℤ) : ℂ))) =
    ∑ m, g m
  rw [hsum]
  exact FiniteFiveTerm.finite_telescope e f b g (fun m => hbζ m)

/-- On every vertical line, the telescoping identity of the residue sum holds outside a
countable set, hence almost everywhere. -/
theorem ae_fiveTermWordResidueSum_sub_shift_eq {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y : ℂ)
    (hw : Complex.exp (2 * Real.pi * I *
        (w / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * (w + (ℓ - 1) * (τ : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I *
        (y / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * (y + p * (τ : ℂ))))
    (x : ℝ) :
    ∀ᵐ t : ℝ,
      fiveTermWordResidueSum bs ℓ p w y τ ((x : ℂ) + t * I) -
        fiveTermWordResidueSum bs ℓ p w y τ
          ((x : ℂ) + t * I + (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) /
            ((letterWord bs 1 0 : ℤ) : ℂ)) =
      fiveTermWordDifferenceSum bs ℓ p w y τ ((x : ℂ) + t * I) := by
  have ht := ae_eq_comp_affine_of_forall_eventuallyEq_nhdsNE
    (fun z => fiveTermWordResidueSum_sub_shift_eventuallyEq h ℓ p w y hw hy z)
    I (x : ℂ) Complex.I_ne_zero
  simpa only [mul_comm I, add_comm] using ht

end SIC

end
