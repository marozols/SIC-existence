/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.FiveTerm.ResidueBounds
import SICs.SpecialFunctions.Faddeev.WordFiveTerm.ClosedForm

/-!
# The difference kernels of a letter word at shifted parameters

The difference kernel of a letter word is a multiple of the five-term word kernel at shifted
parameters, and the continued upper-half-plane closed form at these parameters tends to
`√ε E(u+v)/(F⁻(u)F⁻(v))` divided by that multiple, including at the zero classes.

This module follows the last lines of the proof of [RW26, Radchenko, Wheeler (2026), Theorem 2,
`thm:fg.equs`, Section 3.2], which evaluate the telescoped integral by Theorem 3,
`thm:5term.mod.fad`, equation (23), `eq:5term.int`, for `γ = ∏_j T^{b_j}S = (a b; c d)` at an
attractive fixed point `τ`, `ε = j_γ(τ)`. The principal word is treated directly in
`SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ShiftedIdentity`.

## The argument

The difference kernel `J_m(z) = (1 - q^p e(y)) Φ_{m+1,0}(z)/Φ_{m+p,1}(z+y) · e(phase)` is
`1 - q^p e(y)` times the five-term kernel at the parameters `(ℓ, p - a, w, y + aτ + b)`, since
`Φ_{m+p-a,0}(z + y + aτ + b) = Φ_{m+p,1}(z+y)` by the word shift laws at the fixed point, and
`aτ + b = ετ` is real. The upper rate is unchanged and the lower rate drops by `1/ε`. The closed
form is `Φ_{0,0}(0) Φ_{p+ℓ,1}(w+y)/(Φ_{p,1}(y)Φ_{ℓ,1}(w))`; at the source arguments the index
shift law moves the second indices to `0`: `Φ_{ℓ,1}(z_u) = Φ_{u₁,0}(z_u)`,
`(1 - q^p e(y))/Φ_{p,1}(z_v) = 1/Φ_{v₁,0}(z_v)`, and `Φ_{p+ℓ,1}(z_{u+v}) = Φ_{u₁+v₁,0}(z_{u+v})`,
which with `Φ_{0,0}(0) = √ε/μ_γ` (`faddeevWord_zero_eq_etaMultiplier`) and the finite values of
`etaMultiplier_mul_faddeevWordContinued_latticeArgument` gives `√ε E(u+v)/(F⁻(u)F⁻(v))`. At the
zero left class the literal origin `u = 0` uses the zero-left closed form, and at the zero sum
class the source sum `(a-1,b)` makes the numerator the removable origin.
-/

noncomputable section

open Complex Filter MeasureTheory
open scoped Topology MatrixGroups

namespace SIC

/-! ### The shifted parameters -/

/-- The shifted second parameter `y' = y + aτ + b` of the five-term identity evaluated in the
telescoped integral. -/
def fiveTermShiftedParameter (γ : SL(2, ℤ)) (τ y : ℝ) : ℝ :=
  y + ((γ 0 0 : ℝ) * τ + γ 0 1)

/-- As germs, the difference kernel is `1 - q^p e(y)` times the five-term word kernel at the
parameters `(ℓ, p - a, w, y + aτ + b)`. -/
theorem fiveTermWordDifferenceKernel_eventuallyEq {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y : ℝ) (m : ℤ) (z : ℂ) :
    fiveTermWordDifferenceKernel bs ℓ p w y τ m =ᶠ[𝓝[≠] z]
      (fun ζ => (1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (τ : ℂ)))) *
        fiveTermWordKernel bs ℓ (p - letterWord bs 0 0) w
          (fiveTermShiftedParameter (letterWord bs) τ y) τ m ζ) := by
  have ht : Tendsto (fun ζ : ℂ => ζ + (y : ℂ)) (𝓝[≠] z) (𝓝[≠] (z + y)) := by
    simpa only [Function.id_def] using
      ((hasDerivAt_id z).add_const (y : ℂ)).tendsto_nhdsNE one_ne_zero
  have hshift := (faddeevWord_add_lattice_eventuallyEq bs h.ne_nil
    (m + p - letterWord bs 0 0) 0 (letterWord bs 0 0) (letterWord bs 0 1)
    h.periodsPos.slitPlane (z + y)).comp_tendsto ht
  have hdet : letterWord bs 0 0 * letterWord bs 1 1 -
      letterWord bs 0 1 * letterWord bs 1 0 = 1 := by
    have hd := Matrix.SpecialLinearGroup.det_coe (letterWord bs)
    rwa [Matrix.det_fin_two] at hd
  filter_upwards [hshift] with ζ hζ
  have hden : faddeevWord bs (m + p - letterWord bs 0 0) 0
      (ζ + (fiveTermShiftedParameter (letterWord bs) τ y : ℂ)) τ =
      faddeevWord bs (m + p) 1 (ζ + y) τ := by
    convert hζ using 1 <;> simp [fiveTermShiftedParameter, hdet, add_assoc]
  simp only [fiveTermWordDifferenceKernel, fiveTermWordKernel]
  rw [show m + (p - letterWord bs 0 0) = m + p - letterWord bs 0 0 by omega,
    ← hden]
  ring

/-- On a vertical line the difference sum agrees almost everywhere with the shifted word
kernel sum; used by `integral_fiveTermWordDifferenceSum_eq`. -/
private theorem ae_fiveTermWordDifferenceSum_shifted {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y x : ℝ) :
    ∀ᵐ t : ℝ,
      fiveTermWordDifferenceSum bs ℓ p w y τ ((x : ℂ) + t * I) =
        (1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (τ : ℂ)))) *
          ∑ m : FiveTermIndex (letterWord bs),
            fiveTermWordKernel bs ℓ (p - letterWord bs 0 0) w
              (fiveTermShiftedParameter (letterWord bs) τ y) τ ((m : ℕ) : ℤ)
              (((x - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
                (letterWord bs 1 0 : ℝ) : ℝ) : ℂ) + t * I) := by
  have h_each (m : FiveTermIndex (letterWord bs)) :
      ∀ᵐ t : ℝ, fiveTermWordDifferenceKernel bs ℓ p w y τ ((m : ℕ) : ℤ)
          (((x : ℂ) + t * I) -
            ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
              (letterWord bs 1 0 : ℂ)) =
        (1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (τ : ℂ)))) *
          fiveTermWordKernel bs ℓ (p - letterWord bs 0 0) w
            (fiveTermShiftedParameter (letterWord bs) τ y) τ ((m : ℕ) : ℤ)
            (((x - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
              (letterWord bs 1 0 : ℝ) : ℝ) : ℂ) + t * I) := by
    have h := ae_eq_comp_affine_of_forall_eventuallyEq_nhdsNE
      (fun z => fiveTermWordDifferenceKernel_eventuallyEq h ℓ p w y
        ((m : ℕ) : ℤ) z) I
      (x - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ)) I_ne_zero
    filter_upwards [h] with t ht
    convert ht using 1 <;> push_cast <;> ring_nf
  filter_upwards [Filter.eventually_all.mpr h_each] with t ht
  simp only [fiveTermWordDifferenceSum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact ht m

/-- The line integral of the difference sum is `1 - q^p e(y)` times the word contour sum at the
shifted parameters, on the shifted crossings `x - mε/c`, when those contours are integrable. -/
theorem integral_fiveTermWordDifferenceSum_eq {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y x : ℝ)
    (hInt : ∀ m : FiveTermIndex (letterWord bs),
      Integrable (fun t : ℝ =>
        fiveTermWordKernel bs ℓ (p - letterWord bs 0 0) w
          (fiveTermShiftedParameter (letterWord bs) τ y) τ ((m : ℕ) : ℤ)
          (((x - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
            (letterWord bs 1 0 : ℝ) : ℝ) : ℂ) + t * I))) :
    (∫ t : ℝ, fiveTermWordDifferenceSum bs ℓ p w y τ ((x : ℂ) + t * I) * I) =
      (1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (τ : ℂ)))) *
        fiveTermWordIntegralSum bs ℓ (p - letterWord bs 0 0) w
          (fiveTermShiftedParameter (letterWord bs) τ y) τ
          (fun m => x - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
            (letterWord bs 1 0 : ℝ)) := by
  have hAE := ae_fiveTermWordDifferenceSum_shifted h ℓ p w y x
  calc
    _ = ∫ t : ℝ,
        ((1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (τ : ℂ)))) *
          ∑ m : FiveTermIndex (letterWord bs),
            fiveTermWordKernel bs ℓ (p - letterWord bs 0 0) w
              (fiveTermShiftedParameter (letterWord bs) τ y) τ ((m : ℕ) : ℤ)
              (((x - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
                (letterWord bs 1 0 : ℝ) : ℝ) : ℂ) + t * I)) * I :=
      integral_congr_ae (hAE.mono fun t ht => congrArg (· * I) ht)
    _ = _ := by
      rw [integral_mul_const, integral_const_mul,
        MeasureTheory.integral_finsetSum Finset.univ (by intro m hm; exact hInt m)]
      rw [fiveTermWordIntegralSum_def, mul_assoc, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      ring

/-- The shift of the right parameter preserves strict lower decay: the lower rate drops by
`1/ε`. -/
theorem fiveTermLowerRate_shifted_neg {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y : ℝ)
    (hlower : fiveTermLowerRate (letterWord bs) ℓ p w y τ < 0) :
    fiveTermLowerRate (letterWord bs) ℓ (p - letterWord bs 0 0) w
      (fiveTermShiftedParameter (letterWord bs) τ y) τ < 0 := by
  have hε : 0 < fltDenominator (letterWord bs : Mat(2, ℤ)) τ :=
    h.fixedPoint.fltDenominator_pos
  have hc : (letterWord bs 1 0 : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt h.fixedPoint.lowerLeft_pos)
  have hdet : (letterWord bs 0 0 : ℝ) * letterWord bs 1 1 -
      letterWord bs 0 1 * letterWord bs 1 0 = 1 := by
    have hd := Matrix.SpecialLinearGroup.det_coe (letterWord bs)
    rw [Matrix.det_fin_two] at hd
    exact_mod_cast hd
  have hunit : (letterWord bs 1 0 : ℝ) *
      ((letterWord bs 0 0 : ℝ) * τ + letterWord bs 0 1) =
      (letterWord bs 0 0 : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1 := by
    dsimp [fltDenominator]
    nlinarith [hdet]
  have hshift : (letterWord bs 1 0 : ℝ) *
      ((letterWord bs 0 0 : ℝ) * τ + letterWord bs 0 1) /
        fltDenominator (letterWord bs : Mat(2, ℤ)) τ -
      (letterWord bs 0 0 : ℝ) =
      -1 / fltDenominator (letterWord bs : Mat(2, ℤ)) τ := by
    apply (sub_eq_iff_eq_add).2
    field_simp
    linarith [hunit]
  have hr : fiveTermLowerRate (letterWord bs) ℓ (p - letterWord bs 0 0) w
      (fiveTermShiftedParameter (letterWord bs) τ y) τ =
      fiveTermLowerRate (letterWord bs) ℓ p w y τ -
        1 / fltDenominator (letterWord bs : Mat(2, ℤ)) τ := by
    simp only [fiveTermLowerRate, fiveTermShiftedParameter, Int.cast_sub]
    linear_combination hshift
  rw [hr]
  have : 0 < 1 / fltDenominator (letterWord bs : Mat(2, ℤ)) τ :=
    one_div_pos.mpr hε
  linarith

/-- A shifted source argument avoids `ℤ+ℤτ` when the residue of its pair is nonzero. -/
theorem not_isPeriodLatticePoint_fiveTermShiftedParameter {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (v₁ v₂ : ℤ)
    (hv : fiveTermCharacteristicResidue γ v₁ v₂ ≠ 0) :
    ¬ IsPeriodLatticePoint (τ : ℂ)
      (fiveTermShiftedParameter γ τ (fiveTermLatticeArgument γ τ v₁ v₂) : ℂ) := by
  simp only [fiveTermShiftedParameter]
  push_cast
  rw [show (fiveTermLatticeArgument γ τ v₁ v₂ : ℂ) +
      ((γ 0 0 : ℂ) * (τ : ℂ) + (γ 0 1 : ℂ)) =
      (fiveTermLatticeArgument γ τ v₁ v₂ : ℂ) +
        (γ 0 0 : ℤ) * (τ : ℂ) + (γ 0 1 : ℤ) by ring,
    isPeriodLatticePoint_add_int_mul_add_int_iff]
  exact (not_isPeriodLatticePoint_fiveTermLatticeArgument_iff h v₁ v₂).2 hv

/-- The factor `1 - q^{v₁} e(z_v)` is nonzero off the zero class. -/
theorem fiveTerm_shifted_factor_ne_zero {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (v₁ v₂ : ℤ)
    (hv : fiveTermCharacteristicResidue γ v₁ v₂ ≠ 0) :
    (1 : ℂ) - Complex.exp (2 * Real.pi * I *
      ((fiveTermLatticeArgument γ τ v₁ v₂ : ℂ) + v₁ * (τ : ℂ))) ≠ 0 := by
  have hlat : SigmaSLatticeFree τ (fiveTermLatticeArgument γ τ v₁ v₂) :=
    (sigmaSLatticeFree_iff_not_isPeriodLatticePoint _ _).2
      ((not_isPeriodLatticePoint_fiveTermLatticeArgument_iff h v₁ v₂).2 hv)
  exact hlat.one_sub_exp_ne_zero v₁

/-! ### The shifted closed form -/

/-- The matrix shift `(aτ+b)` changes the word indices `(m-a,0)` to `(m,1)` off the
period lattice; used by the shifted closed form. -/
private theorem faddeevWord_shifted_matrix {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m : ℤ) (z : ℂ)
    (hz : ¬ IsPeriodLatticePoint (τ : ℂ) z) :
    faddeevWord bs (m - letterWord bs 0 0) 0
        (z + (letterWord bs 0 0 : ℂ) * (τ : ℂ) + (letterWord bs 0 1 : ℂ)) τ =
      faddeevWord bs m 1 z τ := by
  have hdet : letterWord bs 0 0 * letterWord bs 1 1 -
      letterWord bs 0 1 * letterWord bs 1 0 = 1 := by
    have hd := Matrix.SpecialLinearGroup.det_coe (letterWord bs)
    rwa [Matrix.det_fin_two] at hd
  have hs := faddeevWord_add_lattice bs h.ne_nil (m - letterWord bs 0 0) 0
    (letterWord bs 0 0) (letterWord bs 0 1) h.periodsPos.slitPlane hz
  simpa only [sub_add_cancel, zero_add, hdet] using hs

/-- The source identity `z_u/ε-z_u=u₁τ+u₂` identifies the diagonal word indices at a
nonzero source class; used by the shifted closed form. -/
private theorem faddeevWord_source_indices_one {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (u₁ u₂ : ℤ)
    (hu : fiveTermCharacteristicResidue (letterWord bs) u₁ u₂ ≠ 0) :
    faddeevWord bs (u₁ + 1) 1 (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂) τ =
      faddeevWord bs u₁ 0 (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂) τ := by
  have hz := (not_isPeriodLatticePoint_fiveTermLatticeArgument_iff
    h.fixedPoint u₁ u₂).2 hu
  have hfix : flt (letterWord bs : Mat(2, ℤ)) (τ : ℂ) = τ := by
    exact_mod_cast h.fixedPoint.flt_eq
  have hsource : (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂ : ℂ) /
      fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) -
        (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂ : ℂ) =
      u₁ * (τ : ℂ) + u₂ := by
    exact_mod_cast fiveTermLatticeArgument_div_sub_self h.fixedPoint u₁ u₂
  have hphase : Complex.exp (2 * Real.pi * I *
        ((fiveTermLatticeArgument (letterWord bs) τ u₁ u₂ : ℂ) + u₁ * (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I *
        ((fiveTermLatticeArgument (letterWord bs) τ u₁ u₂ : ℂ) /
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) + 0 * (τ : ℂ))) := by
    apply exp_two_pi_I_eq_of_sub_intCast _ _ (-u₂)
    push_cast
    linear_combination -hsource
  simpa only [add_zero, zero_add] using
    faddeevWord_indices_add bs h.ne_nil u₁ 0 1 h.periodsPos.slitPlane hfix hz
      (by simpa only [Int.cast_zero] using hphase)

/-- The factor `1-q^{v₁}e(z_v)` replaces the denominator index `(v₁,1)` by `(v₁,0)`;
used by the shifted closed form. -/
private theorem faddeevWord_shifted_factor_div {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (v₁ v₂ : ℤ)
    (hv : fiveTermCharacteristicResidue (letterWord bs) v₁ v₂ ≠ 0) :
    (1 - Complex.exp (2 * Real.pi * I *
      ((fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ : ℂ) + v₁ * (τ : ℂ)))) /
        faddeevWord bs v₁ 1 (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ =
      1 / faddeevWord bs v₁ 0
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ := by
  have hz := (not_isPeriodLatticePoint_fiveTermLatticeArgument_iff
    h.fixedPoint v₁ v₂).2 hv
  have hs := faddeevWord_index_add_one_left bs h.ne_nil v₁ 1
    h.periodsPos.slitPlane hz
  rw [faddeevWord_source_indices_one h v₁ v₂ hv] at hs
  apply (div_eq_div_iff
    (faddeevWord_ne_zero_of_notMem bs v₁ 1 h.periodsPos.slitPlane hz)
    (faddeevWord_ne_zero_of_notMem bs v₁ 0 h.periodsPos.slitPlane hz)).2
  simpa [mul_comm] using hs

/-- Adding a shifted source argument gives the source sum followed by the matrix period
`aτ+b`; used by the shifted closed form. -/
private theorem fiveTerm_shifted_sum_argument (γ : SL(2, ℤ)) (τ : ℝ)
    (u₁ u₂ v₁ v₂ : ℤ) :
    (fiveTermLatticeArgument γ τ u₁ u₂ : ℂ) +
      (fiveTermShiftedParameter γ τ (fiveTermLatticeArgument γ τ v₁ v₂) : ℂ) =
      (fiveTermLatticeArgument γ τ (u₁ + v₁) (u₂ + v₂) : ℂ) +
        (γ 0 0 : ℂ) * (τ : ℂ) + (γ 0 1 : ℂ) := by
  have hadd : (fiveTermLatticeArgument γ τ u₁ u₂ : ℂ) +
      (fiveTermLatticeArgument γ τ v₁ v₂ : ℂ) =
        (fiveTermLatticeArgument γ τ (u₁ + v₁) (u₂ + v₂) : ℂ) := by
    exact_mod_cast (fiveTermLatticeArgument_add γ τ u₁ u₂ v₁ v₂).symm
  simp only [fiveTermShiftedParameter]
  push_cast
  rw [← hadd]
  ring

/-- The selected zero-sum pair `(a-1,b)` moves the shifted numerator to the removable
origin; used by `tendsto_closedFormUHPContinued_letterWord_shifted`. -/
private theorem fiveTerm_shifted_sum_origin {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (u₁ u₂ v₁ v₂ : ℤ)
    (h₁ : u₁ + v₁ = letterWord bs 0 0 - 1)
    (h₂ : u₂ + v₂ = letterWord bs 0 1) :
    (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂ : ℂ) +
      (fiveTermShiftedParameter (letterWord bs) τ
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) : ℂ) = 0 := by
  let γ := letterWord bs
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  have hε : ε ≠ 0 := h.fixedPoint.fltDenominator_pos.ne'
  have hε1 : ε - 1 ≠ 0 := ne_of_gt (by
    dsimp [ε]
    linarith [h.fixedPoint.one_lt_fltDenominator])
  have hfp : flt (γ : Mat(2, ℤ)) τ = τ := h.fixedPoint.flt_eq
  have hfix := fltDenominator_mul_intCast_add_intCast_mul γ τ hε 0 1
  rw [hfp] at hfix
  simp only [Int.cast_zero, Int.cast_one, zero_add, one_mul, zero_mul] at hfix
  change ε * τ = (γ 0 1 : ℝ) + (γ 0 0 : ℝ) * τ at hfix
  have hpair : (((γ 0 0 - 1 : ℤ) : ℝ) * τ + γ 0 1) = (ε - 1) * τ := by
    push_cast
    linear_combination -hfix
  have harg : fiveTermLatticeArgument γ τ (γ 0 0 - 1) (γ 0 1) =
      -((γ 0 0 : ℝ) * τ + γ 0 1) := by
    rw [fiveTermLatticeArgument_eq h.fixedPoint, hpair]
    change -(ε * ((ε - 1) * τ)) / (ε - 1) =
      -((γ 0 0 : ℝ) * τ + γ 0 1)
    rw [show (γ 0 0 : ℝ) * τ + γ 0 1 = ε * τ by linear_combination -hfix]
    field_simp [hε1]
  rw [fiveTerm_shifted_sum_argument γ τ u₁ u₂ v₁ v₂, h₁, h₂, harg]
  push_cast
  ring

/-- The shifted sum argument is lattice-free or the selected removable origin; used by
`tendsto_closedFormUHPContinued_letterWord_shifted`. -/
private theorem fiveTerm_shifted_sum_admissible {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (u₁ u₂ v₁ v₂ : ℤ)
    (huvZero : fiveTermCharacteristicResidue (letterWord bs) (u₁ + v₁) (u₂ + v₂) = 0 →
      u₁ + v₁ = letterWord bs 0 0 - 1 ∧ u₂ + v₂ = letterWord bs 0 1) :
    ¬ IsPeriodLatticePoint (τ : ℂ)
        ((fiveTermLatticeArgument (letterWord bs) τ u₁ u₂ : ℂ) +
          (fiveTermShiftedParameter (letterWord bs) τ
            (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) : ℂ)) ∨
      ((fiveTermLatticeArgument (letterWord bs) τ u₁ u₂ : ℂ) +
          (fiveTermShiftedParameter (letterWord bs) τ
            (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) : ℂ) = 0 ∧
        (v₁ - letterWord bs 0 0) + (u₁ + 1) = 0) := by
  by_cases hzero : fiveTermCharacteristicResidue (letterWord bs)
      (u₁ + v₁) (u₂ + v₂) = 0
  · obtain ⟨h₁, h₂⟩ := huvZero hzero
    exact Or.inr ⟨fiveTerm_shifted_sum_origin h u₁ u₂ v₁ v₂ h₁ h₂, by omega⟩
  · left
    rw [fiveTerm_shifted_sum_argument]
    rw [show (fiveTermLatticeArgument (letterWord bs) τ (u₁ + v₁) (u₂ + v₂) : ℂ) +
        (letterWord bs 0 0 : ℂ) * (τ : ℂ) + (letterWord bs 0 1 : ℂ) =
        (fiveTermLatticeArgument (letterWord bs) τ (u₁ + v₁) (u₂ + v₂) : ℂ) +
          (letterWord bs 0 0 : ℤ) * (τ : ℂ) + (letterWord bs 0 1 : ℤ) by norm_cast,
      isPeriodLatticePoint_add_int_mul_add_int_iff]
    exact (not_isPeriodLatticePoint_fiveTermLatticeArgument_iff h.fixedPoint _ _).2 hzero

/-- The matrix shift evaluates the denominator at a shifted source argument; used by the
shifted closed form. -/
private theorem faddeevWord_shifted_source {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m v₁ v₂ : ℤ)
    (hv : fiveTermCharacteristicResidue (letterWord bs) v₁ v₂ ≠ 0) :
    faddeevWord bs (m - letterWord bs 0 0) 0
        (fiveTermShiftedParameter (letterWord bs) τ
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)) τ =
      faddeevWord bs m 1 (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ := by
  have hz := (not_isPeriodLatticePoint_fiveTermLatticeArgument_iff
    h.fixedPoint v₁ v₂).2 hv
  have hs := faddeevWord_shifted_matrix h m _ hz
  convert hs using 1
  simp [fiveTermShiftedParameter, add_assoc]

/-- The matrix shift evaluates the numerator at the source sum; used by the shifted
closed form. -/
private theorem faddeevWord_shifted_source_sum {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (u₁ u₂ v₁ v₂ : ℤ)
    (huv : fiveTermCharacteristicResidue (letterWord bs) (u₁ + v₁) (u₂ + v₂) ≠ 0) :
    faddeevWord bs ((v₁ - letterWord bs 0 0) + (u₁ + 1)) 0
        ((fiveTermLatticeArgument (letterWord bs) τ u₁ u₂ : ℂ) +
          (fiveTermShiftedParameter (letterWord bs) τ
            (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) : ℂ)) τ =
      faddeevWord bs (u₁ + v₁ + 1) 1
        (fiveTermLatticeArgument (letterWord bs) τ (u₁ + v₁) (u₂ + v₂)) τ := by
  rw [fiveTerm_shifted_sum_argument]
  have hz := (not_isPeriodLatticePoint_fiveTermLatticeArgument_iff
    h.fixedPoint (u₁ + v₁) (u₂ + v₂)).2 huv
  simpa only [show (v₁ - letterWord bs 0 0) + (u₁ + 1) =
    (u₁ + v₁ + 1) - letterWord bs 0 0 by omega] using
      faddeevWord_shifted_matrix h (u₁ + v₁ + 1) _ hz

/-- The shifted closed form has the finite quotient when the left and sum classes are
nonzero; used by `tendsto_closedFormUHPContinued_letterWord_shifted`. -/
private theorem fiveTerm_shifted_value_nonzero {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (u₁ u₂ v₁ v₂ : ℤ)
    (hu : fiveTermCharacteristicResidue (letterWord bs) u₁ u₂ ≠ 0)
    (hv : fiveTermCharacteristicResidue (letterWord bs) v₁ v₂ ≠ 0)
    (huv : fiveTermCharacteristicResidue (letterWord bs) (u₁ + v₁) (u₂ + v₂) ≠ 0) :
    (1 - Complex.exp (2 * Real.pi * I *
      ((fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ : ℂ) + v₁ * (τ : ℂ)))) *
      fiveTermWordClosedForm bs (u₁ + 1) (v₁ - letterWord bs 0 0)
        (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂)
        (fiveTermShiftedParameter (letterWord bs) τ
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)) τ =
      (Real.sqrt (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) : ℂ) *
        finiteDilogE (letterWord bs) τ
          (fiveTermCharacteristicResidue (letterWord bs) (u₁ + v₁) (u₂ + v₂)) /
          (finiteDilogEMinus (letterWord bs) τ
              (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
            finiteDilogEMinus (letterWord bs) τ
              (fiveTermCharacteristicResidue (letterWord bs) v₁ v₂)) := by
  let γ := letterWord bs
  let R : ℂ := (Real.sqrt (fltDenominator (γ : Mat(2, ℤ)) τ) : ℂ)
  let M : ℂ := etaMultiplier γ
  let U : ℂ := faddeevWord bs u₁ 0 (fiveTermLatticeArgument γ τ u₁ u₂) τ
  let V : ℂ := faddeevWord bs v₁ 0 (fiveTermLatticeArgument γ τ v₁ v₂) τ
  let W : ℂ := faddeevWord bs (u₁ + v₁) 0
    (fiveTermLatticeArgument γ τ (u₁ + v₁) (u₂ + v₂)) τ
  have hμ : M ≠ 0 := etaMultiplier_ne_zero γ
  have hU : U ≠ 0 := faddeevWord_ne_zero_of_notMem bs u₁ 0 h.periodsPos.slitPlane
    ((not_isPeriodLatticePoint_fiveTermLatticeArgument_iff h.fixedPoint u₁ u₂).2 hu)
  have hV : V ≠ 0 := faddeevWord_ne_zero_of_notMem bs v₁ 0 h.periodsPos.slitPlane
    ((not_isPeriodLatticePoint_fiveTermLatticeArgument_iff h.fixedPoint v₁ v₂).2 hv)
  have hshiftNum := faddeevWord_shifted_source_sum h u₁ u₂ v₁ v₂ huv
  have hshiftDen := faddeevWord_shifted_source h v₁ v₁ v₂ hv
  have hdiagNum := faddeevWord_source_indices_one h (u₁ + v₁) (u₂ + v₂) huv
  have hdiagDen := faddeevWord_source_indices_one h u₁ u₂ hu
  have hfactor := faddeevWord_shifted_factor_div h v₁ v₂ hv
  have hEu := etaMultiplier_mul_faddeevWord_latticeArgument h u₁ u₂ hu
  have hEv := etaMultiplier_mul_faddeevWord_latticeArgument h v₁ v₂ hv
  have hEw := etaMultiplier_mul_faddeevWord_latticeArgument h (u₁ + v₁) (u₂ + v₂) huv
  calc
    _ = (R / M) * (W / (V * U)) := by
      rw [fiveTermWordClosedForm, faddeevWord_zero_eq_etaMultiplier h.ne_nil
        h.two_le h.fixedPoint, hshiftNum, hshiftDen, hdiagNum, hdiagDen]
      exact FiniteFiveTerm.closedForm_algebra _ _ _ _ _ _ _ hfactor
    _ = _ := by
      rw [finiteDilogEMinus_of_ne_zero h.fixedPoint hu,
        finiteDilogEMinus_of_ne_zero h.fixedPoint hv,
        ← hEu, ← hEv, ← hEw]
      change R / M * (W / (V * U)) = R * (M * W) / ((M * U) * (M * V))
      field_simp [hμ, hU, hV]

/-- At the literal left origin, the zero-left boundary quotient has the finite value
required by `tendsto_closedFormUHPContinued_letterWord_shifted`. -/
private theorem fiveTerm_shifted_value_zero_left {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (v₁ v₂ : ℤ)
    (hv : fiveTermCharacteristicResidue (letterWord bs) v₁ v₂ ≠ 0) :
    (1 - Complex.exp (2 * Real.pi * I *
      ((fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ : ℂ) + v₁ * (τ : ℂ)))) *
      (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) *
        faddeevWord bs (v₁ - letterWord bs 0 0 + 1) 0
          (fiveTermShiftedParameter (letterWord bs) τ
            (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)) τ /
        faddeevWord bs (v₁ - letterWord bs 0 0) 0
          (fiveTermShiftedParameter (letterWord bs) τ
            (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)) τ) =
      (Real.sqrt (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) : ℂ) *
        finiteDilogE (letterWord bs) τ
          (fiveTermCharacteristicResidue (letterWord bs) v₁ v₂) /
          (finiteDilogEMinus (letterWord bs) τ 0 *
            finiteDilogEMinus (letterWord bs) τ
              (fiveTermCharacteristicResidue (letterWord bs) v₁ v₂)) := by
  have hz := (not_isPeriodLatticePoint_fiveTermLatticeArgument_iff
    h.fixedPoint v₁ v₂).2 hv
  have hV : faddeevWord bs v₁ 0
      (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ≠ 0 :=
    faddeevWord_ne_zero_of_notMem bs v₁ 0 h.periodsPos.slitPlane hz
  have hshiftNum := faddeevWord_shifted_source h (v₁ + 1) v₁ v₂ hv
  have hshiftDen := faddeevWord_shifted_source h v₁ v₁ v₂ hv
  have hdiag := faddeevWord_source_indices_one h v₁ v₂ hv
  have hfactor := faddeevWord_shifted_factor_div h v₁ v₂ hv
  have hs : (Real.sqrt (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr h.fixedPoint.fltDenominator_pos
  have hE : finiteDilogE (letterWord bs) τ
      (fiveTermCharacteristicResidue (letterWord bs) v₁ v₂) ≠ 0 :=
    finiteDilogE_ne_zero h.fixedPoint
      (fiveTermCharacteristicResidue_mem h.fixedPoint v₁ v₂)
  have hsq : (Real.sqrt (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) : ℂ) ^ 2 =
      fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) := by
    exact_mod_cast Real.sq_sqrt h.fixedPoint.fltDenominator_pos.le
  rw [show v₁ - letterWord bs 0 0 + 1 = (v₁ + 1) - letterWord bs 0 0 by omega,
    hshiftNum, hshiftDen, hdiag]
  calc
    _ = fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) *
        faddeevWord bs v₁ 0 (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ *
        ((1 - Complex.exp (2 * Real.pi * I *
          ((fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ : ℂ) + v₁ * (τ : ℂ)))) /
          faddeevWord bs v₁ 1
            (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ) := by ring
    _ = fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) := by
      rw [hfactor]
      field_simp [hV]
    _ = _ := by
      rw [finiteDilogEMinus_zero, finiteDilogEMinus_of_ne_zero h.fixedPoint hv]
      field_simp [hs, hE]
      rw [← hsq]
      push_cast
      field_simp [hs]

/-- At the selected zero sum, the removable numerator is `Φ_{γ,0,0}(0;τ)` and gives
`E(0)` in the finite quotient; used by `tendsto_closedFormUHPContinued_letterWord_shifted`. -/
private theorem fiveTerm_shifted_value_zero_sum {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (u₁ u₂ v₁ v₂ : ℤ)
    (hu : fiveTermCharacteristicResidue (letterWord bs) u₁ u₂ ≠ 0)
    (hv : fiveTermCharacteristicResidue (letterWord bs) v₁ v₂ ≠ 0)
    (hzero : fiveTermCharacteristicResidue (letterWord bs) (u₁ + v₁) (u₂ + v₂) = 0)
    (h₁ : u₁ + v₁ = letterWord bs 0 0 - 1)
    (h₂ : u₂ + v₂ = letterWord bs 0 1) :
    (1 - Complex.exp (2 * Real.pi * I *
      ((fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ : ℂ) + v₁ * (τ : ℂ)))) *
      fiveTermWordClosedForm bs (u₁ + 1) (v₁ - letterWord bs 0 0)
        (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂)
        (fiveTermShiftedParameter (letterWord bs) τ
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)) τ =
      (Real.sqrt (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) : ℂ) *
        finiteDilogE (letterWord bs) τ
          (fiveTermCharacteristicResidue (letterWord bs) (u₁ + v₁) (u₂ + v₂)) /
          (finiteDilogEMinus (letterWord bs) τ
              (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
            finiteDilogEMinus (letterWord bs) τ
              (fiveTermCharacteristicResidue (letterWord bs) v₁ v₂)) := by
  let γ := letterWord bs
  let R : ℂ := (Real.sqrt (fltDenominator (γ : Mat(2, ℤ)) τ) : ℂ)
  let M : ℂ := etaMultiplier γ
  let U : ℂ := faddeevWord bs u₁ 0 (fiveTermLatticeArgument γ τ u₁ u₂) τ
  let V : ℂ := faddeevWord bs v₁ 0 (fiveTermLatticeArgument γ τ v₁ v₂) τ
  have hμ : M ≠ 0 := etaMultiplier_ne_zero γ
  have hU : U ≠ 0 := faddeevWord_ne_zero_of_notMem bs u₁ 0 h.periodsPos.slitPlane
    ((not_isPeriodLatticePoint_fiveTermLatticeArgument_iff h.fixedPoint u₁ u₂).2 hu)
  have hV : V ≠ 0 := faddeevWord_ne_zero_of_notMem bs v₁ 0 h.periodsPos.slitPlane
    ((not_isPeriodLatticePoint_fiveTermLatticeArgument_iff h.fixedPoint v₁ v₂).2 hv)
  have harg := fiveTerm_shifted_sum_origin h u₁ u₂ v₁ v₂ h₁ h₂
  have hidx : (v₁ - γ 0 0) + (u₁ + 1) = 0 := by
    change (v₁ - letterWord bs 0 0) + (u₁ + 1) = 0
    omega
  have hshiftDen := faddeevWord_shifted_source h v₁ v₁ v₂ hv
  have hdiagDen := faddeevWord_source_indices_one h u₁ u₂ hu
  have hfactor := faddeevWord_shifted_factor_div h v₁ v₂ hv
  have hEu := etaMultiplier_mul_faddeevWord_latticeArgument h u₁ u₂ hu
  have hEv := etaMultiplier_mul_faddeevWord_latticeArgument h v₁ v₂ hv
  calc
    _ = (R / M) * ((R / M) / (V * U)) := by
      rw [fiveTermWordClosedForm, hidx, harg,
        faddeevWord_zero_eq_etaMultiplier h.ne_nil h.two_le h.fixedPoint,
        hshiftDen, hdiagDen]
      exact FiniteFiveTerm.closedForm_algebra _ _ _ _ _ _ _ hfactor
    _ = _ := by
      rw [hzero, finiteDilogE_zero, finiteDilogEMinus_of_ne_zero h.fixedPoint hu,
        finiteDilogEMinus_of_ne_zero h.fixedPoint hv, ← hEu, ← hEv]
      change R / M * ((R / M) / (V * U)) = R * R / ((M * U) * (M * V))
      field_simp [hμ, hU, hV]

/-- The continued upper-half-plane closed form of a letter word at the shifted source parameters
`(u₁+1, v₁-a, z_v+aτ+b, z_u)` tends to `√ε E(u+v)/(F⁻(u)F⁻(v))` divided by
`1 - q^{v₁}e(z_v)` at the fixed point, for `v` off the zero class, the literal origin as the
representative of a zero left class, and `(a-1,b)` as the representative of a zero sum class; as
in the proof of [RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, Section 3.2]. -/
theorem tendsto_closedFormUHPContinued_letterWord_shifted {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (u₁ u₂ v₁ v₂ : ℤ)
    (hv0 : fiveTermCharacteristicResidue (letterWord bs) v₁ v₂ ≠ 0)
    (huZero : fiveTermCharacteristicResidue (letterWord bs) u₁ u₂ = 0 → u₁ = 0 ∧ u₂ = 0)
    (huvZero : fiveTermCharacteristicResidue (letterWord bs) (u₁ + v₁) (u₂ + v₂) = 0 →
      u₁ + v₁ = letterWord bs 0 0 - 1 ∧ u₂ + v₂ = letterWord bs 0 1) :
    Tendsto (fun τ' : ℂ => fiveTermClosedFormUHPContinued (letterWord bs)
        (u₁ + 1) (v₁ - letterWord bs 0 0)
        (fiveTermShiftedParameter (letterWord bs) τ
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)) τ'
        (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂))
      (𝓝[{τ' : ℂ | 0 < τ'.im}] (τ : ℂ))
      (𝓝 (((Real.sqrt (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) : ℂ) *
          finiteDilogE (letterWord bs) τ
            (fiveTermCharacteristicResidue (letterWord bs) (u₁ + v₁) (u₂ + v₂)) /
          (finiteDilogEMinus (letterWord bs) τ
              (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
            finiteDilogEMinus (letterWord bs) τ
              (fiveTermCharacteristicResidue (letterWord bs) v₁ v₂))) /
        (1 - Complex.exp (2 * Real.pi * I *
          ((fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ : ℂ) + v₁ * (τ : ℂ)))))) := by
  let γ := letterWord bs
  let P : ℂ := 1 - Complex.exp (2 * Real.pi * I *
    ((fiveTermLatticeArgument γ τ v₁ v₂ : ℂ) + v₁ * (τ : ℂ)))
  let Q : ℂ := (Real.sqrt (fltDenominator (γ : Mat(2, ℤ)) τ) : ℂ) *
    finiteDilogE γ τ (fiveTermCharacteristicResidue γ (u₁ + v₁) (u₂ + v₂)) /
      (finiteDilogEMinus γ τ (fiveTermCharacteristicResidue γ u₁ u₂) *
        finiteDilogEMinus γ τ (fiveTermCharacteristicResidue γ v₁ v₂))
  change Tendsto _ _ (𝓝 (Q / P))
  have hP : P ≠ 0 := fiveTerm_shifted_factor_ne_zero h.fixedPoint v₁ v₂ hv0
  have hy := not_isPeriodLatticePoint_fiveTermShiftedParameter h.fixedPoint v₁ v₂ hv0
  by_cases hu : fiveTermCharacteristicResidue γ u₁ u₂ = 0
  · obtain ⟨hu₁, hu₂⟩ := huZero hu
    subst u₁
    subst u₂
    have hzero : fiveTermCharacteristicResidue γ 0 0 = 0 := by
      funext i
      fin_cases i <;>
        simp [fiveTermCharacteristicResidue, latticeCharacteristic, Matrix.mulVec,
          dotProduct, Fin.sum_univ_two]
    have hvalue : fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ) *
        faddeevWord bs (v₁ - γ 0 0 + 1) 0
          (fiveTermShiftedParameter γ τ (fiveTermLatticeArgument γ τ v₁ v₂)) τ /
        faddeevWord bs (v₁ - γ 0 0) 0
          (fiveTermShiftedParameter γ τ (fiveTermLatticeArgument γ τ v₁ v₂)) τ =
          Q / P := by
      apply (eq_div_iff hP).2
      simpa only [P, Q, zero_add, hzero, mul_comm] using
        fiveTerm_shifted_value_zero_left h v₁ v₂ hv0
    have hlim := tendsto_closedFormUHPContinued_letterWord_zero_left
      bs h.ne_nil h.periodsPos (v₁ - γ 0 0)
      (fiveTermShiftedParameter γ τ (fiveTermLatticeArgument γ τ v₁ v₂)) hy
    rw [hvalue] at hlim
    simpa [γ, fiveTermLatticeArgument] using hlim
  · have hw := (not_isPeriodLatticePoint_fiveTermLatticeArgument_iff
      h.fixedPoint u₁ u₂).2 hu
    have hlim := tendsto_closedFormUHPContinued_letterWord bs h.ne_nil h.periodsPos
      (u₁ + 1) (v₁ - γ 0 0)
      (fiveTermLatticeArgument γ τ u₁ u₂)
      (fiveTermShiftedParameter γ τ (fiveTermLatticeArgument γ τ v₁ v₂))
      hw hy (fiveTerm_shifted_sum_admissible h u₁ u₂ v₁ v₂ huvZero)
    have hvalue : fiveTermWordClosedForm bs (u₁ + 1) (v₁ - γ 0 0)
        (fiveTermLatticeArgument γ τ u₁ u₂)
        (fiveTermShiftedParameter γ τ (fiveTermLatticeArgument γ τ v₁ v₂)) τ =
          Q / P := by
      apply (eq_div_iff hP).2
      by_cases huv : fiveTermCharacteristicResidue γ (u₁ + v₁) (u₂ + v₂) = 0
      · obtain ⟨h₁, h₂⟩ := huvZero huv
        simpa only [P, Q, mul_comm] using
          fiveTerm_shifted_value_zero_sum h u₁ u₂ v₁ v₂ hu hv0 huv h₁ h₂
      · simpa only [P, Q, mul_comm] using
          fiveTerm_shifted_value_nonzero h u₁ u₂ v₁ v₂ hu hv0 huv
    rw [hvalue] at hlim
    exact hlim

end SIC

end
