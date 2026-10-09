/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.FiveTerm.Telescoping
import SICs.SpecialFunctions.Faddeev.WordFiveTerm.Bounds

/-!
# Bounds for the residue kernel of a letter word

Exponential bounds for the residue kernel of a letter word at an attractive fixed point in upper
and lower sectors, its continuity on vertical lines avoiding its poles, and the integrability of
the residue kernel and of their sum on such lines.

This module supplies the estimates behind the strip argument in [RW26, Radchenko, Wheeler
(2026), Section 3.2, the proof of Theorem 2, `thm:fg.equs`], through the asymptotics of Lemma 1,
`lem:asymp`, for the word product in `SICs.SpecialFunctions.Faddeev.WordAsymptotics`. The
principal word is treated directly in
`SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ResidueStripBounds`.

## The argument

The residue kernel is the five-term kernel times `(1 - q^m e(z))/(e(z/ε) - q^m e(z))`. For
`Im z → ∞` the term `e(z/ε)`, of modulus `e^{-2π Im z/ε}`, dominates `q^m e(z)`, of modulus
`e^{-2π Im z}`, since `ε > 1`; the factor is then at most `4e^{2π Im z/ε}`. For `Im z → -∞` the
term `q^m e(z)` dominates and the factor is at most `4`. In an upper sector both word products
tend to one, and the phase has modulus `e^{-2πλ Im z}` up to a constant, so the residue kernel
decays when `λ > 1/ε`. In a lower sector the products, divided by their reflection asymptotes,
tend to one, and the remaining exponential decays with rate `-μ` when `μ < 0`. On a vertical
line whose crossing `x` avoids `ℤ+ℤτ` together with `x+y`, and avoids the poles `z_{(m,k)}`, the
residue kernel is continuous; the two tail bounds make it integrable, and so is the finite sum of
the residue kernels moved to a common line.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology MatrixGroups

namespace SIC

/-! ### The pole factor

The two exponentials in the pole factor have moduli `exp(-2π Im z/ε)` and `exp(-2π Im z)`.
-/

/-! The elementary exponential and quotient estimates are in `SICs.Analysis.NearOne`. -/

/-- The slower pole-factor exponential has modulus `exp(-2π Im z/ε)`; used by the upper and
lower pole bounds. -/
private lemma norm_fiveTermPoleFactor_slow_term (γ : SL(2, ℤ)) (τ : ℝ) (z : ℂ) :
    ‖Complex.exp (2 * Real.pi * I * (z / fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ)))‖ =
      Real.exp (-2 * Real.pi * z.im / fltDenominator (γ : Mat(2, ℤ)) τ) := by
  rw [norm_exp_two_pi_I_mul]
  have him : (z / fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ)).im =
      z.im / fltDenominator (γ : Mat(2, ℤ)) τ := by
    simpa [fltDenominator] using
      (Complex.div_ofReal_im z ((γ 1 0 : ℝ) * τ + (γ 1 1 : ℝ)))
  rw [him]
  congr 1
  ring_nf

/-- The faster pole-factor exponential has modulus `exp(-2π Im z)`; used by the upper and
lower pole bounds. -/
private lemma norm_fiveTermPoleFactor_fast_term (m : ℤ) (τ : ℝ) (z : ℂ) :
    ‖Complex.exp (2 * Real.pi * I * (z + m * (τ : ℂ)))‖ =
      Real.exp (-2 * Real.pi * z.im) := by
  rw [norm_exp_two_pi_I_mul]
  simp [Complex.add_im, Complex.mul_im]

/-- The pole quotient grows at most as `4 exp(2π Im z/ε)` on a sufficiently high tail. -/
private lemma exists_norm_div_fiveTermPoleFactor_upper {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m : ℤ) :
    ∃ T : ℝ, ∀ z : ℂ, T ≤ z.im →
      ‖(1 - Complex.exp (2 * Real.pi * I * (z + m * (τ : ℂ)))) /
          fiveTermPoleFactor γ τ m z‖ ≤
        4 * Real.exp (2 * Real.pi * z.im / fltDenominator (γ : Mat(2, ℤ)) τ) := by
  let r := fltDenominator (γ : Mat(2, ℤ)) τ
  let T := max 0 (Real.log 2 / (2 * Real.pi * (r - 1) / r))
  have hr : 1 < r := h.one_lt_fltDenominator
  refine ⟨T, fun z hz => ?_⟩
  let a := Complex.exp (2 * Real.pi * I * (z / fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ)))
  let b := Complex.exp (2 * Real.pi * I * (z + m * (τ : ℂ)))
  have ha : ‖a‖ = Real.exp (-2 * Real.pi * z.im / r) := by
    simpa only [a, r] using norm_fiveTermPoleFactor_slow_term γ τ z
  have hb : ‖b‖ = Real.exp (-2 * Real.pi * z.im) := by
    simpa only [b] using norm_fiveTermPoleFactor_fast_term m τ z
  have hba : ‖b‖ ≤ ‖a‖ / 2 := by
    rw [ha, hb]
    exact exp_neg_two_pi_le_half_exp_div r z.im hr ((le_max_right _ _).trans hz)
  have hb1 : ‖b‖ ≤ 1 := by
    rw [hb, Real.exp_le_one_iff]
    have ht : 0 ≤ z.im := (le_max_left _ _).trans hz
    nlinarith [Real.pi_pos]
  have hquot := norm_one_sub_div_le_four_div_of_first_dominates a b
    (by rw [ha]; positivity) hb1 hba
  rw [ha] at hquot
  have hright : 4 / Real.exp (-2 * Real.pi * z.im / r) =
      4 * Real.exp (2 * Real.pi * z.im / r) := by
    rw [div_eq_mul_inv, ← Real.exp_neg]
    congr 1
    ring_nf
  rw [hright] at hquot
  simpa only [fiveTermPoleFactor, a, b, r] using hquot

/-- The pole quotient is bounded by `4` on a sufficiently low tail. -/
private lemma exists_norm_div_fiveTermPoleFactor_lower {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m : ℤ) :
    ∃ T : ℝ, ∀ z : ℂ, z.im ≤ -T →
      ‖(1 - Complex.exp (2 * Real.pi * I * (z + m * (τ : ℂ)))) /
          fiveTermPoleFactor γ τ m z‖ ≤ 4 := by
  let r := fltDenominator (γ : Mat(2, ℤ)) τ
  let T := max 0 (Real.log 2 / (2 * Real.pi * (r - 1) / r))
  have hr : 1 < r := h.one_lt_fltDenominator
  refine ⟨T, fun z hz => ?_⟩
  let a := Complex.exp (2 * Real.pi * I * (z / fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ)))
  let b := Complex.exp (2 * Real.pi * I * (z + m * (τ : ℂ)))
  have ha : ‖a‖ = Real.exp (-2 * Real.pi * z.im / r) := by
    simpa only [a, r] using norm_fiveTermPoleFactor_slow_term γ τ z
  have hb : ‖b‖ = Real.exp (-2 * Real.pi * z.im) := by
    simpa only [b] using norm_fiveTermPoleFactor_fast_term m τ z
  have hab : ‖a‖ ≤ ‖b‖ / 2 := by
    rw [ha, hb]
    have hT : Real.log 2 / (2 * Real.pi * (r - 1) / r) ≤ T := le_max_right _ _
    exact exp_div_le_half_exp_neg_two_pi r z.im hr (by linarith)
  have hb1 : 1 ≤ ‖b‖ := by
    rw [hb, Real.one_le_exp_iff]
    have hT : 0 ≤ T := le_max_left _ _
    have ht : z.im ≤ 0 := by linarith
    nlinarith [Real.pi_pos]
  simpa only [fiveTermPoleFactor, a, b] using
    norm_one_sub_div_le_four_of_second_dominates a b hb1 hab

/-! ### Sector bounds -/

/-- At a real period the word kernel phase has modulus `exp(-2πλ Im z)`. -/
private lemma norm_exp_fiveTermWordPhase_real (bs : List ℤ) (ℓ m : ℤ)
    (w τ : ℝ) (z : ℂ) :
    ‖Complex.exp (fiveTermWordPhase bs ℓ w m z τ)‖ =
      ‖Complex.exp (fiveTermWordPhase bs ℓ w m 0 τ)‖ *
        Real.exp (-2 * Real.pi * fiveTermUpperRate (letterWord bs) ℓ w τ * z.im) := by
  rw [fiveTermWordPhase_eq_affine, fiveTermWordPhaseCoeff_atReal,
    Complex.exp_add, norm_mul, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * I *
      (fiveTermUpperRate (letterWord bs) ℓ w τ : ℂ) * z).re =
      -2 * Real.pi * fiveTermUpperRate (letterWord bs) ℓ w τ * z.im := by
    simp [Complex.mul_re]
  rw [hre]
  ring_nf

/-- At a real period the reflected phase has slope `-2πμ` in the imaginary direction. -/
private lemma norm_exp_fiveTermWordReflectedPhase_real (bs : List ℤ) (ℓ p m : ℤ)
    (w y τ : ℝ) (z : ℂ) :
    ‖Complex.exp (fiveTermWordReflectedPhase bs ℓ p m w y z τ)‖ =
      ‖Complex.exp (fiveTermWordReflectedPhase bs ℓ p m w y 0 τ)‖ *
        Real.exp ((-2 * Real.pi * fiveTermLowerRate (letterWord bs) ℓ p w y τ) * z.im) := by
  rw [fiveTermWordReflectedPhase_eq_affine,
    fiveTermWordReflectedPhaseCoeff_atReal, Complex.exp_add, norm_mul, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * I *
      (fiveTermLowerRate (letterWord bs) ℓ p w y τ : ℂ) * z).re =
      (-2 * Real.pi * fiveTermLowerRate (letterWord bs) ℓ p w y τ) * z.im := by
    simp [Complex.mul_re]
  rw [hre]
  ring_nf


/-- In every upper sector the residue kernel of a letter word at an attractive fixed point decays
exponentially when the upper rate exceeds `1/ε`. -/
theorem exists_norm_fiveTermWordResidueKernel_upper {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p m : ℤ) (w y K : ℝ)
    (hRate : (fltDenominator (letterWord bs : Mat(2, ℤ)) τ)⁻¹ <
      fiveTermUpperRate (letterWord bs) ℓ w τ) :
    ∃ C κ R : ℝ, 0 < κ ∧ ∀ z : ℂ, |z.re| ≤ K * z.im → R ≤ z.im →
      ‖fiveTermWordResidueKernel bs ℓ p w y τ m z‖ ≤ C * Real.exp (-κ * z.im) := by
  obtain ⟨ε₁, R₁, hε₁, hR₁, hratio⟩ :=
    exists_norm_fiveTermWord_ratio_upper_sector bs h.periodsPos p m y K
  obtain ⟨R₂, hpole⟩ :=
    exists_norm_div_fiveTermPoleFactor_upper h.fixedPoint m
  let r := fltDenominator (letterWord bs : Mat(2, ℤ)) τ
  let A := ‖Complex.exp (fiveTermWordPhase bs ℓ w m 0 τ)‖
  let κ := 2 * Real.pi * (fiveTermUpperRate (letterWord bs) ℓ w τ - r⁻¹)
  have hκ : 0 < κ := mul_pos (by positivity) (sub_pos.mpr hRate)
  refine ⟨12 * A, κ, max R₁ R₂, hκ, fun z hz ht => ?_⟩
  have hratio' := hratio τ (by simpa using hε₁.le) z hz ((le_max_left _ _).trans ht)
  have hpole' := hpole z ((le_max_right _ _).trans ht)
  have hphase := norm_exp_fiveTermWordPhase_real bs ℓ m w τ z
  have hk : ‖fiveTermWordKernel bs ℓ p w y τ m z‖ ≤
      3 * (A * Real.exp ((-2 * Real.pi * fiveTermUpperRate (letterWord bs) ℓ w τ) * z.im)) := by
    change ‖faddeevWord bs (m + 1) 0 z τ /
      faddeevWord bs (m + p) 0 (z + y) τ *
        Complex.exp (fiveTermWordPhase bs ℓ w m z τ)‖ ≤ _
    rw [norm_mul, hphase]
    exact mul_le_mul_of_nonneg_right hratio' (by positivity)
  rw [fiveTermWordResidueKernel, mul_div_assoc, norm_mul]
  calc
    _ ≤ (3 * (A * Real.exp ((-2 * Real.pi * fiveTermUpperRate (letterWord bs) ℓ w τ) * z.im))) *
        (4 * Real.exp (2 * Real.pi * z.im / r)) :=
      mul_le_mul hk hpole' (norm_nonneg _) (by positivity)
    _ = 12 * A * (Real.exp (-2 * Real.pi * fiveTermUpperRate
          (letterWord bs) ℓ w τ * z.im) * Real.exp (2 * Real.pi * z.im / r)) := by ring_nf
    _ = 12 * A * Real.exp (-κ * z.im) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [κ]
      rw [inv_eq_one_div]
      ring_nf

/-- In every lower sector the residue kernel of a letter word at an attractive fixed point decays
exponentially when the lower rate is negative. -/
theorem exists_norm_fiveTermWordResidueKernel_lower {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p m : ℤ) (w y K : ℝ)
    (hRate : fiveTermLowerRate (letterWord bs) ℓ p w y τ < 0) :
    ∃ C κ R : ℝ, 0 < κ ∧ ∀ z : ℂ, |z.re| ≤ K * -z.im → R ≤ -z.im →
      ‖fiveTermWordResidueKernel bs ℓ p w y τ m z‖ ≤ C * Real.exp (-κ * -z.im) := by
  obtain ⟨ε₁, R₁, hε₁, hR₁, hratio⟩ :=
    exists_norm_fiveTermWord_ratio_lower_sector bs h.ne_nil h.periodsPos p m y K
  obtain ⟨R₂, hpole⟩ :=
    exists_norm_div_fiveTermPoleFactor_lower h.fixedPoint m
  let A := ‖Complex.exp (fiveTermWordReflectedPhase bs ℓ p m w y 0 τ)‖
  let κ := -2 * Real.pi * fiveTermLowerRate (letterWord bs) ℓ p w y τ
  have hκ : 0 < κ := by
    dsimp [κ]
    nlinarith [mul_pos Real.pi_pos (neg_pos.mpr hRate)]
  refine ⟨12 * A, κ, max R₁ R₂, hκ, fun z hz ht => ?_⟩
  have hratio' := hratio τ (by simpa using hε₁.le) z hz ((le_max_left _ _).trans ht)
  have hpole' := hpole z (by linarith [le_max_right R₁ R₂])
  have hk : ‖fiveTermWordKernel bs ℓ p w y τ m z‖ ≤
      3 * (A * Real.exp (κ * z.im)) := by
    rw [fiveTermWordKernel_eq_lower_normalized, norm_mul,
      norm_fiveTermWord_reflection_phase,
      norm_exp_fiveTermWordReflectedPhase_real]
    exact mul_le_mul_of_nonneg_right hratio' (by positivity)
  rw [fiveTermWordResidueKernel, mul_div_assoc, norm_mul]
  calc
    _ ≤ (3 * (A * Real.exp (κ * z.im))) * 4 :=
      mul_le_mul hk hpole' (norm_nonneg _) (by positivity)
    _ = 12 * A * Real.exp (-κ * -z.im) := by ring_nf

/-! ### Vertical lines -/

/-- A real crossing is regular for the `m`-th residue kernel when it is a regular period-lattice
crossing for the shift `y` and is not a pole `z_{(m,k)}`. -/
structure IsFiveTermResidueCrossing (γ : SL(2, ℤ)) (τ : ℝ) (m : ℤ) (y x : ℝ) : Prop where
  /-- The crossing and its translate by `y` avoid the period lattice. -/
  lattice : IsRegularPeriodLatticeCrossing τ y x
  /-- The crossing is not a source argument of first coordinate `m`. -/
  pole : ∀ k : ℤ, x ≠ fiveTermLatticeArgument γ τ m k

/-- A regular crossing excludes every zero of the pole factor on its vertical line; used by
`continuous_fiveTermWordResidueKernel_vertical`. -/
private lemma fiveTermPoleFactor_vertical_ne_zero {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m : ℤ) (y x t : ℝ)
    (hx : IsFiveTermResidueCrossing (letterWord bs) τ m y x) :
    fiveTermPoleFactor (letterWord bs) τ m ((x : ℂ) + t * I) ≠ 0 := by
  intro hzero
  obtain ⟨k, hk⟩ := (fiveTermPoleFactor_eq_zero_iff h.fixedPoint m _).mp hzero
  have him : t = 0 := by
    have h' := congrArg Complex.im hk
    simpa using h'
  have hreal : x = fiveTermLatticeArgument (letterWord bs) τ m k := by
    have h' := congrArg Complex.re hk
    simpa [him] using h'
  exact hx.pole k hreal

/-- On a vertical line through a regular residue crossing, the residue kernel of a letter word is
continuous. -/
private theorem continuous_fiveTermWordResidueKernel_vertical {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p m : ℤ) (w y x : ℝ)
    (hx : IsFiveTermResidueCrossing (letterWord bs) τ m y x) :
    Continuous (fun t : ℝ => fiveTermWordResidueKernel bs ℓ p w y τ m ((x : ℂ) + t * I)) := by
  have hk : Continuous (fun t : ℝ =>
      fiveTermWordKernel bs ℓ p w y τ m ((x : ℂ) + t * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hcont := continuousAt_fiveTermWordKernel_vertical bs h.periodsPos
      ℓ p m w y x t hx.lattice
    have harg : ContinuousAt (fun s : ℝ => (s, (τ : ℂ))) t := by fun_prop
    simpa only [Function.comp_def] using hcont.comp_of_eq harg rfl
  have hnum : Continuous (fun t : ℝ =>
      (1 : ℂ) - Complex.exp (2 * Real.pi * I *
        (((x : ℂ) + t * I) + m * (τ : ℂ)))) := by fun_prop
  have hden : Continuous (fun t : ℝ =>
      fiveTermPoleFactor (letterWord bs) τ m ((x : ℂ) + t * I)) := by
    unfold fiveTermPoleFactor
    fun_prop
  have hdiv := hnum.div hden (fun t =>
    fiveTermPoleFactor_vertical_ne_zero h m y x t hx)
  have hres : Continuous (fun t : ℝ =>
      fiveTermWordKernel bs ℓ p w y τ m ((x : ℂ) + t * I) *
        ((1 - Complex.exp (2 * Real.pi * I *
          (((x : ℂ) + t * I) + m * (τ : ℂ)))) /
          fiveTermPoleFactor (letterWord bs) τ m ((x : ℂ) + t * I))) := by
    convert hk.mul hdiv using 1
  simpa only [fiveTermWordResidueKernel, mul_div_assoc] using hres

/-- The upper sector bound gives integrability on a high vertical ray; used by
`integrable_fiveTermWordResidueKernel`. -/
private lemma integrableOn_fiveTermWordResidueKernel_upper {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p m : ℤ) (w y x : ℝ)
    (hx : IsFiveTermResidueCrossing (letterWord bs) τ m y x)
    (hupper : (fltDenominator (letterWord bs : Mat(2, ℤ)) τ)⁻¹ <
      fiveTermUpperRate (letterWord bs) ℓ w τ) :
    ∃ T : ℝ, IntegrableOn
      (fun t : ℝ => fiveTermWordResidueKernel bs ℓ p w y τ m ((x : ℂ) + t * I))
      (Ioi T) := by
  obtain ⟨C, κ, R, hκ, hbound⟩ :=
    exists_norm_fiveTermWordResidueKernel_upper h ℓ p m w y 1 hupper
  let T := max R |x|
  have hf := continuous_fiveTermWordResidueKernel_vertical h ℓ p m w y x hx
  refine ⟨T, ?_⟩
  apply Integrable.mono' ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hκ) T).const_mul C)
    hf.aestronglyMeasurable
  apply (ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  have hsector : |(((x : ℂ) + t * I).re)| ≤
      (1 : ℝ) * (((x : ℂ) + t * I).im) := by
    simpa using (le_max_right R |x|).trans ht.le
  have hR : R ≤ (((x : ℂ) + t * I).im) := by
    simpa using (le_max_left R |x|).trans ht.le
  simpa using hbound _ hsector hR

/-- The lower sector bound gives integrability on a low vertical ray; used by
`integrable_fiveTermWordResidueKernel`. -/
private lemma integrableOn_fiveTermWordResidueKernel_lower {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p m : ℤ) (w y x : ℝ)
    (hx : IsFiveTermResidueCrossing (letterWord bs) τ m y x)
    (hlower : fiveTermLowerRate (letterWord bs) ℓ p w y τ < 0) :
    ∃ T : ℝ, IntegrableOn
      (fun t : ℝ => fiveTermWordResidueKernel bs ℓ p w y τ m ((x : ℂ) + t * I))
      (Iio (-T)) := by
  obtain ⟨C, κ, R, hκ, hbound⟩ :=
    exists_norm_fiveTermWordResidueKernel_lower h ℓ p m w y 1 hlower
  let T := max R |x|
  have hf := continuous_fiveTermWordResidueKernel_vertical h ℓ p m w y x hx
  refine ⟨T, ?_⟩
  have hi : IntegrableOn (fun t : ℝ => C * Real.exp (κ * t)) (Iic (-T)) :=
    (integrableOn_exp_mul_Iic hκ (-T)).const_mul C
  apply Integrable.mono' (hi.mono_set Iio_subset_Iic_self) hf.aestronglyMeasurable
  apply (ae_restrict_mem measurableSet_Iio).mono
  intro t ht
  have hheight : T ≤ -t := by
    change t < -T at ht
    linarith
  have hsector : |(((x : ℂ) + t * I).re)| ≤
      (1 : ℝ) * -(((x : ℂ) + t * I).im) := by
    simpa using (le_max_right R |x|).trans hheight
  have hR : R ≤ -(((x : ℂ) + t * I).im) := by
    simpa using (le_max_left R |x|).trans hheight
  simpa using hbound _ hsector hR

/-- On a vertical line through a regular residue crossing, the residue kernel of a letter word is
integrable when `1/ε < λ` and `μ < 0`. -/
private theorem integrable_fiveTermWordResidueKernel {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p m : ℤ) (w y x : ℝ)
    (hx : IsFiveTermResidueCrossing (letterWord bs) τ m y x)
    (hupper : (fltDenominator (letterWord bs : Mat(2, ℤ)) τ)⁻¹ <
      fiveTermUpperRate (letterWord bs) ℓ w τ)
    (hlower : fiveTermLowerRate (letterWord bs) ℓ p w y τ < 0) :
    Integrable (fun t : ℝ => fiveTermWordResidueKernel bs ℓ p w y τ m ((x : ℂ) + t * I)) := by
  let f : ℝ → ℂ := fun t =>
    fiveTermWordResidueKernel bs ℓ p w y τ m ((x : ℂ) + t * I)
  obtain ⟨T₁, hupperT⟩ :=
    integrableOn_fiveTermWordResidueKernel_upper h ℓ p m w y x hx hupper
  obtain ⟨T₂, hlowerT⟩ :=
    integrableOn_fiveTermWordResidueKernel_lower h ℓ p m w y x hx hlower
  let a := min (-T₂) T₁
  let b := max (-T₂) T₁
  have ha : IntegrableOn f (Iio a) :=
    hlowerT.mono_set (Iio_subset_Iio (min_le_left _ _))
  have hb : IntegrableOn f (Ioi b) :=
    hupperT.mono_set (Ioi_subset_Ioi (le_max_right _ _))
  have hm : IntegrableOn f (Icc a b) :=
    (continuous_fiveTermWordResidueKernel_vertical h ℓ p m w y x hx).continuousOn
      |>.integrableOn_Icc
  have hab : a ≤ b := (min_le_left _ _).trans (le_max_left _ _)
  change Integrable f
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := b),
    ← Set.Iio_union_Icc_eq_Iic hab]
  exact (ha.union hm).union hb

/-- The residue sum `L` of a letter word is integrable on a vertical line `x + iℝ` whose shifted
crossings `x - mε/c` are regular residue crossings, when `1/ε < λ` and `μ < 0`. -/
theorem integrable_fiveTermWordResidueSum {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y x : ℝ)
    (hx : ∀ m : FiveTermIndex (letterWord bs),
      IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ) y
        (x - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
          (letterWord bs 1 0 : ℝ)))
    (hupper : (fltDenominator (letterWord bs : Mat(2, ℤ)) τ)⁻¹ <
      fiveTermUpperRate (letterWord bs) ℓ w τ)
    (hlower : fiveTermLowerRate (letterWord bs) ℓ p w y τ < 0) :
    Integrable (fun t : ℝ => fiveTermWordResidueSum bs ℓ p w y τ ((x : ℂ) + t * I)) := by
  let f : FiveTermIndex (letterWord bs) → ℝ → ℂ := fun m t =>
    fiveTermWordResidueKernel bs ℓ p w y τ ((m : ℕ) : ℤ)
      (((x : ℂ) + t * I) -
        ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          ((letterWord bs 1 0 : ℤ) : ℂ))
  have hterm : ∀ m : FiveTermIndex (letterWord bs), Integrable (f m) := by
    intro m
    have h := integrable_fiveTermWordResidueKernel h ℓ p ((m : ℕ) : ℤ)
      w y (x - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ)) (hx m) hupper hlower
    convert h using 1
    funext t
    dsimp [f]
    congr 1
    push_cast
    ring_nf
  simpa only [fiveTermWordResidueSum, f] using
    (integrable_finsetSum Finset.univ (fun m _ => hterm m))

end SIC

end
