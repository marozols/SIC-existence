/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.FiveTerm.Kernel
import SICs.SpecialFunctions.Faddeev.WordAsymptotics
import SICs.SpecialFunctions.Faddeev.WordDivisor

/-!
# The five-term kernel along a letter word

The five-term integrand of a letter word with its period varying near a real period, its finite
contour sum, its meromorphy and divisor in the argument, its joint continuity off the period
lattice, and its almost-everywhere agreement with the upper-half-plane kernel on affine contours.

This module defines the integrand of [RW26, Radchenko, Wheeler (2026), Theorem 3,
`thm:5term.mod.fad`, equation (23), `eq:5term.int`], at `n = h = 0`, for a letter word
`γ = ∏_j T^{b_j}S` with the modular quotient replaced by the word product of Proposition 2(ii),
`prop:prod.id.mod,fad`, equation (20), `eq:modulartofaddeevCF`. For `ε = j_γ(τ) = cτ+d` it is
`K_m(z) = Φ_{γ,m+1,0}(z;τ)/Φ_{γ,m+p,0}(z+y;τ) · e((cz+εm)w/ε+ℓ(z+mτ))`. Unlike the
upper-half-plane kernel `fiveTermKernelUHP`, it is defined at real periods; the principal
three-letter word keeps its own kernel in `SICs.Principal.Dilogarithm.Faddeev.FiveTerm`.

## The argument

The word product is meromorphic in its argument at slit-plane word periods, and the phase
exponential is entire and nonvanishing, so the kernel is meromorphic with the numerator divisor
minus the shifted denominator divisor. Off the period lattice `ℤ+ℤτ₀` every factor of the word
product lies in its gamma domain and the product is nonzero, so the kernel is jointly continuous
in the argument and the period there. For a fixed upper-half-plane period the modular quotient
and the word product have the same punctured germs, so the two kernels agree outside a countable
subset of every nonconstant affine real contour.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology MatrixGroups

namespace SIC

/-! ### The kernel and its contour sum -/

/-- The `m`-th integrand of [RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`,
equation (23), `eq:5term.int`] at `n = h = 0` for the letter word `γ = ∏_j T^{b_j}S`, written
with the word product of equation (20), `eq:modulartofaddeevCF`:
`K_m(z) = Φ_{γ,m+1,0}(z;τ)/Φ_{γ,m+p,0}(z+y;τ) · e((cz+εm)w/ε+ℓ(z+mτ))`, `ε = j_γ(τ)`. -/
def fiveTermWordKernel (bs : List ℤ) (ℓ p : ℤ) (w y τ : ℂ) (m : ℤ) (z : ℂ) : ℂ :=
  faddeevWord bs (m + 1) 0 z τ / faddeevWord bs (m + p) 0 (z + y) τ *
    Complex.exp (2 * Real.pi * I *
      ((((letterWord bs 1 0 : ℤ) : ℂ) * z + fltDenominator (letterWord bs : Mat(2, ℤ)) τ * m) *
          w / fltDenominator (letterWord bs : Mat(2, ℤ)) τ + ℓ * (z + m * τ)))

/-- The finite sum of straight-contour integrals on the left side of [RW26, Radchenko, Wheeler
(2026), Theorem 3, `thm:5term.mod.fad`, equation (23), `eq:5term.int`] for a letter word,
parametrized by `z = x_m + it` and hence with the factor `i = dz/dt`. -/
def fiveTermWordIntegralSum (bs : List ℤ) (ℓ p : ℤ) (w y τ : ℂ)
    (x : FiveTermIndex (letterWord bs) → ℝ) : ℂ :=
  ∑ m : FiveTermIndex (letterWord bs),
    I * ∫ t : ℝ, fiveTermWordKernel bs ℓ p w y τ ((m : ℕ) : ℤ) ((x m : ℂ) + t * I)

/-- Expands the named straight-contour sum of a letter word. -/
theorem fiveTermWordIntegralSum_def (bs : List ℤ) (ℓ p : ℤ) (w y τ : ℂ)
    (x : FiveTermIndex (letterWord bs) → ℝ) :
    fiveTermWordIntegralSum bs ℓ p w y τ x =
      ∑ m : FiveTermIndex (letterWord bs),
        I * ∫ t : ℝ, fiveTermWordKernel bs ℓ p w y τ ((m : ℕ) : ℤ) ((x m : ℂ) + t * I) :=
  rfl

/-! ### Meromorphy and divisor -/

/-- At slit-plane word periods, the five-term kernel of a letter word is meromorphic in its
argument at every point. -/
theorem meromorphicAt_fiveTermWordKernel (bs : List ℤ) (ℓ p m : ℤ) {w y τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (z : ℂ) :
    MeromorphicAt (fiveTermWordKernel bs ℓ p w y τ m) z := by
  unfold fiveTermWordKernel
  apply MeromorphicAt.mul
  · apply MeromorphicAt.div
    · exact meromorphicAt_faddeevWord bs (m + 1) 0 hτ z
    · have h := (meromorphicAt_faddeevWord bs (m + p) 0 hτ (z + y)).comp_analyticAt
        (g := fun ζ : ℂ => ζ + y) (by fun_prop)
      simpa only [Function.comp_def] using h
  · exact (show AnalyticAt ℂ (fun ζ : ℂ =>
      Complex.exp (2 * Real.pi * I *
        (((((letterWord bs 1 0 : ℤ) : ℂ) * ζ +
            fltDenominator (letterWord bs : Mat(2, ℤ)) τ * m) * w) /
          fltDenominator (letterWord bs : Mat(2, ℤ)) τ + ℓ * (ζ + m * τ)))) z
      by fun_prop).meromorphicAt

/-- At slit-plane word periods, the divisor of the five-term kernel of a letter word is the
numerator divisor minus the shifted denominator divisor; the phase exponential has order zero. -/
theorem meromorphicOrderAt_fiveTermWordKernel (bs : List ℤ) (ℓ p m : ℤ) {w y τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (z : ℂ) :
    meromorphicOrderAt (fiveTermWordKernel bs ℓ p w y τ m) z =
      meromorphicOrderAt (fun ζ : ℂ => faddeevWord bs (m + 1) 0 ζ τ) z -
        meromorphicOrderAt (fun ζ : ℂ => faddeevWord bs (m + p) 0 (ζ + y) τ) z := by
  let N : ℂ → ℂ := fun ζ => faddeevWord bs (m + 1) 0 ζ τ
  let D : ℂ → ℂ := fun ζ => faddeevWord bs (m + p) 0 (ζ + y) τ
  let E : ℂ → ℂ := fun ζ => Complex.exp (2 * Real.pi * I *
    (((((letterWord bs 1 0 : ℤ) : ℂ) * ζ +
        fltDenominator (letterWord bs : Mat(2, ℤ)) τ * m) * w) /
      fltDenominator (letterWord bs : Mat(2, ℤ)) τ + ℓ * (ζ + m * τ)))
  have hN : MeromorphicAt N z := meromorphicAt_faddeevWord bs (m + 1) 0 hτ z
  have hD : MeromorphicAt D z := by
    have h := (meromorphicAt_faddeevWord bs (m + p) 0 hτ (z + y)).comp_analyticAt
      (g := fun ζ : ℂ => ζ + y) (by fun_prop)
    simpa only [D, Function.comp_def] using h
  have hE : AnalyticAt ℂ E z := by dsimp [E]; fun_prop
  have hEord : meromorphicOrderAt E z = 0 := by
    simp [hE.meromorphicOrderAt_eq,
      (hE.analyticOrderAt_eq_zero).mpr (Complex.exp_ne_zero _)]
  change meromorphicOrderAt ((N / D) * E) z = _
  rw [meromorphicOrderAt_mul (hN.div hD) hE.meromorphicAt,
    meromorphicOrderAt_div hN hD, hEord]
  simp only [add_zero, N, D]

/-! ### Continuity off the period lattice -/

/-- At a real period with positive word periods, the five-term kernel of a letter word is
jointly continuous in the argument and the period at every argument `z` with `z` and `z+y`
off `ℤ+ℤτ₀`. -/
theorem continuousAt_fiveTermWordKernel (bs : List ℤ) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p m : ℤ) (w y z : ℂ)
    (hz : ¬ IsPeriodLatticePoint τ₀ z) (hzy : ¬ IsPeriodLatticePoint τ₀ (z + y)) :
    ContinuousAt (fun q : ℂ × ℂ => fiveTermWordKernel bs ℓ p w y q.2 m q.1) (z, (τ₀ : ℂ)) := by
  have hslit := hτ₀.slitPlane
  have hn := continuousAt_faddeevWord bs (m + 1) 0 hslit
    (faddeevWordGammaRegular_of_notMem bs (m + 1) 0 hslit hz)
  have harg : ContinuousAt (fun q : ℂ × ℂ => (q.1 + y, q.2))
      (z, (τ₀ : ℂ)) := by fun_prop
  have hden0 := continuousAt_faddeevWord bs (m + p) 0 hslit
    (faddeevWordGammaRegular_of_notMem bs (m + p) 0 hslit hzy)
  have hden : ContinuousAt (fun q : ℂ × ℂ =>
      faddeevWord bs (m + p) 0 (q.1 + y) q.2) (z, (τ₀ : ℂ)) := by
    simpa only [Function.comp_def] using hden0.comp_of_eq harg rfl
  have hnonzero : faddeevWord bs (m + p) 0 (z + y) τ₀ ≠ 0 :=
    faddeevWord_ne_zero_of_notMem bs (m + p) 0 hslit hzy
  have hJ : fltDenominator (letterWord bs : Mat(2, ℤ)) (τ₀ : ℂ) ≠ 0 := by
    cases bs with
    | nil => simp [letterWord_nil, fltDenominator_one]
    | cons b bs =>
        exact_mod_cast (ne_of_gt (hτ₀.fltDenominator_pos (by simp)))
  have hphase := continuousAt_fiveTermPhase (letterWord bs : Mat(2, ℤ)) ℓ m w z
    (τ₀ : ℂ) hJ
  exact (hn.div hden hnonzero).mul hphase

/-- Joint continuity of the word kernel along a vertical line with two regular real
crossings; used by the vertical bounds and contour limits. -/
theorem continuousAt_fiveTermWordKernel_vertical (bs : List ℤ) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p m : ℤ) (w y x t : ℝ)
    (hx : IsRegularPeriodLatticeCrossing τ₀ y x) :
    ContinuousAt (fun q : ℝ × ℂ =>
      fiveTermWordKernel bs ℓ p w y q.2 m (x + q.1 * I)) (t, (τ₀ : ℂ)) := by
  have hz := not_isPeriodLatticePoint_vertical τ₀ x t hx.base
  have hshift : ((x : ℂ) + (t : ℂ) * I) + y =
      ((x + y : ℝ) : ℂ) + t * I := by push_cast; ring
  have hzy : ¬ IsPeriodLatticePoint τ₀ (((x : ℂ) + t * I) + y) := by
    rw [hshift]
    exact not_isPeriodLatticePoint_vertical τ₀ (x + y) t
      (by simpa only [Complex.ofReal_add] using hx.shifted)
  have h := continuousAt_fiveTermWordKernel bs hτ₀ ℓ p m w y
    ((x : ℂ) + t * I) hz hzy
  have harg : ContinuousAt (fun q : ℝ × ℂ =>
      ((x : ℂ) + q.1 * I, q.2)) (t, (τ₀ : ℂ)) := by fun_prop
  simpa only [Function.comp_def] using h.comp_of_eq harg rfl

/-! ### Comparison with the upper-half-plane kernel -/

/-- For a fixed upper-half-plane period, the modular five-term kernel at `γ = ∏_j T^{b_j}S` and
the word kernel agree almost everywhere on every nonconstant affine real contour `t ↦ at+b`.
This bridges `fiveTermKernelUHP` and `fiveTermWordKernel` through
`ae_faddeevModularUHP_eq_faddeevWord`. -/
theorem ae_fiveTermKernelUHP_eq_fiveTermWordKernel (bs : List ℤ) (hbs : bs ≠ [])
    (ℓ p m : ℤ) (w y τ a b : ℂ) (hτ : 0 < τ.im) (ha : a ≠ 0) :
    ∀ᵐ t : ℝ, fiveTermKernelUHP (letterWord bs) ℓ p w y τ m (a * t + b) =
      fiveTermWordKernel bs ℓ p w y τ m (a * t + b) := by
  have hn := ae_faddeevModularUHP_eq_faddeevWord bs hbs (m + 1) 0 τ a b hτ ha
  have hden := ae_faddeevModularUHP_eq_faddeevWord bs hbs (m + p) 0 τ a (b + y) hτ ha
  filter_upwards [hn, hden] with t hnt hdt
  have harg : (a * (t : ℂ) + b) + y = a * t + (b + y) := by ring
  rw [fiveTermKernelUHP, fiveTermWordKernel, hnt, harg, hdt]

end SIC

end
