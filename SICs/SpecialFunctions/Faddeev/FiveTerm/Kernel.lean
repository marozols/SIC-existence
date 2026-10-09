/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.Modular

/-!
# The upper-half-plane five-term kernel

The five-term integrand at `n = h = 0`, its named finite contour sum, q-product expansion,
holomorphy and measurability.

This module defines the integrand in [RW26, Radchenko, Wheeler (2026), Theorem 3,
`thm:5term.mod.fad`, equation (23), `eq:5term.int`], at `n = h = 0`.
For `ε = cτ+d` and `σ = γτ`, it is
`K_m(z) = Φ_{γ,m+1,0}(z;τ)/Φ_{γ,m+p,0}(z+y;τ) · e((cz+εm)w/ε+ℓ(z+mτ))`.

For real crossings `x_m`, the straight contours are parametrized by `z=x_m+it`, so
`dz=i dt`; `fiveTermIntegralSumUHP` records the resulting finite sum.

## The argument

Expanding the two modular q-products gives a quotient of four entire q-products times
an exponential. Its phase is jointly continuous in the argument and period wherever the
Jacobi denominator is nonzero. The expansion proves holomorphy away from the two denominator
zero sets.
The totalized quotients remain measurable at denominator zeros, including removable
points where their raw values differ from the continued values.
-/

noncomputable section

open Complex Real Filter Set MeasureTheory
open scoped Topology MatrixGroups

namespace SIC

/-- The finite index type `m = 0, ..., c - 1` for a five-term contour sum when `c > 0`, where
`c = γ₂₁`. -/
abbrev FiveTermIndex (γ : SL(2, ℤ)) := Fin (γ 1 0).toNat

/-- The integrand of [RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`,
equation (23), `eq:5term.int`] at `n = h = 0` on the upper half plane:
`K_m(z) = Φ_{γ,m+1,0}(z;τ)/Φ_{γ,m+p,0}(z+y;τ) · e((cz+(cτ+d)m)w/(cτ+d) + ℓ(z+mτ))`. -/
def fiveTermKernelUHP (γ : SL(2, ℤ)) (ℓ p : ℤ) (w y τ : ℂ) (m : ℤ) (z : ℂ) : ℂ :=
  faddeevModularUHP γ (m + 1) 0 z τ / faddeevModularUHP γ (m + p) 0 (z + y) τ *
    Complex.exp (2 * π * I *
      ((((γ 1 0 : ℤ) : ℂ) * z + fltDenominator (γ : Mat(2, ℤ)) τ * m) * w /
          fltDenominator (γ : Mat(2, ℤ)) τ + ℓ * (z + m * τ)))

/-- The finite contour sum on the left side of [RW26, Radchenko, Wheeler (2026), Theorem 3,
`thm:5term.mod.fad`, equation (23), `eq:5term.int`] at `n = h = 0`. -/
def fiveTermIntegralSumUHP (γ : SL(2, ℤ)) (ℓ p : ℤ)
    (y τ : ℂ) (x : FiveTermIndex γ → ℝ) (w : ℂ) : ℂ :=
  ∑ m : FiveTermIndex γ, I * (∫ t : ℝ,
    fiveTermKernelUHP γ ℓ p w y τ ((m : ℕ) : ℤ) ((x m : ℂ) + t * I))

/-- Expansion of the finite upper-half-plane five-term contour sum. -/
theorem fiveTermIntegralSumUHP_def (γ : SL(2, ℤ)) (ℓ p : ℤ)
    (y τ : ℂ) (x : FiveTermIndex γ → ℝ) (w : ℂ) :
    fiveTermIntegralSumUHP γ ℓ p y τ x w =
      ∑ m : FiveTermIndex γ, I * (∫ t : ℝ,
        fiveTermKernelUHP γ ℓ p w y τ ((m : ℕ) : ℤ) ((x m : ℂ) + t * I)) :=
  rfl

/-- The expanded kernel of Appendix A.2 of [RW26, Radchenko, Wheeler (2026), `app:mod.fad`]:
`K_m(z) = g_m(z) ϖ((z+y)/ε,σ)/ϖ(z/ε,σ)` with
`g_m(z) = ϖ(z+(m+1)τ,τ)/ϖ(z+y+(m+p)τ,τ) · e((cz+εm)w/ε + ℓ(z+mτ))`.
The identity is pointwise, including at zeros of the denominators. -/
theorem fiveTermKernelUHP_eq (γ : SL(2, ℤ)) (ℓ p : ℤ) (w y τ : ℂ) (m : ℤ) (z : ℂ) :
    fiveTermKernelUHP γ ℓ p w y τ m z =
      qPochhammer (z + ((m : ℂ) + 1) * τ) τ / qPochhammer (z + y + ((m : ℂ) + p) * τ) τ *
        Complex.exp (2 * π * I *
          ((((γ 1 0 : ℤ) : ℂ) * z + fltDenominator (γ : Mat(2, ℤ)) τ * m) * w /
              fltDenominator (γ : Mat(2, ℤ)) τ + ℓ * (z + m * τ))) *
        (qPochhammer ((z + y) / fltDenominator (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ) /
          qPochhammer (z / fltDenominator (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ)) := by
  unfold fiveTermKernelUHP faddeevModularUHP
  simp only [Int.cast_zero, zero_mul, add_zero]
  have h₁ : z + ((m + 1 : ℤ) : ℂ) * τ = z + ((m : ℂ) + 1) * τ := by push_cast; ring
  have h₂ : z + y + ((m + p : ℤ) : ℂ) * τ = z + y + ((m : ℂ) + p) * τ := by
    push_cast; ring
  rw [h₁, h₂]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- The exponential phase of [RW26, Radchenko, Wheeler (2026), equation (23),
`eq:5term.int`] is jointly continuous in `z,τ` where `cτ+d≠0`. -/
theorem continuousAt_fiveTermPhase (γ : Mat(2, ℤ)) (ℓ m : ℤ)
    (w z τ : ℂ)
    (hJ : fltDenominator γ τ ≠ 0) :
    ContinuousAt (fun q : ℂ × ℂ =>
      Complex.exp (2 * Real.pi * I *
        ((((γ 1 0 : ℤ) : ℂ) * q.1 +
              fltDenominator γ q.2 * m) * w /
            fltDenominator γ q.2 +
              ℓ * (q.1 + m * q.2)))) (z, τ) := by
  unfold fltDenominator at hJ ⊢
  fun_prop

/-- The kernel is holomorphic wherever neither `ϖ(z/ε,σ)` nor `ϖ(z+y+(m+p)τ,τ)` vanishes;
its other factors are entire in `z`. -/
theorem differentiableAt_fiveTermKernelUHP (γ : SL(2, ℤ)) (ℓ p : ℤ) (w y τ : ℂ)
    (hτ : 0 < τ.im) (m : ℤ) (z : ℂ)
    (h₁ : qPochhammer (z / fltDenominator (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ) ≠ 0)
    (h₂ : qPochhammer (z + y + ((m : ℂ) + p) * τ) τ ≠ 0) :
    DifferentiableAt ℂ (fiveTermKernelUHP γ ℓ p w y τ m) z := by
  have hσ := flt_im_pos γ hτ
  change DifferentiableAt ℂ (fun z => fiveTermKernelUHP γ ℓ p w y τ m z) z
  simp_rw [fiveTermKernelUHP_eq]
  have hn : DifferentiableAt ℂ
      (fun z => qPochhammer (z + ((m : ℂ) + 1) * τ) τ) z :=
    (qPochhammer_differentiable τ hτ).differentiableAt.comp z (by fun_prop)
  have hd : DifferentiableAt ℂ
      (fun z => qPochhammer (z + y + ((m : ℂ) + p) * τ) τ) z :=
    (qPochhammer_differentiable τ hτ).differentiableAt.comp z (by fun_prop)
  have hen : DifferentiableAt ℂ
      (fun z => Complex.exp (2 * π * I *
        ((((γ 1 0 : ℤ) : ℂ) * z + fltDenominator (γ : Mat(2, ℤ)) τ * m) * w /
          fltDenominator (γ : Mat(2, ℤ)) τ + ℓ * (z + m * τ)))) z := by fun_prop
  have hqn : DifferentiableAt ℂ
      (fun z => qPochhammer ((z + y) / fltDenominator (γ : Mat(2, ℤ)) τ)
        (flt (γ : Mat(2, ℤ)) τ)) z :=
    (qPochhammer_differentiable _ hσ).differentiableAt.comp z (by fun_prop)
  have hqd : DifferentiableAt ℂ
      (fun z => qPochhammer (z / fltDenominator (γ : Mat(2, ℤ)) τ)
        (flt (γ : Mat(2, ℤ)) τ)) z :=
    (qPochhammer_differentiable _ hσ).differentiableAt.comp z (by fun_prop)
  exact ((hn.div hd h₂).mul hen).mul (hqn.div hqd h₁)

/-- The totalized kernel of [RW26, Radchenko, Wheeler (2026), equation (23), `eq:5term.int`]
is Borel measurable, including at its removable exceptional points. -/
theorem measurable_fiveTermKernelUHP (γ : SL(2, ℤ)) (ℓ p : ℤ)
    (w y τ : ℂ) (hτ : 0 < τ.im) (m : ℤ) :
    Measurable (fiveTermKernelUHP γ ℓ p w y τ m) := by
  unfold fiveTermKernelUHP
  exact ((measurable_faddeevModularUHP γ (m + 1) 0 τ hτ).div
    ((measurable_faddeevModularUHP γ (m + p) 0 τ hτ).comp (by fun_prop))).mul
    (by fun_prop)

end SIC
