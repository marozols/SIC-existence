/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.ImproperConvergence
import SICs.SpecialFunctions.Faddeev.WordFiveTerm.Boundary
import SICs.SpecialFunctions.Faddeev.WordFiveTerm.Bounds

/-!
# Whole five-term contours of a letter word at the real boundary

The whole contour integral of the five-term kernel of a letter word on a fixed regular vertical
line, and the named finite sum of such integrals of the upper-half-plane kernel, converge to their
values at a real period with positive word periods as the period approaches it through the upper
half-plane.

This module formalizes the boundary passage in [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`] for the integrals of Theorem 3, `thm:5term.mod.fad`, equation (23),
`eq:5term.int`, along a letter word. It complements the finite-segment passage in
`SICs.SpecialFunctions.Faddeev.WordFiveTerm.Boundary`; the principal word is treated directly in
`SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ImproperBoundary`.

## The argument

At each upper-half-plane period, the modular kernel and the word kernel agree almost everywhere
on the vertical line. The uniform exponential estimates of
`SICs.SpecialFunctions.Faddeev.WordFiveTerm.Bounds` on both vertical tails, together with
uniform convergence on the compact middle segment, give one integrable majorant for all periods
near `τ₀`. Dominated convergence then passes the whole integral to the boundary.
Almost-everywhere equality transfers the limit back to the modular kernel, and continuity of
finite sums gives the limit of the contour sum.
-/

noncomputable section

open Complex Filter Topology MeasureTheory Set
open scoped MatrixGroups

namespace SIC

/-! ### Measurability and uniform tails -/

/-- Measurability of the word kernel on nearby upper-half-plane vertical lines, for
`fiveTermWordKernel_convergence_data`. -/
private lemma eventually_aestronglyMeasurable_fiveTermWordKernel
    (bs : List ℤ) (hbs : bs ≠ []) (ℓ p m : ℤ) (w y x : ℝ) {τ₀ : ℝ} :
    ∀ᶠ τ in 𝓝[{q : ℂ | 0 < q.im}] (τ₀ : ℂ),
      AEStronglyMeasurable (fun t : ℝ =>
        fiveTermWordKernel bs ℓ p w y τ m ((x : ℂ) + t * I)) := by
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact aestronglyMeasurable_fiveTermWordKernel bs hbs ℓ p m w y τ hτ x

/-- The uniform upper-tail bound for the word kernel in the eventual form needed by
`tendsto_integral_of_exp_tails`. -/
private lemma exists_eventually_upperTail_fiveTermWordKernel
    (bs : List ℤ) {τ₀ : ℝ} (hτ₀ : FaddeevWordPeriodsPos bs τ₀)
    (ℓ p m : ℤ) (w y x : ℝ)
    (hRate : 0 < fiveTermUpperRate (letterWord bs) ℓ w τ₀) :
    ∃ C κ T : ℝ, 0 < κ ∧
      ∀ᶠ τ in 𝓝[{q : ℂ | 0 < q.im}] (τ₀ : ℂ), ∀ t : ℝ, T ≤ t →
        ‖fiveTermWordKernel bs ℓ p w y τ m ((x : ℂ) + t * I)‖ ≤
          C * Real.exp (-κ * t) := by
  obtain ⟨ε, C, κ, T, hε, _, hκ, _, hbound⟩ :=
    exists_norm_fiveTermWordKernel_upper bs hτ₀ ℓ p m w y x hRate
  exact ⟨C, κ, T, hκ, eventually_tail_bound_of_uniform hε
    (fun τ t => fiveTermWordKernel bs ℓ p w y τ m ((x : ℂ) + t * I))
    (fun t => T ≤ t) (fun t => C * Real.exp (-κ * t)) hbound⟩

/-- The uniform lower-tail bound for the word kernel in the eventual form needed by
`tendsto_integral_of_exp_tails`. -/
private lemma exists_eventually_lowerTail_fiveTermWordKernel
    (bs : List ℤ) (hbs : bs ≠ []) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p m : ℤ) (w y x : ℝ)
    (hRate : fiveTermLowerRate (letterWord bs) ℓ p w y τ₀ < 0) :
    ∃ C κ T : ℝ, 0 < κ ∧
      ∀ᶠ τ in 𝓝[{q : ℂ | 0 < q.im}] (τ₀ : ℂ), ∀ t : ℝ, t ≤ -T →
        ‖fiveTermWordKernel bs ℓ p w y τ m ((x : ℂ) + t * I)‖ ≤
          C * Real.exp (κ * t) := by
  obtain ⟨ε, C, κ, T, hε, _, hκ, _, hbound⟩ :=
    exists_norm_fiveTermWordKernel_lower bs hbs hτ₀ ℓ p m w y x hRate
  exact ⟨C, κ, T, hκ, eventually_tail_bound_of_uniform hε
    (fun τ t => fiveTermWordKernel bs ℓ p w y τ m ((x : ℂ) + t * I))
    (fun t => t ≤ -T) (fun t => C * Real.exp (κ * t)) hbound⟩

/-! ### Whole vertical lines -/

/-- Continuity, measurability, and both eventual tail bounds used by
`tendsto_integral_fiveTermWordKernel`. -/
private lemma fiveTermWordKernel_convergence_data
    (bs : List ℤ) (hbs : bs ≠ []) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p m : ℤ) (w y x : ℝ)
    (hx : IsRegularPeriodLatticeCrossing τ₀ y x)
    (hupper : 0 < fiveTermUpperRate (letterWord bs) ℓ w τ₀)
    (hlower : fiveTermLowerRate (letterWord bs) ℓ p w y τ₀ < 0) :
    (∀ t, ContinuousAt (fun q : ℝ × ℂ =>
      fiveTermWordKernel bs ℓ p w y q.2 m ((x : ℂ) + q.1 * I)) (t, (τ₀ : ℂ))) ∧
    (∀ᶠ τ in 𝓝[{q : ℂ | 0 < q.im}] (τ₀ : ℂ),
      AEStronglyMeasurable (fun t : ℝ =>
        fiveTermWordKernel bs ℓ p w y τ m ((x : ℂ) + t * I))) ∧
    (∃ C κ T : ℝ, 0 < κ ∧
      ∀ᶠ τ in 𝓝[{q : ℂ | 0 < q.im}] (τ₀ : ℂ), ∀ t : ℝ, T ≤ t →
        ‖fiveTermWordKernel bs ℓ p w y τ m ((x : ℂ) + t * I)‖ ≤
          C * Real.exp (-κ * t)) ∧
    (∃ C κ T : ℝ, 0 < κ ∧
      ∀ᶠ τ in 𝓝[{q : ℂ | 0 < q.im}] (τ₀ : ℂ), ∀ t : ℝ, t ≤ -T →
        ‖fiveTermWordKernel bs ℓ p w y τ m ((x : ℂ) + t * I)‖ ≤
          C * Real.exp (κ * t)) := by
  exact ⟨(fun t => continuousAt_fiveTermWordKernel_vertical bs hτ₀ ℓ p m w y x t hx),
    eventually_aestronglyMeasurable_fiveTermWordKernel bs hbs ℓ p m w y x,
    exists_eventually_upperTail_fiveTermWordKernel bs hτ₀ ℓ p m w y x hupper,
    exists_eventually_lowerTail_fiveTermWordKernel bs hbs hτ₀ ℓ p m w y x hlower⟩

/-- The integral of the five-term kernel of a nonempty letter word along a regular vertical line
converges to its value at a real period with positive word periods as the period approaches it
through the upper half-plane, under the strict convergence conditions at `τ₀`; used by
`tendsto_integral_fiveTermKernelUHP_letterWord_bare`. -/
private theorem tendsto_integral_fiveTermWordKernel (bs : List ℤ) (hbs : bs ≠ []) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p m : ℤ) (w y x : ℝ)
    (hx : IsRegularPeriodLatticeCrossing τ₀ y x)
    (hupper : 0 < fiveTermUpperRate (letterWord bs) ℓ w τ₀)
    (hlower : fiveTermLowerRate (letterWord bs) ℓ p w y τ₀ < 0) :
    Tendsto (fun τ : ℂ => ∫ t : ℝ, fiveTermWordKernel bs ℓ p w y τ m ((x : ℂ) + t * I))
      (𝓝[{q : ℂ | 0 < q.im}] (τ₀ : ℂ))
      (𝓝 (∫ t : ℝ, fiveTermWordKernel bs ℓ p w y τ₀ m ((x : ℂ) + t * I))) := by
  obtain ⟨hcont, hmeas, hu, hl⟩ :=
    fiveTermWordKernel_convergence_data bs hbs hτ₀ ℓ p m w y x hx hupper hlower
  exact tendsto_integral_of_exp_tails nhdsWithin_le_nhds hcont hmeas hu hl

/-- Almost-everywhere comparison transfers the word-kernel limit to the bare modular
kernel integral, for `tendsto_integral_fiveTermKernelUHP_letterWord`. -/
private lemma tendsto_integral_fiveTermKernelUHP_letterWord_bare
    (bs : List ℤ) (hbs : bs ≠ []) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p m : ℤ) (w y x : ℝ)
    (hx : IsRegularPeriodLatticeCrossing τ₀ y x)
    (hupper : 0 < fiveTermUpperRate (letterWord bs) ℓ w τ₀)
    (hlower : fiveTermLowerRate (letterWord bs) ℓ p w y τ₀ < 0) :
    Tendsto (fun τ : ℂ => ∫ t : ℝ,
        fiveTermKernelUHP (letterWord bs) ℓ p w y τ m ((x : ℂ) + t * I))
      (𝓝[{q : ℂ | 0 < q.im}] (τ₀ : ℂ))
      (𝓝 (∫ t : ℝ, fiveTermWordKernel bs ℓ p w y τ₀ m ((x : ℂ) + t * I))) := by
  have heq : (fun τ : ℂ => ∫ t : ℝ,
      fiveTermKernelUHP (letterWord bs) ℓ p w y τ m ((x : ℂ) + t * I)) =ᶠ[
      𝓝[{q : ℂ | 0 < q.im}] (τ₀ : ℂ)] (fun τ : ℂ => ∫ t : ℝ,
        fiveTermWordKernel bs ℓ p w y τ m ((x : ℂ) + t * I)) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    apply integral_congr_ae
    change ∀ᵐ t : ℝ,
      fiveTermKernelUHP (letterWord bs) ℓ p w y τ m ((x : ℂ) + t * I) =
        fiveTermWordKernel bs ℓ p w y τ m ((x : ℂ) + t * I)
    simpa only [mul_comm, add_comm] using
      (ae_fiveTermKernelUHP_eq_fiveTermWordKernel bs hbs ℓ p m w y τ I x hτ I_ne_zero)
  exact (tendsto_integral_fiveTermWordKernel
    bs hbs hτ₀ ℓ p m w y x hx hupper hlower).congr' heq.symm

/-- The integral of the upper-half-plane five-term kernel of a nonempty letter word along a
regular vertical line converges to the word kernel's integral at a real period with positive
word periods, under the strict convergence conditions at `τ₀`; used by
`tendsto_fiveTermIntegralSumUHP_letterWord`. -/
private theorem tendsto_integral_fiveTermKernelUHP_letterWord (bs : List ℤ) (hbs : bs ≠ []) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p m : ℤ) (w y x : ℝ)
    (hx : IsRegularPeriodLatticeCrossing τ₀ y x)
    (hupper : 0 < fiveTermUpperRate (letterWord bs) ℓ w τ₀)
    (hlower : fiveTermLowerRate (letterWord bs) ℓ p w y τ₀ < 0) :
    Tendsto (fun τ : ℂ => ∫ t : ℝ,
        fiveTermKernelUHP (letterWord bs) ℓ p w y τ m ((x : ℂ) + t * I) * I)
      (𝓝[{q : ℂ | 0 < q.im}] (τ₀ : ℂ))
      (𝓝 (∫ t : ℝ, fiveTermWordKernel bs ℓ p w y τ₀ m ((x : ℂ) + t * I) * I)) := by
  simpa only [integral_mul_const] using
    (tendsto_integral_fiveTermKernelUHP_letterWord_bare
      bs hbs hτ₀ ℓ p m w y x hx hupper hlower).mul_const I

/-! ### The finite contour sum -/

/-- The named finite sum of upper-half-plane straight-contour integrals of a nonempty letter
word converges to the word contour sum at a real period with positive word periods, on regular
crossings and under the strict convergence conditions at `τ₀`. -/
theorem tendsto_fiveTermIntegralSumUHP_letterWord (bs : List ℤ) (hbs : bs ≠ []) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p : ℤ) (w y : ℝ)
    (x : FiveTermIndex (letterWord bs) → ℝ)
    (hx : ∀ m, IsRegularPeriodLatticeCrossing τ₀ y (x m))
    (hupper : 0 < fiveTermUpperRate (letterWord bs) ℓ w τ₀)
    (hlower : fiveTermLowerRate (letterWord bs) ℓ p w y τ₀ < 0) :
    Tendsto (fun τ : ℂ => fiveTermIntegralSumUHP (letterWord bs) ℓ p y τ x w)
      (𝓝[{q : ℂ | 0 < q.im}] (τ₀ : ℂ))
      (𝓝 (fiveTermWordIntegralSum bs ℓ p w y τ₀ x)) := by
  simpa only [fiveTermIntegralSumUHP_def, fiveTermWordIntegralSum_def] using
    tendsto_finsetSum (Finset.univ : Finset (FiveTermIndex (letterWord bs)))
      (fun m _ => by
        simpa only [integral_mul_const, mul_comm I] using
          tendsto_integral_fiveTermKernelUHP_letterWord
            bs hbs hτ₀ ℓ p ((m : ℕ) : ℤ) w y (x m) (hx m) hupper hlower)

end SIC

end
