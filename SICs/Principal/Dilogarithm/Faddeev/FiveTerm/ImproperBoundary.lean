/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.ImproperConvergence
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ComplexBounds

/-!
# Principal five-term improper contours at the real boundary

The whole vertical contour integral of the complex-period principal five-term kernel converges to
the real-period integral as the period approaches the principal root through the upper half-plane.

This module formalizes the boundary passage in [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`] for the principal matrix `A_d=U_d^3`. It complements the finite-interval passage in
`SICs.Principal.Dilogarithm.Faddeev.FiveTerm.Boundary`.

## The argument

At each upper-half-plane period, the q-product kernel and the three-generator kernel agree almost
everywhere on the vertical line. The latter is jointly continuous in the contour height and period
at the principal real period. Uniform exponential estimates on both vertical tails, together with
compact control of the middle, give one integrable majorant. Dominated convergence then passes the
whole real integral to the boundary. Almost-everywhere equality transfers both integrability and
the integral limit back to the q-product kernel, and continuity of finite sums gives the contour-sum
limit.
-/

noncomputable section

open Complex Filter Topology MeasureTheory

namespace SIC

/-! ### Measurability and uniform tails -/

/-- Near the principal root through the upper half-plane, the complex generator kernels are
eventually almost everywhere strongly measurable. -/
private lemma eventually_aestronglyMeasurable_kernelComplex
    (d : ℕ) (ℓ p m : ℤ) (w y x : ℝ) :
    ∀ᶠ τ in 𝓝[{q : ℂ | 0 < q.im}] (principalRoot d : ℂ),
      AEStronglyMeasurable (fun t : ℝ =>
        principalFiveTermKernelComplex d ℓ p w y τ m ((x : ℂ) + t * I)) := by
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact aestronglyMeasurable_principalFiveTermKernelComplex
    d ℓ p m w y x τ hτ

/-- The uniform upper-tail estimate for the complex generator kernel, expressed in the
existential eventual form used by improper dominated convergence. -/
private lemma exists_eventually_upperTail_kernelComplex
    (d : ℕ) (hd : 3 < d) (ℓ p m : ℤ) (w y x : ℝ)
    (hRate : 0 < principalFiveTermUpperRate d ℓ w) :
    ∃ C κ T : ℝ, 0 < κ ∧
      ∀ᶠ τ in 𝓝[{q : ℂ | 0 < q.im}] (principalRoot d : ℂ), ∀ t : ℝ, T ≤ t →
        ‖principalFiveTermKernelComplex d ℓ p w y τ m ((x : ℂ) + t * I)‖ ≤
          C * Real.exp (-κ * t) := by
  obtain ⟨ε, C, κ, T, hε, _, hκ, _, hbound⟩ :=
    exists_norm_principalFiveTermKernelComplex_upper
      d hd ℓ p m w y x hRate
  exact ⟨C, κ, T, hκ, eventually_tail_bound_of_uniform hε
    (fun τ t =>
      principalFiveTermKernelComplex d ℓ p w y τ m ((x : ℂ) + t * I))
    (fun t => T ≤ t) (fun t => C * Real.exp (-κ * t)) hbound⟩

/-- The uniform lower-tail estimate for the complex generator kernel, expressed in the
existential eventual form used by improper dominated convergence. -/
private lemma exists_eventually_lowerTail_kernelComplex
    (d : ℕ) (hd : 3 < d) (ℓ p m : ℤ) (w y x : ℝ)
    (hRate : principalFiveTermLowerRate d ℓ p w y < 0) :
    ∃ C κ T : ℝ, 0 < κ ∧
      ∀ᶠ τ in 𝓝[{q : ℂ | 0 < q.im}] (principalRoot d : ℂ), ∀ t : ℝ, t ≤ -T →
        ‖principalFiveTermKernelComplex d ℓ p w y τ m ((x : ℂ) + t * I)‖ ≤
          C * Real.exp (κ * t) := by
  obtain ⟨ε, C, κ, T, hε, _, hκ, _, hbound⟩ :=
    exists_norm_principalFiveTermKernelComplex_lower
      d hd ℓ p m w y x hRate
  exact ⟨C, κ, T, hκ, eventually_tail_bound_of_uniform hε
    (fun τ t =>
      principalFiveTermKernelComplex d ℓ p w y τ m ((x : ℂ) + t * I))
    (fun t => t ≤ -T) (fun t => C * Real.exp (κ * t)) hbound⟩

/-! ### Improper integral limits -/

/-- The whole vertical-line integral of the complex generator kernel converges to its real-period
counterpart under the two strict decay inequalities. Specializes
`tendsto_integral_of_exp_tails`. -/
theorem tendsto_integral_principalFiveTermKernelComplex
    (d : ℕ) (hd : 3 < d) (ℓ p m : ℤ) (w y x : ℝ)
    (hx : ¬ IsPeriodLatticePoint (principalRoot d) (x : ℂ))
    (hxy : ¬ IsPeriodLatticePoint (principalRoot d) ((x : ℂ) + y))
    (hupper : 0 < principalFiveTermUpperRate d ℓ w)
    (hlower : principalFiveTermLowerRate d ℓ p w y < 0) :
    Tendsto
      (fun τ : ℂ => ∫ t : ℝ,
        principalFiveTermKernelComplex d ℓ p w y τ m ((x : ℂ) + t * I))
      (𝓝[{q : ℂ | 0 < q.im}] (principalRoot d : ℂ))
      (𝓝 (∫ t : ℝ,
        principalFiveTermKernel d ℓ p w y m ((x : ℂ) + t * I))) := by
  have hlim := tendsto_integral_of_exp_tails
    nhdsWithin_le_nhds
    (fun t => continuousAt_principalFiveTermKernelComplex_vertical
      d hd ℓ p m w y x t hx hxy)
    (eventually_aestronglyMeasurable_kernelComplex
      d ℓ p m w y x)
    (exists_eventually_upperTail_kernelComplex
      d hd ℓ p m w y x hupper)
    (exists_eventually_lowerTail_kernelComplex
      d hd ℓ p m w y x hlower)
  simpa only [principalFiveTermKernelComplex_principalRoot d hd ℓ p m w y]
    using hlim

/-- The bare upper-half-plane q-product integral converges to the real-period generator integral;
this helper transfers the complex-generator limit through their almost-everywhere equality. -/
private theorem tendsto_integral_kernelUHP_bare
    (d : ℕ) (hd : 3 < d) (ℓ p m : ℤ) (w y x : ℝ)
    (hx : ¬ IsPeriodLatticePoint (principalRoot d) (x : ℂ))
    (hxy : ¬ IsPeriodLatticePoint (principalRoot d) ((x : ℂ) + y))
    (hupper : 0 < principalFiveTermUpperRate d ℓ w)
    (hlower : principalFiveTermLowerRate d ℓ p w y < 0) :
    Tendsto
      (fun τ : ℂ => ∫ t : ℝ,
        fiveTermKernelUHP (principalA d) ℓ p w y τ m ((x : ℂ) + t * I))
      (𝓝[{q : ℂ | 0 < q.im}] (principalRoot d : ℂ))
      (𝓝 (∫ t : ℝ,
        principalFiveTermKernel d ℓ p w y m ((x : ℂ) + t * I))) := by
  have heq : (fun τ : ℂ => ∫ t : ℝ,
      fiveTermKernelUHP (principalA d) ℓ p w y τ m ((x : ℂ) + t * I)) =ᶠ[
      𝓝[{q : ℂ | 0 < q.im}] (principalRoot d : ℂ)] (fun τ : ℂ => ∫ t : ℝ,
        principalFiveTermKernelComplex d ℓ p w y τ m ((x : ℂ) + t * I)) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact integral_congr_ae
      (ae_kernelUHP_principalA_vertical
        d ℓ p m w y x τ hτ)
  exact (tendsto_integral_principalFiveTermKernelComplex
    d hd ℓ p m w y x hx hxy hupper hlower).congr' heq.symm

/-! ### Finite contour-sum limit -/

/-- The named finite sum of upper-half-plane principal contour integrals converges termwise to
the named real-period sum. Regularity of each crossing supplies both lattice-avoidance conditions
used by the single-integral boundary theorem. -/
theorem tendsto_integralSumUHP_principalA
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ)
    (x : FiveTermIndex (principalA d) → ℝ)
    (hregular : ∀ m, IsRegularPeriodLatticeCrossing (principalRoot d) y (x m))
    (hupper : 0 < principalFiveTermUpperRate d ℓ w)
    (hlower : principalFiveTermLowerRate d ℓ p w y < 0) :
    Tendsto (fun τ : ℂ =>
      fiveTermIntegralSumUHP (principalA d) ℓ p y τ x w)
      (𝓝[{q : ℂ | 0 < q.im}] (principalRoot d : ℂ))
      (𝓝 (principalFiveTermIntegralSum d ℓ p w y x)) := by
  simpa only [fiveTermIntegralSumUHP_def,
    principalFiveTermIntegralSum_def] using tendsto_finsetSum
    (Finset.univ : Finset (FiveTermIndex (principalA d))) (fun m _ =>
      (tendsto_integral_kernelUHP_bare
        d hd ℓ p ((m : ℕ) : ℤ) w y (x m) (hregular m).base
          (hregular m).shifted hupper hlower).const_mul I)

end SIC
