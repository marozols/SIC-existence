/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.FiveTerm.Integral
import SICs.SpecialFunctions.Faddeev.FiveTerm.ClosedForm
import SICs.SpecialFunctions.Faddeev.FiveTerm.CrossedPoles
import SICs.SpecialFunctions.Faddeev.FiveTerm.Holomorphy

/-!
# Analytic continuation of the five-term integral

The upper-half-plane five-term integral, corrected by the residues of the right poles to the left
of its contours, equals the continued closed form throughout its convergence strip.

This module follows [RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`,
equation (23), `eq:5term.int`, Appendix A.2, `app:mod.fad`] at `n = h = 0`.

## The argument

The finite sum of upward contour integrals is holomorphic in the open convergence strip.
The raw q-product quotient is meromorphic there. From any point in the strip, translation
in the direction `iε`, with `ε = cτ+d`, reaches the residue region while staying in the strip.
At that point the
residue calculation identifies the two functions on a neighborhood. Convexity and the
meromorphic identity theorem propagate equality of their punctured germs throughout the
strip. The integral sum is analytic at every target point, so uniqueness of the
meromorphic normal form evaluates the quotient even at removable common zeros.

The parameter `y` remains fixed. The hypothesis `ϖ(pτ+y,τ) ≠ 0` keeps the right poles
simple; continuation at common zeros in `y` is not part of this result.

When finitely many right poles lie to the left of the contours, their residues form a finite
sum entire in `w`. The contour sum minus `2πi` times that sum is again holomorphic on the strip
and equals the closed form near a residue-region point, so the same continuation applies.

Near an irrational real period `τ₀`, fix contours that avoid `ℤ+ℤτ₀` and lie to the right of
the shifted left poles at `τ₀`. For nearby periods they still do, no right pole lies on them,
and the right poles to their left are those at `τ₀`. Each of their residues is the boundary
integral of the kernel over a small square centred at the pole's position at `τ₀`. This form of
the identity has every term defined at `τ₀`, ready for the boundary limit.
-/

noncomputable section

open Complex Real Filter Set MeasureTheory
open scoped Topology MatrixGroups

namespace SIC

/-! ### Holomorphic contour sum and local residue identity

The corrected contour sum is analytic on the convergence strip. The residue calculation
gives an identity on a neighborhood of each point where both residue-series inequalities hold. -/

/-- The contour sum after subtracting the residues of the right poles to its left. -/
private def fiveTermCorrectedIntegralSumUHP
    (γ : SL(2, ℤ)) (ℓ p : ℤ) (y τ : ℂ)
    (x : FiveTermIndex γ → ℝ)
    (F : FiveTermIndex γ → Finset (ℤ × ℕ)) (w : ℂ) : ℂ :=
  fiveTermIntegralSumUHP γ ℓ p y τ x w -
    2 * π * I * fiveTermResidueSumUHP γ ℓ p w y τ F

/-- Holomorphy on the convergence strip of the contour sum over lines to the right of the shifted
left poles that meet no genuine right pole; used by
`differentiableOn_correctedIntegralSum`. -/
private theorem differentiableOn_fiveTermIntegralSumUHP
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (ℓ p : ℤ) (y τ : ℂ)
    (hτ : 0 < τ.im) (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (x : FiveTermIndex γ → ℝ)
    (hxP : ∀ m : FiveTermIndex γ,
      ∀ u ∈ faddeevModularUHPPoles γ (((m : ℕ) : ℤ) + 1) τ, u.re ≠ x m)
    (hxL : ∀ m : FiveTermIndex γ, (-((((m : ℕ) : ℤ) + p : ℤ) : ℝ) *
      (fltDenominator (γ : Mat(2, ℤ)) τ).re - 1) /
      (γ 1 0 : ℝ) - y.re < x m) :
    DifferentiableOn ℂ (fiveTermIntegralSumUHP γ ℓ p y τ x)
      (fiveTermParameterStrip γ ℓ p y τ) := by
  unfold fiveTermIntegralSumUHP
  apply DifferentiableOn.fun_sum
  intro m _
  exact (differentiableOn_integral_fiveTermKernelUHP_of_regular γ hc ℓ p
    ((m : ℕ) : ℤ) y τ hτ he (x m) (hxP m) (hxL m)).const_mul I

/-- Holomorphy on the convergence strip of the contour sum corrected by the finite residues. -/
private theorem differentiableOn_correctedIntegralSum
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (ℓ p : ℤ) (y τ : ℂ)
    (hτ : 0 < τ.im) (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (x : FiveTermIndex γ → ℝ)
    (hxP : ∀ m : FiveTermIndex γ,
      ∀ u ∈ faddeevModularUHPPoles γ (((m : ℕ) : ℤ) + 1) τ, u.re ≠ x m)
    (hxL : ∀ m : FiveTermIndex γ, (-((((m : ℕ) : ℤ) + p : ℤ) : ℝ) *
      (fltDenominator (γ : Mat(2, ℤ)) τ).re - 1) /
      (γ 1 0 : ℝ) - y.re < x m)
    (F : FiveTermIndex γ → Finset (ℤ × ℕ)) :
    DifferentiableOn ℂ (fiveTermCorrectedIntegralSumUHP γ ℓ p y τ x F)
      (fiveTermParameterStrip γ ℓ p y τ) := by
  change DifferentiableOn ℂ (fun w => fiveTermIntegralSumUHP γ ℓ p y τ x w -
    2 * π * I * fiveTermResidueSumUHP γ ℓ p w y τ F) _
  exact (differentiableOn_fiveTermIntegralSumUHP γ hc ℓ p y τ hτ he x hxP hxL).sub
    ((differentiable_fiveTermResidueSumUHP γ ℓ p y τ F).differentiableOn.const_mul _)

/-- Near a residue-region point, the raw closed form equals the corrected contour sum. -/
private theorem closedForm_eventuallyEq_correctedIntegralSum
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (ℓ p : ℤ) (v y τ : ℂ)
    (hτ : 0 < τ.im) (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (hvStrip : v ∈ fiveTermParameterStrip γ ℓ p y τ)
    (hu : 0 < ((ℓ : ℂ) * τ + v).im)
    (hv : 0 < ((y + v) / fltDenominator (γ : Mat(2, ℤ)) τ).im)
    (ha : qPochhammer ((p : ℂ) * τ + y) τ ≠ 0)
    (x : FiveTermIndex γ → ℝ)
    (hxP : ∀ m : FiveTermIndex γ,
      ∀ u ∈ faddeevModularUHPPoles γ (((m : ℕ) : ℤ) + 1) τ, u.re ≠ x m)
    (hxL : ∀ m : FiveTermIndex γ, (-((((m : ℕ) : ℤ) + p : ℤ) : ℝ) *
      (fltDenominator (γ : Mat(2, ℤ)) τ).re - 1) /
      (γ 1 0 : ℝ) - y.re < x m)
    (F : FiveTermIndex γ → Finset (ℤ × ℕ))
    (hF : ∀ (m : FiveTermIndex γ) (kj : ℤ × ℕ), kj ∈ F m ↔
      0 ≤ faddeevModularUHPIndex γ ((m : ℕ) : ℤ) kj.1 kj.2 ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).re < x m) :
    fiveTermClosedFormUHP γ ℓ p y τ =ᶠ[𝓝 v]
      fiveTermCorrectedIntegralSumUHP γ ℓ p y τ x F := by
  have hOpenU := isOpen_fiveTermParameterStrip γ ℓ p y τ
  have hOpenu : IsOpen {z : ℂ | 0 < ((ℓ : ℂ) * τ + z).im} :=
    isOpen_lt (by fun_prop) (by fun_prop)
  have hOpenv : IsOpen {z : ℂ |
      0 < ((y + z) / fltDenominator (γ : Mat(2, ℤ)) τ).im} :=
    isOpen_lt (by fun_prop) (by fun_prop)
  filter_upwards [hOpenU.mem_nhds hvStrip, hOpenu.mem_nhds hu,
    hOpenv.mem_nhds hv] with z hzStrip hzu hzv
  obtain ⟨hLam, hMu⟩ := (mem_fiveTermParameterStrip γ ℓ p y τ z).mp hzStrip
  have hres : fiveTermIntegralSumUHP γ ℓ p y τ x z =
      fiveTermClosedFormUHP γ ℓ p y τ z +
        2 * π * I * fiveTermResidueSumUHP γ ℓ p z y τ F := by
    simpa only [fiveTermIntegralSumUHP_def, fiveTermClosedFormUHP] using
      sum_integral_fiveTermKernelUHP_of_im_pos_of_crossed γ hc ℓ p z y τ
        hτ he hLam hMu hzu hzv ha x hxP hxL F hF
  change fiveTermClosedFormUHP γ ℓ p y τ z =
    fiveTermIntegralSumUHP γ ℓ p y τ x z -
      2 * π * I * fiveTermResidueSumUHP γ ℓ p z y τ F
  rw [hres]
  ring

/-! ### Continuation across the strip

The meromorphic germ of the raw quotient agrees with the corrected analytic contour sum at
one residue-region point, hence at every point of the convex strip. For contours to the right
of the shifted left poles that meet no right pole, this corrected sum subtracts the finitely many
right-pole residues on their left. The separating case has an empty correction. -/

/-- The upper-half-plane five-term identity at `n=h=0` throughout the convergence strip, for
contours to the right of the shifted left poles that meet no genuine right pole: the finitely
many right poles to the left of the `m`-th contour, indexed by `F m`, contribute
`2πi fiveTermResidueSumUHP`. This is the straight-line form of the contour deformation in
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`, equation (23),
`eq:5term.int`, Appendix A.2, `app:mod.fad`]; in the separating case every `F m` is empty. -/
theorem sum_integral_fiveTermKernelUHP_of_crossed
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (ℓ p : ℤ) (w y τ : ℂ)
    (hτ : 0 < τ.im)
    (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (hLam : 0 < ((((γ 1 0 : ℤ) : ℂ) * w /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ)).re)
    (hMu : ((((γ 1 0 : ℤ) : ℂ) * (w + y) /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1)).re < 0)
    (ha : qPochhammer ((p : ℂ) * τ + y) τ ≠ 0)
    (x : FiveTermIndex γ → ℝ)
    (hxP : ∀ m : FiveTermIndex γ,
      ∀ u ∈ faddeevModularUHPPoles γ (((m : ℕ) : ℤ) + 1) τ, u.re ≠ x m)
    (hxL : ∀ m : FiveTermIndex γ, (-((((m : ℕ) : ℤ) + p : ℤ) : ℝ) *
      (fltDenominator (γ : Mat(2, ℤ)) τ).re - 1) /
      (γ 1 0 : ℝ) - y.re < x m)
    (F : FiveTermIndex γ → Finset (ℤ × ℕ))
    (hF : ∀ (m : FiveTermIndex γ) (kj : ℤ × ℕ), kj ∈ F m ↔
      0 ≤ faddeevModularUHPIndex γ ((m : ℕ) : ℤ) kj.1 kj.2 ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).re < x m) :
    (∑ m : FiveTermIndex γ, I * (∫ t : ℝ,
      fiveTermKernelUHP γ ℓ p w y τ ((m : ℕ) : ℤ) ((x m : ℂ) + t * I))) =
      fiveTermClosedFormUHPContinued γ ℓ p y τ w +
        2 * π * I * fiveTermResidueSumUHP γ ℓ p w y τ F := by
  let U := fiveTermParameterStrip γ ℓ p y τ
  have hw : w ∈ U := (mem_fiveTermParameterStrip γ ℓ p y τ w).mpr ⟨hLam, hMu⟩
  obtain ⟨v, hvU, hu, hv⟩ :=
    exists_mem_fiveTermParameterStrip_im_pos γ ℓ p y τ w he hw
  have hL : DifferentiableOn ℂ
      (fiveTermCorrectedIntegralSumUHP γ ℓ p y τ x F) U :=
    differentiableOn_correctedIntegralSum γ hc ℓ p y τ
      hτ he x hxP hxL F
  have hR : MeromorphicOn (fiveTermClosedFormUHP γ ℓ p y τ) U :=
    (meromorphic_fiveTermClosedFormUHP γ ℓ p y τ hτ).meromorphicOn
  have hlocal : fiveTermClosedFormUHP γ ℓ p y τ =ᶠ[𝓝[≠] v]
      fiveTermCorrectedIntegralSumUHP γ ℓ p y τ x F :=
    (closedForm_eventuallyEq_correctedIntegralSum γ hc ℓ p v y τ
      hτ he hvU hu hv ha x hxP hxL F hF).filter_mono nhdsWithin_le_nhds
  have hgerm := SIC.MeromorphicOn.eventuallyEq_nhdsNE_of_isPreconnected hR
    (hL.analyticOnNhd (isOpen_fiveTermParameterStrip γ ℓ p y τ)).meromorphicOn
    (convex_fiveTermParameterStrip γ ℓ p y τ).isPreconnected hvU hw hlocal
  have hvalue := fiveTermClosedFormUHPContinued_eq_of_nhdsNE
    γ ℓ p y τ w (hL.analyticAt
      ((isOpen_fiveTermParameterStrip γ ℓ p y τ).mem_nhds hw)) hgerm
  rw [hvalue, fiveTermCorrectedIntegralSumUHP, fiveTermIntegralSumUHP_def]
  ring

/-! ### Crossed right poles near a real period

Near an irrational real period, the contours and the crossed right poles at `τ₀` serve all
nearby periods, and each crossed residue is a square boundary integral. -/

/-- The crossed right poles stay strictly off every contour and keep their side of it near the
real period; used by `eventually_fiveTermIntegralSumUHP_eq_add`. -/
private theorem eventually_fiveTerm_crossedPolesStable
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (τ₀ : ℝ)
    (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ)).re)
    (x : FiveTermIndex γ → ℝ)
    (hxP : ∀ m : FiveTermIndex γ, ¬ IsPeriodLatticePoint τ₀ (x m : ℂ)) :
    ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ),
      ∀ m : FiveTermIndex γ, ∀ kj : ℤ × ℕ,
        0 ≤ faddeevModularUHPIndex γ ((m : ℕ) : ℤ) kj.1 kj.2 →
          (faddeevModularUHPPole γ τ kj.1 kj.2).re ≠ x m ∧
            ((faddeevModularUHPPole γ τ kj.1 kj.2).re < x m ↔
              (faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2).re < x m) := by
  have hε : fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ) ≠ 0 :=
    Complex.ne_zero_of_re_pos he
  have hx (m : FiveTermIndex γ) (kj : ℤ × ℕ) :
      (faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2).re ≠ x m :=
    re_faddeevModularUHPPole_ofReal_ne γ τ₀ hε (x m) (hxP m) kj.1 kj.2
  apply Filter.eventually_all.mpr
  intro m
  exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
    (eventually_fiveTermPoles_re_lt_iff γ hc ((m : ℕ) : ℤ) (τ₀ : ℂ)
      he (x m) (fun kj _ => hx m kj))

/-- The strip, contour bounds, and crossed-pole data persist together near the real period;
used by `eventually_fiveTermIntegralSumUHP_eq_add`. -/
private theorem eventually_fiveTerm_crossedConditions
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (ℓ p : ℤ) (w : ℂ) (y τ₀ : ℝ)
    (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ)).re)
    (hw : w ∈ fiveTermParameterStrip γ ℓ p y τ₀)
    (x : FiveTermIndex γ → ℝ)
    (hxP : ∀ m : FiveTermIndex γ, ¬ IsPeriodLatticePoint τ₀ (x m : ℂ))
    (hxL : ∀ m : FiveTermIndex γ, (-((((m : ℕ) : ℤ) + p : ℤ) : ℝ) *
      (fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ)).re - 1) / (γ 1 0 : ℝ) - y < x m) :
    ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ),
      0 < τ.im ∧ 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re ∧
        w ∈ fiveTermParameterStrip γ ℓ p y τ ∧
        (∀ m : FiveTermIndex γ, (-((((m : ℕ) : ℤ) + p : ℤ) : ℝ) *
          (fltDenominator (γ : Mat(2, ℤ)) τ).re - 1) /
          (γ 1 0 : ℝ) - (y : ℂ).re < x m) ∧
        (∀ m : FiveTermIndex γ, ∀ kj : ℤ × ℕ,
          0 ≤ faddeevModularUHPIndex γ ((m : ℕ) : ℤ) kj.1 kj.2 →
            (faddeevModularUHPPole γ τ kj.1 kj.2).re ≠ x m ∧
              ((faddeevModularUHPPole γ τ kj.1 kj.2).re < x m ↔
                (faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2).re < x m)) := by
  have hε : fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ) ≠ 0 :=
    Complex.ne_zero_of_re_pos he
  have hDen : ∀ᶠ τ : ℂ in 𝓝 (τ₀ : ℂ),
      0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re :=
    ((Complex.continuous_re.continuousAt.tendsto.comp
      (fltDenominator_tendsto (γ : Mat(2, ℤ)) tendsto_id)).eventually_const_lt he)
  have hBounds : ∀ᶠ τ : ℂ in 𝓝 (τ₀ : ℂ),
      ∀ m : FiveTermIndex γ, (-((((m : ℕ) : ℤ) + p : ℤ) : ℝ) *
        (fltDenominator (γ : Mat(2, ℤ)) τ).re - 1) /
        (γ 1 0 : ℝ) - (y : ℂ).re < x m := by
    apply Filter.eventually_all.mpr
    intro m
    exact eventually_fiveTerm_leftBound_lt γ ((m : ℕ) : ℤ) p
      (y : ℂ) (τ₀ : ℂ) (x m) (by simpa using hxL m)
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hDen,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_mem_fiveTermParameterStrip γ ℓ p y w τ₀ hε hw),
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hBounds,
    eventually_fiveTerm_crossedPolesStable γ hc τ₀ he x hxP]
    with τ hτ hDen hStrip hBounds hPoles
  exact ⟨hτ, hDen, hStrip, hBounds, hPoles⟩

/-- The finitely many crossed residues have simultaneous square-integral expressions; used by
`eventually_fiveTermIntegralSumUHP_eq_add`. -/
private theorem eventually_fiveTerm_squareResidueTerms
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (ℓ p : ℤ) (w : ℂ) (y τ₀ : ℝ)
    (hτ₀ : Irrational τ₀) (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ)).re)
    (hy : ¬ IsPeriodLatticePoint τ₀ (y : ℂ))
    (F : FiveTermIndex γ → Finset (ℤ × ℕ))
    (hN : ∀ (m : FiveTermIndex γ) (kj : ℤ × ℕ), kj ∈ F m →
      0 ≤ faddeevModularUHPIndex γ ((m : ℕ) : ℤ) kj.1 kj.2) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ),
      ∀ m : FiveTermIndex γ, ∀ kj ∈ F m,
        rectBoundaryIntegral (fiveTermKernelUHP γ ℓ p w y τ ((m : ℕ) : ℤ))
            (faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2 - (r + r * I))
            (faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2 + (r + r * I)) =
          2 * π * I * fiveTermResidueUHP γ ℓ p w y τ
            (faddeevModularUHPIndex γ ((m : ℕ) : ℤ) kj.1 kj.2) kj.2 := by
  have hEach (m : FiveTermIndex γ) (kj : ℤ × ℕ) (hkj : kj ∈ F m) :=
    eventually_rectBoundaryIntegral_fiveTermKernelUHP γ hc ℓ p
      ((m : ℕ) : ℤ) w y τ₀ hτ₀ he hy kj.1 kj.2 (hN m kj hkj)
  have hr : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ m : FiveTermIndex γ, ∀ kj ∈ F m,
      ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ),
        rectBoundaryIntegral (fiveTermKernelUHP γ ℓ p w y τ ((m : ℕ) : ℤ))
            (faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2 - (r + r * I))
            (faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2 + (r + r * I)) =
          2 * π * I * fiveTermResidueUHP γ ℓ p w y τ
            (faddeevModularUHPIndex γ ((m : ℕ) : ℤ) kj.1 kj.2) kj.2 := by
    apply Filter.eventually_all.mpr
    intro m
    apply (Finset.eventually_all (F m)).mpr
    exact hEach m
  filter_upwards [hr] with r hr
  apply Filter.eventually_all.mpr
  intro m
  apply (Finset.eventually_all (F m)).mpr
  exact hr m

/-- Replaces the residue correction by its termwise square integrals; used by
`eventually_fiveTermIntegralSumUHP_eq_add`. -/
private theorem fiveTermResidueSumUHP_eq_squareSum
    (γ : SL(2, ℤ)) (ℓ p : ℤ) (w : ℂ) (y τ₀ : ℝ) (τ : ℂ) (r : ℝ)
    (F : FiveTermIndex γ → Finset (ℤ × ℕ))
    (hSquares : ∀ m : FiveTermIndex γ, ∀ kj ∈ F m,
      rectBoundaryIntegral (fiveTermKernelUHP γ ℓ p w y τ ((m : ℕ) : ℤ))
          (faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2 - (r + r * I))
          (faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2 + (r + r * I)) =
        2 * π * I * fiveTermResidueUHP γ ℓ p w y τ
          (faddeevModularUHPIndex γ ((m : ℕ) : ℤ) kj.1 kj.2) kj.2) :
    2 * π * I * fiveTermResidueSumUHP γ ℓ p w y τ F =
      ∑ m : FiveTermIndex γ, ∑ kj ∈ F m,
        rectBoundaryIntegral (fiveTermKernelUHP γ ℓ p w y τ ((m : ℕ) : ℤ))
          (faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2 - (r + r * I))
          (faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2 + (r + r * I)) := by
  unfold fiveTermResidueSumUHP
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro kj hkj
  exact (hSquares m kj hkj).symm

/-- The fixed finite sets still index exactly the crossed poles at a nearby period; used by
`eventually_fiveTermIntegralSumUHP_eq_add`. -/
private theorem fiveTerm_crossedPoleIndexSets
    (γ : SL(2, ℤ)) (τ₀ : ℝ) (τ : ℂ) (x : FiveTermIndex γ → ℝ)
    (F : FiveTermIndex γ → Finset (ℤ × ℕ))
    (hF : ∀ (m : FiveTermIndex γ) (kj : ℤ × ℕ), kj ∈ F m ↔
      0 ≤ faddeevModularUHPIndex γ ((m : ℕ) : ℤ) kj.1 kj.2 ∧
        (faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2).re < x m)
    (hStable : ∀ m : FiveTermIndex γ, ∀ kj : ℤ × ℕ,
      0 ≤ faddeevModularUHPIndex γ ((m : ℕ) : ℤ) kj.1 kj.2 →
        ((faddeevModularUHPPole γ τ kj.1 kj.2).re < x m ↔
          (faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2).re < x m)) :
    ∀ (m : FiveTermIndex γ) (kj : ℤ × ℕ), kj ∈ F m ↔
      0 ≤ faddeevModularUHPIndex γ ((m : ℕ) : ℤ) kj.1 kj.2 ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).re < x m := by
  intro m kj
  constructor
  · intro hkj
    obtain ⟨hN, hlt⟩ := (hF m kj).mp hkj
    exact ⟨hN, (hStable m kj hN).mpr hlt⟩
  · rintro ⟨hN, hlt⟩
    exact (hF m kj).mpr ⟨hN, (hStable m kj hN).mp hlt⟩

/-- Near an irrational real period `τ₀` with `j_γ(τ₀) > 0` and `y` outside `ℤ+ℤτ₀`, the
upper-half-plane five-term identity at `n=h=0` holds on straight contours whose crossings avoid
`ℤ+ℤτ₀` and lie to the right of the shifted left poles at `τ₀`, with the residue of each right
pole to the left of the `m`-th contour at `τ₀`, indexed by `F m`, written as the boundary
integral of the kernel over the square of half-side `r` centred at the pole's position at `τ₀`;
this holds for all small `r` and all periods in the upper half plane near `τ₀`. It carries
`sum_integral_fiveTermKernelUHP_of_crossed` to the boundary by
`eventually_fiveTermPoles_re_lt_iff` and
`eventually_rectBoundaryIntegral_fiveTermKernelUHP`. -/
theorem eventually_fiveTermIntegralSumUHP_eq_add
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (ℓ p : ℤ) (w : ℂ) (y τ₀ : ℝ)
    (hτ₀ : Irrational τ₀) (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ)).re)
    (hy : ¬ IsPeriodLatticePoint τ₀ (y : ℂ))
    (hw : w ∈ fiveTermParameterStrip γ ℓ p y τ₀)
    (x : FiveTermIndex γ → ℝ)
    (hxP : ∀ m : FiveTermIndex γ, ¬ IsPeriodLatticePoint τ₀ (x m : ℂ))
    (hxL : ∀ m : FiveTermIndex γ, (-((((m : ℕ) : ℤ) + p : ℤ) : ℝ) *
      (fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ)).re - 1) / (γ 1 0 : ℝ) - y < x m)
    (F : FiveTermIndex γ → Finset (ℤ × ℕ))
    (hF : ∀ (m : FiveTermIndex γ) (kj : ℤ × ℕ), kj ∈ F m ↔
      0 ≤ faddeevModularUHPIndex γ ((m : ℕ) : ℤ) kj.1 kj.2 ∧
        (faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2).re < x m) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ),
      fiveTermIntegralSumUHP γ ℓ p y τ x w =
        fiveTermClosedFormUHPContinued γ ℓ p y τ w +
          ∑ m : FiveTermIndex γ, ∑ kj ∈ F m,
            rectBoundaryIntegral (fiveTermKernelUHP γ ℓ p w y τ ((m : ℕ) : ℤ))
              (faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2 - (r + r * I))
              (faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2 + (r + r * I)) := by
  have hConditions := eventually_fiveTerm_crossedConditions γ hc ℓ p w y τ₀
    he hw x hxP hxL
  have hSquares := eventually_fiveTerm_squareResidueTerms γ hc ℓ p w y τ₀
    hτ₀ he hy F (fun m kj hkj => ((hF m kj).mp hkj).1)
  filter_upwards [hSquares] with r hSquares
  filter_upwards [hConditions, hSquares] with τ hData hSquares
  obtain ⟨hτ, heτ, hStrip, hxLτ, hStable⟩ := hData
  obtain ⟨hLam, hMu⟩ :=
    (mem_fiveTermParameterStrip γ ℓ p y τ w).mp hStrip
  have ha := qPochhammer_intCast_mul_add_ofReal_ne_zero τ hτ p y
    ((sigmaSLatticeFree_iff_not_isPeriodLatticePoint τ₀ y).mpr hy).ne_intCast
  have hxPτ (m : FiveTermIndex γ) :
      ∀ u ∈ faddeevModularUHPPoles γ (((m : ℕ) : ℤ) + 1) τ, u.re ≠ x m := by
    intro u hu
    obtain ⟨k, j, rfl, hN⟩ :=
      (mem_faddeevModularUHPPoles_iff γ ((m : ℕ) : ℤ) hτ).mp hu
    exact (hStable m (k, j) hN).1
  have hFτ : ∀ (m : FiveTermIndex γ) (kj : ℤ × ℕ), kj ∈ F m ↔
      0 ≤ faddeevModularUHPIndex γ ((m : ℕ) : ℤ) kj.1 kj.2 ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).re < x m :=
    fiveTerm_crossedPoleIndexSets γ τ₀ τ x F hF
      (fun m kj hN => (hStable m kj hN).2)
  have hIdentity := sum_integral_fiveTermKernelUHP_of_crossed γ hc ℓ p w y τ
    hτ heτ hLam hMu ha x hxPτ hxLτ F hFτ
  rw [fiveTermIntegralSumUHP_def]
  rw [← fiveTermResidueSumUHP_eq_squareSum γ ℓ p w y τ₀ τ r F hSquares]
  exact hIdentity

end SIC
