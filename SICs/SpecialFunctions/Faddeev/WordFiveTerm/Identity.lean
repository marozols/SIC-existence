/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.FiveTerm.Continuation
import SICs.SpecialFunctions.Faddeev.WordFiveTerm.Improper

/-!
# The five-term integral identity of a letter word at a real period

The crossed-contour five-term identity of a letter word passes from the upper half-plane to a
real period with positive word periods, given a boundary limit of its continued closed form.

This module formalizes the crossed-pole boundary passage for [RW26, Radchenko, Wheeler (2026),
Theorem 3, `thm:5term.mod.fad`, equation (23), `eq:5term.int`, Appendix A.2, `app:mod.fad`] at
`n = h = 0`, for a letter word `γ = ∏_j T^{b_j}S`. The principal word is treated directly in
`SICs.Principal.Dilogarithm.Faddeev.FiveTerm.IntegralIdentity`.

## The argument

Contours to the right of the shifted left poles may still have finitely many right poles on
their left at `τ₀`. Near the irrational period `τ₀` these crossed poles do not change, and the
upper-half-plane identity holds with each of their residues written as the boundary integral of
the kernel over a small square centred at the pole's position at `τ₀`
(`eventually_fiveTermIntegralSumUHP_eq_add`). Every term then has a limit: the contour
integrals by whole-line convergence, the closed form by the supplied limit, and each square
integral by uniform convergence on its boundary, which avoids the real lattice when its
vertical sides cross the real axis at regular crossings. Uniqueness of limits gives the
real-period identity. This is the source's deformed contour in straight-line form.

The supplied closed-form limit can be specialized at a fixed point, as in
`SICs.Dilogarithm.FiveTerm.CrossedIdentity`. Away from fixed points, the printed prefactor of
Theorem 3 differs from the exact prefactor at the end of Appendix A.2 by
`exp(πi(γτ - τ)/12)`; the theorem here asserts no particular closed-form evaluation.

The result concerns straight vertical contours deformed around finitely many crossed right
poles.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology MatrixGroups

namespace SIC

/-! ### Boundary passage for crossed right poles -/

/-- The upper-half-plane neighborhood of a real period is nontrivial; used by
`fiveTermWordIntegralSum_eq_of_tendsto`. -/
private theorem neBot_real_upperHalfPlane (τ₀ : ℝ) :
    NeBot (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ)) := by
  have hclosure : (τ₀ : ℂ) ∈ closure {τ : ℂ | 0 < τ.im} := by
    rw [show {τ : ℂ | 0 < τ.im} = Complex.im ⁻¹' Ioi 0 by rfl,
      Complex.closure_preimage_im]
    simp
  exact mem_closure_iff_nhdsWithin_neBot.mp hclosure

/-- The vertical sides of a square around a right pole cross the real axis at period-lattice
translates of `-r` and `r`; used by `tendsto_fiveTermWord_crossed_corrections`. -/
private theorem regular_fiveTerm_square_crossings
    (γ : SL(2, ℤ)) (τ₀ y r : ℝ)
    (hε : fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ) ≠ 0)
    (hneg : IsRegularPeriodLatticeCrossing τ₀ y (-r))
    (hpos : IsRegularPeriodLatticeCrossing τ₀ y r)
    (k : ℤ) (j : ℕ) :
    IsRegularPeriodLatticeCrossing τ₀ y
      (faddeevModularUHPPole γ τ₀ k j - (r + r * I)).re ∧
    IsRegularPeriodLatticeCrossing τ₀ y
      (faddeevModularUHPPole γ τ₀ k j + (r + r * I)).re := by
  let K : ℤ := k * γ 1 0 - (j : ℤ) * γ 0 0
  let L : ℤ := k * γ 1 1 - (j : ℤ) * γ 0 1
  let P := faddeevModularUHPPole γ (τ₀ : ℂ) k j
  have hP : P = (K : ℂ) * (τ₀ : ℂ) + L :=
    faddeevModularUHPPole_eq γ τ₀ hε k j
  have hPre : P.re = (K : ℝ) * τ₀ + L := by
    rw [hP]
    simp
  have hleft : (P - (r + r * I)).re = -r + (K : ℝ) * τ₀ + L := by
    simp [hPre]
    ring
  have hright : (P + (r + r * I)).re = r + (K : ℝ) * τ₀ + L := by
    simp [hPre]
    ring
  change IsRegularPeriodLatticeCrossing τ₀ y (P - (r + r * I)).re ∧
    IsRegularPeriodLatticeCrossing τ₀ y (P + (r + r * I)).re
  rw [hleft, hright]
  exact ⟨IsRegularPeriodLatticeCrossing.add_int_mul_add_int τ₀ y (-r) K L hneg,
    IsRegularPeriodLatticeCrossing.add_int_mul_add_int τ₀ y r K L hpos⟩

/-- The finite sum of square corrections tends to its word-kernel boundary value; used by
`fiveTermWordIntegralSum_eq_of_tendsto`. -/
private theorem tendsto_fiveTermWord_crossed_corrections
    (bs : List ℤ) (hbs : bs ≠ []) {τ₀ : ℝ} (hτ₀ : FaddeevWordPeriodsPos bs τ₀)
    (ℓ p : ℤ) (w y r : ℝ) (hr : 0 < r)
    (hpos : IsRegularPeriodLatticeCrossing τ₀ y r)
    (hneg : IsRegularPeriodLatticeCrossing τ₀ y (-r))
    (F : FiveTermIndex (letterWord bs) → Finset (ℤ × ℕ)) :
    Tendsto (fun τ : ℂ =>
      ∑ m : FiveTermIndex (letterWord bs), ∑ kj ∈ F m,
        rectBoundaryIntegral
          (fiveTermKernelUHP (letterWord bs) ℓ p w y τ ((m : ℕ) : ℤ))
          (faddeevModularUHPPole (letterWord bs) (τ₀ : ℂ) kj.1 kj.2 - (r + r * I))
          (faddeevModularUHPPole (letterWord bs) (τ₀ : ℂ) kj.1 kj.2 + (r + r * I)))
      (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ))
      (𝓝 (∑ m : FiveTermIndex (letterWord bs), ∑ kj ∈ F m,
        rectBoundaryIntegral (fiveTermWordKernel bs ℓ p w y τ₀ ((m : ℕ) : ℤ))
          (faddeevModularUHPPole (letterWord bs) (τ₀ : ℂ) kj.1 kj.2 - (r + r * I))
          (faddeevModularUHPPole (letterWord bs) (τ₀ : ℂ) kj.1 kj.2 +
            (r + r * I)))) := by
  apply tendsto_finsetSum
  intro m _
  apply tendsto_finsetSum
  intro kj _
  let P := faddeevModularUHPPole (letterWord bs) (τ₀ : ℂ) kj.1 kj.2
  have hPim : P.im = 0 :=
    im_faddeevModularUHPPole_ofReal (letterWord bs) τ₀ kj.1 kj.2
  have hleft : (P - (r + r * I)).im ≠ 0 := by
    have heq : (P - (r + r * I)).im = -r := by simp [hPim]
    rw [heq]
    exact neg_ne_zero.mpr (ne_of_gt hr)
  have hright : (P + (r + r * I)).im ≠ 0 := by
    have heq : (P + (r + r * I)).im = r := by simp [hPim]
    rw [heq]
    exact ne_of_gt hr
  have hε : fltDenominator (letterWord bs : Mat(2, ℤ)) (τ₀ : ℂ) ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    simpa only [← ofReal_fltDenominator, Complex.ofReal_re] using
      hτ₀.fltDenominator_pos hbs
  obtain ⟨hregLeft, hregRight⟩ :=
    regular_fiveTerm_square_crossings (letterWord bs) τ₀ y r hε hneg hpos kj.1 kj.2
  exact tendsto_rectBoundaryIntegral_kernelUHP_letterWord
    bs hbs hτ₀ ℓ p ((m : ℕ) : ℤ) w y (P - (r + r * I)) (P + (r + r * I))
      hleft hright hregLeft hregRight

/-- The boundary passage for the crossed-contour five-term identity of a letter word at an
irrational real period with positive word periods. Given a limit `L` of the continued closed
form, the word contour sum equals `L` plus the integrals around the crossed right poles.
This formalizes the boundary passage of [RW26, Radchenko, Wheeler (2026), Theorem 3,
`thm:5term.mod.fad`, equation (23), `eq:5term.int`, Appendix A.2, `app:mod.fad`] for letter
words, at `n = h = 0` and on straight contours deformed around finitely many right poles;
it does not evaluate `L`. The exact Appendix A.2 prefactor differs from the printed theorem
prefactor by `exp(πi(γτ - τ)/12)` away from fixed points. -/
@[source
  "RW26, Appendix A.2, p. 28, app:mod.fad (letter words, crossed-pole boundary, supplied limit)"]
theorem fiveTermWordIntegralSum_eq_of_tendsto (bs : List ℤ)
    (hc : 0 < letterWord bs 1 0) {τ₀ : ℝ} (hirr : Irrational τ₀)
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p : ℤ) (w y : ℝ)
    (hy : ¬ IsPeriodLatticePoint τ₀ (y : ℂ)) (L : ℂ)
    (hClosed : Tendsto (fun τ : ℂ => fiveTermClosedFormUHPContinued (letterWord bs) ℓ p y τ w)
      (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ)) (𝓝 L))
    (x : FiveTermIndex (letterWord bs) → ℝ)
    (hxL : ∀ m : FiveTermIndex (letterWord bs),
      (-((((m : ℕ) : ℤ) + p : ℤ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ₀ - 1) /
        (letterWord bs 1 0 : ℝ) - y < x m)
    (hx : ∀ m : FiveTermIndex (letterWord bs), IsRegularPeriodLatticeCrossing τ₀ y (x m))
    (hupper : 0 < fiveTermUpperRate (letterWord bs) ℓ w τ₀)
    (hlower : fiveTermLowerRate (letterWord bs) ℓ p w y τ₀ < 0)
    (F : FiveTermIndex (letterWord bs) → Finset (ℤ × ℕ))
    (hF : ∀ (m : FiveTermIndex (letterWord bs)) (kj : ℤ × ℕ), kj ∈ F m ↔
      0 ≤ faddeevModularUHPIndex (letterWord bs) ((m : ℕ) : ℤ) kj.1 kj.2 ∧
        (faddeevModularUHPPole (letterWord bs) (τ₀ : ℂ) kj.1 kj.2).re < x m) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, IsRegularPeriodLatticeCrossing τ₀ y r →
      IsRegularPeriodLatticeCrossing τ₀ y (-r) →
      fiveTermWordIntegralSum bs ℓ p w y τ₀ x =
        L + ∑ m : FiveTermIndex (letterWord bs), ∑ kj ∈ F m,
          rectBoundaryIntegral (fiveTermWordKernel bs ℓ p w y τ₀ ((m : ℕ) : ℤ))
            (faddeevModularUHPPole (letterWord bs) (τ₀ : ℂ) kj.1 kj.2 - (r + r * I))
            (faddeevModularUHPPole (letterWord bs) (τ₀ : ℂ) kj.1 kj.2 + (r + r * I)) := by
  have hbs : bs ≠ [] := by
    intro h
    subst bs
    simp [letterWord_nil] at hc
  let l : Filter ℂ := 𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ)
  have he : 0 < (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ₀ : ℂ)).re := by
    simpa only [← ofReal_fltDenominator, Complex.ofReal_re] using
      hτ₀.fltDenominator_pos hbs
  have hxL' : ∀ m : FiveTermIndex (letterWord bs),
      (-((((m : ℕ) : ℤ) + p : ℤ) : ℝ) *
        (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ₀ : ℂ)).re - 1) /
        (letterWord bs 1 0 : ℝ) - y < x m := by
    intro m
    simpa only [← ofReal_fltDenominator, Complex.ofReal_re] using hxL m
  have hNear := eventually_fiveTermIntegralSumUHP_eq_add
    (letterWord bs) hc ℓ p (w : ℂ) y τ₀ hirr he hy
      ((mem_fiveTermParameterStrip_ofReal_iff (letterWord bs) ℓ p w y τ₀).mpr
        ⟨hupper, hlower⟩) x (fun m => (hx m).base) hxL' F hF
  let _ : NeBot l := neBot_real_upperHalfPlane τ₀
  filter_upwards [hNear, self_mem_nhdsWithin] with r hNearR hrIoi
  have hr : 0 < r := hrIoi
  intro hpos hneg
  have hIntegral := tendsto_fiveTermIntegralSumUHP_letterWord
    bs hbs hτ₀ ℓ p w y x hx hupper hlower
  have hCorr := tendsto_fiveTermWord_crossed_corrections
    bs hbs hτ₀ ℓ p w y r hr hpos hneg F
  exact tendsto_nhds_unique hIntegral
    ((hClosed.add hCorr).congr' (hNearR.mono fun _ h => h.symm))

end SIC

end
