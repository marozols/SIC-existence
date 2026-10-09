/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ImproperBoundary
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ParameterDomain
import SICs.SpecialFunctions.Faddeev.FiveTerm.Continuation

/-!
# The principal five-term identity on straight contours

Along fixed regular straight contours, deformed around finitely many crossed right poles, the
continued upper-half-plane five-term identity passes to the positive principal period for every
limit of its closed form.

This module follows [RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`,
equation (23), `eq:5term.int`, and Appendix A.2, `app:mod.fad`] at `A_d` and `τ=ρ_d`.

## The argument

Strict convergence and the separation intervals of a fixed contour family persist near `ρ_d`.
For each nearby upper-half-plane period, a nonintegral real `y` keeps the required q-product
denominator nonzero. Contours to the right of the shifted left poles may still have finitely many
right poles on their left at `ρ_d`. Near `ρ_d` these crossed poles do not change, and the
upper-half-plane identity holds with each of their residues written as the boundary integral of
the kernel over a small square centred at the pole's position at `ρ_d`
(`eventually_fiveTermIntegralSumUHP_eq_add`). Every term then has a limit: the whole-line contour
integrals converge termwise at the boundary, and each square integral converges by uniform
convergence on its boundary, which avoids the real lattice when its vertical sides cross the real
axis at regular crossings. Given a limit of the continued closed form, uniqueness of limits along
the upper-half-plane filter gives the real-period identity. This is the source's deformed contour
in straight-line form: a straight line together with small squares around the crossed poles.

The closed-form limit is a hypothesis here, so the continued zero-left value of
`SICs.Principal.Dilogarithm.Faddeev.FiveTerm.CrossedIdentity` uses the same square corrections.
The results are restricted to straight vertical contours, deformed only around finitely many
crossed right poles; they do not assert the full contour-deformation theorem.
-/

noncomputable section

open Complex Filter Set
open scoped Topology MatrixGroups

namespace SIC

/-! ### The upper-half-plane filter

The continued closed form and the contour sum have limits along the same nontrivial
upper-half-plane neighborhood filter. Uniqueness equates their boundary values. -/

/-- The upper-half-plane neighborhood of `ρ_d` is nontrivial; used by
`principalFiveTermIntegralSum_eq_of_tendsto`. -/
private theorem neBot_principalRoot_upperHalfPlane (d : ℕ) :
    NeBot (𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ)) := by
  have hclosure : (principalRoot d : ℂ) ∈ closure {τ : ℂ | 0 < τ.im} := by
    rw [show {τ : ℂ | 0 < τ.im} = Complex.im ⁻¹' Ioi 0 by rfl,
      Complex.closure_preimage_im]
    simp
  exact mem_closure_iff_nhdsWithin_neBot.mp hclosure

/-! ### Contours with crossed right poles

A regular straight contour to the right of the shifted left poles may have finitely many right
poles on its left at `ρ_d`. The nearby upper-half-plane identity with square corrections passes
to the limit term by term. -/

/-- The vertical sides of a square around a right pole cross the real axis at integral
translates of `-r` and `r`; used by
`tendsto_principalFiveTerm_crossed_corrections`. -/
private theorem regular_principalFiveTerm_square_crossings
    (d : ℕ) (hd : 3 < d) (y r : ℝ)
    (hneg : IsRegularPeriodLatticeCrossing (principalRoot d) y (-r))
    (hpos : IsRegularPeriodLatticeCrossing (principalRoot d) y r)
    (k : ℤ) (j : ℕ) :
    IsRegularPeriodLatticeCrossing (principalRoot d) y
      (faddeevModularUHPPole (principalA d) (principalRoot d) k j - (r + r * I)).re ∧
    IsRegularPeriodLatticeCrossing (principalRoot d) y
      (faddeevModularUHPPole (principalA d) (principalRoot d) k j + (r + r * I)).re := by
  let K : ℤ := k * (principalA d) 1 0 - (j : ℤ) * (principalA d) 0 0
  let L : ℤ := k * (principalA d) 1 1 - (j : ℤ) * (principalA d) 0 1
  let P := faddeevModularUHPPole (principalA d) (principalRoot d) k j
  have hP : P = (K : ℂ) * (principalRoot d : ℂ) + L :=
    faddeevModularUHPPole_eq (principalA d) (principalRoot d)
      (fltDenominator_principalA_principalRoot_ne_zero d hd) k j
  have hPre : P.re = (K : ℝ) * principalRoot d + L := by
    rw [hP]
    simp
  have hleft : (P - (r + r * I)).re = -r + (K : ℝ) * principalRoot d + L := by
    simp [hPre]
    ring
  have hright : (P + (r + r * I)).re = r + (K : ℝ) * principalRoot d + L := by
    simp [hPre]
    ring
  change IsRegularPeriodLatticeCrossing (principalRoot d) y (P - (r + r * I)).re ∧
    IsRegularPeriodLatticeCrossing (principalRoot d) y (P + (r + r * I)).re
  rw [hleft, hright]
  exact ⟨IsRegularPeriodLatticeCrossing.add_int_mul_add_int
    (principalRoot d) y (-r) K L hneg,
    IsRegularPeriodLatticeCrossing.add_int_mul_add_int
      (principalRoot d) y r K L hpos⟩

/-- The finite sum of square corrections tends to its real-period value; used by
`principalFiveTermIntegralSum_eq_of_tendsto`. -/
private theorem tendsto_principalFiveTerm_crossed_corrections
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y r : ℝ) (hr : 0 < r)
    (hpos : IsRegularPeriodLatticeCrossing (principalRoot d) y r)
    (hneg : IsRegularPeriodLatticeCrossing (principalRoot d) y (-r))
    (F : FiveTermIndex (principalA d) → Finset (ℤ × ℕ)) :
    Tendsto (fun τ : ℂ =>
      ∑ m : FiveTermIndex (principalA d), ∑ kj ∈ F m,
        rectBoundaryIntegral
          (fiveTermKernelUHP (principalA d) ℓ p w y τ ((m : ℕ) : ℤ))
          (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 - (r + r * I))
          (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 + (r + r * I)))
      (𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ))
      (𝓝 (∑ m : FiveTermIndex (principalA d), ∑ kj ∈ F m,
        rectBoundaryIntegral (principalFiveTermKernel d ℓ p w y ((m : ℕ) : ℤ))
          (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 - (r + r * I))
          (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 +
            (r + r * I)))) := by
  apply tendsto_finsetSum
  intro m _
  apply tendsto_finsetSum
  intro kj _
  let P := faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2
  have hPim : P.im = 0 :=
    im_faddeevModularUHPPole_ofReal (principalA d) (principalRoot d) kj.1 kj.2
  have hleft : (P - (r + r * I)).im ≠ 0 := by
    have heq : (P - (r + r * I)).im = -r := by simp [hPim]
    rw [heq]
    exact neg_ne_zero.mpr (ne_of_gt hr)
  have hright : (P + (r + r * I)).im ≠ 0 := by
    have heq : (P + (r + r * I)).im = r := by simp [hPim]
    rw [heq]
    exact ne_of_gt hr
  obtain ⟨hregLeft, hregRight⟩ :=
    regular_principalFiveTerm_square_crossings d hd y r hneg hpos kj.1 kj.2
  exact tendsto_rectBoundaryIntegral_kernelUHP_principalA
    d hd ℓ p ((m : ℕ) : ℤ) w y (P - (r + r * I)) (P + (r + r * I))
      hleft hright hregLeft hregRight

/-- The boundary limit of the crossed-contour identity for any established limit `C` of its
continued closed form. This separates the contour argument from the evaluation of the closed
form, so the continued zero-left value uses the same square corrections. -/
theorem principalFiveTermIntegralSum_eq_of_tendsto
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ)
    (hy : ¬ IsPeriodLatticePoint (principalRoot d) (y : ℂ))
    (C : ℂ)
    (hClosed : Tendsto (fun τ : ℂ =>
      fiveTermClosedFormUHPContinued (principalA d) ℓ p y τ w)
      (𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ)) (𝓝 C))
    (x : FiveTermIndex (principalA d) → ℝ)
    (hxL : ∀ m : FiveTermIndex (principalA d),
      (-((((m : ℕ) : ℤ) + p : ℤ) : ℝ) * principalRoot d ^ 3 - 1) /
        ((principalA d) 1 0 : ℝ) - y < x m)
    (hx : ∀ m : FiveTermIndex (principalA d),
      IsRegularPeriodLatticeCrossing (principalRoot d) y (x m))
    (hupper : 0 < principalFiveTermUpperRate d ℓ w)
    (hlower : principalFiveTermLowerRate d ℓ p w y < 0)
    (F : FiveTermIndex (principalA d) → Finset (ℤ × ℕ))
    (hF : ∀ (m : FiveTermIndex (principalA d)) (kj : ℤ × ℕ), kj ∈ F m ↔
      0 ≤ faddeevModularUHPIndex (principalA d) ((m : ℕ) : ℤ) kj.1 kj.2 ∧
        (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2).re < x m) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, IsRegularPeriodLatticeCrossing (principalRoot d) y r →
      IsRegularPeriodLatticeCrossing (principalRoot d) y (-r) →
      principalFiveTermIntegralSum d ℓ p w y x =
        C +
          ∑ m : FiveTermIndex (principalA d), ∑ kj ∈ F m,
            rectBoundaryIntegral (principalFiveTermKernel d ℓ p w y ((m : ℕ) : ℤ))
              (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 - (r + r * I))
              (faddeevModularUHPPole (principalA d) (principalRoot d) kj.1 kj.2 +
                (r + r * I)) := by
  let l : Filter ℂ := 𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ)
  have he : 0 < (fltDenominator (principalA d : Mat(2, ℤ))
      (principalRoot d : ℂ)).re := by
    simpa only [fltDenominator_principalA_principalRoot_complex d hd,
      ← Complex.ofReal_pow, Complex.ofReal_re] using pow_pos (principalRoot_pos d hd) 3
  have hxL' : ∀ m : FiveTermIndex (principalA d),
      (-((((m : ℕ) : ℤ) + p : ℤ) : ℝ) *
        (fltDenominator (principalA d : Mat(2, ℤ)) (principalRoot d : ℂ)).re - 1) /
        ((principalA d) 1 0 : ℝ) - y < x m := by
    intro m
    simpa only [fltDenominator_principalA_principalRoot_complex d hd,
      ← Complex.ofReal_pow, Complex.ofReal_re] using hxL m
  have hNear := eventually_fiveTermIntegralSumUHP_eq_add
    (principalA d) (principalA_lowerLeft_pos d hd) ℓ p (w : ℂ) y
      (principalRoot d) (principalRoot_irrational d hd) he hy
      ((mem_fiveTermParameterStrip_principalRoot d hd ℓ p w y).2
        ⟨hupper, hlower⟩) x (fun m => (hx m).base) hxL' F hF
  let _ : NeBot l := neBot_principalRoot_upperHalfPlane d
  filter_upwards [hNear, self_mem_nhdsWithin] with r hNearR hrIoi
  have hr : 0 < r := hrIoi
  intro hpos hneg
  have hIntegral := tendsto_integralSumUHP_principalA
    d hd ℓ p w y x hx hupper hlower
  have hCorr := tendsto_principalFiveTerm_crossed_corrections d hd ℓ p w y r hr hpos hneg F
  exact tendsto_nhds_unique hIntegral
    ((hClosed.add hCorr).congr' (hNearR.mono fun _ h => h.symm))

end SIC
