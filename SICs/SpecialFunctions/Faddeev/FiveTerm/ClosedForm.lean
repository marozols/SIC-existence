/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.Modular
import SICs.Analysis.IdentityTheorem
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# The continued closed form of the five-term integral

The meromorphic closed expression of the five-term identity with its removable values restored.

This module follows [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`].
The exact prefactor is `ε ϖ(τ,τ)/ϖ(γτ,γτ)`, as in the appendix's residue computation.

## The argument

The expression is meromorphic in `w`, being a quotient of entire q-products.
Its continued value is the normal form of that meromorphic germ. This restores values
at common zeros without assuming that the raw quotient is nonzero. At a genuine pole
the normal form has the totalized value zero. Throughout the convergence strip of the five-term
integral, `sum_integral_fiveTermKernelUHP_of_crossed` identifies it with a holomorphic function.
-/

noncomputable section

open Complex Real Filter Set
open scoped Topology MatrixGroups

namespace SIC

/-- The raw closed expression in [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`], at `n=h=0`, including its exact q-product prefactor.
At common zeros this totalized expression can differ from its continued value. -/
def fiveTermClosedFormUHP (γ : SL(2, ℤ)) (ℓ p : ℤ) (y τ w : ℂ) : ℂ :=
  faddeevModularUHPOriginValue γ τ *
    (faddeevModularUHP γ (p + ℓ) 0 (w + y) τ /
      (faddeevModularUHP γ p 0 y τ * faddeevModularUHP γ ℓ 1 w τ))

/-- The continued value of the closed expression of [RW26, Radchenko, Wheeler (2026),
Theorem 3, `thm:5term.mod.fad`, equation (23), `eq:5term.int`], on the upper half plane.
It is the value of the meromorphic normal form in `w`, including removable common zeros. -/
def fiveTermClosedFormUHPContinued (γ : SL(2, ℤ)) (ℓ p : ℤ) (y τ w : ℂ) : ℂ :=
  toMeromorphicNFAt (fiveTermClosedFormUHP γ ℓ p y τ) w w

/-! ### Meromorphy of the raw quotient

Each factor in the expression of [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`] is a quotient of entire q-products when `τ ∈ ℍ`. -/

/-- For `τ ∈ ℍ`, the raw five-term expression is meromorphic in `w`, as the q-product
expression in [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem meromorphic_fiveTermClosedFormUHP (γ : SL(2, ℤ)) (ℓ p : ℤ)
    (y τ : ℂ) (hτ : 0 < τ.im) :
    Meromorphic (fiveTermClosedFormUHP γ ℓ p y τ) := by
  have hnum : Meromorphic (fun w => faddeevModularUHP γ (p + ℓ) 0 (w + y) τ) :=
    Meromorphic.meromorphic_fun_comp_add_const_iff_meromorphic.mpr
      (meromorphic_faddeevModularUHP γ (p + ℓ) 0 τ hτ)
  have hden := meromorphic_faddeevModularUHP γ ℓ 1 τ hτ
  unfold fiveTermClosedFormUHP
  exact (Meromorphic.const _).mul (hnum.div
    ((Meromorphic.const _).mul hden))

/-! ### Identification of continued values

The meromorphic normal form is determined by its punctured germ. Where the raw quotient is
analytic, its value already equals that normal form. -/

/-- An analytic function with the same punctured germ as the five-term quotient gives its
continued value at `w`. This is the normal-form uniqueness used for continuation in
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem fiveTermClosedFormUHPContinued_eq_of_nhdsNE
    (γ : SL(2, ℤ)) (ℓ p : ℤ) (y τ w : ℂ) {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f w)
    (heq : fiveTermClosedFormUHP γ ℓ p y τ =ᶠ[𝓝[≠] w] f) :
    fiveTermClosedFormUHPContinued γ ℓ p y τ w = f w := by
  unfold fiveTermClosedFormUHPContinued
  exact toMeromorphicNFAt_self_eq hf heq

/-- At an analytic point of the raw quotient, its value is already the continued value of
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem fiveTermClosedFormUHPContinued_eq
    (γ : SL(2, ℤ)) (ℓ p : ℤ) (y τ w : ℂ)
    (h : AnalyticAt ℂ (fiveTermClosedFormUHP γ ℓ p y τ) w) :
    fiveTermClosedFormUHPContinued γ ℓ p y τ w =
      fiveTermClosedFormUHP γ ℓ p y τ w := by
  exact fiveTermClosedFormUHPContinued_eq_of_nhdsNE
    γ ℓ p y τ w h Filter.EventuallyEq.rfl

/-! ### The zero-left parameter

At `ℓ=1,w=0` the denominator product is already regular in the upper half plane.
Its value cancels the origin prefactor, leaving the factor `cτ+d`.
-/

/-- The factor `Φ_{γ,1,1}(w;τ)` is analytic and nonzero at the origin, as needed for
`fiveTermClosedFormUHPContinued_zero_left`. -/
private lemma analyticAt_and_ne_zero_faddeevModularUHP_one_one
    (γ : SL(2, ℤ)) (τ : ℂ) (hτ : 0 < τ.im) :
    AnalyticAt ℂ (fun w => faddeevModularUHP γ 1 1 w τ) 0 ∧
      faddeevModularUHP γ 1 1 0 τ ≠ 0 := by
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  have hσ : 0 < σ.im := flt_im_pos γ hτ
  have hn : AnalyticAt ℂ (fun w : ℂ => qPochhammer (w + (1 : ℤ) * τ) τ) 0 :=
    ((qPochhammer_differentiable τ hτ).comp (by fun_prop)).analyticAt 0
  have hd : AnalyticAt ℂ (fun w : ℂ => qPochhammer (w / ε + (1 : ℤ) * σ) σ) 0 :=
    ((qPochhammer_differentiable σ hσ).comp (by fun_prop)).analyticAt 0
  have hdne : qPochhammer (0 / ε + (1 : ℤ) * σ) σ ≠ 0 := by
    simpa using qPochhammer_tau_ne_zero σ hσ
  have hne : faddeevModularUHP γ 1 1 0 τ ≠ 0 := by
    simpa [faddeevModularUHP, ε, σ] using
      div_ne_zero (qPochhammer_tau_ne_zero τ hτ) (qPochhammer_tau_ne_zero σ hσ)
  exact ⟨by
    change AnalyticAt ℂ (fun w : ℂ => qPochhammer (w + (1 : ℤ) * τ) τ /
      qPochhammer (w / ε + (1 : ℤ) * σ) σ) 0
    exact hn.div hd hdne, hne⟩

/-- The raw five-term quotient is analytic at `ℓ=1,w=0` when `y` is off the lattice;
used by `fiveTermClosedFormUHPContinued_zero_left`. -/
private lemma analyticAt_fiveTermClosedFormUHP_one_zero
    (γ : SL(2, ℤ)) (p : ℤ) (y τ : ℂ)
    (hτ : 0 < τ.im) (hy : ¬ IsPeriodLatticePoint τ y) :
    AnalyticAt ℂ (fiveTermClosedFormUHP γ 1 p y τ) 0 := by
  obtain ⟨h11, h11ne⟩ :=
    analyticAt_and_ne_zero_faddeevModularUHP_one_one γ τ hτ
  have hnum : AnalyticAt ℂ
      (fun w => faddeevModularUHP γ (p + 1) 0 (w + y) τ) 0 := by
    have h := analyticAt_faddeevModularUHP_of_not_mem_lattice
      γ (p + 1) 0 y τ hτ hy
    simpa only [Function.comp_def] using
      h.comp_of_eq (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w + y) 0) (by simp)
  have hden : faddeevModularUHP γ p 0 y τ ≠ 0 :=
    faddeevModularUHP_ne_zero_of_not_mem_lattice γ p 0 y τ hτ hy
  change AnalyticAt ℂ (fun w =>
    faddeevModularUHPOriginValue γ τ *
      (faddeevModularUHP γ (p + 1) 0 (w + y) τ /
        (faddeevModularUHP γ p 0 y τ * faddeevModularUHP γ 1 1 w τ))) 0
  exact analyticAt_const.mul (hnum.div (analyticAt_const.mul h11)
    (mul_ne_zero hden h11ne))

/-- The zero-left-parameter closed form used in [RW26, Radchenko, Wheeler (2026), Section 3.2,
proof of Theorem 2, `thm:fg.equs`]: `C^cont_{1,p}(0,y;τ) = (cτ+d) Φ_{p+1,0}(y;τ)/Φ_{p,0}(y;τ)`.
The denominator `Φ_{1,1}(0;τ)=ϖ(τ,τ)/ϖ(γτ,γτ)` is nonzero on the upper half plane. -/
theorem fiveTermClosedFormUHPContinued_zero_left
    (γ : SL(2, ℤ)) (p : ℤ) (y τ : ℂ) (hτ : 0 < τ.im)
    (hy : ¬ IsPeriodLatticePoint τ y) :
    fiveTermClosedFormUHPContinued γ 1 p y τ 0 =
      fltDenominator (γ : Mat(2, ℤ)) τ *
        faddeevModularUHP γ (p + 1) 0 y τ / faddeevModularUHP γ p 0 y τ := by
  rw [fiveTermClosedFormUHPContinued_eq γ 1 p y τ 0
    (analyticAt_fiveTermClosedFormUHP_one_zero γ p y τ hτ hy)]
  have hσ : 0 < (flt (γ : Mat(2, ℤ)) τ).im := flt_im_pos γ hτ
  have hqσ : qPochhammer (flt (γ : Mat(2, ℤ)) τ)
      (flt (γ : Mat(2, ℤ)) τ) ≠ 0 :=
    qPochhammer_tau_ne_zero _ hσ
  have hqτ : qPochhammer τ τ ≠ 0 := qPochhammer_tau_ne_zero τ hτ
  simp only [fiveTermClosedFormUHP, zero_add,
    faddeevModularUHPOriginValue]
  have h11 : faddeevModularUHP γ 1 1 0 τ =
      qPochhammer τ τ /
        qPochhammer (flt (γ : Mat(2, ℤ)) τ)
          (flt (γ : Mat(2, ℤ)) τ) := by
    simp [faddeevModularUHP]
  rw [h11]
  field_simp

end SIC
