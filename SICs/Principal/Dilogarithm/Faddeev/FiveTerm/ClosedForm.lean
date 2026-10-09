/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.Cocycle
import SICs.Principal.Dilogarithm.Faddeev.Boundary
import SICs.SpecialFunctions.Faddeev.FiveTerm.ClosedForm

/-!
# The principal five-term closed form at the real-period boundary

The generator expression for the continued five-term closed form and its limit at the positive
principal period.

This module follows [RW26, Radchenko, Wheeler (2026), Theorem 3,
`thm:5term.mod.fad`, equation (23), `eq:5term.int`] and Appendix A.2, `app:mod.fad`, using the
three-generator formula of Proposition 2(ii), `prop:prod.id.mod,fad`, equation (20),
`eq:modulartofaddeevCF`.

## The argument

For a fixed upper-half-plane period, the modular factors and principal generator factors have
the same punctured germs. If the numerator generator is analytic and the two denominator values
are nonzero, their gamma domains make the denominator generators analytic. Their quotient is the
analytic normal form of the raw modular quotient. This identifies the continued value even when
the raw numerator has a common q-product zero.

Near the positive principal period, lattice-free boundary arguments provide all denominator
conditions. The core boundary theorem assumes the sufficient factorwise gamma domain for the
numerator; both a lattice-free numerator and the removable zero-index origin lie in this domain.
Joint continuity of the generator products then passes the identified upper-half-plane values to
the real-period closed form.
-/

noncomputable section

open Filter Topology
open scoped MatrixGroups

namespace SIC

/-! ### The removable prefactor near the real period

For periods near the positive fixed point, the three periods in the principal word have positive
real part. Their inverse Barnes double-gamma denominators are therefore nonzero at the origin,
so the generator product is continuous there. Its punctured germ agrees with the modular
q-product, whose removable value is the exact scalar
`(cτ+d) ϖ(τ,τ)/ϖ(A_d·τ,A_d·τ)`. Uniqueness of the punctured limit identifies that scalar
with the generator product.
-/

/-- The three-generator principal product is continuous in its argument at zero whenever its
three periods have positive real part; used to recover the removable q-product
value in `eventually_faddeevModularUHPOriginValue_principalA`. -/
private lemma continuousAt_complex_zero_of_re_pos
    (d : ℕ) (tau : ℂ) (hre₀ : 0 < tau.re)
    (hre₁ : 0 < (flt (principalU d : Mat(2, ℤ)) tau).re)
    (hre₂ : 0 < (flt (principalU d : Mat(2, ℤ))
      (flt (principalU d : Mat(2, ℤ)) tau)).re) :
    ContinuousAt (fun z : ℂ => principalFaddeevComplex d 0 0 z tau) 0 := by
  let U : Mat(2, ℤ) := principalU d
  let tau₁ := flt U tau
  let tau₂ := flt U tau₁
  have h₂ := continuousAt_faddeevS_zero_of_re_pos (by simpa [tau₂, tau₁, U] using hre₂)
  have h₁ := continuousAt_faddeevS_zero_of_re_pos (by simpa [tau₁, U] using hre₁)
  have h₀ := continuousAt_faddeevS_zero_of_re_pos hre₀
  have ha₂ : ContinuousAt (fun z : ℂ => z / tau / tau₁) 0 :=
    continuousAt_id.div_const tau |>.div_const tau₁
  have ha₁ : ContinuousAt (fun z : ℂ => z / tau) 0 :=
    continuousAt_id.div_const tau
  have hf₂ : ContinuousAt (fun z : ℂ => faddeevS (z / tau / tau₁) tau₂) 0 :=
    h₂.comp_of_eq ha₂ (by simp)
  have hf₁ : ContinuousAt (fun z : ℂ => faddeevS (z / tau) tau₁) 0 :=
    h₁.comp_of_eq ha₁ (by simp)
  have heq : (fun z : ℂ => principalFaddeevComplex d 0 0 z tau) =
      ((fun z : ℂ => faddeevS (z / tau / tau₁) tau₂) *
        (fun z : ℂ => faddeevS (z / tau) tau₁)) *
        (fun z : ℂ => faddeevS z tau) := by
    funext z
    simp [principalFaddeevComplex, U, tau₁, tau₂]
  rw [heq]
  exact (hf₂.mul hf₁).mul h₀

/-- For `τ` sufficiently close to `ρ_d` in the upper half plane, the exact q-product scalar

`j_{A_d}(τ) ϖ(τ,τ)/ϖ(A_d·τ,A_d·τ)`

is the value at the removable origin of the principal three-generator product. This combines the
punctured comparison in [RW26, Radchenko, Wheeler (2026), Proposition 2(ii),
`prop:prod.id.mod,fad`, equation (20), `eq:modulartofaddeevCF`] with the origin residue calculation
in Appendix A.2, `app:mod.fad`. -/
theorem eventually_faddeevModularUHPOriginValue_principalA
    (d : ℕ) (hd : 3 < d) :
    ∀ᶠ tau : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ),
      faddeevModularUHPOriginValue (principalA d) tau =
        principalFaddeevComplex d 0 0 0 tau := by
  have hpos : ∀ᶠ tau : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ),
      0 < tau.re ∧
        0 < (flt (principalU d : Mat(2, ℤ)) tau).re ∧
        0 < (flt (principalU d : Mat(2, ℤ))
          (flt (principalU d : Mat(2, ℤ)) tau)).re :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_principalFaddeevPeriods_re_pos d hd)
  filter_upwards [self_mem_nhdsWithin, hpos] with tau htau hpos
  have hproduct : Tendsto (fun z : ℂ => principalFaddeevComplex d 0 0 z tau)
      (𝓝[≠] 0) (𝓝 (principalFaddeevComplex d 0 0 0 tau)) :=
    (continuousAt_complex_zero_of_re_pos
      d tau hpos.1 hpos.2.1 hpos.2.2).tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique_of_eventuallyEq
    (tendsto_faddeevModularUHP_zero (principalA d) tau htau)
    hproduct
    (faddeevModularUHP_principalA_eventuallyEq_complex
      d 0 0 0 tau htau)

/-! ### Generator closed forms -/

/-- The complex-period generator expression obtained by substituting
[RW26, Radchenko, Wheeler (2026), Proposition 2(ii), `prop:prod.id.mod,fad`, equation (20),
`eq:modulartofaddeevCF`] into the closed form of Theorem 3, equation (23), `eq:5term.int`.
Its regularity domain is supplied by the comparison theorems below. -/
def principalFiveTermClosedFormComplex
    (d : ℕ) (ℓ p : ℤ) (w y τ : ℂ) : ℂ :=
  principalFaddeevComplex d 0 0 0 τ *
    (principalFaddeevComplex d (p + ℓ) 0 (w + y) τ /
      (principalFaddeevComplex d p 0 y τ *
        principalFaddeevComplex d ℓ 1 w τ))

/-- The real-period generator closed form corresponding to
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`, equation (23),
`eq:5term.int`] for the principal word. -/
def principalFiveTermClosedForm (d : ℕ) (ℓ p : ℤ) (w y : ℂ) : ℂ :=
  principalFaddeev d 0 0 0 *
    (principalFaddeev d (p + ℓ) 0 (w + y) /
      (principalFaddeev d p 0 y * principalFaddeev d ℓ 1 w))

/-- The principal real-period closed form with the scalar
`μ_{A_d}^{-1}√(ρ_d³)` displayed as in [RW26, Radchenko, Wheeler (2026), Theorem 3,
`thm:5term.mod.fad`, equation (23), `eq:5term.int`]. -/
theorem principalFiveTermClosedForm_eq_etaMultiplier
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℂ) :
    principalFiveTermClosedForm d ℓ p w y =
      (Real.sqrt (principalRoot d ^ 3) : ℂ) / etaMultiplier (principalA d) *
        (principalFaddeev d (p + ℓ) 0 (w + y) /
          (principalFaddeev d p 0 y * principalFaddeev d ℓ 1 w)) := by
  simp only [principalFiveTermClosedForm,
    principalFaddeev_zero_eq_etaMultiplier d hd]

/-- At `τ=ρ_d`, the complex-period generator closed form equals its real-period value. -/
theorem principalFiveTermClosedFormComplex_principalRoot
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℂ) :
    principalFiveTermClosedFormComplex d ℓ p w y (principalRoot d) =
      principalFiveTermClosedForm d ℓ p w y := by
  simp only [principalFiveTermClosedFormComplex,
    principalFiveTermClosedForm,
    principalFaddeevComplex_principalRoot d hd]

/-! ### Identification at a fixed upper-half-plane period -/

/-- At a fixed upper-half-plane period, analytic principal generator factors with the modular
point values shown below give the continued five-term closed form, including removable common
zeros of its raw q-product numerator. -/
theorem fiveTermClosedFormUHPContinued_principalA
    (d : ℕ) (ℓ p : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im)
    (hscalar : faddeevModularUHPOriginValue (principalA d) τ =
      principalFaddeevComplex d 0 0 0 τ)
    (hyEq : faddeevModularUHP (principalA d) p 0 y τ =
      principalFaddeevComplex d p 0 y τ)
    (hnum : AnalyticAt ℂ
      (fun v => principalFaddeevComplex d (p + ℓ) 0 v τ) (w + y))
    (hyne : principalFaddeevComplex d p 0 y τ ≠ 0)
    (hwne : principalFaddeevComplex d ℓ 1 w τ ≠ 0) :
    fiveTermClosedFormUHPContinued (principalA d) ℓ p y τ w =
      principalFiveTermClosedFormComplex d ℓ p w y τ := by
  let f : ℂ → ℂ := fun v => principalFaddeevComplex d 0 0 0 τ *
    (principalFaddeevComplex d (p + ℓ) 0 (v + y) τ /
      (principalFaddeevComplex d p 0 y τ *
        principalFaddeevComplex d ℓ 1 v τ))
  have hden := analyticAt_principalFaddeevComplex_of_ne_zero
    d ℓ 1 w τ hτ hwne
  have hf : AnalyticAt ℂ f w := by
    change AnalyticAt ℂ
      ((fun _ : ℂ => principalFaddeevComplex d 0 0 0 τ) *
        ((fun v : ℂ => principalFaddeevComplex d (p + ℓ) 0 (v + y) τ) /
          ((fun _ : ℂ => principalFaddeevComplex d p 0 y τ) *
            (fun v : ℂ => principalFaddeevComplex d ℓ 1 v τ)))) w
    simpa only [Function.comp_def] using analyticAt_const.mul
      ((hnum.comp (f := fun v : ℂ => v + y) (by fun_prop)).div
        (analyticAt_const.mul hden) (mul_ne_zero hyne hwne))
  have hnumEq :=
    (faddeevModularUHP_principalA_eventuallyEq_complex
      d (p + ℓ) 0 (w + y) τ hτ).comp_tendsto
        (Filter.map_add_right_nhdsNE (c := y) (a := w)).le
  have hdenEq := faddeevModularUHP_principalA_eventuallyEq_complex
    d ℓ 1 w τ hτ
  have heq : fiveTermClosedFormUHP (principalA d) ℓ p y τ =ᶠ[𝓝[≠] w] f := by
    filter_upwards [hnumEq, hdenEq] with v hvnum hvden
    simp only [Function.comp_def] at hvnum
    simp only [fiveTermClosedFormUHP, f]
    rw [hscalar, hyEq, hvnum, hvden]
  simpa only [f, principalFiveTermClosedFormComplex] using
    fiveTermClosedFormUHPContinued_eq_of_nhdsNE
      (principalA d) ℓ p y τ w hf heq

/-! ### Boundary regularity -/

/-- Restricts joint generator continuity to variation of the period on its factorwise gamma
domain; used by the closed-form boundary theorem. -/
private lemma continuousAt_complex_period_of_gammaRegular
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ)
    (hz : PrincipalFaddeevGammaRegular d m n z) :
    ContinuousAt (fun τ => principalFaddeevComplex d m n z τ)
      (principalRoot d : ℂ) := by
  have hpair : ContinuousAt (fun τ : ℂ => (z, τ)) (principalRoot d : ℂ) :=
    continuousAt_const.prodMk continuousAt_id
  simpa only [Function.comp_def] using
    (continuousAt_principalFaddeevComplex_of_gammaRegular
      d hd m n z hz).comp (f := fun τ : ℂ => (z, τ)) hpair

/-- Restricts nearby joint nonvanishing to variation of the period at a fixed lattice-free
argument; used for both denominator factors in the continued closed form. -/
private lemma eventually_complex_ne_zero_period
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ)
    (hz : ¬ IsPeriodLatticePoint (principalRoot d) z) :
    ∀ᶠ τ : ℂ in 𝓝 (principalRoot d : ℂ),
      principalFaddeevComplex d m n z τ ≠ 0 := by
  have hpair : Tendsto (fun τ : ℂ => (z, τ))
      (𝓝 (principalRoot d : ℂ)) (𝓝 (z, (principalRoot d : ℂ))) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  simpa only [] using hpair.eventually
    (eventually_principalFaddeevComplex_ne_zero_of_notMem
      d hd m n z hz)

/-- The lattice-free-or-origin numerator condition supplies the factorwise gamma domain; used by
`tendsto_closedFormUHPContinued_principalA`. -/
private lemma principalFiveTerm_numerator_gammaRegular
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℂ)
    (hwy : ¬ IsPeriodLatticePoint (principalRoot d) (w + y) ∨
      (w + y = 0 ∧ p + ℓ = 0)) :
    PrincipalFaddeevGammaRegular d (p + ℓ) 0 (w + y) := by
  rcases hwy with hwy | ⟨hwy, hpℓ⟩
  · exact principalFaddeevGammaRegular_of_notMem
      d hd (p + ℓ) 0 (w + y) hwy
  · simpa only [hwy, hpℓ] using principalFaddeevGammaRegular_zero d hd

/-- Near `ρ_d` in the upper half plane, the continued modular closed form equals the complex
generator closed form when its denominator arguments are lattice-free and its numerator lies
in the factorwise gamma domain. -/
theorem eventually_closedFormUHPContinued_principalA_of_gammaRegular
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ)
    (hw : ¬ IsPeriodLatticePoint (principalRoot d) (w : ℂ))
    (hy : ¬ IsPeriodLatticePoint (principalRoot d) (y : ℂ))
    (hnum : PrincipalFaddeevGammaRegular d (p + ℓ) 0 ((w : ℂ) + y)) :
    ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ),
      fiveTermClosedFormUHPContinued (principalA d) ℓ p y τ w =
        principalFiveTermClosedFormComplex d ℓ p w y τ := by
  have hyEq := eventually_faddeevModularUHP_principalA
    d hd p 0 y hy
  have hnumAnalytic :=
    eventually_analyticAt_principalFaddeevComplex
      d hd (p + ℓ) 0 ((w : ℂ) + y) hnum
  have hyne := eventually_complex_ne_zero_period d hd p 0 y hy
  have hwne := eventually_complex_ne_zero_period d hd ℓ 1 w hw
  have hnum' : ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ),
      AnalyticAt ℂ (fun v => principalFaddeevComplex d (p + ℓ) 0 v τ)
        ((w : ℂ) + y) := Filter.Eventually.filter_mono nhdsWithin_le_nhds hnumAnalytic
  have hyne' : ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ),
      principalFaddeevComplex d p 0 y τ ≠ 0 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hyne
  have hwne' : ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ),
      principalFaddeevComplex d ℓ 1 w τ ≠ 0 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hwne
  filter_upwards [self_mem_nhdsWithin,
    eventually_faddeevModularUHPOriginValue_principalA d hd,
    hyEq, hnum', hyne', hwne'] with τ hτ hscalar hyEqτ hnumτ hyneτ hwneτ
  exact fiveTermClosedFormUHPContinued_principalA
    d ℓ p w y τ hτ hscalar hyEqτ hnumτ hyneτ hwneτ

/-- The complex-period principal closed form is continuous at `ρ_d` when its denominator
arguments are lattice-free and its numerator lies in the factorwise gamma domain. The argument
variables may be arbitrary complex numbers. -/
theorem continuousAt_principalFiveTermClosedFormComplex
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℂ)
    (hw : ¬ IsPeriodLatticePoint (principalRoot d) w)
    (hy : ¬ IsPeriodLatticePoint (principalRoot d) y)
    (hnum : PrincipalFaddeevGammaRegular d (p + ℓ) 0 (w + y)) :
    ContinuousAt (fun τ => principalFiveTermClosedFormComplex d ℓ p w y τ)
      (principalRoot d : ℂ) := by
  have hscalar := continuousAt_complex_period_of_gammaRegular
    d hd 0 0 0 (principalFaddeevGammaRegular_zero d hd)
  have hnumCont := continuousAt_complex_period_of_gammaRegular
    d hd (p + ℓ) 0 (w + y) hnum
  have hycont := continuousAt_complex_period_of_gammaRegular
    d hd p 0 y (principalFaddeevGammaRegular_of_notMem d hd p 0 y hy)
  have hwcont := continuousAt_complex_period_of_gammaRegular
    d hd ℓ 1 w (principalFaddeevGammaRegular_of_notMem d hd ℓ 1 w hw)
  have hyne : principalFaddeevComplex d p 0 y (principalRoot d) ≠ 0 := by
    rw [principalFaddeevComplex_principalRoot d hd]
    exact principalFaddeev_ne_zero_of_notMem d hd p 0 y hy
  have hwne : principalFaddeevComplex d ℓ 1 w (principalRoot d) ≠ 0 := by
    rw [principalFaddeevComplex_principalRoot d hd]
    exact principalFaddeev_ne_zero_of_notMem d hd ℓ 1 w hw
  change ContinuousAt
    ((fun τ : ℂ => principalFaddeevComplex d 0 0 0 τ) *
      ((fun τ : ℂ => principalFaddeevComplex d (p + ℓ) 0 (w + y) τ) /
        ((fun τ : ℂ => principalFaddeevComplex d p 0 y τ) *
          (fun τ : ℂ => principalFaddeevComplex d ℓ 1 w τ))))
    (principalRoot d : ℂ)
  exact hscalar.mul (hnumCont.div (hycont.mul hwcont) (mul_ne_zero hyne hwne))

/-! ### The real-period boundary value -/

/-- The continued upper-half-plane closed form tends to the principal real-period generator
closed form when its numerator lies in the factorwise gamma domain. -/
theorem tendsto_closedFormUHPContinued_principalA_of_gammaRegular
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ)
    (hw : ¬ IsPeriodLatticePoint (principalRoot d) (w : ℂ))
    (hy : ¬ IsPeriodLatticePoint (principalRoot d) (y : ℂ))
    (hnum : PrincipalFaddeevGammaRegular d (p + ℓ) 0 ((w : ℂ) + y)) :
    Tendsto (fun τ : ℂ =>
      fiveTermClosedFormUHPContinued (principalA d) ℓ p y τ w)
      (𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ))
      (𝓝 (principalFiveTermClosedForm d ℓ p w y)) := by
  have hcomplex : Tendsto
      (fun τ : ℂ => principalFiveTermClosedFormComplex d ℓ p w y τ)
      (𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ))
      (𝓝 (principalFiveTermClosedFormComplex d ℓ p w y (principalRoot d))) :=
    (continuousAt_principalFiveTermClosedFormComplex
      d hd ℓ p w y hw hy hnum).tendsto.mono_left nhdsWithin_le_nhds
  have hlimit : Tendsto
      (fun τ : ℂ => principalFiveTermClosedFormComplex d ℓ p w y τ)
      (𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ))
      (𝓝 (principalFiveTermClosedForm d ℓ p w y)) := by
    simpa only [principalFiveTermClosedFormComplex_principalRoot d hd] using hcomplex
  exact hlimit.congr'
    ((eventually_closedFormUHPContinued_principalA_of_gammaRegular
      d hd ℓ p w y hw hy hnum).mono fun _ h => h.symm)

/-- The continued upper-half-plane closed form tends to the principal real-period generator
closed form. This includes the removable numerator at `w+y=0`, `p+ℓ=0`, where the raw modular
q-product quotient does not carry the continued value. -/
theorem tendsto_closedFormUHPContinued_principalA
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ)
    (hw : ¬ IsPeriodLatticePoint (principalRoot d) (w : ℂ))
    (hy : ¬ IsPeriodLatticePoint (principalRoot d) (y : ℂ))
    (hwy : ¬ IsPeriodLatticePoint (principalRoot d) ((w : ℂ) + y) ∨
      ((w : ℂ) + y = 0 ∧ p + ℓ = 0)) :
    Tendsto (fun τ : ℂ =>
      fiveTermClosedFormUHPContinued (principalA d) ℓ p y τ w)
      (𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ))
      (𝓝 (principalFiveTermClosedForm d ℓ p w y)) :=
  tendsto_closedFormUHPContinued_principalA_of_gammaRegular
    d hd ℓ p w y hw hy
      (principalFiveTerm_numerator_gammaRegular d hd ℓ p w y hwy)

/-- The zero-left-parameter boundary value of the continued closed form in
[RW26, Radchenko, Wheeler (2026), Section 3.2, proof of Theorem 2, `thm:fg.equs`].
The continued modular factor `Φ_{1,1}(0)` is `Φ_{0,0}(0)/ε`, so at `ℓ=1,w=0` the closed
form is `ε Φ_{p+1,0}(y)/Φ_{p,0}(y)`. This uses the origin identity before the period limit;
it makes no assertion of joint continuity for arbitrary removable lattice points. -/
theorem tendsto_closedFormUHPContinued_principalA_zero_left
    (d : ℕ) (hd : 3 < d) (p : ℤ) (y : ℝ)
    (hy : ¬ IsPeriodLatticePoint (principalRoot d) (y : ℂ)) :
    Tendsto (fun τ : ℂ =>
      fiveTermClosedFormUHPContinued (principalA d) 1 p y τ 0)
      (𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ))
      (𝓝 ((principalRoot d : ℂ) ^ 3 *
        principalFaddeev d (p + 1) 0 y / principalFaddeev d p 0 y)) := by
  have hyint : ∀ n : ℤ, y ≠ n := by
    intro n hyn
    apply hy
    exact ⟨n, 0, by simp [hyn]⟩
  have heq : ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ),
      fiveTermClosedFormUHPContinued (principalA d) 1 p y τ 0 =
        fltDenominator (principalA d : Mat(2, ℤ)) τ *
          principalFaddeevComplex d (p + 1) 0 y τ /
            principalFaddeevComplex d p 0 y τ := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_faddeevModularUHP_principalA
        d hd (p + 1) 0 y hy,
      eventually_faddeevModularUHP_principalA
        d hd p 0 y hy] with τ hτ hnum hden
    rw [fiveTermClosedFormUHPContinued_zero_left (principalA d) p y τ hτ
      (not_isPeriodLatticePoint_ofReal τ hτ.ne' y hyint), hnum, hden]
  have hpair : ContinuousAt (fun τ : ℂ => ((y : ℂ), τ))
      (principalRoot d : ℂ) := continuousAt_const.prodMk continuousAt_id
  have hnum : Tendsto
      (fun τ : ℂ => principalFaddeevComplex d (p + 1) 0 y τ)
      (𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ))
      (𝓝 (principalFaddeevComplex d (p + 1) 0 y (principalRoot d))) := by
    exact ((continuousAt_principalFaddeevComplex_of_notMem
      d hd (p + 1) 0 y hy).comp hpair).tendsto.mono_left nhdsWithin_le_nhds
  have hden : Tendsto
      (fun τ : ℂ => principalFaddeevComplex d p 0 y τ)
      (𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ))
      (𝓝 (principalFaddeevComplex d p 0 y (principalRoot d))) := by
    exact ((continuousAt_principalFaddeevComplex_of_notMem
      d hd p 0 y hy).comp hpair).tendsto.mono_left nhdsWithin_le_nhds
  have hdenne : principalFaddeevComplex d p 0 y (principalRoot d) ≠ 0 := by
    rw [principalFaddeevComplex_principalRoot d hd]
    exact principalFaddeev_ne_zero_of_notMem d hd p 0 y hy
  have hscalar : Tendsto
      (fun τ : ℂ => fltDenominator (principalA d : Mat(2, ℤ)) τ)
      (𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ))
      (𝓝 (fltDenominator (principalA d : Mat(2, ℤ)) (principalRoot d : ℂ))) :=
    (fltDenominator_tendsto _ tendsto_id).mono_left nhdsWithin_le_nhds
  have hlimit := (hscalar.mul hnum).div hden hdenne
  simpa only [fltDenominator_principalA_principalRoot_complex d hd,
    principalFaddeevComplex_principalRoot d hd] using
    hlimit.congr' (heq.mono fun _ h => h.symm)

end SIC
