/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.FiveTerm.ClosedForm
import SICs.SpecialFunctions.Faddeev.WordFiveTerm.Kernel

/-!
# The five-term closed form of a letter word at the real boundary

The word-product expression of the continued five-term closed form of a letter word and its
limit as the period approaches a real period with positive word periods through the upper
half-plane.

This module follows [RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`,
equation (23), `eq:5term.int`] and Appendix A.2, `app:mod.fad`, using the word product of
Proposition 2(ii), `prop:prod.id.mod,fad`, equation (20), `eq:modulartofaddeevCF`. The principal
word is treated directly in `SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ClosedForm`.

## The argument

Near a real period with positive word periods, every word period has positive real part, so
every factor of `Φ_{γ,0,0}(z;τ)` is regular at `z = 0` and the word product is continuous there.
Its punctured germ agrees with that of the modular q-product, whose removable value is the exact
prefactor `(cτ+d) ϖ(τ,τ)/ϖ(γ·τ,γ·τ)`; uniqueness of the punctured limit identifies the two,
and joint continuity at `(0,τ₀)` gives the boundary limit.

For a fixed upper-half-plane period, the modular and word factors of the closed form have the
same punctured germs. If the numerator word product is analytic and the two denominator values
are nonzero, the denominator word products are analytic, and their quotient is the analytic
normal form of the raw modular quotient. This identifies the continued value even when the raw
numerator has a common q-product zero. Near `τ₀`, lattice-free boundary arguments supply the
denominator conditions, and a lattice-free numerator or the removable zero-index origin lies in
the gamma domain of the numerator. Joint continuity of the word products then passes the
identified upper-half-plane values to the real-period closed form. At `w = 0`, `ℓ = 1` the
continued closed form is `(cτ+d) Φ_{γ,p+1,0}(y;τ)/Φ_{γ,p,0}(y;τ)` on the upper half-plane, and
its limit is taken factorwise.
-/

noncomputable section

open Complex Filter Set
open scoped Topology MatrixGroups

namespace SIC

/-! ### The prefactor -/

/-- At the origin, positive real parts of all word periods put each unshifted factor in its
Barnes gamma domain. Used by `faddeevWordGammaRegular_zero_of_periodsPos`. -/
private theorem faddeevWordGammaRegular_zero_of_re_pos (bs : List ℤ) {τ : ℂ}
    (hpos : ∀ w ∈ bs.tail.tails,
      0 < (flt (letterWord w : Mat(2, ℤ)) τ).re) :
    FaddeevWordGammaRegular bs 0 0 0 τ := by
  induction bs with
  | nil => trivial
  | cons a bs ih =>
      cases bs with
      | nil =>
          have hτ : 0 < τ.re := by
            simpa [letterWord_nil, flt_one] using hpos [] (by simp)
          have hslit : τ ∈ Complex.slitPlane :=
            Complex.mem_slitPlane_iff.mpr (Or.inl hτ)
          simpa [FaddeevWordGammaRegular] using
            barnesDoubleGammaInv_ne_zero_of_re_pos τ τ hslit hτ.le hτ
      | cons b bs =>
          have hσ : 0 < (flt (letterWord (b :: bs) : Mat(2, ℤ)) τ).re :=
            hpos (b :: bs) (by simp)
          have hslit : flt (letterWord (b :: bs) : Mat(2, ℤ)) τ ∈
              Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hσ)
          have hfirst : barnesDoubleGammaInv
              (flt (letterWord (b :: bs) : Mat(2, ℤ)) τ) 1
              (flt (letterWord (b :: bs) : Mat(2, ℤ)) τ) ≠ 0 :=
            barnesDoubleGammaInv_ne_zero_of_re_pos _ _ hslit hσ.le hσ
          have htail := ih (forall_tail_tails_of_cons a (b :: bs) hpos)
          simpa [FaddeevWordGammaRegular] using And.intro hfirst htail

/-- Positive real word periods give the origin gamma domain at the real boundary. Used by
`eventually_faddeevModularUHPOriginValue_letterWord`. -/
private lemma faddeevWordGammaRegular_zero_of_periodsPos (bs : List ℤ) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) :
    FaddeevWordGammaRegular bs 0 0 0 (τ₀ : ℂ) := by
  apply faddeevWordGammaRegular_zero_of_re_pos bs
  intro w hw
  simpa only [← ofReal_flt, Complex.ofReal_re] using (hτ₀ w hw).2

/-- Near a real period with positive word periods, through the upper half-plane, the removable
value of the modular q-product of a nonempty letter word at the origin is the word product
`Φ_{γ,0,0}(0;τ)`; used by `eventually_closedForm_eq_word`. -/
private theorem eventually_faddeevModularUHPOriginValue_letterWord (bs : List ℤ) (hbs : bs ≠ [])
    {τ₀ : ℝ} (hτ₀ : FaddeevWordPeriodsPos bs τ₀) :
    ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ),
      faddeevModularUHPOriginValue (letterWord bs) τ = faddeevWord bs 0 0 0 τ := by
  have hslit := hτ₀.slitPlane
  have hreg := faddeevWordGammaRegular_zero_of_periodsPos bs hτ₀
  have hperiod : ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ),
      FaddeevWordPeriodsSlitPlane bs τ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_faddeevWordPeriodsSlitPlane bs hslit)
  have hgamma : ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ),
      FaddeevWordGammaRegular bs 0 0 0 τ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_faddeevWordGammaRegular bs 0 0 hslit hreg)
  filter_upwards [self_mem_nhdsWithin, hperiod, hgamma] with τ hτ hslitτ hregτ
  have hproduct : Tendsto (fun z : ℂ => faddeevWord bs 0 0 z τ)
      (𝓝[≠] 0) (𝓝 (faddeevWord bs 0 0 0 τ)) :=
    ((analyticAt_faddeevWord bs 0 0 hslitτ hregτ).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  exact tendsto_nhds_unique_of_eventuallyEq
    (tendsto_faddeevModularUHP_zero (letterWord bs) τ hτ) hproduct
    (faddeevModularUHP_eventuallyEq_faddeevWord bs hbs 0 0 0 τ hτ)

/-! ### The closed form -/

/-- The word-product expression of the closed form in [RW26, Radchenko, Wheeler (2026),
Appendix A.2, `app:mod.fad`], using Proposition 2(ii), `prop:prod.id.mod,fad`, equation (20),
`eq:modulartofaddeevCF`:
`Φ_{γ,0,0}(0;τ) Φ_{γ,p+ℓ,0}(w+y;τ)/(Φ_{γ,p,0}(y;τ) Φ_{γ,ℓ,1}(w;τ))`.
Appendix A.2 gives the origin-value prefactor
`(cτ+d)(q;q)∞/(q̃;q̃)∞ = μ_γ⁻¹ √(cτ+d) exp(πi(γτ−τ)/12)`.
The displayed Theorem 3, equation (23), `eq:5term.int`, omits the exponential factor; it is
one when `γτ = τ`. -/
def fiveTermWordClosedForm (bs : List ℤ) (ℓ p : ℤ) (w y τ : ℂ) : ℂ :=
  faddeevWord bs 0 0 0 τ *
    (faddeevWord bs (p + ℓ) 0 (w + y) τ /
      (faddeevWord bs p 0 y τ * faddeevWord bs ℓ 1 w τ))

/-- At a fixed upper-half-plane period, analytic word factors with the modular point values
shown give the continued five-term closed form of a nonempty letter word, including removable
common zeros of its raw q-product numerator; used by `eventually_closedForm_eq_word`. -/
private theorem fiveTermClosedFormUHPContinued_letterWord (bs : List ℤ) (hbs : bs ≠ [])
    (ℓ p : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im)
    (hscalar : faddeevModularUHPOriginValue (letterWord bs) τ = faddeevWord bs 0 0 0 τ)
    (hyEq : faddeevModularUHP (letterWord bs) p 0 y τ = faddeevWord bs p 0 y τ)
    (hnum : AnalyticAt ℂ (fun v => faddeevWord bs (p + ℓ) 0 v τ) (w + y))
    (hyne : faddeevWord bs p 0 y τ ≠ 0) (hwne : faddeevWord bs ℓ 1 w τ ≠ 0) :
    fiveTermClosedFormUHPContinued (letterWord bs) ℓ p y τ w =
      fiveTermWordClosedForm bs ℓ p w y τ := by
  let f : ℂ → ℂ := fun v => faddeevWord bs 0 0 0 τ *
    (faddeevWord bs (p + ℓ) 0 (v + y) τ /
      (faddeevWord bs p 0 y τ * faddeevWord bs ℓ 1 v τ))
  have hden := analyticAt_faddeevWord_of_ne_zero bs ℓ 1 hτ hwne
  have hf : AnalyticAt ℂ f w := by
    change AnalyticAt ℂ
      ((fun _ : ℂ => faddeevWord bs 0 0 0 τ) *
        ((fun v : ℂ => faddeevWord bs (p + ℓ) 0 (v + y) τ) /
          ((fun _ : ℂ => faddeevWord bs p 0 y τ) *
            (fun v : ℂ => faddeevWord bs ℓ 1 v τ)))) w
    simpa only [Function.comp_def] using analyticAt_const.mul
      ((hnum.comp (f := fun v : ℂ => v + y) (by fun_prop)).div
        (analyticAt_const.mul hden) (mul_ne_zero hyne hwne))
  have hnumEq :=
    (faddeevModularUHP_eventuallyEq_faddeevWord
      bs hbs (p + ℓ) 0 (w + y) τ hτ).comp_tendsto
        (Filter.map_add_right_nhdsNE (c := y) (a := w)).le
  have hdenEq := faddeevModularUHP_eventuallyEq_faddeevWord
    bs hbs ℓ 1 w τ hτ
  have heq : fiveTermClosedFormUHP (letterWord bs) ℓ p y τ =ᶠ[𝓝[≠] w] f := by
    filter_upwards [hnumEq, hdenEq] with v hvnum hvden
    simp only [Function.comp_def] at hvnum
    simp only [fiveTermClosedFormUHP, f]
    rw [hscalar, hyEq, hvnum, hvden]
  simpa only [f, fiveTermWordClosedForm] using
    fiveTermClosedFormUHPContinued_eq_of_nhdsNE
      (letterWord bs) ℓ p y τ w hf heq

/-! ### Boundary limits -/

/-- Near the real boundary, the continued modular closed form agrees with the word closed
form when its numerator lies in the word gamma domain. Used by the boundary limit below. -/
private lemma eventually_closedForm_eq_word (bs : List ℤ) (hbs : bs ≠ [])
    {τ₀ : ℝ} (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p : ℤ) (w y : ℝ)
    (hw : ¬ IsPeriodLatticePoint τ₀ (w : ℂ))
    (hy : ¬ IsPeriodLatticePoint τ₀ (y : ℂ))
    (hnum : FaddeevWordGammaRegular bs (p + ℓ) 0 ((w : ℂ) + y) τ₀) :
    ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ),
      fiveTermClosedFormUHPContinued (letterWord bs) ℓ p y τ w =
        fiveTermWordClosedForm bs ℓ p w y τ := by
  have hslit := hτ₀.slitPlane
  have hyreg := faddeevWordGammaRegular_of_notMem bs p 0 hslit hy
  have hwreg := faddeevWordGammaRegular_of_notMem bs ℓ 1 hslit hw
  have hyint : ∀ k : ℤ, y ≠ k := by
    intro k heq
    apply hy
    exact ⟨k, 0, by simp [heq]⟩
  have hyEq := eventually_faddeevModularUHP_eq_faddeevWord
    bs hbs p 0 hslit y hyint hyreg
  have hnumAnalytic : ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ),
      AnalyticAt ℂ (fun v => faddeevWord bs (p + ℓ) 0 v τ) ((w : ℂ) + y) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_analyticAt_faddeevWord bs (p + ℓ) 0 hslit hnum)
  have hycont : ContinuousAt (fun τ : ℂ => faddeevWord bs p 0 y τ) (τ₀ : ℂ) := by
    have hpair : ContinuousAt (fun τ : ℂ => ((y : ℂ), τ)) (τ₀ : ℂ) :=
      continuousAt_const.prodMk continuousAt_id
    simpa only [Function.comp_def] using
      (continuousAt_faddeevWord bs p 0 hslit hyreg).comp hpair
  have hwcont : ContinuousAt (fun τ : ℂ => faddeevWord bs ℓ 1 w τ) (τ₀ : ℂ) := by
    have hpair : ContinuousAt (fun τ : ℂ => ((w : ℂ), τ)) (τ₀ : ℂ) :=
      continuousAt_const.prodMk continuousAt_id
    simpa only [Function.comp_def] using
      (continuousAt_faddeevWord bs ℓ 1 hslit hwreg).comp hpair
  have hyne : ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ),
      faddeevWord bs p 0 y τ ≠ 0 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (hycont.eventually_ne (faddeevWord_ne_zero_of_notMem bs p 0 hslit hy))
  have hwne : ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ),
      faddeevWord bs ℓ 1 w τ ≠ 0 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (hwcont.eventually_ne (faddeevWord_ne_zero_of_notMem bs ℓ 1 hslit hw))
  filter_upwards [self_mem_nhdsWithin,
    eventually_faddeevModularUHPOriginValue_letterWord bs hbs hτ₀,
    hyEq, hnumAnalytic, hyne, hwne] with τ hτ hscalar hyEqτ hnumτ hyneτ hwneτ
  exact fiveTermClosedFormUHPContinued_letterWord
    bs hbs ℓ p w y τ hτ hscalar hyEqτ hnumτ hyneτ hwneτ

/-- The word closed form is continuous in the period at a positive real word period when its
numerator lies in the gamma domain and its denominator arguments avoid the period lattice. -/
private lemma continuousAt_fiveTermWordClosedForm (bs : List ℤ) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p : ℤ) (w y : ℂ)
    (hw : ¬ IsPeriodLatticePoint τ₀ w) (hy : ¬ IsPeriodLatticePoint τ₀ y)
    (hnum : FaddeevWordGammaRegular bs (p + ℓ) 0 (w + y) τ₀) :
    ContinuousAt (fun τ => fiveTermWordClosedForm bs ℓ p w y τ) (τ₀ : ℂ) := by
  have hslit := hτ₀.slitPlane
  have hwordCont (m n : ℤ) (z : ℂ)
      (hγ : FaddeevWordGammaRegular bs m n z τ₀) :
      ContinuousAt (fun τ : ℂ => faddeevWord bs m n z τ) (τ₀ : ℂ) := by
    have hpair : ContinuousAt (fun τ : ℂ => (z, τ)) (τ₀ : ℂ) :=
      continuousAt_const.prodMk continuousAt_id
    simpa only [Function.comp_def] using
      (continuousAt_faddeevWord bs m n hslit hγ).comp hpair
  have hscalar := hwordCont 0 0 0 (faddeevWordGammaRegular_zero_of_periodsPos bs hτ₀)
  have hnumCont := hwordCont (p + ℓ) 0 (w + y) hnum
  have hycont := hwordCont p 0 y (faddeevWordGammaRegular_of_notMem bs p 0 hslit hy)
  have hwcont := hwordCont ℓ 1 w (faddeevWordGammaRegular_of_notMem bs ℓ 1 hslit hw)
  have hyne := faddeevWord_ne_zero_of_notMem bs p 0 hslit hy
  have hwne := faddeevWord_ne_zero_of_notMem bs ℓ 1 hslit hw
  change ContinuousAt
    ((fun τ : ℂ => faddeevWord bs 0 0 0 τ) *
      ((fun τ : ℂ => faddeevWord bs (p + ℓ) 0 (w + y) τ) /
        ((fun τ : ℂ => faddeevWord bs p 0 y τ) *
          (fun τ : ℂ => faddeevWord bs ℓ 1 w τ)))) (τ₀ : ℂ)
  exact hscalar.mul (hnumCont.div (hycont.mul hwcont) (mul_ne_zero hyne hwne))

/-- The continued upper-half-plane five-term closed form of a nonempty letter word tends to the
word closed form at a real period with positive word periods, when `w` and `y` avoid `ℤ+ℤτ₀`
and the numerator lies in the gamma domain of its word product; used by
`tendsto_closedFormUHPContinued_letterWord`. -/
private theorem tendsto_closedFormUHPContinued_letterWord_of_gammaRegular (bs : List ℤ)
    (hbs : bs ≠ []) {τ₀ : ℝ} (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p : ℤ) (w y : ℝ)
    (hw : ¬ IsPeriodLatticePoint τ₀ (w : ℂ)) (hy : ¬ IsPeriodLatticePoint τ₀ (y : ℂ))
    (hnum : FaddeevWordGammaRegular bs (p + ℓ) 0 ((w : ℂ) + y) τ₀) :
    Tendsto (fun τ : ℂ => fiveTermClosedFormUHPContinued (letterWord bs) ℓ p y τ w)
      (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ)) (𝓝 (fiveTermWordClosedForm bs ℓ p w y τ₀)) := by
  have hlimit : Tendsto (fun τ : ℂ => fiveTermWordClosedForm bs ℓ p w y τ)
      (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ))
      (𝓝 (fiveTermWordClosedForm bs ℓ p w y τ₀)) :=
    (continuousAt_fiveTermWordClosedForm bs hτ₀ ℓ p w y hw hy hnum).tendsto.mono_left
      nhdsWithin_le_nhds
  exact hlimit.congr'
    ((eventually_closedForm_eq_word bs hbs hτ₀ ℓ p w y hw hy hnum).mono
      fun _ h => h.symm)

/-- The continued upper-half-plane five-term closed form of a nonempty letter word tends to the
word closed form at a real period with positive word periods, when `w` and `y` avoid `ℤ+ℤτ₀`
and `w+y` either avoids it or is the removable zero-index origin. -/
theorem tendsto_closedFormUHPContinued_letterWord (bs : List ℤ) (hbs : bs ≠ []) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p : ℤ) (w y : ℝ)
    (hw : ¬ IsPeriodLatticePoint τ₀ (w : ℂ)) (hy : ¬ IsPeriodLatticePoint τ₀ (y : ℂ))
    (hwy : ¬ IsPeriodLatticePoint τ₀ ((w : ℂ) + y) ∨ ((w : ℂ) + y = 0 ∧ p + ℓ = 0)) :
    Tendsto (fun τ : ℂ => fiveTermClosedFormUHPContinued (letterWord bs) ℓ p y τ w)
      (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ)) (𝓝 (fiveTermWordClosedForm bs ℓ p w y τ₀)) := by
  apply tendsto_closedFormUHPContinued_letterWord_of_gammaRegular
    bs hbs hτ₀ ℓ p w y hw hy
  rcases hwy with hwy | ⟨hwy, hpℓ⟩
  · exact faddeevWordGammaRegular_of_notMem bs (p + ℓ) 0 hτ₀.slitPlane hwy
  · simpa only [hwy, hpℓ] using faddeevWordGammaRegular_zero_of_periodsPos bs hτ₀

/-- The zero-left-parameter boundary value of the continued closed form of a nonempty letter
word in [RW26, Radchenko, Wheeler (2026), Section 3.2, proof of Theorem 2, `thm:fg.equs`]: at
`ℓ = 1`, `w = 0` it tends to `ε Φ_{γ,p+1,0}(y;τ₀)/Φ_{γ,p,0}(y;τ₀)`, `ε = j_γ(τ₀)`, at a real
period with positive word periods. -/
theorem tendsto_closedFormUHPContinued_letterWord_zero_left (bs : List ℤ) (hbs : bs ≠ [])
    {τ₀ : ℝ} (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (p : ℤ) (y : ℝ)
    (hy : ¬ IsPeriodLatticePoint τ₀ (y : ℂ)) :
    Tendsto (fun τ : ℂ => fiveTermClosedFormUHPContinued (letterWord bs) 1 p y τ 0)
      (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ))
      (𝓝 ((fltDenominator (letterWord bs : Mat(2, ℤ)) τ₀ : ℂ) *
        faddeevWord bs (p + 1) 0 y τ₀ / faddeevWord bs p 0 y τ₀)) := by
  have hyint : ∀ k : ℤ, y ≠ k := by
    intro k heq
    apply hy
    exact ⟨k, 0, by simp [heq]⟩
  have hslit := hτ₀.slitPlane
  have hnumReg := faddeevWordGammaRegular_of_notMem bs (p + 1) 0 hslit hy
  have hdenReg := faddeevWordGammaRegular_of_notMem bs p 0 hslit hy
  have heq : ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ),
      fiveTermClosedFormUHPContinued (letterWord bs) 1 p y τ 0 =
        fltDenominator (letterWord bs : Mat(2, ℤ)) τ *
          faddeevWord bs (p + 1) 0 y τ / faddeevWord bs p 0 y τ := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_faddeevModularUHP_eq_faddeevWord bs hbs (p + 1) 0 hslit y hyint hnumReg,
      eventually_faddeevModularUHP_eq_faddeevWord bs hbs p 0 hslit y hyint hdenReg]
      with τ hτ hnum hden
    rw [fiveTermClosedFormUHPContinued_zero_left (letterWord bs) p y τ hτ
      (not_isPeriodLatticePoint_ofReal τ hτ.ne' y hyint), hnum, hden]
  have hpair : ContinuousAt (fun τ : ℂ => ((y : ℂ), τ)) (τ₀ : ℂ) :=
    continuousAt_const.prodMk continuousAt_id
  have hnum : Tendsto (fun τ : ℂ => faddeevWord bs (p + 1) 0 y τ)
      (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ))
      (𝓝 (faddeevWord bs (p + 1) 0 y τ₀)) :=
    ((continuousAt_faddeevWord bs (p + 1) 0 hslit hnumReg).comp hpair).tendsto.mono_left
      nhdsWithin_le_nhds
  have hden : Tendsto (fun τ : ℂ => faddeevWord bs p 0 y τ)
      (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ))
      (𝓝 (faddeevWord bs p 0 y τ₀)) :=
    ((continuousAt_faddeevWord bs p 0 hslit hdenReg).comp hpair).tendsto.mono_left
      nhdsWithin_le_nhds
  have hdenne := faddeevWord_ne_zero_of_notMem bs p 0 hslit hy
  have hscalar : Tendsto
      (fun τ : ℂ => fltDenominator (letterWord bs : Mat(2, ℤ)) τ)
      (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ))
      (𝓝 (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ₀ : ℂ))) :=
    (fltDenominator_tendsto _ tendsto_id).mono_left nhdsWithin_le_nhds
  have hlimit := (hscalar.mul hnum).div hden hdenne
  simpa only [ofReal_fltDenominator] using
    hlimit.congr' (heq.mono fun _ h => h.symm)

end SIC

end
