/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.Word

/-!
# The Faddeev word product at a boundary period

Continuity, argument analyticity, and the upper-half-plane comparison of the word product
near a complex period whose successive word periods lie in the slit plane.

This module follows [RW26, Radchenko, Wheeler (2026), Proposition 2(ii),
`prop:prod.id.mod,fad`, equation (20), `eq:modulartofaddeevCF`] for an arbitrary word
`γ=∏_{j=1}^r T^{b_j}S`. Its successive periods are `τ_j=γ_j·τ` for the proper suffixes
`γ_j=∏_{i>j}T^{b_i}S`, with `τ_r=τ`. The source uses this product at a real period
`τ` whose word periods are positive, the case supplied by `WordSigmaSVisits.period_pos`
for the Hirzebruch--Jung word of a hyperbolic matrix.

## The argument

Each factor `Φ(x_j;τ_j)` of `faddeevWord` is continuous in `(x_j,τ_j)` at a slit-plane
period wherever its Barnes double-gamma denominator `Γ₂(τ_j-x_j|1,τ_j)^{-1}` is nonzero.
The arguments `x_j=z/j_{γ_j}(τ)-m_{j-1}` and periods `τ_j` are rational in `(z,τ)`, regular
where the Jacobi denominators `j_{γ_j}(τ)` are nonzero. Induction on the word, peeling the
first letter as `faddeevWord_cons_cons` does, gives joint continuity of the product on its
factorwise gamma domain, and analyticity in `z` at a fixed period. Since the denominators
are continuous, the period and gamma conditions persist for nearby complex periods.

The gamma domain contains every argument off the period lattice `ℤ+ℤτ`: for `M∈SL₂(ℤ)` with
`j_M(τ)≠0`, division by `j_M(τ)` maps `ℤ+ℤτ` onto `ℤ+ℤ(M·τ)`
(`isPeriodLatticePoint_div_fltDenominator_iff`), so each `x_j` lies off the lattice of its own
period `τ_j`.

For upper-half-plane periods near the base period, the modular q-product and the word
product are both analytic at a fixed noninteger real argument in the gamma domain; their
meromorphic germs agree by `faddeevModularUHP_eventuallyEq_faddeevWord`, so they agree at
that argument.
-/

noncomputable section

open Filter Topology
open scoped MatrixGroups

namespace SIC

/-! ### Periods along the word

The factor of the suffix `w` has period `w·τ` and argument scaled by `1/j_w(τ)`; the empty
suffix gives the last factor, at period `τ`. The condition is open in `τ` and holds on the
upper half plane and at real periods whose word periods are positive. -/

/-- The successive periods `τ_j=γ_j·τ` of `faddeevWord bs` at the proper suffixes `γ_j` of
`bs` lie in the slit plane, and their Jacobi denominators `j_{γ_j}(τ)` are nonzero. The empty
suffix gives the condition `τ∈ℂ∖(-∞,0]`. [RW26, Radchenko, Wheeler (2026), equation (20),
`eq:modulartofaddeevCF`]. -/
def FaddeevWordPeriodsSlitPlane (bs : List ℤ) (τ : ℂ) : Prop :=
  ∀ w ∈ bs.tail.tails, fltDenominator (letterWord w : Mat(2, ℤ)) τ ≠ 0 ∧
    flt (letterWord w : Mat(2, ℤ)) τ ∈ Complex.slitPlane

/-- A one-letter word has the single period `τ`. -/
theorem faddeevWordPeriodsSlitPlane_singleton (b : ℤ) (τ : ℂ) :
    FaddeevWordPeriodsSlitPlane [b] τ ↔ τ ∈ Complex.slitPlane := by
  simp [FaddeevWordPeriodsSlitPlane, List.tails, letterWord_nil]

/-- Peeling the first letter of `FaddeevWordPeriodsSlitPlane`. -/
theorem faddeevWordPeriodsSlitPlane_cons_cons (a b : ℤ) (bs : List ℤ) (τ : ℂ) :
    FaddeevWordPeriodsSlitPlane (a :: b :: bs) τ ↔
      (fltDenominator (letterWord (b :: bs) : Mat(2, ℤ)) τ ≠ 0 ∧
        flt (letterWord (b :: bs) : Mat(2, ℤ)) τ ∈ Complex.slitPlane) ∧
        FaddeevWordPeriodsSlitPlane (b :: bs) τ := by
  simp only [FaddeevWordPeriodsSlitPlane, List.tail_cons, List.tails_cons,
    List.mem_cons]
  constructor
  · intro h
    exact ⟨h _ (Or.inl rfl), fun w hw => h w (Or.inr hw)⟩
  · rintro ⟨hhead, htail⟩ w (rfl | hw)
    · exact hhead
    · exact htail w hw

/-- Upper-half-plane periods make every word period slit-plane admissible. -/
theorem faddeevWordPeriodsSlitPlane_of_im_pos (bs : List ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    FaddeevWordPeriodsSlitPlane bs τ := by
  intro w hw
  exact ⟨fltDenominator_ne_zero_of_im_ne_zero (letterWord w) hτ.ne',
    Complex.mem_slitPlane_iff.mpr (Or.inr (flt_im_pos (letterWord w) hτ).ne')⟩

/-- At a real base period, the word periods lie in the slit plane exactly when
their real values are positive and their Jacobi denominators are nonzero. -/
theorem faddeevWordPeriodsSlitPlane_ofReal_iff (bs : List ℤ) (τ : ℝ) :
    FaddeevWordPeriodsSlitPlane bs τ ↔
      ∀ w ∈ bs.tail.tails, fltDenominator (letterWord w : Mat(2, ℤ)) τ ≠ 0 ∧
        0 < flt (letterWord w : Mat(2, ℤ)) τ := by
  constructor
  · intro h w hw
    obtain ⟨hden, hslit⟩ := h w hw
    refine ⟨?_, ?_⟩
    · exact_mod_cast hden
    · rcases Complex.mem_slitPlane_iff.mp hslit with hpos | him
      · simpa only [← ofReal_flt, Complex.ofReal_re] using hpos
      · exfalso
        apply him
        simp only [← ofReal_flt, Complex.ofReal_im]
  · intro h w hw
    obtain ⟨hden, hpos⟩ := h w hw
    constructor
    · exact_mod_cast hden
    · apply Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
      simpa only [← ofReal_flt, Complex.ofReal_re] using hpos

/-- Irrationality supplies the nonzero Jacobi denominators for positive real word
periods. Specializes `faddeevWordPeriodsSlitPlane_ofReal_iff`. -/
theorem faddeevWordPeriodsSlitPlane_of_irrational (bs : List ℤ) {τ : ℝ}
    (hirr : Irrational τ)
    (hpos : ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ) :
    FaddeevWordPeriodsSlitPlane bs τ :=
  (faddeevWordPeriodsSlitPlane_ofReal_iff bs τ).mpr fun w hw =>
    ⟨fltDenominator_ne_zero_of_irrational hirr (letterWord w), hpos w hw⟩

/-- The slit-plane condition on the word periods persists for nearby complex periods. -/
theorem eventually_faddeevWordPeriodsSlitPlane (bs : List ℤ) {τ₀ : ℂ}
    (h : FaddeevWordPeriodsSlitPlane bs τ₀) :
    ∀ᶠ τ in 𝓝 τ₀, FaddeevWordPeriodsSlitPlane bs τ := by
  have hfinite : ∀ w ∈ bs.tail.tails,
      ∀ᶠ τ in 𝓝 τ₀, fltDenominator (letterWord w : Mat(2, ℤ)) τ ≠ 0 ∧
        flt (letterWord w : Mat(2, ℤ)) τ ∈ Complex.slitPlane := by
    intro w hw
    obtain ⟨hden, hslit⟩ := h w hw
    have hd := (fltDenominator_tendsto (letterWord w : Mat(2, ℤ)) tendsto_id).eventually_ne
      hden
    have hp := (flt_tendsto (letterWord w : Mat(2, ℤ)) tendsto_id hden).eventually
      (Complex.isOpen_slitPlane.mem_nhds hslit)
    exact hd.and hp
  exact (Filter.eventually_all_finite (List.finite_toSet bs.tail.tails)).2 hfinite

/-! ### The gamma domain

The factorwise gamma domain mirrors the recursion of `faddeevWord`. It contains every
nonzero value of the product and, at slit-plane word periods, every argument off the
period lattice. -/

/-- The factorwise gamma domain of `faddeevWord`: the Barnes denominator
`Γ₂(τ_j-x_j|1,τ_j)^{-1}` of every factor `Φ(x_j;τ_j)` is nonzero.
[RW26, Radchenko, Wheeler (2026), equation (20), `eq:modulartofaddeevCF`]. -/
def FaddeevWordGammaRegular : List ℤ → ℤ → ℤ → ℂ → ℂ → Prop
  | [], _, _, _, _ => True
  | [_], m, n, z, τ => barnesDoubleGammaInv (τ - (z + m * τ - n)) 1 τ ≠ 0
  | _ :: b :: bs, m, n, z, τ =>
      barnesDoubleGammaInv (flt (letterWord (b :: bs) : Mat(2, ℤ)) τ -
          (z / fltDenominator (letterWord (b :: bs) : Mat(2, ℤ)) τ - n)) 1
          (flt (letterWord (b :: bs) : Mat(2, ℤ)) τ) ≠ 0 ∧
        FaddeevWordGammaRegular (b :: bs) m 0 z τ

/-- A nonzero word product lies in its factorwise gamma domain. -/
theorem faddeevWordGammaRegular_of_ne_zero (bs : List ℤ) (m n : ℤ) (z τ : ℂ)
    (hz : faddeevWord bs m n z τ ≠ 0) :
    FaddeevWordGammaRegular bs m n z τ := by
  induction bs generalizing n with
  | nil => trivial
  | cons a bs ih =>
      cases bs with
      | nil =>
          exact faddeevS_denominator_ne_zero_of_ne_zero
            (by simpa only [faddeevWord_singleton] using hz)
      | cons b bs =>
          rw [faddeevWord_cons_cons] at hz
          exact ⟨faddeevS_denominator_ne_zero_of_ne_zero (mul_ne_zero_iff.mp hz).1,
            ih 0 (mul_ne_zero_iff.mp hz).2⟩

/-- At slit-plane word periods, every argument off `ℤ+ℤτ` lies in the gamma domain of the
word product. -/
theorem faddeevWordGammaRegular_of_notMem (bs : List ℤ) (m n : ℤ) {z τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (hz : ¬ IsPeriodLatticePoint τ z) :
    FaddeevWordGammaRegular bs m n z τ := by
  induction bs generalizing n with
  | nil => trivial
  | cons a bs ih =>
      cases bs with
      | nil =>
          have hperiod := (faddeevWordPeriodsSlitPlane_singleton a τ).mp hτ
          exact faddeevS_denominator_ne_zero_of_not_mem_lattice
            (z + m * τ - n) τ hperiod
            ((isPeriodLatticePoint_add_int_mul_sub_int_iff τ z m n).not.mpr hz)
      | cons b bs =>
          obtain ⟨⟨hden, hperiod⟩, htail⟩ :=
            (faddeevWordPeriodsSlitPlane_cons_cons a b bs τ).mp hτ
          exact ⟨faddeevS_denominator_ne_zero_of_not_mem_lattice _ _ hperiod
              (by simpa only [Int.cast_zero, zero_mul, add_zero] using
                (not_isPeriodLatticePoint_div_fltDenominator_add
                  (letterWord (b :: bs)) hden hz 0 n)),
            ih 0 htail⟩

/-- The argument and period maps of a word factor are jointly continuous at a nonzero
Jacobi denominator; used by the gamma and product continuity proofs below. -/
private lemma continuousAt_faddeevWordFactorMaps (w : List ℤ) (n : ℤ) {z τ : ℂ}
    (hden : fltDenominator (letterWord w : Mat(2, ℤ)) τ ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ =>
      p.1 / fltDenominator (letterWord w : Mat(2, ℤ)) p.2 - n) (z, τ) ∧
      ContinuousAt (fun p : ℂ × ℂ => flt (letterWord w : Mat(2, ℤ)) p.2)
        (z, τ) := by
  let M : Mat(2, ℤ) := letterWord w
  have hdenMap : ContinuousAt (fun p : ℂ × ℂ => fltDenominator M p.2) (z, τ) :=
    fltDenominator_tendsto M continuousAt_snd
  have hperiodMap : ContinuousAt (fun p : ℂ × ℂ => flt M p.2) (z, τ) :=
    flt_tendsto M continuousAt_snd hden
  exact ⟨(continuousAt_fst.div hdenMap hden).sub continuousAt_const, hperiodMap⟩

/-- A regular word factor is jointly continuous; used at each induction step of
`continuousAt_faddeevWord`. -/
private lemma continuousAt_faddeevWordFactor (w : List ℤ) (n : ℤ) {z τ : ℂ}
    (hden : fltDenominator (letterWord w : Mat(2, ℤ)) τ ≠ 0)
    (hperiod : flt (letterWord w : Mat(2, ℤ)) τ ∈ Complex.slitPlane)
    (hgamma : barnesDoubleGammaInv
      (flt (letterWord w : Mat(2, ℤ)) τ -
        (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n)) 1
      (flt (letterWord w : Mat(2, ℤ)) τ) ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ =>
      faddeevS (p.1 / fltDenominator (letterWord w : Mat(2, ℤ)) p.2 - n)
        (flt (letterWord w : Mat(2, ℤ)) p.2)) (z, τ) := by
  obtain ⟨ha, hb⟩ := continuousAt_faddeevWordFactorMaps w n hden
  simpa only [Function.comp_def] using
    (continuousAt_faddeevS hperiod hgamma).comp
      (f := fun p : ℂ × ℂ =>
        (p.1 / fltDenominator (letterWord w : Mat(2, ℤ)) p.2 - n,
          flt (letterWord w : Mat(2, ℤ)) p.2)) (ha.prodMk hb)

/-- A regular word factor remains gamma regular at nearby periods; used by
`eventually_faddeevWordGammaRegular`. -/
private lemma eventually_faddeevWordFactorGammaRegular (w : List ℤ) (n : ℤ) {z τ₀ : ℂ}
    (hden : fltDenominator (letterWord w : Mat(2, ℤ)) τ₀ ≠ 0)
    (hperiod : flt (letterWord w : Mat(2, ℤ)) τ₀ ∈ Complex.slitPlane)
    (hgamma : barnesDoubleGammaInv
      (flt (letterWord w : Mat(2, ℤ)) τ₀ -
        (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ₀ - n)) 1
      (flt (letterWord w : Mat(2, ℤ)) τ₀) ≠ 0) :
    ∀ᶠ τ in 𝓝 τ₀, barnesDoubleGammaInv
      (flt (letterWord w : Mat(2, ℤ)) τ -
        (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n)) 1
      (flt (letterWord w : Mat(2, ℤ)) τ) ≠ 0 := by
  obtain ⟨ha, hb⟩ := continuousAt_faddeevWordFactorMaps w n hden
  have hc : ContinuousAt (fun p : ℂ × ℂ => barnesDoubleGammaInv
      (flt (letterWord w : Mat(2, ℤ)) p.2 -
        (p.1 / fltDenominator (letterWord w : Mat(2, ℤ)) p.2 - n)) 1
      (flt (letterWord w : Mat(2, ℤ)) p.2)) (z, τ₀) := by
    simpa only [Function.comp_def] using
      (continuousAt_barnesDoubleGammaInv hperiod).comp
        (f := fun p : ℂ × ℂ =>
          (flt (letterWord w : Mat(2, ℤ)) p.2 -
            (p.1 / fltDenominator (letterWord w : Mat(2, ℤ)) p.2 - n),
            flt (letterWord w : Mat(2, ℤ)) p.2)) ((hb.sub ha).prodMk hb)
  have hpair : Tendsto (fun τ : ℂ => (z, τ)) (𝓝 τ₀) (𝓝 (z, τ₀)) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  exact (hc.tendsto.comp hpair).eventually_ne hgamma

/-- The factorwise gamma domain at a base period persists for nearby complex periods. -/
theorem eventually_faddeevWordGammaRegular (bs : List ℤ) (m n : ℤ) {z τ₀ : ℂ}
    (hτ₀ : FaddeevWordPeriodsSlitPlane bs τ₀) (hz : FaddeevWordGammaRegular bs m n z τ₀) :
    ∀ᶠ τ in 𝓝 τ₀, FaddeevWordGammaRegular bs m n z τ := by
  induction bs generalizing n with
  | nil => exact Filter.Eventually.of_forall (fun _ => trivial)
  | cons a bs ih =>
      cases bs with
      | nil =>
          have hperiod := (faddeevWordPeriodsSlitPlane_singleton a τ₀).mp hτ₀
          have ha : ContinuousAt (fun τ : ℂ => z + m * τ - n) τ₀ := by fun_prop
          have hb : ContinuousAt (fun τ : ℂ => τ) τ₀ := continuousAt_id
          have hc : ContinuousAt (fun τ : ℂ =>
              barnesDoubleGammaInv (τ - (z + m * τ - n)) 1 τ) τ₀ := by
            simpa only [Function.comp_def] using
              (continuousAt_barnesDoubleGammaInv hperiod).comp
                (f := fun τ : ℂ => (τ - (z + m * τ - n), τ)) ((hb.sub ha).prodMk hb)
          exact hc.eventually_ne hz
      | cons b bs =>
          obtain ⟨⟨hden, hperiod⟩, htail⟩ :=
            (faddeevWordPeriodsSlitPlane_cons_cons a b bs τ₀).mp hτ₀
          obtain ⟨hgamma, hgammaTail⟩ := hz
          have hfirst := eventually_faddeevWordFactorGammaRegular
            (b :: bs) n hden hperiod hgamma
          have hrest := ih 0 htail hgammaTail
          filter_upwards [hfirst, hrest] with τ hfirstτ hrestτ
          exact ⟨hfirstτ, hrestτ⟩

/-! ### Continuity and analyticity

Each factor is `continuousAt_faddeevS` or `analyticAt_faddeevS` composed with its rational
argument and period. -/

/-- The word product is jointly continuous in `(z,τ)` at slit-plane word periods on its
factorwise gamma domain. Composes `continuousAt_faddeevS` along the word. -/
theorem continuousAt_faddeevWord (bs : List ℤ) (m n : ℤ) {z τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (hz : FaddeevWordGammaRegular bs m n z τ) :
    ContinuousAt (fun p : ℂ × ℂ => faddeevWord bs m n p.1 p.2) (z, τ) := by
  induction bs generalizing n with
  | nil => exact continuousAt_const
  | cons a bs ih =>
      cases bs with
      | nil =>
          have hperiod := (faddeevWordPeriodsSlitPlane_singleton a τ).mp hτ
          have ha : ContinuousAt (fun p : ℂ × ℂ => p.1 + m * p.2 - n) (z, τ) :=
            (continuousAt_fst.add (continuousAt_const.mul continuousAt_snd)).sub
              continuousAt_const
          have hb : ContinuousAt (fun p : ℂ × ℂ => p.2) (z, τ) := continuousAt_snd
          simpa only [faddeevWord_singleton, Function.comp_def] using
            (continuousAt_faddeevS hperiod hz).comp
              (f := fun p : ℂ × ℂ => (p.1 + m * p.2 - n, p.2)) (ha.prodMk hb)
      | cons b bs =>
          obtain ⟨⟨hden, hperiod⟩, htail⟩ :=
            (faddeevWordPeriodsSlitPlane_cons_cons a b bs τ).mp hτ
          obtain ⟨hgamma, hgammaTail⟩ := hz
          have hfirst := continuousAt_faddeevWordFactor (b :: bs) n hden hperiod hgamma
          have hrest := ih 0 htail hgammaTail
          convert hfirst.mul hrest using 1
          funext p
          exact faddeevWord_cons_cons a b bs m n p.1 p.2

/-- A regular word factor is analytic in the argument; used at each induction step of
`analyticAt_faddeevWord`. -/
private lemma analyticAt_faddeevWordFactor (w : List ℤ) (n : ℤ) {z τ : ℂ}
    (hperiod : flt (letterWord w : Mat(2, ℤ)) τ ∈ Complex.slitPlane)
    (hgamma : barnesDoubleGammaInv
      (flt (letterWord w : Mat(2, ℤ)) τ -
        (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n)) 1
      (flt (letterWord w : Mat(2, ℤ)) τ) ≠ 0) :
    AnalyticAt ℂ (fun v : ℂ =>
      faddeevS (v / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n)
        (flt (letterWord w : Mat(2, ℤ)) τ)) z := by
  simpa only [Function.comp_def] using
    (analyticAt_faddeevS _ _ hperiod hgamma).comp
      (f := fun v : ℂ => v / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n)
      (by fun_prop)

/-- At slit-plane word periods, the word product is analytic in its argument on its factorwise
gamma domain. Composes `analyticAt_faddeevS` along the word. -/
theorem analyticAt_faddeevWord (bs : List ℤ) (m n : ℤ) {z τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (hz : FaddeevWordGammaRegular bs m n z τ) :
    AnalyticAt ℂ (fun v => faddeevWord bs m n v τ) z := by
  induction bs generalizing n with
  | nil => exact analyticAt_const
  | cons a bs ih =>
      cases bs with
      | nil =>
          have hperiod := (faddeevWordPeriodsSlitPlane_singleton a τ).mp hτ
          simpa only [faddeevWord_singleton, Function.comp_def] using
            (analyticAt_faddeevS _ _ hperiod hz).comp
              (f := fun v : ℂ => v + m * τ - n) (by fun_prop)
      | cons b bs =>
          obtain ⟨⟨_, hperiod⟩, htail⟩ :=
            (faddeevWordPeriodsSlitPlane_cons_cons a b bs τ).mp hτ
          obtain ⟨hgamma, hgammaTail⟩ := hz
          have hfirst := analyticAt_faddeevWordFactor (b :: bs) n hperiod hgamma
          have hrest := ih 0 htail hgammaTail
          convert hfirst.mul hrest using 1
          funext v
          exact faddeevWord_cons_cons a b bs m n v τ

/-- At slit-plane word periods, the word product is meromorphic in its argument at every
point. Composes `meromorphicAt_faddeevS` along the word. -/
theorem meromorphicAt_faddeevWord (bs : List ℤ) (m n : ℤ) {τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (z : ℂ) :
    MeromorphicAt (fun w => faddeevWord bs m n w τ) z := by
  induction bs generalizing n with
  | nil => exact MeromorphicAt.const 1 z
  | cons a bs ih =>
      cases bs with
      | nil =>
          have hperiod := (faddeevWordPeriodsSlitPlane_singleton a τ).mp hτ
          simpa only [faddeevWord_singleton, Function.comp_def] using
            (meromorphicAt_faddeevS (z + m * τ - n) τ hperiod).comp_analyticAt
              (g := fun w : ℂ => w + m * τ - n) (by fun_prop)
      | cons b bs =>
          obtain ⟨⟨_, hperiod⟩, htail⟩ :=
            (faddeevWordPeriodsSlitPlane_cons_cons a b bs τ).mp hτ
          have hfirst := meromorphicAt_faddeevS_div_add _ hperiod
            (fltDenominator (letterWord (b :: bs) : Mat(2, ℤ)) τ) (-n) z
          have hrest := ih 0 htail
          convert hfirst.mul hrest using 1
          funext w
          exact faddeevWord_cons_cons a b bs m n w τ

/-- At an upper-half-plane period, a nonzero word product is analytic in its argument. -/
theorem analyticAt_faddeevWord_of_ne_zero (bs : List ℤ) (m n : ℤ) {z τ : ℂ}
    (hτ : 0 < τ.im) (hz : faddeevWord bs m n z τ ≠ 0) :
    AnalyticAt ℂ (fun v => faddeevWord bs m n v τ) z := by
  exact analyticAt_faddeevWord bs m n (faddeevWordPeriodsSlitPlane_of_im_pos bs hτ)
    (faddeevWordGammaRegular_of_ne_zero bs m n z τ hz)

/-- Near a base period with slit-plane word periods, the word product is analytic in its
argument at every point of the base gamma domain. -/
theorem eventually_analyticAt_faddeevWord (bs : List ℤ) (m n : ℤ) {z τ₀ : ℂ}
    (hτ₀ : FaddeevWordPeriodsSlitPlane bs τ₀) (hz : FaddeevWordGammaRegular bs m n z τ₀) :
    ∀ᶠ τ in 𝓝 τ₀, AnalyticAt ℂ (fun v => faddeevWord bs m n v τ) z := by
  filter_upwards [eventually_faddeevWordPeriodsSlitPlane bs hτ₀,
    eventually_faddeevWordGammaRegular bs m n hτ₀ hz] with τ hperiod hgamma
  exact analyticAt_faddeevWord bs m n hperiod hgamma

/-! ### Comparison in the upper half plane

At a noninteger real argument, the modular q-product is analytic for every upper-half-plane
period, and the word product is analytic for periods near the base on its gamma domain. The
germ comparison of `faddeevModularUHP_eventuallyEq_faddeevWord` then holds at the point. -/

/-- For upper-half-plane periods near a base period with slit-plane word periods, the modular
q-product at `γ=∏_jT^{b_j}S` equals the word product at a fixed noninteger real argument in
the base gamma domain. This extends the punctured comparison of [RW26, Radchenko, Wheeler
(2026), equation (20), `eq:modulartofaddeevCF`] to the point by analyticity of both sides. -/
theorem eventually_faddeevModularUHP_eq_faddeevWord (bs : List ℤ) (hbs : bs ≠ [])
    (m n : ℤ) {τ₀ : ℂ} (hτ₀ : FaddeevWordPeriodsSlitPlane bs τ₀) (y : ℝ)
    (hy : ∀ k : ℤ, y ≠ k) (hγ : FaddeevWordGammaRegular bs m n y τ₀) :
    ∀ᶠ τ in 𝓝[{τ : ℂ | 0 < τ.im}] τ₀,
      faddeevModularUHP (letterWord bs) m n y τ = faddeevWord bs m n y τ := by
  have hproduct : ∀ᶠ τ in 𝓝[{τ : ℂ | 0 < τ.im}] τ₀,
      AnalyticAt ℂ (fun v => faddeevWord bs m n v τ) y :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_analyticAt_faddeevWord bs m n hτ₀ hγ)
  filter_upwards [self_mem_nhdsWithin, hproduct] with τ hτ hprod
  have hyτ := not_isPeriodLatticePoint_ofReal τ hτ.ne' y hy
  have hmodular := analyticAt_faddeevModularUHP_of_not_mem_lattice
    (letterWord bs) m n y τ hτ hyτ
  exact tendsto_nhds_unique_of_eventuallyEq
    (hmodular.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hprod.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (faddeevModularUHP_eventuallyEq_faddeevWord bs hbs m n y τ hτ)

end SIC
