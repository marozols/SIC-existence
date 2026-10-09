/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.ComplexPeriodAsymptotics
import SICs.SpecialFunctions.Faddeev.WordReflection

/-!
# Complex-period asymptotics of the Faddeev word product

Uniformly for complex periods near a real period with positive word periods, the word product
`Φ_{γ,m,n}(z;τ)` tends exponentially to one in every upper sector, and its quotient by the
reflection asymptote `(-1)^{m+n} e(Q_{γ,-m,-n}(-z,τ)) κ_γ` does so in every lower sector.

These are quantitative boundary-neighborhood extensions of both clauses of [RW26, Radchenko,
Wheeler (2026), Lemma 1, `lem:asymp`] for a letter word `γ = ∏_j T^{b_j}S`, through the product
formula of Proposition 2(ii), `prop:prod.id.mod,fad`, equation (20), `eq:modulartofaddeevCF`.
At the real period itself they give Lemma 1 with exponential rates. The principal three-letter
word keeps its own direct proof in `SICs.Principal.Dilogarithm.Faddeev.ComplexPeriodAsymptotics`.
The novelty search for the two neighborhood estimates covered [AFK25] and [RW26, Radchenko,
Wheeler (2026)] only: the manuscript of Garoufalidis, Kashaev and Zagier that [RW26] cites for
these asymptotics was not available.

## The argument

The factor of `faddeevWord` attached to a proper suffix `γ_j` of the word is the Faddeev
generator `Φ(z/j_{γ_j}(τ) - n_j; γ_j·τ)`, an affine function of `z` whose slope `1/j_{γ_j}(τ)`
and period `γ_j·τ` depend continuously on `τ` and are positive at the real period `τ₀`. The
complex-period affine estimates for the generator therefore bound each factor uniformly near
`τ₀`, and induction on the word combines the finitely many near-one bounds.

In a lower sector each factor is within an exponentially small error of its reflected quadratic
exponential `exp(-πi(x²/τ_j - (1-τ_j⁻¹)x + (τ_j+τ_j⁻¹)/6 - 1/2))`, by the generator reflection
law. The pairing behind the word reflection law of Proposition 1, `prop:reflection`, identifies
the product of these exponentials exactly with `(-1)^{m+n} e(Q_{γ,-m,-n}(-z,τ)) κ_γ`, where
`κ_γ = exp(-πi(∑_j b_j - 3r)/6)` is the word expansion of `μ_γ⁻²` in
`SICs.SpecialFunctions.Faddeev.WordReflection`.
-/

noncomputable section

open Complex Real Set Filter
open scoped MatrixGroups

namespace SIC

/-! ### Positive word periods

At a real period, the hypotheses of the asymptotic estimates are positivity of every word period
and of its Jacobi denominator. -/

/-- At a real period `τ`, every proper suffix `γ_j` of the letter word `bs` (including the empty
suffix, whose period is `τ`) has a positive Jacobi denominator `j_{γ_j}(τ)` and a positive
period `γ_j·τ`. These are the periods and slopes of the factors of [RW26, Radchenko, Wheeler
(2026), equation (20), `eq:modulartofaddeevCF`]. -/
def FaddeevWordPeriodsPos (bs : List ℤ) (τ : ℝ) : Prop :=
  ∀ w ∈ bs.tail.tails, 0 < fltDenominator (letterWord w : Mat(2, ℤ)) τ ∧
    0 < flt (letterWord w : Mat(2, ℤ)) τ

/-- Positive word periods lie in the slit plane. -/
theorem FaddeevWordPeriodsPos.slitPlane {bs : List ℤ} {τ : ℝ}
    (h : FaddeevWordPeriodsPos bs τ) : FaddeevWordPeriodsSlitPlane bs (τ : ℂ) := by
  apply (faddeevWordPeriodsSlitPlane_ofReal_iff bs τ).mpr
  intro w hw
  exact ⟨(h w hw).1.ne', (h w hw).2⟩

/-- At a real period with positive word periods, the Jacobi denominator `j_γ(τ)` of the whole
nonempty letter word is positive: it is the product of the period and the Jacobi denominator of
its first proper suffix. -/
theorem FaddeevWordPeriodsPos.fltDenominator_pos {bs : List ℤ} {τ : ℝ}
    (h : FaddeevWordPeriodsPos bs τ) (hbs : bs ≠ []) :
    0 < fltDenominator (letterWord bs : Mat(2, ℤ)) τ := by
  obtain ⟨a, w, rfl⟩ := List.exists_cons_of_ne_nil hbs
  have hw := h w (by simp)
  rw [fltDenominator_letterWord_cons a w hw.1.ne']
  exact mul_pos hw.2 hw.1

/-! ### Affine data of a word factor

The suffix denominator supplies the positive slope, and its image supplies the positive
generator period. These data are shared by both sector estimates. -/

/-- With a positive Jacobi denominator at a real period, the affine slope and generator period
of a suffix factor are continuous there and have their expected real values. This supplies the
affine data for both sector estimates below. -/
private lemma wordFactor_affine_data (w : List ℤ) {τ₀ : ℝ}
    (hj : 0 < fltDenominator (letterWord w : Mat(2, ℤ)) τ₀) :
    ContinuousAt (fun τ : ℂ => (1 : ℂ) /
      fltDenominator (letterWord w : Mat(2, ℤ)) τ) (τ₀ : ℂ) ∧
    ContinuousAt (fun τ : ℂ => flt (letterWord w : Mat(2, ℤ)) τ) (τ₀ : ℂ) ∧
    (1 : ℂ) / fltDenominator (letterWord w : Mat(2, ℤ)) (τ₀ : ℂ) =
      (((fltDenominator (letterWord w : Mat(2, ℤ)) τ₀)⁻¹ : ℝ) : ℂ) ∧
    flt (letterWord w : Mat(2, ℤ)) (τ₀ : ℂ) =
      ((flt (letterWord w : Mat(2, ℤ)) τ₀ : ℝ) : ℂ) := by
  have hjC : fltDenominator (letterWord w : Mat(2, ℤ)) (τ₀ : ℂ) ≠ 0 := by
    exact_mod_cast hj.ne'
  refine ⟨continuousAt_const.div (fltDenominator_tendsto _ tendsto_id) hjC,
    flt_tendsto _ tendsto_id hjC, ?_, ?_⟩
  · simp only [← ofReal_fltDenominator, one_div, Complex.ofReal_inv]
  · exact (ofReal_flt _ _).symm

/-- The factor attached to a positive proper suffix is exponentially close to one in every
upper sector; used by `exists_norm_faddeevWord_sub_one_le`. -/
private lemma exists_wordFactor_sub_one_le (w : List ℤ) {τ₀ : ℝ}
    (hj : 0 < fltDenominator (letterWord w : Mat(2, ℤ)) τ₀)
    (hσ : 0 < flt (letterWord w : Mat(2, ℤ)) τ₀) (n : ℤ) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ τ z : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → |z.re| ≤ K * z.im → R ≤ z.im →
        ‖faddeevS (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n)
          (flt (letterWord w : Mat(2, ℤ)) τ) - 1‖ ≤
            C * Real.exp (-κ * z.im) := by
  obtain ⟨ha, ht, ha₀, ht₀⟩ := wordFactor_affine_data w hj
  obtain ⟨ε, C, κ, R, hε, hC, hκ, hR, hbound⟩ :=
    exists_norm_faddeevS_affine_sub_one_le
      (q₀ := (τ₀ : ℂ))
      (a := fun τ => (1 : ℂ) / fltDenominator (letterWord w : Mat(2, ℤ)) τ)
      (b := fun _ => -(n : ℂ))
      (t := fun τ => flt (letterWord w : Mat(2, ℤ)) τ)
      ha continuousAt_const ht ha₀ ht₀ (inv_pos.mpr hj) hσ K
  refine ⟨ε, C, κ, R, hε, hC, hκ, hR, fun τ z hτ hz hy => ?_⟩
  have harg : ((1 : ℂ) / fltDenominator (letterWord w : Mat(2, ℤ)) τ) * z +
      -(n : ℂ) = z / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n := by ring_nf
  simpa only [harg] using hbound τ z hτ hz hy

/-! ### Upper sectors -/

/-- **New.** Uniformly for complex periods near a real period with positive word periods, the
Faddeev word product tends exponentially to one in every upper sector: there are `ε, C, κ, R > 0`
with `‖Φ_{γ,m,n}(z;τ) - 1‖ ≤ C e^{-κ Im z}` for `|τ - τ₀| ≤ ε`, `|Re z| ≤ K Im z`, and
`Im z ≥ R`. This is the quantitative boundary-neighborhood extension of the upper clause of
[RW26, Radchenko, Wheeler (2026), Lemma 1, `lem:asymp`] along equation (20),
`eq:modulartofaddeevCF`. The neighborhood statement is absent from the searched [AFK25] and
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem exists_norm_faddeevWord_sub_one_le (bs : List ℤ) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (m n : ℤ) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ τ z : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → |z.re| ≤ K * z.im → R ≤ z.im →
        ‖faddeevWord bs m n z τ - 1‖ ≤ C * Real.exp (-κ * z.im) := by
  induction bs generalizing n with
  | nil =>
    refine ⟨1, 1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    intro τ z _ _ _
    simp only [faddeevWord, sub_self, norm_zero, one_mul]
    positivity
  | cons a w ih =>
    cases w with
    | nil =>
      have hbase : 0 < τ₀ := by
        simpa [letterWord_nil] using (hτ₀ [] (by simp)).2
      obtain ⟨ε, C, κ, R, hε, hC, hκ, hR, hbound⟩ :=
        exists_norm_faddeevS_affine_sub_one_le
          (q₀ := (τ₀ : ℂ)) (a := fun _ => 1)
          (b := fun τ => (m : ℂ) * τ - n) (t := id)
          continuousAt_const (by fun_prop) continuousAt_id rfl rfl
          (by norm_num) hbase K
      refine ⟨ε, C, κ, R, hε, hC, hκ, hR, fun τ z hτ hz hy => ?_⟩
      simpa only [faddeevWord_singleton, id_eq, one_mul, add_sub_assoc] using
        hbound τ z hτ hz hy
    | cons b w =>
      have hhead := hτ₀ (b :: w) (by simp)
      have htail : FaddeevWordPeriodsPos (b :: w) τ₀ :=
        forall_tail_tails_of_cons a (b :: w) hτ₀
      obtain ⟨ε₁, C₁, κ₁, R₁, hε₁, hC₁, hκ₁, hR₁, h₁⟩ :=
        exists_wordFactor_sub_one_le (b :: w) hhead.1 hhead.2 n K
      obtain ⟨ε₂, C₂, κ₂, R₂, hε₂, hC₂, hκ₂, hR₂, h₂⟩ :=
        ih htail 0
      refine ⟨min ε₁ ε₂, (1 + C₁) * C₂ + C₁, min κ₁ κ₂, max R₁ R₂,
        (by positivity), (by positivity), (by positivity), (by positivity), ?_⟩
      intro τ z hτ hz hy
      have hy0 : 0 ≤ z.im := by linarith [hR₁, (le_max_left R₁ R₂).trans hy]
      have hfirst := h₁ τ z (hτ.trans (min_le_left _ _)) hz
        ((le_max_left _ _).trans hy)
      have hrest := h₂ τ z (hτ.trans (min_le_right _ _)) hz
        ((le_max_right _ _).trans hy)
      simpa only [faddeevWord_cons_cons] using
        norm_mul_sub_one_le_of_exponential_bounds _ _ hκ₁.le hy0 hfirst hrest

/-! ### Lower sectors -/

/-- The reflected quadratic exponential of one Faddeev generator. This is the normalizer in
`exists_norm_faddeevWord_div_reflection_sub_one_le`. -/
private def wordFactorLowerNormalizer (x t : ℂ) : ℂ :=
  Complex.exp (-Real.pi * I *
    (x ^ 2 / t - (1 - t⁻¹) * x + (t + t⁻¹) / 6 - 1 / 2))

/-- The generator normalizer is the paired exponent of `WordReflection` at the negative
argument; used by the lower word estimate. -/
private lemma wordFactorLowerNormalizer_eq (x t : ℂ) :
    wordFactorLowerNormalizer x t =
      Complex.exp ((Real.pi : ℂ) * I * reflectionPairBracket (-x) t) := by
  unfold wordFactorLowerNormalizer reflectionPairBracket
  congr 1
  ring_nf

/-- The factor attached to a positive proper suffix has an exponentially accurate reflected
normalization in lower sectors; used by `exists_norm_faddeevWord_div_reflection_sub_one_le`. -/
private lemma exists_wordFactor_div_exp_sub_one_le (w : List ℤ) {τ₀ : ℝ}
    (hj : 0 < fltDenominator (letterWord w : Mat(2, ℤ)) τ₀)
    (hσ : 0 < flt (letterWord w : Mat(2, ℤ)) τ₀) (n : ℤ) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ τ z : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → |z.re| ≤ K * (-z.im) →
        R ≤ -z.im →
        ‖faddeevS (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n)
          (flt (letterWord w : Mat(2, ℤ)) τ) /
          wordFactorLowerNormalizer
            (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n)
            (flt (letterWord w : Mat(2, ℤ)) τ) - 1‖ ≤
              C * Real.exp (-κ * (-z.im)) := by
  obtain ⟨ha, ht, ha₀, ht₀⟩ := wordFactor_affine_data w hj
  obtain ⟨ε, C, κ, R, hε, hC, hκ, hR, hbound⟩ :=
    exists_norm_faddeevS_affine_div_exp_sub_one_le
      (q₀ := (τ₀ : ℂ))
      (a := fun τ => (1 : ℂ) / fltDenominator (letterWord w : Mat(2, ℤ)) τ)
      (b := fun _ => -(n : ℂ))
      (t := fun τ => flt (letterWord w : Mat(2, ℤ)) τ)
      ha continuousAt_const ht ha₀ ht₀ (inv_pos.mpr hj) hσ K
  refine ⟨ε, C, κ, R, hε, hC, hκ, hR, fun τ z hτ hz hy => ?_⟩
  have harg : ((1 : ℂ) / fltDenominator (letterWord w : Mat(2, ℤ)) τ) * z +
      -(n : ℂ) = z / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n := by ring_nf
  simpa only [harg, wordFactorLowerNormalizer] using hbound τ z hτ hz hy

/-- The lower asymptote in the statement of the word estimate, expressed through the
reflection kernel of `WordReflection`. -/
private def wordLowerAsymptote (bs : List ℤ) (m n : ℤ) (z τ : ℂ) : ℂ :=
  (-1 : ℂ) ^ (m + n) * reflectionWordKernel bs (-m) (-n) (-z) τ

/-- The one-factor normalizer equals the reflected word asymptote. -/
private lemma wordLowerAsymptote_singleton (a m n : ℤ) (z τ : ℂ) (hτ : τ ≠ 0) :
    wordFactorLowerNormalizer (z + m * τ - n) τ =
      wordLowerAsymptote [a] m n z τ := by
  have hp := reflectionSingleton_phase a (-m) (-n) (-z) τ hτ
  have harg : -z + (-m : ℤ) * τ - (-n : ℤ) = -(z + m * τ - n) := by
    push_cast
    ring_nf
  rw [harg] at hp
  have hsign : (-1 : ℂ) ^ (-m + -n) = (-1 : ℂ) ^ (m + n) := by
    have hs : -m + -n = -(m + n) := by ring_nf
    rw [hs, zpow_neg]
    simp only [neg_one_zpow_eq_ite]
    split_ifs <;> norm_num
  rw [hsign] at hp
  rw [wordFactorLowerNormalizer_eq]
  simpa [wordLowerAsymptote, reflectionWordKernel, mul_assoc] using hp

/-- Peeling the first letter multiplies the generator normalizer by the suffix asymptote. -/
private lemma wordLowerAsymptote_cons (a : ℤ) (w : List ℤ) (m n : ℤ) (z τ : ℂ)
    (hj : fltDenominator (letterWord w : Mat(2, ℤ)) τ ≠ 0)
    (hσ : flt (letterWord w : Mat(2, ℤ)) τ ≠ 0) :
    wordFactorLowerNormalizer
        (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n)
        (flt (letterWord w : Mat(2, ℤ)) τ) *
      wordLowerAsymptote w m 0 z τ = wordLowerAsymptote (a :: w) m n z τ := by
  have hp := reflectionCons_phase a w (-m) (-n) (-z) τ hj hσ
  have harg : (-z) / fltDenominator (letterWord w : Mat(2, ℤ)) τ - (-n : ℤ) =
      -(z / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n) := by
    push_cast
    ring_nf
  simp only [reflectionFirstPair, harg, ← wordFactorLowerNormalizer_eq] at hp
  simp only [wordLowerAsymptote, add_zero] at *
  have hsign : (-1 : ℂ) ^ (-n) = (-1 : ℂ) ^ n := by
    rw [neg_one_zpow_eq_ite, neg_one_zpow_eq_ite]
    simp
  rw [hsign] at hp
  calc
    _ = (-1 : ℂ) ^ m *
        (wordFactorLowerNormalizer
          (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n)
          (flt (letterWord w : Mat(2, ℤ)) τ) *
            reflectionWordKernel w (-m) 0 (-z) τ) := by ring_nf
    _ = (-1 : ℂ) ^ m * ((-1 : ℂ) ^ n *
          reflectionWordKernel (a :: w) (-m) (-n) (-z) τ) := by rw [hp]
    _ = _ := by rw [← mul_assoc, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]

/-- The normalized quotient of a nonempty word factors into the first normalized generator
and the normalized quotient of its suffix; used by the lower word estimate. -/
private lemma wordLowerQuotient_cons (a b : ℤ) (w : List ℤ) (m n : ℤ) (z τ : ℂ)
    (hj : fltDenominator (letterWord (b :: w) : Mat(2, ℤ)) τ ≠ 0)
    (hσ : flt (letterWord (b :: w) : Mat(2, ℤ)) τ ≠ 0) :
    faddeevWord (a :: b :: w) m n z τ /
        wordLowerAsymptote (a :: b :: w) m n z τ =
      (faddeevS
        (z / fltDenominator (letterWord (b :: w) : Mat(2, ℤ)) τ - n)
        (flt (letterWord (b :: w) : Mat(2, ℤ)) τ) /
          wordFactorLowerNormalizer
            (z / fltDenominator (letterWord (b :: w) : Mat(2, ℤ)) τ - n)
            (flt (letterWord (b :: w) : Mat(2, ℤ)) τ)) *
        (faddeevWord (b :: w) m 0 z τ /
          wordLowerAsymptote (b :: w) m 0 z τ) := by
  rw [faddeevWord_cons_cons, ← wordLowerAsymptote_cons a (b :: w) m n z τ hj hσ]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring_nf

/-- A positive real word period has a closed complex neighborhood on which all proper suffix
periods remain in the slit plane; used to apply `wordLowerAsymptote_cons`. -/
private lemma exists_wordPeriodsSlitPlane_radius (bs : List ℤ) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ δ →
      FaddeevWordPeriodsSlitPlane bs τ := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (eventually_faddeevWordPeriodsSlitPlane bs hτ₀.slitPlane)
  refine ⟨δ / 2, half_pos hδ, fun τ hτ => hball ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt hτ (half_lt_self hδ)

/-- The one-letter case of the lower word estimate, using the generator estimate and the
one-letter reflection phase. -/
private lemma exists_wordSingleton_div_asymptote_sub_one_le (a : ℤ) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos [a] τ₀) (m n : ℤ) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ τ z : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → |z.re| ≤ K * (-z.im) →
        R ≤ -z.im →
        ‖faddeevWord [a] m n z τ / wordLowerAsymptote [a] m n z τ - 1‖ ≤
          C * Real.exp (-κ * (-z.im)) := by
  have hbase : 0 < τ₀ := by
    simpa [letterWord_nil] using (hτ₀ [] (by simp)).2
  obtain ⟨ε₀, C, κ, R, hε₀, hC, hκ, hR, hbound⟩ :=
    exists_norm_faddeevS_affine_div_exp_sub_one_le
      (q₀ := (τ₀ : ℂ)) (a := fun _ => 1)
      (b := fun τ => (m : ℂ) * τ - n) (t := id)
      continuousAt_const (by fun_prop) continuousAt_id rfl rfl
      (by norm_num) hbase K
  obtain ⟨δ, hδ, hnear⟩ := exists_wordPeriodsSlitPlane_radius [a] hτ₀
  refine ⟨min ε₀ δ, C, κ, R, (by positivity), hC, hκ, hR, ?_⟩
  intro τ z hτ hz hy
  have hperiod := (faddeevWordPeriodsSlitPlane_singleton a τ).mp
    (hnear τ (hτ.trans (min_le_right _ _)))
  have hτne := Complex.slitPlane_ne_zero hperiod
  have hnorm := hbound τ z (hτ.trans (min_le_left _ _)) hz hy
  rw [faddeevWord_singleton, ← wordLowerAsymptote_singleton a m n z τ hτne]
  simpa only [wordFactorLowerNormalizer, id_eq, one_mul, add_sub_assoc] using hnorm

/-- The lower word estimate with its reflection asymptote abbreviated for the induction. -/
private lemma exists_norm_faddeevWord_div_asymptote_sub_one_le
    (bs : List ℤ) (hbs : bs ≠ []) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (m n : ℤ) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ τ z : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → |z.re| ≤ K * (-z.im) →
        R ≤ -z.im →
        ‖faddeevWord bs m n z τ / wordLowerAsymptote bs m n z τ - 1‖ ≤
          C * Real.exp (-κ * (-z.im)) := by
  induction bs generalizing n with
  | nil => exact (hbs rfl).elim
  | cons a w ih =>
    cases w with
    | nil =>
      exact exists_wordSingleton_div_asymptote_sub_one_le a hτ₀ m n K
    | cons b w =>
      have hhead := hτ₀ (b :: w) (by simp)
      have htail : FaddeevWordPeriodsPos (b :: w) τ₀ :=
        forall_tail_tails_of_cons a (b :: w) hτ₀
      obtain ⟨ε₁, C₁, κ₁, R₁, hε₁, hC₁, hκ₁, hR₁, h₁⟩ :=
        exists_wordFactor_div_exp_sub_one_le (b :: w) hhead.1 hhead.2 n K
      obtain ⟨ε₂, C₂, κ₂, R₂, hε₂, hC₂, hκ₂, hR₂, h₂⟩ :=
        ih (by simp) htail 0
      obtain ⟨δ, hδ, hnear⟩ :=
        exists_wordPeriodsSlitPlane_radius (a :: b :: w) hτ₀
      refine ⟨min δ (min ε₁ ε₂), (1 + C₁) * C₂ + C₁, min κ₁ κ₂,
        max R₁ R₂, (by positivity), (by positivity), (by positivity),
        (by positivity), ?_⟩
      intro τ z hτ hz hy
      obtain ⟨⟨hj, hσ⟩, _⟩ :=
        (faddeevWordPeriodsSlitPlane_cons_cons a b w τ).mp
          (hnear τ (hτ.trans (min_le_left _ _)))
      have hfirst := h₁ τ z (hτ.trans ((min_le_right _ _).trans (min_le_left _ _))) hz
        ((le_max_left _ _).trans hy)
      have hrest := h₂ τ z (hτ.trans ((min_le_right _ _).trans (min_le_right _ _))) hz
        ((le_max_right _ _).trans hy)
      have hy0 : 0 ≤ -z.im := by linarith [hR₁, (le_max_left R₁ R₂).trans hy]
      have hprod := norm_mul_sub_one_le_of_exponential_bounds _ _ hκ₁.le hy0
        hfirst hrest
      rw [wordLowerQuotient_cons a b w m n z τ hj (Complex.slitPlane_ne_zero hσ)]
      exact hprod

/-- **New.** Uniformly for complex periods near a real period with positive word periods, the
Faddeev word product divided by its reflection asymptote
`(-1)^{m+n} e(Q_{γ,-m,-n}(-z,τ)) κ_γ`, `κ_γ = exp(-πi(∑_j b_j - 3r)/6)`, tends exponentially to
one in every lower sector. This is the quantitative boundary-neighborhood extension of the lower
clause of [RW26, Radchenko, Wheeler (2026), Lemma 1, `lem:asymp`] for the word product of
equation (20), `eq:modulartofaddeevCF`, with the asymptote of Proposition 1,
`prop:reflection`. The neighborhood statement is absent from the searched [AFK25] and [RW26,
Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem exists_norm_faddeevWord_div_reflection_sub_one_le (bs : List ℤ) (hbs : bs ≠ [])
    {τ₀ : ℝ} (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (m n : ℤ) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ τ z : ℂ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → |z.re| ≤ K * (-z.im) → R ≤ -z.im →
        ‖faddeevWord bs m n z τ /
            ((-1 : ℂ) ^ (m + n) *
              Complex.exp (2 * Real.pi * I *
                faddeevReflectionExponent (letterWord bs) (-m) (-n) (-z) τ) *
              Complex.exp (-(Real.pi : ℂ) * I *
                (((bs.sum : ℤ) : ℂ) - 3 * bs.length) / 6)) - 1‖ ≤
          C * Real.exp (-κ * (-z.im)) := by
  simpa only [wordLowerAsymptote, reflectionWordKernel, ← mul_assoc] using
    exists_norm_faddeevWord_div_asymptote_sub_one_le bs hbs hτ₀ m n K

end SIC

end
