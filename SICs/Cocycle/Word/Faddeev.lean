/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.Word.Basic
import SICs.Cocycle.SigmaS.Faddeev
import SICs.SpecialFunctions.Faddeev.Word

/-!
# The word-chained cocycle as a reciprocal Faddeev word product

At a real point off the period lattices, the Faddeev word product of a letter word is the
reciprocal of the word-chained cocycle `wordSigmaS`, with the finite correction of the outer index.

This module compares [RW26, Radchenko, Wheeler (2026), Proposition 2(ii), `prop:prod.id.mod,fad`,
equation (20), `eq:modulartofaddeevCF`] at real periods with the real cocycle of
[AFK25, Definition 1.18, `def:shin`]: for `γ = ∏_{j=1}^r T^{b_j}S` with `b_j ≥ 2` for `j ≥ 2`,
$$\Phi_{\gamma,0,n}(z;\tau) = \Bigl(\sigma_\gamma(z,\tau)\big/\varpi_n\bigl(z/j_\gamma(\tau),
\gamma\cdot\tau\bigr)\Bigr)^{-1}.$$

## The argument

When the letters after the first are at least `2`, the ratio `γ₀₀/γ₁₀` of every tail lies in
`(b-1,b)` for its first letter `b`, so `hjStep` peels exactly one letter
(`hjStep_letterWord_cons`). Hence `wordSigmaS` along `γ` is the product of the factors
`σ_S(z/j_{γ_j}(τ), γ_j·τ)` over the tails `γ_j` of the word, the same arguments and periods as the
factors `Φ_{S,0,0}` of the word product. At each such factor the period is positive and the
argument avoids the lattice `ℤγ_j·τ + ℤ`, so `faddeevS_eq_inv_sigmaSHonest` identifies the two
factors. The outer index `n` shifts the first argument by `-n`; moving it out of `σ_S` inserts
`ϖ_n(z₁/τ₁, -1/τ₁)` with `τ₁ = γ'·τ` and `z₁ = z/j_{γ'}(τ)`. Since `-1/τ₁ = γ·τ - b₁` and
`z₁/τ₁ = z/j_γ(τ)`, integer periodicity of the finite product in its period gives
`ϖ_n(z/j_γ(τ), γ·τ)`.

Positivity of the word periods is the positivity of the periods `wordSigmaS` visits: the visited
matrices are the letter words of the proper tails, and `WordSigmaSVisits.period_pos` makes their
periods positive once `j_γ(τ) > 0`.

At the literal origin every factor is in the base chamber of `σ_S`, and the comparison uses
`faddeevS_eq_inv_sigmaSBase` instead.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The visited matrices of a letter word

`wordSigmaS` along a letter word peels one letter per step, so it visits the letter words of the
proper tails, and their periods are positive. -/

/-- The matrices `wordSigmaS` visits from a nonempty letter word, whose letters after the first
are at least `2`, include the letter words of all proper tails. -/
theorem wordSigmaSVisits_letterWord {bs : List ℤ} (hne : bs ≠ [])
    (hbs : ∀ b ∈ bs.tail, 2 ≤ b) :
    ∀ w ∈ bs.tail.tails, WordSigmaSVisits (letterWord bs) (letterWord w) := by
  induction bs with
  | nil => exact (hne rfl).elim
  | cons a bs ih =>
      intro w hw
      simp only [List.tail_cons] at hw hbs
      have hstep : WordSigmaSVisits (letterWord (a :: bs)) (letterWord bs) := by
        have hz := (letterWord_lowerLeft_pos a hbs).ne'
        simpa only [hjStep_letterWord_cons a hbs] using WordSigmaSVisits.base hz
      cases bs with
      | nil =>
          have hweq : w = [] := by simpa [List.tails] using hw
          subst w
          exact hstep
      | cons b cs =>
          rw [List.tails_cons] at hw
          rcases List.mem_cons.mp hw with hw | hw
          · subst w
            exact hstep
          · have htail : ∀ x ∈ (b :: cs).tail, 2 ≤ x :=
              fun x hx => hbs x (List.mem_cons_of_mem _ hx)
            exact hstep.trans (ih (by simp) htail w hw)

/-- At an irrational real point with `j_γ(τ) > 0`, every word period `γ_j·τ` of a letter word
`γ` whose letters after the first are at least `2` is positive. These are the hypotheses of
`faddeevWordPeriodsSlitPlane_of_irrational`. -/
theorem flt_letterWord_pos_of_mem_tails {bs : List ℤ} (hne : bs ≠ [])
    (hbs : ∀ b ∈ bs.tail, 2 ≤ b) {τ : ℝ} (hτ : Irrational τ)
    (hjac : 0 < fltDenominator (letterWord bs : Mat(2, ℤ)) τ) :
    ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ := by
  intro w hw
  exact (WordSigmaSVisits.period_pos τ hτ (letterWord_lowerLeft_nonneg hbs) hjac
    (wordSigmaSVisits_letterWord hne hbs w hw)).1

/-- `wordSigmaS` peels the first letter of a letter word whose remaining letters are at least `2`:
`σ_{T^aSγ'}(z,τ) = σ_S(z/j_{γ'}(τ), γ'·τ) σ_{γ'}(z,τ)`. -/
theorem wordSigmaS_letterWord_cons (z τ : ℝ) (a : ℤ) {bs : List ℤ} (hbs : ∀ b ∈ bs, 2 ≤ b)
    (h0 : 0 ≤ letterWord (a :: bs) 1 0) (h0' : 0 ≤ letterWord bs 1 0) :
    wordSigmaS z τ (letterWord (a :: bs)) h0 =
      sigmaSHonest (z / fltDenominator (letterWord bs : Mat(2, ℤ)) τ)
          (flt (letterWord bs : Mat(2, ℤ)) τ) *
        wordSigmaS z τ (letterWord bs) h0' := by
  exact wordSigmaS_step z τ h0 (letterWord_lowerLeft_pos a hbs).ne'
    (congrArg Prod.snd (hjStep_letterWord_cons a hbs)) h0'

/-! ### Comparison with the word product

Off the lattices every factor of the word product is the reciprocal `σ_S` factor; the outer index
contributes the finite product, and the origin is compared in the base chamber. -/

/-- A factorwise reciprocal identity gives the zero-index word comparison used by
`faddeevWord_ofReal_eq_inv_wordSigmaS` and `faddeevWord_zero_eq_inv_wordSigmaS`. -/
private lemma faddeevWord_zeroIndex_of_factors (bs : List ℤ) (hne : bs ≠ [])
    (hbs : ∀ b ∈ bs.tail, 2 ≤ b) {z τ : ℝ}
    (hfactors : ∀ w ∈ bs.tail.tails,
      faddeevS ((z : ℂ) / fltDenominator (letterWord w : Mat(2, ℤ)) (τ : ℂ))
        (flt (letterWord w : Mat(2, ℤ)) (τ : ℂ)) =
        (sigmaSHonest (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ)
          (flt (letterWord w : Mat(2, ℤ)) τ))⁻¹)
    (h0 : 0 ≤ letterWord bs 1 0) :
    faddeevWord bs 0 0 z τ = (wordSigmaS z τ (letterWord bs) h0)⁻¹ := by
  induction bs with
  | nil => exact (hne rfl).elim
  | cons a bs ih =>
      cases bs with
      | nil =>
          have hS := hfactors [] (by simp [List.tails])
          have h0' : 0 ≤ letterWord [] 1 0 := by simp [letterWord_nil]
          have hword : wordSigmaS z τ (letterWord [a]) h0 = sigmaSHonest z τ := by
            rw [wordSigmaS_letterWord_cons z τ a (by simp) h0 h0',
              wordSigmaS_of_lowerLeft_eq_zero z τ (letterWord []) h0'
                (by simp [letterWord_nil])]
            simp [letterWord_nil, flt_one, fltDenominator_one]
          rw [hword]
          simpa [faddeevWord_singleton, letterWord_nil, flt_one, fltDenominator_one]
            using hS
      | cons b cs =>
          have hbs' : ∀ x ∈ (b :: cs).tail, 2 ≤ x :=
            fun x hx => hbs x (by simp only [List.tail_cons]; exact List.mem_cons_of_mem _ hx)
          have h0' : 0 ≤ letterWord (b :: cs) 1 0 := letterWord_lowerLeft_nonneg hbs'
          have hS := hfactors (b :: cs) (by simp [List.tails])
          have hfactor' : ∀ w ∈ (b :: cs).tail.tails,
              faddeevS ((z : ℂ) / fltDenominator (letterWord w : Mat(2, ℤ)) (τ : ℂ))
                (flt (letterWord w : Mat(2, ℤ)) (τ : ℂ)) =
                (sigmaSHonest (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ)
                  (flt (letterWord w : Mat(2, ℤ)) τ))⁻¹ :=
            forall_tail_tails_of_cons a (b :: cs) hfactors
          rw [faddeevWord_cons_cons,
            wordSigmaS_letterWord_cons z τ a (by
              intro x hx
              exact hbs x (by simpa using hx)) h0 h0',
            Int.cast_zero, sub_zero, hS, ih (by simp) hbs' hfactor' h0']
          simp only [mul_inv_rev]
          ring

/-- The lattice-free factor identity supplies the word comparison before the outer shift. -/
private lemma faddeevWord_zeroIndex_eq_inv_wordSigmaS (bs : List ℤ) (hne : bs ≠ [])
    (hbs : ∀ b ∈ bs.tail, 2 ≤ b) {z τ : ℝ}
    (hpos : ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ)
    (hlat : ∀ w ∈ bs.tail.tails, SigmaSLatticeFree (flt (letterWord w : Mat(2, ℤ)) τ)
      (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ))
    (h0 : 0 ≤ letterWord bs 1 0) :
    faddeevWord bs 0 0 z τ = (wordSigmaS z τ (letterWord bs) h0)⁻¹ := by
  apply faddeevWord_zeroIndex_of_factors bs hne hbs (h0 := h0)
  intro w hw
  simpa only [Complex.ofReal_div, ofReal_flt, ofReal_fltDenominator] using
    (faddeevS_eq_inv_sigmaSHonest
      (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ)
      (flt (letterWord w : Mat(2, ℤ)) τ) (hpos w hw) (hlat w hw))

/-- Moving an integer shift out of the first Faddeev factor in
`faddeevWord_ofReal_eq_inv_wordSigmaS`. -/
private lemma faddeevS_sub_int (w ν : ℝ) (n : ℤ) (hν : 0 < ν)
    (hlat : SigmaSLatticeFree ν w) :
    faddeevS ((w : ℂ) - n) ν =
      qPochhammerFin n ((w : ℂ) / (ν : ℂ)) (-1 / (ν : ℂ)) * faddeevS w ν := by
  have hlat' : SigmaSLatticeFree ν (w - n) := by
    simpa [sub_eq_add_neg] using hlat.add 0 (-n)
  have hF := faddeevS_eq_inv_sigmaSHonest w ν hν hlat
  have hF' := faddeevS_eq_inv_sigmaSHonest (w - n) ν hν hlat'
  have hq : qPochhammerFin n ((w : ℂ) / (ν : ℂ)) (-1 / (ν : ℂ)) ≠ 0 :=
    qPochhammerFin_ne_zero_of_forall_factor_ne_zero _ _ _
      (one_sub_exp_dual_ne_zero hν hlat)
  have hshift : sigmaSHonest (w - n) ν *
      qPochhammerFin n ((w : ℂ) / (ν : ℂ)) (-1 / (ν : ℂ)) =
        sigmaSHonest w ν := by
    simpa [qPochhammerFin, sub_eq_add_neg] using
      (sigmaSHonest_lattice_shift w ν 0 (-n) hν hlat)
  calc
    faddeevS ((w : ℂ) - n) ν = (sigmaSHonest (w - n) ν)⁻¹ := by
      simpa only [Complex.ofReal_sub, Complex.ofReal_intCast] using hF'
    _ = qPochhammerFin n ((w : ℂ) / (ν : ℂ)) (-1 / (ν : ℂ)) *
          (sigmaSHonest w ν)⁻¹ := by
      rw [← hshift, mul_inv_rev]
      simp [hq]
    _ = _ := by rw [hF]

/-- The dual period and transported argument of the first Faddeev factor are those
of the whole letter word, up to an integer period shift. Used by
`faddeevWord_ofReal_eq_inv_wordSigmaS`. -/
private lemma qPochhammerFin_letterWord_period (a : ℤ) (bs : List ℤ)
    (n : ℤ) (z τ : ℝ)
    (hν : 0 < flt (letterWord bs : Mat(2, ℤ)) τ) :
    qPochhammerFin n
        (((z / fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℝ) : ℂ) /
          (flt (letterWord bs : Mat(2, ℤ)) τ : ℂ))
        (-1 / (flt (letterWord bs : Mat(2, ℤ)) τ : ℂ)) =
      qPochhammerFin n
        ((z : ℂ) / (fltDenominator (letterWord (a :: bs) : Mat(2, ℤ)) τ : ℂ))
        (flt (letterWord (a :: bs) : Mat(2, ℤ)) τ : ℂ) := by
  let ν := flt (letterWord bs : Mat(2, ℤ)) τ
  let J := fltDenominator (letterWord bs : Mat(2, ℤ)) τ
  change 0 < ν at hν
  have hJ : J ≠ 0 := by
    intro hz
    have hflt : ν = ((letterWord bs 0 0 : ℝ) * τ + (letterWord bs 0 1 : ℝ)) / J := rfl
    rw [hflt, hz] at hν
    simp at hν
  have hνC : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have hJC : (J : ℂ) ≠ 0 := by exact_mod_cast hJ
  have hper := flt_letterWord_cons a bs hJ hν.ne'
  have hjac := fltDenominator_letterWord_cons a bs hJ
  have hperC : (flt (letterWord (a :: bs) : Mat(2, ℤ)) τ : ℂ) =
      (a : ℂ) - 1 / (ν : ℂ) := by exact_mod_cast hper
  have hjacC : (fltDenominator (letterWord (a :: bs) : Mat(2, ℤ)) τ : ℂ) =
      (ν : ℂ) * (J : ℂ) := by exact_mod_cast hjac
  have harg : (((z / J : ℝ) : ℂ) / (ν : ℂ)) =
      (z : ℂ) / (fltDenominator (letterWord (a :: bs) : Mat(2, ℤ)) τ : ℂ) := by
    rw [Complex.ofReal_div, hjacC]
    field_simp
  have hperiod : (-1 / (ν : ℂ)) =
      (flt (letterWord (a :: bs) : Mat(2, ℤ)) τ : ℂ) + ((-a : ℤ) : ℂ) := by
    rw [hperC]
    push_cast
    ring
  simp only [← ofReal_flt, ← ofReal_fltDenominator] at harg hperiod ⊢
  rw [harg, hperiod]
  exact qPochhammerFin_tau_add_intCast n _ _ (-a)

/-- The outer index changes only the first factor of a Faddeev word. Its finite
factor is expressed at the period and Jacobi denominator of the whole word. -/
private lemma faddeevWord_outer_index (bs : List ℤ) (hne : bs ≠ []) (n : ℤ)
    {z τ : ℝ}
    (hpos : ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ)
    (hlat : ∀ w ∈ bs.tail.tails, SigmaSLatticeFree (flt (letterWord w : Mat(2, ℤ)) τ)
      (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ)) :
    faddeevWord bs 0 n z τ =
      qPochhammerFin n ((z : ℂ) /
        (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ))
        (flt (letterWord bs : Mat(2, ℤ)) τ : ℂ) *
        faddeevWord bs 0 0 z τ := by
  cases bs with
  | nil => exact (hne rfl).elim
  | cons a bs =>
      cases bs with
      | nil =>
          have hν : 0 < flt (letterWord [] : Mat(2, ℤ)) τ :=
            hpos [] (by simp [List.tails])
          have hlat0 : SigmaSLatticeFree
              (flt (letterWord [] : Mat(2, ℤ)) τ)
              (z / fltDenominator (letterWord [] : Mat(2, ℤ)) τ) :=
            hlat [] (by simp [List.tails])
          have hshift := faddeevS_sub_int z τ n
            (by simpa [letterWord_nil, flt_one] using hν)
            (by simpa [letterWord_nil, flt_one, fltDenominator_one] using hlat0)
          have hq := qPochhammerFin_letterWord_period a [] n z τ hν
          rw [faddeevWord_singleton, faddeevWord_singleton]
          simp only [Int.cast_zero, zero_mul, add_zero, sub_zero]
          rw [hshift]
          simpa [letterWord_nil, flt_one, fltDenominator_one] using
            congrArg (fun q : ℂ => q * faddeevS z τ) hq
      | cons b cs =>
          let w := z / fltDenominator (letterWord (b :: cs) : Mat(2, ℤ)) τ
          let ν := flt (letterWord (b :: cs) : Mat(2, ℤ)) τ
          have hν : 0 < ν := hpos (b :: cs) (by simp [List.tails])
          have hlat0 : SigmaSLatticeFree ν w :=
            hlat (b :: cs) (by simp [List.tails])
          have hshift := faddeevS_sub_int w ν n hν hlat0
          have hq := qPochhammerFin_letterWord_period a (b :: cs) n z τ hν
          rw [faddeevWord_cons_cons, faddeevWord_cons_cons]
          simp only [Int.cast_zero, sub_zero]
          dsimp [w, ν] at hshift
          simp only [Complex.ofReal_div] at hshift
          simp only [← ofReal_flt, ← ofReal_fltDenominator] at hshift hq ⊢
          simp only [Complex.ofReal_div] at hq
          rw [hshift, hq]
          ring

/-- At a real point whose word arguments `z/j_{γ_j}(τ)` avoid the lattices `ℤγ_j·τ + ℤ` and whose
word periods are positive, `Φ_{γ,0,n}(z;τ) = (σ_γ(z,τ)/ϖ_n(z/j_γ(τ), γ·τ))⁻¹` for
`γ = ∏_j T^{b_j}S`. This is [RW26, Radchenko, Wheeler (2026), Proposition 2(ii),
`prop:prod.id.mod,fad`, equation (20), `eq:modulartofaddeevCF`] at real periods, read through
[AFK25, Definition 1.18, `def:shin`]. -/
theorem faddeevWord_ofReal_eq_inv_wordSigmaS (bs : List ℤ) (hne : bs ≠ [])
    (hbs : ∀ b ∈ bs.tail, 2 ≤ b) (n : ℤ) {z τ : ℝ}
    (hpos : ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ)
    (hlat : ∀ w ∈ bs.tail.tails, SigmaSLatticeFree (flt (letterWord w : Mat(2, ℤ)) τ)
      (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ))
    (h0 : 0 ≤ letterWord bs 1 0) :
    faddeevWord bs 0 n z τ =
      (wordSigmaS z τ (letterWord bs) h0 /
        qPochhammerFin n ((z : ℂ) / (fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℂ))
          (flt (letterWord bs : Mat(2, ℤ)) τ : ℂ))⁻¹ := by
  rw [faddeevWord_outer_index bs hne n hpos hlat,
    faddeevWord_zeroIndex_eq_inv_wordSigmaS bs hne hbs hpos hlat h0]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]

/-- At the origin and positive word periods, `Φ_{γ,0,0}(0;τ) = σ_γ(0,τ)⁻¹`. This is the origin
case of `faddeevWord_ofReal_eq_inv_wordSigmaS`, where every factor is in the base chamber. -/
theorem faddeevWord_zero_eq_inv_wordSigmaS (bs : List ℤ) (hne : bs ≠ [])
    (hbs : ∀ b ∈ bs.tail, 2 ≤ b) {τ : ℝ}
    (hpos : ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ)
    (h0 : 0 ≤ letterWord bs 1 0) :
    faddeevWord bs 0 0 0 τ = (wordSigmaS 0 τ (letterWord bs) h0)⁻¹ := by
  apply faddeevWord_zeroIndex_of_factors bs hne hbs (h0 := h0)
  intro w hw
  have hν := hpos w hw
  have hS := faddeevS_eq_inv_sigmaSBase 0
    (flt (letterWord w : Mat(2, ℤ)) τ) hν (by norm_num) hν
  simpa only [zero_div, Complex.ofReal_zero, ofReal_flt, sigmaSHonest_zero] using hS

end SIC

end
