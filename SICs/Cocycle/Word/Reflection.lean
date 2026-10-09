/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.WordAccumulator
import SICs.Cocycle.Word.Shifts
import SICs.Cocycle.SigmaS.Reflection

/-!
# The reflection law for the word-chained `σ_M`

The telescoping reflection law for `wordSigmaS` and its accumulated exponential.

This file proves how the word-chained cocycle `SICs.Cocycle.Word.Basic.wordSigmaS` responds to
negating
its first argument. It is the analytic half of the reciprocity identity
`ν̃_t(p)·ν̃_t(-p) = 1` of [AFK25, Theorem 5.8, `thm:nupnumpeq1`]; the phase half is the evenness
`SIC.AdmissibleTuple.sfPhase_neg` in `SICs.Ghost.CandidateOverlaps`.

## The identity, and why it telescopes

Write `E(x) = e^{-2πi x}` and `j_M(τ)` for the Jacobi denominator. The result
(`wordSigmaS_mul_neg`) is

```text
σ_M(z,τ) · σ_M(-z,τ) · (1 - E(z)) = (1 - E(z / j_M(τ))) · exp(2·X_M(z,τ)),
```

with `X_M` the sum of the one-letter exponential arguments `sfExpArg` along the word
(`wordSfExpArg`). No hypothesis of nonvanishing appears, because the identity is stated
multiplicatively.

The proof is an induction along `wordSigmaS`'s own Hirzebruch--Jung recursion. Two facts make it
telescope. First, `z` and `-z` walk the *same* word: `wordSigmaS`'s recursion peels letters off the
matrix only, so negating the argument negates each letter's argument and nothing else. Second, the
single-letter law
`SICs.Cocycle.SigmaS.Reflection.sigmaSHonest_mul_neg_closed` contributes, at the step whose reduced
matrix is `N`,

```text
σ_S(w,ν)·σ_S(-w,ν) = (1 - E(w/ν)) / (1 - E(w)) · exp(2·X(w,ν)),
      w = z / j_N(τ),   ν = N·τ,
```

and `w/ν = z / j_M(τ)` exactly, because `j_M(τ) = (N·τ)·j_N(τ)`
(`SICs.SL2Z.WordPeriods.fltDenominator_hjStep`). So each step's numerator is the
previous step's denominator, the chain collapses to its two ends, and the terminal matrix `T^k` --
where `j_{T^k}(τ) = 1` and the word contributes nothing -- supplies the remaining factor `1 - E(z)`.

Positivity `0 < j_M(τ)` is used only at that terminal matrix, exactly as in
`SICs.Cocycle.Word.Shifts.wordSigmaS_lattice_shift`: it rules out `-T^k`, at which `wordSigmaS`'s
base value `1` would be wrong.

## What this is not

This is the reflection at a *fixed* matrix, `z ↦ -z` with `M` unchanged. It is not the
`GL₂(ℤ)` conjugation law [72, Kopp (2024), Theorem 4.37, `thm:shinconj`], where two different
matrices produce two different words.

## Main declarations

- `wordSfExpArg`: the exponential argument accumulated along the word.
- `wordSigmaS_mul_neg`: the reflection identity above.
- `wordSfExpArg_eq`: the accumulated argument in closed form, and
  `norm_exp_two_wordSfExpArg_of_flt_eq_self`: at a fixed point its exponential is a phase.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Theorem 5.8 (`thm:nupnumpeq1`)
- [72] G. S. Kopp, "The Shintani--Faddeev modular cocycle: Stark units from q-Pochhammer
  ratios," arXiv:2411.06763v3, Theorem 4.36 (`thm:shincharacter`)
-/

open ModularGroup MatrixGroups

open scoped MatrixGroups

namespace SIC

/-! ### The word-accumulated exponential argument

`sigmaSHonest`'s reflection law produces one exponential factor per letter. Summing those
arguments along the same recursion `wordSigmaS` walks gives the single exponential appearing in
the word-level law. -/

/-- **The exponential argument accumulated along the Hirzebruch--Jung word.** Mirrors
`SICs.Cocycle.Word.Basic.wordSigmaS` step for step, replacing each letter's `σ_S` factor by the
argument `X(z/j_{M'}(τ), M'·τ)` of `SICs.Cocycle.SigmaS.Basic.sfExpArg` that the letter's
reflection law contributes, and the base value `1` by `0`. It exists to state
`wordSigmaS_mul_neg`. -/
noncomputable def wordSfExpArg (z τ : ℝ) : (M : SL(2, ℤ)) → 0 ≤ M 1 0 → ℂ
  | M, h0 =>
    if hz : M 1 0 = 0 then
      0
    else
      have hpos : 0 < M 1 0 := h0.lt_of_ne (Ne.symm hz)
      have h0' : 0 ≤ (hjStep M).2 1 0 := by
        rw [hjStep_snd_lowerLeft]; exact Int.emod_nonneg _ hpos.ne'
      have hlt : (hjStep M).2 1 0 < M 1 0 := by
        rw [hjStep_snd_lowerLeft]; exact Int.emod_lt_of_pos _ hpos
      sfExpArg (z / fltDenominator ((hjStep M).2 : Mat(2, ℤ)) τ)
          (flt ((hjStep M).2 : Mat(2, ℤ)) τ)
        + wordSfExpArg z τ (hjStep M).2 h0'
termination_by M _ => M 1 0 |>.toNat
decreasing_by omega

/-- **Base case**: at a pure `T`-power the word is empty, so it accumulates no exponential
argument. -/
theorem wordSfExpArg_of_lowerLeft_eq_zero (z τ : ℝ) (M : SL(2, ℤ)) (h0 : 0 ≤ M 1 0)
    (hz : M 1 0 = 0) : wordSfExpArg z τ M h0 = 0 := by
  rw [wordSfExpArg, dite_eq_left hz]

/-- **Recursive step**, with the reduced matrix supplied by the caller, matching
`SICs.Cocycle.Word.Basic.wordSigmaS_step`. -/
theorem wordSfExpArg_step (z τ : ℝ) {M N : SL(2, ℤ)} (h0 : 0 ≤ M 1 0) (hz : M 1 0 ≠ 0)
    (hN : (hjStep M).2 = N) (h0N : 0 ≤ N 1 0) :
    wordSfExpArg z τ M h0 =
      sfExpArg (z / fltDenominator (N : Mat(2, ℤ)) τ)
          (flt (N : Mat(2, ℤ)) τ)
        + wordSfExpArg z τ N h0N := by
  subst hN
  rw [wordSfExpArg, dite_eq_right hz]

/-! ### The reflection law

The induction follows `wordSigmaS`'s recursion on the lower-left entry, exactly as in
`SICs.Cocycle.Word.Shifts`. The base case is where `0 < j_M(τ)` is used. -/

/-- **The base case of `wordSigmaS_mul_neg`.** At a pure `T`-power, positivity of the Jacobi
denominator forces `M₁₁ = M₀₀ = 1`, hence `j_M(τ) = 1`; both `wordSigmaS` values are `1` and the
word accumulates no exponential argument, so the identity reads `1 - E(z) = 1 - E(z/1)`. -/
private lemma wordSigmaS_mul_neg_base {τ : ℝ} (z : ℝ) (M : SL(2, ℤ)) (h0 : 0 ≤ M 1 0)
    (hz : M 1 0 = 0) (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ) :
    wordSigmaS z τ M h0 * wordSigmaS (-z) τ M h0 *
        (1 - Complex.exp (-(2 * Real.pi * Complex.I * (z : ℂ)))) =
      (1 - Complex.exp (-(2 * Real.pi * Complex.I *
          ((z : ℂ) / ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ))))) *
        Complex.exp (2 * wordSfExpArg z τ M h0) := by
  rw [wordSigmaS_of_lowerLeft_eq_zero _ _ _ _ hz, wordSigmaS_of_lowerLeft_eq_zero _ _ _ _ hz,
    wordSfExpArg_of_lowerLeft_eq_zero _ _ _ _ hz,
    fltDenominator_eq_one_of_lowerLeft_eq_zero hz hjac]
  simp

/-- The reflection identity for one letter, with its numerator transported to the whole
word; used by `wordSigmaS_mul_neg_step`. -/
private lemma wordSigmaS_mul_neg_letter {τ : ℝ} (hτ : Irrational τ) (z : ℝ)
    (hlat : SigmaSLatticeFree τ z) {M N : SL(2, ℤ)} (hN : (hjStep M).2 = N)
    (hpos : 0 < M 1 0) (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ) :
    let w := z / fltDenominator (N : Mat(2, ℤ)) τ
    let ν := flt (N : Mat(2, ℤ)) τ
    sigmaSHonest w ν * sigmaSHonest (-w) ν *
        (1 - Complex.exp (-(2 * Real.pi * Complex.I * (w : ℂ)))) =
      (1 - Complex.exp (-(2 * Real.pi * Complex.I *
        ((z : ℂ) / ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ))))) *
        Complex.exp (2 * sfExpArg w ν) := by
  obtain ⟨hνpos, hJpos⟩ := flt_and_fltDenominator_pos_of_hjStep M τ hτ hpos hjac
  rw [hN] at hνpos hJpos
  have hJ0 : fltDenominator (N : Mat(2, ℤ)) τ ≠ 0 := hJpos.ne'
  have hMden : fltDenominator (M : Mat(2, ℤ)) τ =
      flt (N : Mat(2, ℤ)) τ *
        fltDenominator (N : Mat(2, ℤ)) τ := by
    rw [← hN]; exact fltDenominator_hjStep M τ hτ
  set w : ℝ := z / fltDenominator (N : Mat(2, ℤ)) τ with hw
  set ν : ℝ := flt (N : Mat(2, ℤ)) τ with hν
  have hlatw : SigmaSLatticeFree ν w := hlat.div_fltDenominator hJ0
  have hne : (1 : ℂ) - Complex.exp (-(2 * Real.pi * Complex.I * (w : ℂ))) ≠ 0 := by
    have h := one_sub_exp_two_pi_I_ne_zero_of_forall_ne_int (-w) fun m hm =>
      hlatw.ne_intCast (-m) (by push_cast; linarith)
    rw [show (2 : ℂ) * Real.pi * Complex.I * ((-w : ℝ) : ℂ) =
        -(2 * Real.pi * Complex.I * (w : ℂ)) from by push_cast; ring] at h
    exact h
  have hstep := sigmaSHonest_mul_neg_closed w ν hνpos hlatw
  rw [div_mul_eq_mul_div, eq_div_iff hne] at hstep
  have hquot : ((w : ℝ) : ℂ) / ((ν : ℝ) : ℂ) =
      (z : ℂ) / ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) := by
    simp [hw, hMden, div_div, mul_comm]
  rw [hquot] at hstep
  exact hstep

/-- Multiplies the single-letter reflection law by the remaining word's law; used by
`wordSigmaS_mul_neg`. -/
private lemma wordSigmaS_mul_neg_step {τ : ℝ} (hτ : Irrational τ) (z : ℝ)
    (hlat : SigmaSLatticeFree τ z) {M N : SL(2, ℤ)} (h0 : 0 ≤ M 1 0)
    (hz : M 1 0 ≠ 0) (hN : (hjStep M).2 = N) (h0N : 0 ≤ N 1 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hih :
    wordSigmaS z τ N h0N * wordSigmaS (-z) τ N h0N *
        (1 - Complex.exp (-(2 * Real.pi * Complex.I * (z : ℂ)))) =
      (1 - Complex.exp (-(2 * Real.pi * Complex.I *
          ((z : ℂ) / ((fltDenominator (N : Mat(2, ℤ)) τ : ℝ) : ℂ))))) *
        Complex.exp (2 * wordSfExpArg z τ N h0N)) :
    wordSigmaS z τ M h0 * wordSigmaS (-z) τ M h0 *
        (1 - Complex.exp (-(2 * Real.pi * Complex.I * (z : ℂ)))) =
      (1 - Complex.exp (-(2 * Real.pi * Complex.I *
          ((z : ℂ) / ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ))))) *
        Complex.exp (2 * wordSfExpArg z τ M h0) := by
  have hstep := wordSigmaS_mul_neg_letter hτ z hlat hN (h0.lt_of_ne (Ne.symm hz)) hjac
  dsimp only at hstep
  rw [wordSigmaS_step z τ h0 hz hN h0N, wordSigmaS_step (-z) τ h0 hz hN h0N,
    wordSfExpArg_step z τ h0 hz hN h0N, neg_div, mul_add, Complex.exp_add]
  simp only [Complex.ofReal_div] at hstep
  linear_combination
    (sigmaSHonest (z / fltDenominator (N : Mat(2, ℤ)) τ)
      (flt (N : Mat(2, ℤ)) τ) *
    sigmaSHonest (-(z / fltDenominator (N : Mat(2, ℤ)) τ))
      (flt (N : Mat(2, ℤ)) τ)) * hih +
    Complex.exp (2 * wordSfExpArg z τ N h0N) * hstep

/-- **The reflection law for the word-chained `σ_M`.** For `z` off the lattice `ℤτ + ℤ` and `τ` in
`M`'s real domain,

```text
σ_M(z,τ) · σ_M(-z,τ) · (1 - e^{-2πi z}) = (1 - e^{-2πi z/j_M(τ)}) · exp(2·X_M(z,τ)),
```

where `X_M` is the word-accumulated `wordSfExpArg`. This is the real-line form of the
functional equation behind [72, Kopp (2024), Theorem 4.36, `thm:shincharacter`], and the analytic
input to the reciprocity identity [AFK25, Theorem 5.8, `thm:nupnumpeq1`]. It is stated
multiplicatively, so no nonvanishing hypothesis is needed.

The hypotheses are the word walk's standing ones, as in
`SICs.Cocycle.Word.Shifts.wordSigmaS_lattice_shift`: `hlat` is [AFK25, Theorem 5.8,
`thm:nupnumpeq1`]'s `p ≢ 0 (mod d)` in disguise (see `SICs.Cocycle.Modular.Values`), and `hjac` is
`τ ∈ D_M`. -/
theorem wordSigmaS_mul_neg {τ : ℝ} (hτ : Irrational τ) (z : ℝ)
    (hlat : SigmaSLatticeFree τ z) (M : SL(2, ℤ)) (h0 : 0 ≤ M 1 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ) :
    wordSigmaS z τ M h0 * wordSigmaS (-z) τ M h0 *
        (1 - Complex.exp (-(2 * Real.pi * Complex.I * (z : ℂ)))) =
      (1 - Complex.exp (-(2 * Real.pi * Complex.I *
          ((z : ℂ) / ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ))))) *
        Complex.exp (2 * wordSfExpArg z τ M h0) := by
  induction M, h0 using wordSigmaS.induct with
  | case1 M h0 hz _ => exact wordSigmaS_mul_neg_base z M h0 hz hjac
  | case2 M h0 hz hpos h0N _ _ ih =>
      have hJpos := (flt_and_fltDenominator_pos_of_hjStep M τ hτ hpos hjac).2
      exact wordSigmaS_mul_neg_step hτ z hlat h0 hz rfl h0N hjac (ih hJpos)


/-! ### The closed form of the accumulated exponential

The sum defining `wordSfExpArg` telescopes completely. Splitting `sfExpArg` into its three parts,

```text
2·X(w,ν) = πi·w²/ν + πi·(1/ν - 1)·w + (πi/6)·(ν + 1/ν - 3),
```

each part sums along the word for its own reason, using only `j_M(τ) = (N·τ)·j_N(τ)`,
`M·τ = r - 1/(N·τ)`, and that `N`'s top row is `M`'s bottom row:

- the `w²` terms have `w_i²/ν_i = z²/(j_{i-1}j_i)`, and `det N = 1` makes `-N₁₀/j_i` a discrete
  antiderivative of that, so the sum collapses to `M₁₀z²/j_M(τ)`;
- the `w` terms have `1/(ν_i j_i) = 1/j_{i-1}`, so the sum telescopes to `1/j_M(τ) - 1`;
- the constant terms have `1/ν_i = r_i - ν_{i-1}`, so the sum telescopes to `τ - M·τ`, plus
  `Σ(r_i - 3)` and the terminal exponent, namely `SICs.SL2Z.WordAccumulator.wordRademacher`.

The first term is the source's `e(cz²/(2(cτ+d)))` and the third its `e((τ - A·τ)/12)`, in
[72, Kopp (2024), Theorem 4.31]; identifying the remaining `wordRademacher` with the
Rademacher invariant is a separate statement about Dedekind sums. -/

/-- **The base case of `wordSfExpArg_eq`.** At a pure `T`-power positivity forces `j_M(τ) = 1`
and `M·τ = τ + M₀₁`, while `M₁₀ = 0`, the word accumulates nothing, and
`wordRademacher M = M₀₁`; every term vanishes. -/
private lemma wordSfExpArg_eq_base {τ : ℝ} (z : ℝ) (M : SL(2, ℤ)) (h0 : 0 ≤ M 1 0)
    (hz : M 1 0 = 0) (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ) :
    2 * wordSfExpArg z τ M h0 =
      Real.pi * Complex.I * ((M 1 0 : ℤ) : ℂ) * (z : ℂ) ^ 2 /
          ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) +
        Real.pi * Complex.I * (z : ℂ) *
          (1 / ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) - 1) +
        Real.pi * Complex.I / 6 *
          ((τ : ℂ) - ((flt (M : Mat(2, ℤ)) τ : ℝ) : ℂ) +
            ((wordRademacher M h0 : ℤ) : ℂ)) := by
  rw [wordSfExpArg_of_lowerLeft_eq_zero _ _ _ _ hz,
    wordRademacher_of_lowerLeft_eq_zero _ _ hz, fltDenominator_eq_one_of_lowerLeft_eq_zero hz hjac,
    flt_eq_add_of_lowerLeft_eq_zero hz hjac, hz]
  push_cast
  ring

/-- The determinant identity supplies the quadratic coefficient that telescopes through a
word step; used by `wordSfExpArg_eq_step`. -/
private lemma wordSfExpArg_quadratic_coefficient {τ : ℝ} {M N : SL(2, ℤ)}
    (hNe : (hjStep M).2 = N)
    (hMden : fltDenominator (M : Mat(2, ℤ)) τ =
      flt (N : Mat(2, ℤ)) τ *
        fltDenominator (N : Mat(2, ℤ)) τ)
    (hJNC : ((fltDenominator (N : Mat(2, ℤ)) τ : ℝ) : ℂ) ≠ 0) :
    ((N 0 0 : ℤ) : ℂ) =
          (1 + ((N 1 0 : ℤ) : ℂ) *
              (((flt (N : Mat(2, ℤ)) τ : ℝ) : ℂ) *
                ((fltDenominator (N : Mat(2, ℤ)) τ : ℝ) : ℂ))) /
            ((fltDenominator (N : Mat(2, ℤ)) τ : ℝ) : ℂ) := by
  have hN00 : N 0 0 = M 1 0 := by rw [← hNe]; exact (hjStep_snd_entries M).1
  have hN01 : N 0 1 = M 1 1 := by rw [← hNe]; exact hjStep_snd_topRight M
  have hdetN : (N 0 0 : ℝ) * (N 1 1 : ℝ) - (N 0 1 : ℝ) * (N 1 0 : ℝ) = 1 := by
    have h : (N : Mat(2, ℤ)).det = 1 := N.2
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have hkey : 1 + (N 1 0 : ℝ) * fltDenominator (M : Mat(2, ℤ)) τ =
      (N 0 0 : ℝ) * fltDenominator (N : Mat(2, ℤ)) τ := by
    have hJM : fltDenominator (M : Mat(2, ℤ)) τ =
        (N 0 0 : ℝ) * τ + (N 0 1 : ℝ) := by
      change (M 1 0 : ℝ) * τ + (M 1 1 : ℝ) = _
      rw [hN00, hN01]
    have hJN : fltDenominator (N : Mat(2, ℤ)) τ =
        (N 1 0 : ℝ) * τ + (N 1 1 : ℝ) := rfl
    rw [hJM, hJN]
    linear_combination -hdetN
  have h := congrArg (fun t : ℝ => (t : ℂ)) hkey
  simp only [hMden, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one,
    Complex.ofReal_intCast] at h
  field_simp
  linear_combination -h

/-- One letter telescopes the closed exponential formula; used by `wordSfExpArg_eq`. -/
private lemma wordSfExpArg_eq_step {τ : ℝ} (hτ : Irrational τ) (z : ℝ)
    {M N : SL(2, ℤ)} (h0 : 0 ≤ M 1 0) (hz : M 1 0 ≠ 0)
    (hNe : (hjStep M).2 = N) (h0N : 0 ≤ N 1 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hihN :
    2 * wordSfExpArg z τ N h0N =
      Real.pi * Complex.I * ((N 1 0 : ℤ) : ℂ) * (z : ℂ) ^ 2 /
          ((fltDenominator (N : Mat(2, ℤ)) τ : ℝ) : ℂ) +
        Real.pi * Complex.I * (z : ℂ) *
          (1 / ((fltDenominator (N : Mat(2, ℤ)) τ : ℝ) : ℂ) - 1) +
        Real.pi * Complex.I / 6 *
          ((τ : ℂ) - ((flt (N : Mat(2, ℤ)) τ : ℝ) : ℂ) +
            ((wordRademacher N h0N : ℤ) : ℂ))) :
    2 * wordSfExpArg z τ M h0 =
      Real.pi * Complex.I * ((M 1 0 : ℤ) : ℂ) * (z : ℂ) ^ 2 /
          ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) +
        Real.pi * Complex.I * (z : ℂ) *
          (1 / ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) - 1) +
        Real.pi * Complex.I / 6 *
          ((τ : ℂ) - ((flt (M : Mat(2, ℤ)) τ : ℝ) : ℂ) +
            ((wordRademacher M h0 : ℤ) : ℂ)) := by
  have hpos := h0.lt_of_ne (Ne.symm hz)
  obtain ⟨hνpos, hJpos⟩ := flt_and_fltDenominator_pos_of_hjStep M τ hτ hpos hjac
  rw [hNe] at hνpos hJpos
  have hN00 : N 0 0 = M 1 0 := by rw [← hNe]; exact (hjStep_snd_entries M).1
  have hMden : fltDenominator (M : Mat(2, ℤ)) τ =
      flt (N : Mat(2, ℤ)) τ *
        fltDenominator (N : Mat(2, ℤ)) τ := by
    rw [← hNe]; exact fltDenominator_hjStep M τ hτ
  have hMflt : flt (M : Mat(2, ℤ)) τ =
      ((hjStep M).1 : ℝ) - 1 / flt (N : Mat(2, ℤ)) τ := by
    rw [← hNe]; exact flt_hjStep M τ hτ
  have hνC : ((flt (N : Mat(2, ℤ)) τ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hνpos.ne'
  have hJNC : ((fltDenominator (N : Mat(2, ℤ)) τ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hJpos.ne'
  have hc00 := wordSfExpArg_quadratic_coefficient hNe hMden hJNC
  rw [wordSfExpArg_step z τ h0 hz hNe h0N, wordRademacher_step h0 hz hNe h0N, mul_add, hihN,
    ← hN00, sfExpArg, faddeevSExpArg, hMflt, hMden]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_intCast, Int.cast_add, Int.cast_sub, Int.cast_ofNat]
  rw [hc00]
  field_simp
  ring

/-- **The word-accumulated exponential in closed form.** For irrational `τ` in `M`'s real domain,

```text
2·X_M(z,τ) = πi·M₁₀·z²/j_M(τ) + πi·z·(1/j_M(τ) - 1) + (πi/6)·(τ - M·τ + W(M)),
```

with `W = SICs.SL2Z.WordAccumulator.wordRademacher`. Every trace of the word has vanished
except `W(M)`: the sum is determined by `M`'s bottom row, its Möbius data at `τ`,
and that one integer.

This evaluates the functional-equation prefactors of [72, Kopp (2024),
Theorem 4.31], and it is what `sfModularCocycleReal_mul_neg`
needs in order to become [72, Kopp (2024), Theorem 4.36, `thm:shincharacter`] at a fixed point:
there `τ - M·τ = 0`, so only `W(M)` and the elementary `z`-terms survive.

Proved by induction along `wordSigmaS`'s own recursion; the section comment says why each of the
three parts telescopes. -/
theorem wordSfExpArg_eq {τ : ℝ} (hτ : Irrational τ) (z : ℝ) (M : SL(2, ℤ)) (h0 : 0 ≤ M 1 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ) :
    2 * wordSfExpArg z τ M h0 =
      Real.pi * Complex.I * ((M 1 0 : ℤ) : ℂ) * (z : ℂ) ^ 2 /
          ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) +
        Real.pi * Complex.I * (z : ℂ) *
          (1 / ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) - 1) +
        Real.pi * Complex.I / 6 *
          ((τ : ℂ) - ((flt (M : Mat(2, ℤ)) τ : ℝ) : ℂ) +
            ((wordRademacher M h0 : ℤ) : ℂ)) := by
  induction M, h0 using wordSfExpArg.induct with
  | case1 M h0 hz _ => exact wordSfExpArg_eq_base z M h0 hz hjac
  | case2 M h0 hz hpos h0N _ _ ih =>
      have hJpos := (flt_and_fltDenominator_pos_of_hjStep M τ hτ hpos hjac).2
      exact wordSfExpArg_eq_step hτ z h0 hz rfl h0N hjac (ih hJpos)


/-! ### The accumulated exponential at a fixed point

At a fixed point of `M` in its real domain the term `τ - M·τ` of the closed form vanishes, and
what is left is `πi` times a real number: the exponential `exp(2X_M)` is a phase. Hence the
reflected product `ש^r_M(τ)ש^{-r}_M(τ)` has modulus one, which
[72, Kopp (2024), Theorem 4.36, `thm:shincharacter`] expresses by writing it as the root of unity
`ψ²(A)χ_r(A)`. -/

/-- **The accumulated exponential is a phase at a fixed point**: `|exp(2X_M(z,τ))| = 1` when
`M·τ = τ` and `j_M(τ) > 0`, because the closed form `wordSfExpArg_eq` is then `πi` times the
real number `M₁₀z²/j_M(τ) + z(1/j_M(τ) - 1) + W(M)/6`. -/
theorem norm_exp_two_wordSfExpArg_of_flt_eq_self {τ : ℝ} (hτ : Irrational τ) (z : ℝ)
    (M : SL(2, ℤ)) (h0 : 0 ≤ M 1 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    ‖Complex.exp (2 * wordSfExpArg z τ M h0)‖ = 1 := by
  obtain ⟨x, hx⟩ : ∃ x : ℝ, 2 * wordSfExpArg z τ M h0 = Real.pi * Complex.I * (x : ℂ) := by
    refine ⟨(M 1 0 : ℤ) * z ^ 2 / fltDenominator (M : Mat(2, ℤ)) τ +
      z * (1 / fltDenominator (M : Mat(2, ℤ)) τ - 1) +
      (wordRademacher M h0 : ℤ) / 6, ?_⟩
    rw [wordSfExpArg_eq hτ z M h0 hjac, hfix]
    push_cast
    ring
  rw [hx, Complex.norm_exp]
  simp

/-! ### Nonvanishing of the word value

The reflection law is stated multiplicatively; away from the lattice it shows that neither factor
vanishes, since its right-hand side is a nonzero multiple of an exponential. -/

/-- **The word value does not vanish**: `σ_M(z,τ) ≠ 0` for an irrational `τ`, a lattice-free `z`,
`j_M(τ) > 0`, and `z/j_M(τ) ∉ ℤ`. From `wordSigmaS_mul_neg`: its right-hand side is
`(1 - e(-z/j_M(τ)))·exp(2X_M(z,τ))`, nonzero by
`one_sub_exp_two_pi_I_ne_zero_of_forall_ne_int` and `Complex.exp_ne_zero`, so the left-hand
product, and with it `σ_M(z,τ)`, is nonzero. The last hypothesis holds for `z = ⟨⟨r,τ⟩⟩` with
`r ∉ ℤ²` by `sigmaSLatticeFree_fracSymplecticFormRat_div` at `a = 0`. -/
theorem wordSigmaS_ne_zero {τ : ℝ} (hτ : Irrational τ) (z : ℝ)
    (hlat : SigmaSLatticeFree τ z) (M : SL(2, ℤ)) (h0 : 0 ≤ M 1 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hdiv : ∀ b : ℤ, z / fltDenominator (M : Mat(2, ℤ)) τ ≠ (b : ℝ)) :
    wordSigmaS z τ M h0 ≠ 0 := by
  have hfactor : (1 : ℂ) - Complex.exp (-(2 * Real.pi * Complex.I *
      ((z : ℂ) / ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ)))) ≠ 0 := by
    have h := one_sub_exp_two_pi_I_ne_zero_of_forall_ne_int
      (-(z / fltDenominator (M : Mat(2, ℤ)) τ)) fun b hb =>
        hdiv (-b) (by push_cast at hb ⊢; linarith)
    simpa only [Complex.ofReal_neg, Complex.ofReal_div, mul_neg] using h
  have hrhs : (1 - Complex.exp (-(2 * Real.pi * Complex.I *
      ((z : ℂ) / ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ))))) *
      Complex.exp (2 * wordSfExpArg z τ M h0) ≠ 0 :=
    mul_ne_zero hfactor (Complex.exp_ne_zero _)
  intro hz
  have hlhs : wordSigmaS z τ M h0 * wordSigmaS (-z) τ M h0 *
      (1 - Complex.exp (-(2 * Real.pi * Complex.I * (z : ℂ)))) = 0 :=
    mul_eq_zero.mpr (.inl (mul_eq_zero.mpr (.inl hz)))
  have href := wordSigmaS_mul_neg hτ z hlat M h0 hjac
  rw [hlhs] at href
  exact hrhs href.symm

end SIC
