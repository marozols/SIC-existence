/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.FractionalLinear
import SICs.SL2Z.Words

/-!
# Real periods along a Hirzebruch--Jung word

Real word-step period recursion, the positive-Jacobi-denominator invariant, and letter
identities over any field for both real and complex words.

The canonical word algorithm of [AFK25, Appendix C] reconstructs `M = T^r S M'`
from `(r,M') = hjStep M`. The fractional-linear composition laws therefore give
`M·τ = r - 1/(M'·τ)` and `j_M(τ) = (M'·τ) j_{M'}(τ)` at irrational real `τ`.

When the lower-left entry and `j_M(τ)` are positive, the row-ratio bound gives `M·τ < r`.
The recursion then forces the next period `M'·τ` to be positive, and the denominator
factorization makes `j_{M'}(τ)` positive too. This one-step invariant supplies
`WordSigmaSVisits.period_pos` in `SICs.Cocycle.Word.Basic`, without a fixed-point or
conjugate-root assumption.
-/

open ModularGroup MatrixGroups

open scoped MatrixGroups

namespace SIC

/-! ### The `hjStep` real period recursion

The matrix decomposition `M = T^r S M'` translates into the negative-continued-fraction update
`M·τ = r - 1/(M'·τ)`.  The accompanying denominator formula maintains the positivity invariant
along the recursive word. -/

/-- Shared prerequisites for `flt_hjStep` and `fltDenominator_hjStep`: writing
`(r, M') := hjStep M`, `M'`'s denominator and numerator at `τ` are nonzero, and the intermediate
factor `S·M'` also has nonzero denominator at `τ`. Private since it exists only to deduplicate
those two theorems' proofs; everything here comes for free from `τ`'s irrationality and
`M'.2 : (M' : Mat(2, ℤ)).det = 1`, no extra hypothesis beyond `hτ` needed. Both
theorems also need `M`'s reconstruction as `T^r·(S·M')`, but that identity needs neither `τ` nor
`hτ`, so it is factored out separately as `hjStep_reconstruct_coe` (`SICs.SL2Z.Words`) rather
than bundled here. -/
private theorem hjStep_setup (M : SL(2, ℤ)) (τ : ℝ) (hτ : Irrational τ) :
    fltDenominator ((hjStep M).2 : Mat(2, ℤ)) τ ≠ 0 ∧
      flt ((hjStep M).2 : Mat(2, ℤ)) τ ≠ 0 ∧
      fltDenominator
        ((S : Mat(2, ℤ)) * ((hjStep M).2 : Mat(2, ℤ))) τ ≠ 0 := by
  have hden' : fltDenominator ((hjStep M).2 : Mat(2, ℤ)) τ ≠ 0 :=
    fltDenominator_ne_zero_of_irrational hτ (hjStep M).2
  have hnum' : flt ((hjStep M).2 : Mat(2, ℤ)) τ ≠ 0 :=
    flt_ne_zero_of_irrational hτ (hjStep M).2
  have hSM' : fltDenominator
      ((S : Mat(2, ℤ)) * ((hjStep M).2 : Mat(2, ℤ))) τ ≠ 0 := by
    rw [fltDenominator_mul _ _ τ hden', fltDenominator_S]
    exact mul_ne_zero hnum' hden'
  exact ⟨hden', hnum', hSM'⟩

/-- **The `hjStep` real period recursion**: `flt M τ = r - 1/flt M' τ` for
`(r, M') = hjStep M`, given only that `τ` is irrational. This is the real-number counterpart of
the period recursion used in the word construction: peeling one `hjStep` (`M = T^r·S·M'`,
`hjStep_reconstruct`, `SICs.SL2Z.Words`) and composing `flt_mul` twice — first through `S·M'`,
then through `T^r·(S·M')` — collapses to this one-line update, using `flt_T_zpow`/`flt_S`
to evaluate the two elementary factors. -/
theorem flt_hjStep (M : SL(2, ℤ)) (τ : ℝ) (hτ : Irrational τ) :
    flt (M : Mat(2, ℤ)) τ =
      ((hjStep M).1 : ℝ) - 1 / flt ((hjStep M).2 : Mat(2, ℤ)) τ := by
  obtain ⟨hden', _, hSM'⟩ := hjStep_setup M τ hτ
  have step1 : flt
      ((S : Mat(2, ℤ)) * ((hjStep M).2 : Mat(2, ℤ))) τ =
      -1 / flt ((hjStep M).2 : Mat(2, ℤ)) τ := by
    rw [flt_mul _ _ τ hden', flt_S]
  rw [hjStep_reconstruct_coe M,
    flt_mul _ _ τ hSM',
    step1, flt_T_zpow]
  ring

/-- **The Jacobi-denominator companion to `flt_hjStep`**: `fltDenominator M τ =
flt M' τ · fltDenominator M' τ` for `(r, M') = hjStep M`, given only that `τ` is
irrational. Proved by the same `T^r·(S·M')` reconstruction, using `fltDenominator_mul` twice
(through `S·M'`, then through `M'`) and `fltDenominator_T_zpow`/`fltDenominator_S` for the
elementary factors, in place of `flt_hjStep`'s `flt_mul` chain. This is exactly the
telescoping identity `flt_and_fltDenominator_pos_of_hjStep` needs to propagate
Jacobi-denominator positivity from one word step to the next. -/
theorem fltDenominator_hjStep (M : SL(2, ℤ)) (τ : ℝ) (hτ : Irrational τ) :
    fltDenominator (M : Mat(2, ℤ)) τ =
      flt ((hjStep M).2 : Mat(2, ℤ)) τ *
        fltDenominator ((hjStep M).2 : Mat(2, ℤ)) τ := by
  obtain ⟨hden', _, hSM'⟩ := hjStep_setup M τ hτ
  rw [hjStep_reconstruct_coe M, fltDenominator_mul _ _ τ hSM', fltDenominator_T_zpow,
    one_mul, fltDenominator_mul _ _ τ hden', fltDenominator_S]

/-- **`hjStep`'s exponent is an upper bound for the top-left/lower-left ratio**: `a ≤ r·c` for
`c := M 1 0 > 0` and `r := (hjStep M).1` (equivalently `a/c ≤ r`). Follows directly from
`hjStep_snd_lowerLeft`'s nonnegative-remainder fact (`(hjStep M).2 1 0 = r·c - a ≥ 0`); this is
the one purely-integer fact `flt_and_fltDenominator_pos_of_hjStep` needs to locate
`hjStep`'s exponent relative to `M`'s own image of `τ`, without needing the *equality* `r = ⌈a/c⌉`
that a since-superseded approach once chased (see the "Periods stay positive" section below). -/
theorem hjStep_topLeft_le (M : SL(2, ℤ)) (hc : 0 < M 1 0) :
    (M 0 0 : ℝ) ≤ (hjStep M).1 * (M 1 0 : ℝ) := by
  have hnn : 0 ≤ (hjStep M).2 1 0 := by
    rw [hjStep_snd_lowerLeft]; exact Int.emod_nonneg _ hc.ne'
  rw [(hjStep_snd_entries M).2] at hnn
  have : (M 0 0 : ℤ) ≤ (hjStep M).1 * M 1 0 := by linarith
  exact_mod_cast this

/-! ### The positive-denominator invariant

The row-ratio identity in `topLeft_div_lowerLeft_sub_flt` combines with the ceiling
bound to put the current period below the next exponent. The two period recursions then
propagate positivity to the next period and its denominator. -/

/-- **The Jacobi-denominator invariant, one `hjStep` at a time.** If `M ∈ SL₂(ℤ)` has positive
lower-left entry and positive Jacobi denominator at `τ`, so do the next period and the next
Jacobi denominator produced by peeling one `hjStep`: writing `(r, M') := hjStep M`,
`0 < flt M' τ` and `0 < fltDenominator M' τ`. No hypothesis relates `M` to `τ` beyond the
starting sign of `M`'s own Jacobi denominator — `M` need not fix `τ`, and no conjugate root enters
at all. The argument: `topLeft_div_lowerLeft_sub_flt` and `hjStep_topLeft_le` combine to give
`flt M τ < r` (the current period sits strictly below `hjStep`'s exponent, from `M`'s Jacobi
denominator being positive); feeding this into `flt_hjStep`'s recursion
(`flt M τ = r - 1/flt M' τ`) forces `1/flt M' τ > 0`, hence `flt M' τ > 0`
(`one_div_pos`); and `fltDenominator_hjStep`'s identity
(`fltDenominator M τ = flt M' τ · fltDenominator M' τ`) then forces
`fltDenominator M' τ > 0` too, since a product and one factor are both positive. -/
theorem flt_and_fltDenominator_pos_of_hjStep (M : SL(2, ℤ)) (τ : ℝ) (hτ : Irrational τ)
    (hc : 0 < M 1 0) (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ) :
    0 < flt ((hjStep M).2 : Mat(2, ℤ)) τ ∧
      0 < fltDenominator ((hjStep M).2 : Mat(2, ℤ)) τ := by
  have hcR : (0 : ℝ) < (M 1 0 : ℝ) := by exact_mod_cast hc
  have hbound := topLeft_div_lowerLeft_sub_flt M τ hcR.ne' hjac.ne'
  have hratio_pos :
      0 < (M 0 0 : ℝ) / (M 1 0 : ℝ) - flt (M : Mat(2, ℤ)) τ := by
    rw [hbound]; positivity
  have hler : (M 0 0 : ℝ) / (M 1 0 : ℝ) ≤ ((hjStep M).1 : ℝ) :=
    (div_le_iff₀ hcR).mpr (hjStep_topLeft_le M hc)
  have hlt : flt (M : Mat(2, ℤ)) τ < (hjStep M).1 := by linarith
  have hrec := flt_hjStep M τ hτ
  have hinv_pos : 0 < 1 / flt ((hjStep M).2 : Mat(2, ℤ)) τ := by
    have hkey : 1 / flt ((hjStep M).2 : Mat(2, ℤ)) τ =
        (hjStep M).1 - flt (M : Mat(2, ℤ)) τ := by linarith
    rw [hkey]; linarith
  have hMpos : 0 < flt ((hjStep M).2 : Mat(2, ℤ)) τ := one_div_pos.mp hinv_pos
  have hjac' := fltDenominator_hjStep M τ hτ
  have hjacpos : 0 < flt ((hjStep M).2 : Mat(2, ℤ)) τ *
      fltDenominator ((hjStep M).2 : Mat(2, ℤ)) τ := hjac' ▸ hjac
  have heq : fltDenominator ((hjStep M).2 : Mat(2, ℤ)) τ =
      fltDenominator (M : Mat(2, ℤ)) τ /
        flt ((hjStep M).2 : Mat(2, ℤ)) τ := by
    rw [hjac']; field_simp
  exact ⟨hMpos, heq ▸ div_pos hjac hMpos⟩

/-! ### The Hirzebruch--Jung generator

Every letter of a Hirzebruch--Jung word contributes the single matrix `T^b S`, so the two
evaluations below are the elementary building blocks of every period computation along a word:
the Möbius action is the negative-continued-fraction step `x ↦ b - 1/x` of [85, Popescu-Pampu
(2007), Definition 2.1, `continued`], and the Jacobi denominator is the argument itself. These
identities hold over any field, so they also evaluate letters in complex words. -/

/-- The matrix of the Hirzebruch--Jung generator: `T^b S = [[b, -1], [1, 0]]`. -/
theorem coe_T_zpow_mul_S (b : ℤ) :
    ((T ^ b * S : SL(2, ℤ)) : Mat(2, ℤ)) = !![b, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, coe_S]
  norm_num [Matrix.mul_fin_two]

/-- **The Möbius action of the Hirzebruch--Jung generator**: `(T^b S)·x = b - 1/x`, the
negative-continued-fraction step. The hypothesis `x ≠ 0` is the generator's own pole: at `x = 0`
the left side is Lean's junk value `0` while the right side is `b`. -/
theorem flt_T_zpow_mul_S {K : Type*} [Field K] (b : ℤ) {x : K} (hx : x ≠ 0) :
    flt ((T ^ b * S : SL(2, ℤ)) : Mat(2, ℤ)) x = b - 1 / x := by
  rw [flt, coe_T_zpow_mul_S]
  norm_num
  field_simp
  ring

/-- **The Jacobi denominator of the Hirzebruch--Jung generator**: `j_{T^b S}(x) = x`. -/
theorem fltDenominator_T_zpow_mul_S {K : Type*} [Field K] (b : ℤ) (x : K) :
    fltDenominator ((T ^ b * S : SL(2, ℤ)) : Mat(2, ℤ)) x = x := by
  rw [fltDenominator, coe_T_zpow_mul_S]
  norm_num

/-! ### Letter words

Peeling a letter replaces the lower row by the old upper row and applies one
negative-continued-fraction step to the period. -/

/-- The lower row of `letterWord (a :: w)` is the upper row of `letterWord w`. -/
theorem letterWord_cons_apply_one (a : ℤ) (w : List ℤ) (j : Fin 2) :
    letterWord (a :: w) 1 j = letterWord w 0 j := by
  rw [letterWord_cons, Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow_mul_S]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The upper row of `letterWord (a :: w)` is `a` times the old upper row minus
the old lower row. -/
theorem letterWord_cons_apply_zero (a : ℤ) (w : List ℤ) (j : Fin 2) :
    letterWord (a :: w) 0 j = a * letterWord w 0 j - letterWord w 1 j := by
  rw [letterWord_cons, Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow_mul_S]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The Jacobi denominator of a peeled letter is the suffix period times its
Jacobi denominator. -/
theorem fltDenominator_letterWord_cons {K : Type*} [Field K] (a : ℤ) (w : List ℤ) {τ : K}
    (hden : fltDenominator (letterWord w : Mat(2, ℤ)) τ ≠ 0) :
    fltDenominator (letterWord (a :: w) : Mat(2, ℤ)) τ =
      flt (letterWord w : Mat(2, ℤ)) τ *
        fltDenominator (letterWord w : Mat(2, ℤ)) τ := by
  rw [letterWord_cons, Matrix.SpecialLinearGroup.coe_mul,
    fltDenominator_mul _ _ τ hden, fltDenominator_T_zpow_mul_S]

/-- The period of a peeled letter is the next negative-continued-fraction step. -/
theorem flt_letterWord_cons {K : Type*} [Field K] (a : ℤ) (w : List ℤ) {τ : K}
    (hden : fltDenominator (letterWord w : Mat(2, ℤ)) τ ≠ 0)
    (hσ : flt (letterWord w : Mat(2, ℤ)) τ ≠ 0) :
    flt (letterWord (a :: w) : Mat(2, ℤ)) τ =
      a - 1 / flt (letterWord w : Mat(2, ℤ)) τ := by
  rw [letterWord_cons, Matrix.SpecialLinearGroup.coe_mul, flt_mul _ _ τ hden,
    flt_T_zpow_mul_S a hσ]

/-! ### Letter words as Hirzebruch–Jung words

A letter word `∏_j T^{b_j}S` is the Hirzebruch–Jung word matrix with a trailing exponent `0`.
When every letter after the first is at least `2`, `hjStep` peels its letters one at a time. -/

/-- A letter word is the Hirzebruch–Jung word matrix with trailing exponent zero:
`∏_j T^{b_j}S = T^{b₁}S⋯T^{b_r}S·T^0`. -/
theorem letterWord_eq_wordToMatrix (bs : List ℤ) :
    letterWord bs = wordToMatrix (bs ++ [0]) := by
  induction bs with
  | nil => simp [wordToMatrix]
  | cons a bs ih =>
      rw [letterWord_cons, List.cons_append,
        wordToMatrix_cons_of_ne_nil a (bs ++ [0]) (by simp), ← ih]

/-- `hjStep` peels the first letter of a letter word whose remaining letters are at least `2`:
`hjStep (T^aS·∏_j T^{b_j}S) = (a, ∏_j T^{b_j}S)`. Specializes `hjStep_wordToMatrix_cons`. -/
theorem hjStep_letterWord_cons (a : ℤ) {bs : List ℤ} (hbs : ∀ b ∈ bs, 2 ≤ b) :
    hjStep (letterWord (a :: bs)) = (a, letterWord bs) := by
  have htail : IsHJTail (bs ++ [0]) := by
    refine ⟨by simp, ?_⟩
    simpa using hbs
  simpa only [letterWord_eq_wordToMatrix, List.cons_append] using
    (hjStep_wordToMatrix_cons (r := a) htail)

/-- A property of all proper suffixes remains true after removing the first letter. -/
theorem forall_tail_tails_of_cons {P : List ℤ → Prop} (a : ℤ) (l : List ℤ)
    (h : ∀ w ∈ (a :: l).tail.tails, P w) :
    ∀ w ∈ l.tail.tails, P w := by
  cases l with
  | nil => simpa using h
  | cons b l =>
      intro w hw
      exact h w (by
        simp only [List.tail_cons, List.tails_cons, List.mem_cons]
        exact Or.inr hw)

/-- A nonterminal letter word whose remaining letters are at least `2` has positive lower-left
entry. -/
theorem letterWord_lowerLeft_pos (a : ℤ) {bs : List ℤ}
    (hbs : ∀ b ∈ bs, 2 ≤ b) : 0 < letterWord (a :: bs) 1 0 := by
  rw [letterWord_cons_apply_one, letterWord_eq_wordToMatrix]
  have htail : IsHJTail (bs ++ [0]) := by
    refine ⟨by simp, ?_⟩
    simpa using hbs
  obtain ⟨hnn, hlt⟩ := wordToMatrix_lowerLeft_lt_topLeft htail
  omega

/-- A letter word whose letters after the first are at least `2` has nonnegative lower-left
entry. -/
theorem letterWord_lowerLeft_nonneg {bs : List ℤ} (hbs : ∀ b ∈ bs.tail, 2 ≤ b) :
    0 ≤ letterWord bs 1 0 := by
  cases bs with
  | nil => simp [letterWord_nil]
  | cons a bs => exact (letterWord_lowerLeft_pos a hbs).le

end SIC
