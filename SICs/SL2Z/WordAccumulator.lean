/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.Words

/-!
# The Rademacher accumulator of a Hirzebruch–Jung word

The integer accumulated from the exponents of the canonical Hirzebruch–Jung word.

This module isolates the word sum used in [72, Kopp (2024), Proposition 7.21,
`prop:globalphase`], along the canonical expansion of [AFK25, Theorem C.4,
`thm:tsaltexpn`]. Its identification with the Dedekind-sum definition of the Rademacher
invariant is proved in `SICs.SL2Z.RademacherWord`.

## The argument

Each letter `T^r S` contributes `r - 3`; the terminal `T`-power contributes its exponent.
The recursion follows the ceiling-division step `hjStep` and terminates because the
nonnegative lower-left matrix entry strictly decreases. The base and step equations expose
this recursion to the reflection law of `SICs.Cocycle.Word.Reflection`.
-/

open MatrixGroups

namespace SIC

/-! ### The accumulated exponent

The strict decrease of the nonnegative lower-left entry under `hjStep` makes the exponent sum total
and gives the two equations needed for induction along the word. -/

/-- **The word-level Rademacher accumulator** `W(M) = r₁ + ⋯ + r_n - 3n + r_{n+1}`, for the
Hirzebruch--Jung word `M = T^{r₁}S⋯T^{r_n}S T^{r_{n+1}}` peeled by `hjStep`: each
`T^{r_i}S` letter contributes `r_i - 3` and the terminal `T`-power contributes its exponent.

It is defined by its own recursion along `hjStep`, the recursion of
`SICs.Cocycle.Word.Basic.wordSigmaS`, so that arguments by induction along the word can use it
directly. It exists to express the exponential accumulated
along the word by `SICs.Cocycle.Word.Reflection.wordSfExpArg`, whose closed form
`SICs.Cocycle.Word.Reflection.wordSfExpArg_eq` is stated in terms of it.

`W` is the word sum `-3ℓ + Σ b_n` of [72, Kopp (2024), Proposition 7.21, `prop:globalphase`],
which evaluates the Rademacher function `Φ` along the same Hirzebruch--Jung word as `Φ = W + 3`,
for a purely periodic word with no terminal `T`-power. It is also the Hirzebruch--Jung counterpart
of the word sum `Σ ε_i` that [86, Rademacher (1955), Satz 8, eq. (26)] uses along a cyclically
reduced word in the elliptic generators.
`SICs.SL2Z.RademacherWord.rademacherInvariant_eq_wordRademacher_add` makes the identification
precise for an arbitrary `M`, as `Ψ = W + 3 - 3·sgn(Tr)`. -/
def wordRademacher : (M : SL(2, ℤ)) → 0 ≤ M 1 0 → ℤ
  | M, h0 =>
    if hz : M 1 0 = 0 then
      M 0 1
    else
      have hpos : 0 < M 1 0 := h0.lt_of_ne (Ne.symm hz)
      have h0' : 0 ≤ (hjStep M).2 1 0 := by
        rw [hjStep_snd_lowerLeft]; exact Int.emod_nonneg _ hpos.ne'
      have hlt : (hjStep M).2 1 0 < M 1 0 := by
        rw [hjStep_snd_lowerLeft]; exact Int.emod_lt_of_pos _ hpos
      (hjStep M).1 - 3 + wordRademacher (hjStep M).2 h0'
termination_by M _ => M 1 0 |>.toNat
decreasing_by omega

/-- **Base case**: at a pure `T`-power the accumulator is that power's exponent. -/
theorem wordRademacher_of_lowerLeft_eq_zero (M : SL(2, ℤ)) (h0 : 0 ≤ M 1 0) (hz : M 1 0 = 0) :
    wordRademacher M h0 = M 0 1 := by
  rw [wordRademacher, dite_eq_left hz]

/-- **Recursive step**, with the reduced matrix supplied by the caller, matching
`SICs.Cocycle.Word.Basic.wordSigmaS_step`: one `T^rS` letter contributes `r - 3`. -/
theorem wordRademacher_step {M N : SL(2, ℤ)} (h0 : 0 ≤ M 1 0) (hz : M 1 0 ≠ 0)
    (hN : (hjStep M).2 = N) (h0N : 0 ≤ N 1 0) :
    wordRademacher M h0 = (hjStep M).1 - 3 + wordRademacher N h0N := by
  subst hN
  rw [wordRademacher, dite_eq_right hz]

end SIC
