/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.Basic

/-!
# Hirzebruch–Jung steps and words in `SL₂(ℤ)`

The reduction step `hjStep`, the words `L = T^{r₁}S⋯ST^{r_{n+1}}`, and the tail invariant by which
`hjStep` reads a word off its matrix.

This file sets up the words of [AFK25, Theorem C.4, `thm:tsaltexpn`]: decompositions
`L = T^{r₁} S T^{r₂} S ⋯ S T^{rₙ} S T^{r_{n+1}}` with every interior exponent `rᵢ ≥ 2`
(`1 < i < n+1`). The word is what `sigmaS`/`sigmaSBase` (`SICs.Cocycle.SigmaS.Reduction`) is
chained along to build the real-domain cocycle, generalizing the principal family's own fixed
six-letter word (`SICs.Principal.Quadratic.Stabilizers`, `principalA_eq_T_zpow_mul_S_word`). The
chaining itself is the recursion `SICs.Cocycle.Word.Basic.wordSigmaS` along `hjStep`; this file
shows that on a word of the shape above the step peels exactly the word's letters, and proves
the reverse implication of Theorem C.4: the matrix of such a word has positive lower-left entry.

## The step

For `M = [[a,b],[c,d]] ∈ SL₂(ℤ)` with `c ≠ 0`, `hjStep` computes `r := ⌈a/c⌉` (via Euclidean
division of `-a` by `c`, so it is total even when `c ≤ 0`) and `M' := S⁻¹ T^{-r} M`, satisfying
`M = T^r S M'` unconditionally. When `c > 0`, `M'`'s own lower-left entry is `(-a) % c ∈ [0,c)`,
strictly smaller, so iterating the step terminates exactly when the lower-left entry reaches `0`,
at which point the remaining matrix is a pure power of `T` (`eq_T_zpow_of_lowerLeft_eq_zero`, the
`c = 0` case AFK25 itself handles separately).

## Main declarations

- `hjStep`: one reduction step, `M ↦ (⌈a/c⌉, S⁻¹ T^{-⌈a/c⌉} M)`.
- `hjStep_snd_entries`/`hjStep_snd_topRight`: the reduced matrix's top row is `M`'s bottom row.
- `wordToMatrix`: reconstructs `T^{r₁} S T^{r₂} S ⋯ S T^{r_{n+1}}` from `[r₁,…,r_{n+1}]` ([AFK25,
  equation (C.35), `eq:ltsdecom`] read as a definition); `letterWord`, the letter product
  `∏_j T^{b_j}S`.
- `IsHJWord`: AFK25's interior-`≥2` word-shape predicate, and `IsHJTail` for its tail.
- `wordToMatrix_lowerLeft_lt_topLeft`: the tail invariant `0 ≤ N₁₀ < N₀₀`.
- `hjStep_wordToMatrix_cons`: `hjStep` reads a word's head off its matrix and returns the tail's.
- `wordToMatrix_lowerLeft_pos`: the reverse implication in [AFK25, Theorem C.4,
  `thm:tsaltexpn`].

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Theorem C.4, `thm:tsaltexpn`, and
  equation (C.35), `eq:ltsdecom` (Appendix C, "Hirzebruch–Jung continued fractions").
-/

open ModularGroup MatrixGroups

open scoped MatrixGroups

namespace SIC

/-! ### One ceiling-division step

The identities in this section compute the matrix entries after one Hirzebruch--Jung reduction.
For positive lower-left entry, Euclidean division makes the new lower-left entry a nonnegative,
strictly smaller remainder. The reconstruction identity records the group factor removed by the
step.
-/

/-- One Hirzebruch–Jung reduction step: `r := ⌈(M 0 0)/(M 1 0)⌉`, computed via Euclidean division
so the definition is total even when `M 1 0 ≤ 0`, together with the reduced matrix
`M' := S⁻¹ T^{-r} M`. See `hjStep_reconstruct` for the identity this is built to satisfy and
`hjStep_snd_entries`/`hjStep_snd_lowerLeft` for `M'`'s entries.

On the ratio `x = (M 0 0)/(M 1 0)` the step acts as `x ↦ (⌈x⌉ − x)⁻¹`, the classical map whose
orbits are the minus, or backward, continued fraction expansions
`[r₁, r₂, …]⁻ = r₁ − 1/(r₂ − 1/⋯)` of [85, Popescu-Pampu (2007), Definition 2.1, `continued`];
the `r`'s it emits are the partial quotients of that expansion. -/
def hjStep (M : SL(2, ℤ)) : ℤ × SL(2, ℤ) :=
  (-((-(M 0 0)) / (M 1 0)), S⁻¹ * T ^ (-(-((-(M 0 0)) / (M 1 0)))) * M)

/-- `hjStep` inverts cleanly: `M = T^r S M'` for `(r, M') = hjStep M`, unconditionally (no
hypothesis on `M`'s entries is needed, since this is pure group algebra). -/
theorem hjStep_reconstruct (M : SL(2, ℤ)) :
    M = T ^ (hjStep M).1 * S * (hjStep M).2 := by
  simp only [hjStep]
  group

/-- `hjStep_reconstruct`, cast to matrices and right-associated as `T^r·(S·M')` rather than
`(T^r·S)·M'`. Needed unconditionally (no `τ` or irrationality hypothesis) by
`SICs.SL2Z.WordPeriods`'s `flt_hjStep`/`fltDenominator_hjStep`, which peel one
matrix factor at a time from the right via `flt_mul`/`flt_mul` — first `S·M'`, then
`T^r·(S·M')`. -/
theorem hjStep_reconstruct_coe (M : SL(2, ℤ)) :
    (M : Mat(2, ℤ)) =
      ((T ^ (hjStep M).1 : SL(2, ℤ)) : Mat(2, ℤ)) *
        ((S : Mat(2, ℤ)) * ((hjStep M).2 : Mat(2, ℤ))) := by
  have h := congrArg (fun N : SL(2, ℤ) => (N : Mat(2, ℤ))) (hjStep_reconstruct M)
  simpa only [Matrix.SpecialLinearGroup.coe_mul, mul_assoc] using h

/-- The reduced matrix `M' = S⁻¹ T^{-r} M`'s top-left entry is `M`'s own lower-left entry, and
its lower-left entry is `r * (M 1 0) - M 0 0`. Proved by direct `2×2` block computation. -/
theorem hjStep_snd_entries (M : SL(2, ℤ)) :
    (hjStep M).2 0 0 = M 1 0 ∧
      (hjStep M).2 1 0 = (hjStep M).1 * M 1 0 - M 0 0 := by
  simp only [hjStep]
  rw [S_inv]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    coe_T_zpow, coe_S]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]
  norm_num [zpow_neg]
  ring

/-- The reduced matrix `M' = S⁻¹ T^{-r} M`'s top-right entry is `M`'s own lower-right entry: the
second column's counterpart of `hjStep_snd_entries`' top-left identity, since `M = T^r S M'`
forces `M`'s whole bottom row to be `M'`'s top row. Needed by
`SICs.Cocycle.Word.Shifts.wordSigmaS_lattice_shift`, whose `q`-Pochhammer index `a·M₁₁ - b·M₁₀`
must be transported from one word step to the next. -/
theorem hjStep_snd_topRight (M : SL(2, ℤ)) : (hjStep M).2 0 1 = M 1 1 := by
  simp only [hjStep]
  rw [S_inv]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    coe_T_zpow, coe_S]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]
  norm_num [zpow_neg]

/-- The reduced matrix's lower-left entry is exactly the Euclidean remainder of `-(M 0 0)` by
`M 1 0`: this is what makes `r = ⌈(M 0 0)/(M 1 0)⌉` the *ceiling*, and what gives the strict
decrease `(hjStep M).2 1 0 < M 1 0` used for termination. -/
theorem hjStep_snd_lowerLeft (M : SL(2, ℤ)) :
    (hjStep M).2 1 0 = (-(M 0 0)) % (M 1 0) := by
  rw [(hjStep_snd_entries M).2]
  have h := Int.ediv_mul_add_emod (-(M 0 0)) (M 1 0)
  have hcomm : (-(M 0 0)) / (M 1 0) * (M 1 0) = (M 1 0) * ((-(M 0 0)) / (M 1 0)) := mul_comm _ _
  simp only [hjStep]
  linarith

/-! ### Word evaluation

`wordToMatrix` assembles an exponent list into the alternating word of [AFK25, equation (C.35),
`eq:ltsdecom`]; `letterWord` multiplies letters `T^bS` without a trailing power of `T`.
-/

/-- Reconstructs `T^{r₁} S T^{r₂} S ⋯ S T^{r_{n+1}}` from the exponent list `[r₁,…,r_{n+1}]`:
[AFK25, equation (C.35), `eq:ltsdecom`] read as a definition. -/
def wordToMatrix : List ℤ → SL(2, ℤ)
  | [] => 1
  | [r] => T ^ r
  | r :: rs => T ^ r * S * wordToMatrix rs

/-- `wordToMatrix`'s defining equation on a genuine (nonempty-tailed) cons cell. Stated
separately from the raw pattern match because the tail's shape (singleton vs. longer) is not
syntactically visible at call sites that only know `rs ≠ []`. -/
theorem wordToMatrix_cons_of_ne_nil (r : ℤ) (rs : List ℤ) (h : rs ≠ []) :
    wordToMatrix (r :: rs) = T ^ r * S * wordToMatrix rs := by
  match rs, h with
  | _ :: _, _ => rfl

/-- The letter product `∏_{j=1}^r T^{b_j}S` of `[b₁,…,b_r]`, where
`T^bS = (b -1; 1 0)`: the matrix `γ` of [RW26, Radchenko, Wheeler (2026), Proposition 2(ii),
`prop:prod.id.mod,fad`]. Unlike `wordToMatrix`, it has no trailing power of `T`. -/
def letterWord (bs : List ℤ) : SL(2, ℤ) :=
  (bs.map fun b => T ^ b * S).prod

/-- The empty letter product is the identity. -/
@[simp]
theorem letterWord_nil : letterWord [] = 1 := rfl

/-- Peeling the first letter of `letterWord`. -/
@[simp]
theorem letterWord_cons (b : ℤ) (bs : List ℤ) :
    letterWord (b :: bs) = T ^ b * S * letterWord bs := by
  simp [letterWord]

/-- A one-letter word is its letter `T^aS`. -/
@[simp]
theorem letterWord_singleton (a : ℤ) : letterWord [a] = T ^ a * S := by
  rw [letterWord_cons, letterWord_nil, mul_one]

/-! ### AFK25 word shape

An AFK25 word has at least two exponents, and only its two endpoint exponents may be below two.
-/

/-- AFK25's word-shape predicate: a list `[r₁,…,r_{n+1}]` (length `≥ 2`, so `n ≥ 1`) all of whose
interior entries (every entry but the first and last) are `≥ 2`: the shape of the words of
[AFK25, Theorem C.4, `thm:tsaltexpn`]. -/
structure IsHJWord (l : List ℤ) : Prop where
  /-- The word has at least two entries, i.e. `n ≥ 1`. -/
  two_le_length : 2 ≤ l.length
  /-- Every entry but the first and the last is `≥ 2`. -/
  interior_ge_two : ∀ x ∈ (l.drop 1).dropLast, 2 ≤ x

/-! ### The tail invariant

Everything here follows from one invariant of the word's *tail*:

> if `[r₂,…,r_{n+1}]` has every entry but the last `≥ 2`, then its matrix `N` satisfies
> `0 ≤ N₁₀ < N₀₀`.

The invariant is immediate by induction, because prepending a letter `r ≥ 2` sends `(N₀₀, N₁₀)` to
`(r·N₀₀ - N₁₀, N₀₀)`, and `r·N₀₀ - N₁₀ > N₀₀` exactly when `(r-1)·N₀₀ > N₁₀`. Since `hjStep`'s
exponent is `⌈M₀₀/M₁₀⌉`, and for `M = T^r S N` that is `r - ⌊N₁₀/N₀₀⌋ = r`, the head of the word is
*read off* the matrix, whatever its sign, and `hjStep`'s second component is the matrix of the
tail: `hjStep` inverts the construction one letter at a time. The invariant also gives the reverse
implication of [AFK25, Theorem C.4, `thm:tsaltexpn`]: the lower-left entry of `T^{r₁} S N` is
`N₀₀ > 0`. -/

/-- The shape of the *tail* `[r₂,…,r_{n+1}]` of an AFK25 word: nonempty, with every entry but the
last `≥ 2`. `IsHJWord l` is exactly `l = r₁ :: rest` with `IsHJTail rest`
(`IsHJWord.isHJTail_tail`), the head `r₁` being AFK25's exempt first exponent. -/
structure IsHJTail (l : List ℤ) : Prop where
  /-- The tail is nonempty: an AFK25 word has `n ≥ 1`, hence at least two entries in all. -/
  ne_nil : l ≠ []
  /-- Every entry but the last is `≥ 2`. -/
  dropLast_ge_two : ∀ x ∈ l.dropLast, 2 ≤ x

/-- The first column of `T^r S N`, which is how `wordToMatrix` prepends a letter:
`(T^r S N)₀₀ = r·N₀₀ - N₁₀` and `(T^r S N)₁₀ = N₀₀`. -/
theorem T_zpow_mul_S_mul_firstCol (r : ℤ) (N : SL(2, ℤ)) :
    (T ^ r * S * N : SL(2, ℤ)) 0 0 = r * N 0 0 - N 1 0 ∧
      (T ^ r * S * N : SL(2, ℤ)) 1 0 = N 0 0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, coe_S, Matrix.mul_apply,
    Fin.sum_univ_two]
  norm_num
  ring

/-- The lower-left entry of `T^r` is `0`, its top-left entry `1`. -/
theorem T_zpow_firstCol (r : ℤ) :
    (T ^ r : SL(2, ℤ)) 0 0 = 1 ∧ (T ^ r : SL(2, ℤ)) 1 0 = 0 := by
  simp [coe_T_zpow]

/-- **The tail invariant**: a word whose entries are all `≥ 2` except possibly the last has
`0 ≤ N₁₀ < N₀₀`. Proved by induction on the word; see the section comment for its uses. -/
theorem wordToMatrix_lowerLeft_lt_topLeft :
    ∀ {l : List ℤ}, IsHJTail l →
      0 ≤ (wordToMatrix l) 1 0 ∧ (wordToMatrix l) 1 0 < (wordToMatrix l) 0 0 := by
  intro l
  induction l with
  | nil => intro hl; exact absurd rfl hl.ne_nil
  | cons r rest ih =>
    intro hl
    rcases eq_or_ne rest [] with hrest | hrest
    · subst hrest
      obtain ⟨ha, hc⟩ := T_zpow_firstCol r
      refine ⟨?_, ?_⟩ <;> rw [show wordToMatrix [r] = T ^ r from rfl] <;> omega
    · have hrec : IsHJTail rest :=
        ⟨hrest, fun x hx => hl.dropLast_ge_two x (by
          rw [List.dropLast_cons_of_ne_nil hrest]; exact List.mem_cons_of_mem _ hx)⟩
      have hr : 2 ≤ r := hl.dropLast_ge_two r (by
        rw [List.dropLast_cons_of_ne_nil hrest]; exact List.mem_cons_self)
      obtain ⟨hc0, hlt⟩ := ih hrec
      obtain ⟨ha, hc⟩ := T_zpow_mul_S_mul_firstCol r (wordToMatrix rest)
      rw [wordToMatrix_cons_of_ne_nil r rest hrest, ha, hc]
      constructor
      · omega
      · nlinarith

/-- **`hjStep` reads the head of a word off its matrix.** For `M = T^r S N` with `N` the matrix of
an AFK25-shaped tail, `hjStep M = (r, N)`: the exponent because `⌈M₀₀/M₁₀⌉ = r - ⌊N₁₀/N₀₀⌋` and
the tail invariant makes that floor `0`, the matrix because `S⁻¹ T^{-r} (T^r S N) = N`. No sign
condition on `r` is needed, matching AFK25's exemption of the first exponent. -/
theorem hjStep_wordToMatrix_cons {r : ℤ} {rest : List ℤ} (h : IsHJTail rest) :
    hjStep (wordToMatrix (r :: rest)) = (r, wordToMatrix rest) := by
  obtain ⟨hc0, hlt⟩ := wordToMatrix_lowerLeft_lt_topLeft h
  set N := wordToMatrix rest with hN
  have hcons : wordToMatrix (r :: rest) = T ^ r * S * N :=
    wordToMatrix_cons_of_ne_nil r rest h.ne_nil
  obtain ⟨ha, hc⟩ := T_zpow_mul_S_mul_firstCol r N
  have hpos : 0 < N 0 0 := lt_of_le_of_lt hc0 hlt
  have hexp : -((-((wordToMatrix (r :: rest)) 0 0)) / ((wordToMatrix (r :: rest)) 1 0)) = r := by
    rw [hcons, ha, hc]
    have hrw : -(r * N 0 0 - N 1 0) = N 1 0 + (-r) * (N 0 0) := by ring
    rw [hrw, Int.add_mul_ediv_right _ _ hpos.ne', Int.ediv_eq_zero_of_lt hc0 hlt]
    ring
  refine Prod.ext ?_ ?_
  · exact hexp
  · change S⁻¹ * T ^ (-(-((-((wordToMatrix (r :: rest)) 0 0)) /
      ((wordToMatrix (r :: rest)) 1 0)))) * wordToMatrix (r :: rest) = N
    rw [hexp, hcons]
    group

/-- Every AFK25 word splits as an exempt head and a tail of the shape `IsHJTail`. -/
theorem IsHJWord.isHJTail_tail {r : ℤ} {rest : List ℤ} (h : IsHJWord (r :: rest)) :
    IsHJTail rest :=
  ⟨fun hnil => by
      rw [hnil] at h
      simpa using h.two_le_length,
    fun x hx => h.interior_ge_two x (by simpa using hx)⟩

/-- **Reverse implication in [AFK25, Theorem C.4, `thm:tsaltexpn`]**: the matrix represented by
an AFK25-shaped word has positive lower-left entry. Indeed, that entry is the positive top-left
entry of the word's tail. -/
theorem wordToMatrix_lowerLeft_pos {l : List ℤ} (hl : IsHJWord l) :
    0 < (wordToMatrix l) 1 0 := by
  match l, hl with
  | r :: rest, hl =>
    have htail := hl.isHJTail_tail
    obtain ⟨hc0, hlt⟩ := wordToMatrix_lowerLeft_lt_topLeft htail
    rw [wordToMatrix_cons_of_ne_nil r rest htail.ne_nil,
      (T_zpow_mul_S_mul_firstCol r (wordToMatrix rest)).2]
    omega

end SIC
