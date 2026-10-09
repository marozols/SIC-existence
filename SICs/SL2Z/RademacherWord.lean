/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.DedekindReciprocity
import SICs.SL2Z.WordAccumulator

/-!
# The Rademacher invariant along the Hirzebruch--Jung word

The Rademacher invariant `Ψ` along the canonical Hirzebruch–Jung word.

This file connects the two descriptions of the Rademacher invariant that the project needs: the
Dedekind-sum formula `SICs.SL2Z.Rademacher.rademacherInvariant` of [AFK25, Definition 1.29,
`df:meyinv`], which the Shintani--Faddeev phase is defined with, and the word accumulator
`SICs.SL2Z.WordAccumulator.wordRademacher`, which is what the real cocycle actually produces
(`SICs.Cocycle.Word.Reflection.wordSfExpArg_eq`).

## The identity

For every `M` whose word walk is defined,

```text
Ψ(M) = W(M) + 3 - 3·sgn(Tr M),
```

so the two agree exactly when `Tr M > 0` -- which is automatic at a fixed point in the cocycle's
real domain, since there `Tr M = j_M(τ) + 1/j_M(τ)`.

The proof is an induction along `hjStep`, and its one-step form is
`rademacherInvariant_hjStep`:

```text
Ψ(M) = r - 3 + Ψ(M') + 3·sgn(Tr M') - 3·sgn(Tr M),   (r, M') = hjStep M.
```

The sign terms are not decoration: `Tr M > 0` does **not** propagate to `M'` (at
`M = \begin{pmatrix}100&-167\\3&-5\end{pmatrix}` it fails, with `Tr M' = 0`), so the naive
relation `Ψ(M) = r - 3 + Ψ(M')` is false. What does propagate is the combination
`Ψ - W + 3·sgn(Tr)`, which is constant along the word and equal to `3` at its terminal `T^b`.

## Attribution

None of this is new. Rademacher's own `Ψ` is the invariant of [AFK25, Definition 1.29,
`df:meyinv`] verbatim ([86, Rademacher (1955), Satz 7, eq. (11)]), and he evaluates it along a
word in the modular generators in [86, Rademacher (1955), Satz 8, eq. (26)]: for a cyclically
reduced `M = TU^{ε₁}T⋯TU^{ε_ν}` in his generators, `Ψ(M) = Σ ε_i`. The same statement, in the same
notation, is [88, Rademacher and Grosswald (1972), Lemma 7, eq. (70), p. 58]. The
Hirzebruch--Jung counterpart of that -- the same invariant, along the word this project's cocycle
actually walks -- is published
as [72, Kopp (2024), Proposition 7.21, `prop:globalphase`]; see below. The proof here is
Rademacher's argument using the reciprocity law and the transformation theory of Satz 7,
rather than Kopp's appeal to Meyer and Zagier. Beware that [86] names the generators the other way
round: its `S` is this project's `T`, and its `T` is this project's `S`.

In terms of the Rademacher *function* `Φ = Ψ + 3·sgn(c·Tr)` used by [72, Kopp (2024),
equation (2.5), `eq:Phi`] the identity below reads simply `Φ(M) = W(M) + 3`, for every `M` with
`M₁₀ > 0`; the sign term appears only because [AFK25] and [86] work with the Rademacher *symbol*
`Ψ`, which already carries the `-3·sgn(c·Tr)` correction. At `M₁₀ = 0`, where the word is a bare
`T`-power, both sign terms vanish and the identity is instead `Φ(M) = Ψ(M) = W(M)`.

That form of the identity is [72, Kopp (2024), Proposition 7.21, `prop:globalphase`], which proves
`-3ℓ + Σ b_n = Φ(P) - 3` for `P = T^{b₀}S⋯T^{b_{ℓ-1}}S` with `β = [b₀,…,b_{ℓ-1}]` purely
periodic. That is the same Hirzebruch--Jung word and the same `Φ`. What is added here is an
arbitrary `M` in place of a purely periodic word, a terminal `T`-power in the word, and hence the
`-3·sgn(Tr M)` correction, which the purely periodic case does not need.

All three additions are bookkeeping over the one-step relation `rademacherInvariant_hjStep`, which
is already the per-letter content of [86, Rademacher (1955), Satz 8, eq. (26)]. A purely periodic
word is that same induction closed into a cycle; an arbitrary `M` is the same induction run out to
its terminal `T`-power instead of back to its start; and the sign term is what holds the induction's
invariant constant across the letters where `Tr` changes sign, which a cyclic word never has to
cross. No arithmetic beyond the single reciprocity application enters at any of the three points, so
the result is Rademacher's, evaluated along a different word.

## The arithmetic input

The Dedekind-sum content is one application of `SICs.SL2Z.DedekindReciprocity`'s
`dedekindSum_reciprocity_mul`, at the pair of consecutive lower-left entries of the word walk.
That is reciprocity cleared of denominators, [88, Rademacher and Grosswald (1972),
equation (35)], which is the form that is polynomial in the matrix entries.

## Main declarations

- `rademacherInvariant_hjStep`: the one-step relation.
- `rademacherInvariant_eq_wordRademacher_add`: the identity above.
- `wordRademacher_eq_rademacherInvariant`: its clean form when `Tr M > 0`.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Definition 1.29 (`df:meyinv`),
  equations (1.42) and (1.43)
- [72] G. S. Kopp, arXiv:2411.06763v3, equation (2.5) (`eq:Phi`) and Proposition 7.21
  (`prop:globalphase`)
- [86] H. Rademacher, "Zur Theorie der Dedekindschen Summen", Math. Z. 63:445--463, 1955,
  equation (3) and Sätze 7 and 8
- [88] H. Rademacher and E. Grosswald, "Dedekind Sums", Carus Mathematical Monographs 16,
  Mathematical Association of America, 1972, equation (35)
-/

namespace SIC

open ModularGroup

open scoped MatrixGroups

/-! ### The terminal matrix

Where the walk stops, the invariant is the `T`-power's exponent and the trace is `2`. -/

/-- At the terminal matrix of a word walk -- lower-left entry `0` and positive top-left entry --
the Rademacher invariant is the `T`-power's exponent, and the trace is `2`. -/
lemma rademacherInvariant_of_lowerLeft_eq_zero (M : SL(2, ℤ)) (hz : M 1 0 = 0)
    (ha : 0 < M 0 0) :
    rademacherInvariant M = (M 0 1 : ℚ) ∧ M 0 0 + M 1 1 = 2 := by
  have hdet : (M : Mat(2, ℤ)).det = 1 := M.2
  rw [Matrix.det_fin_two, hz, mul_zero, sub_zero] at hdet
  have h00 : M 0 0 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h
    · exact h
    · omega
  have h11 : M 1 1 = 1 := by rw [h00] at hdet; omega
  refine ⟨?_, by omega⟩
  rw [rademacherInvariant]
  simp [hz, h11]

/-! ### The one-step relation

Peeling one `T^rS` letter changes the invariant by `r - 3`, up to the two sign corrections. The
Dedekind sums are matched by periodicity in the first argument, oddness, and reciprocity. -/

/-- **The Rademacher invariant along one Hirzebruch--Jung step.** For `M` with positive lower-left
entry and `(r, M') = hjStep M`,

```text
Ψ(M) = r - 3 + Ψ(M') + 3·sgn(Tr M') - 3·sgn(Tr M).
```

The Dedekind-sum content is exactly one instance of `dedekindSum_reciprocity_mul`, at the coprime
pair `(M'₁₀, M₁₀)`: `M₀₀ ≡ -M'₁₀ (mod M₁₀)` moves `𝔰(M₀₀, M₁₀)` to `-𝔰(M'₁₀, M₁₀)`, and reciprocity
then pairs it with `𝔰(M₁₀, M'₁₀)`. Everything else is `det M' = 1`. This is the per-letter form of
[86, Rademacher (1955), Satz 8, eq. (26)] for the Hirzebruch--Jung word; see the file docstring. -/
theorem rademacherInvariant_hjStep (M : SL(2, ℤ))
    (hγ : 0 < M 1 0) :
    rademacherInvariant M =
      ((hjStep M).1 : ℚ) - 3 + rademacherInvariant (hjStep M).2 +
        3 * (Int.sign ((hjStep M).2 0 0 + (hjStep M).2 1 1) : ℚ) -
        3 * (Int.sign (M 0 0 + M 1 1) : ℚ) := by
  obtain ⟨N, hNe⟩ : ∃ N : SL(2, ℤ), (hjStep M).2 = N := ⟨_, rfl⟩
  have hγ0 : M 1 0 ≠ 0 := hγ.ne'
  have hN00 : N 0 0 = M 1 0 := by rw [← hNe]; exact (hjStep_snd_entries M).1
  have hN01 : N 0 1 = M 1 1 := by rw [← hNe]; exact hjStep_snd_topRight M
  have hN10 : N 1 0 = (hjStep M).1 * M 1 0 - M 0 0 := by
    rw [← hNe]; exact (hjStep_snd_entries M).2
  have hc0 : 0 ≤ N 1 0 := by rw [← hNe, hjStep_snd_lowerLeft]; exact Int.emod_nonneg _ hγ0
  have hdetN : M 1 0 * N 1 1 - M 1 1 * N 1 0 = 1 := by
    have h : (N : Mat(2, ℤ)).det = 1 := N.2
    rw [Matrix.det_fin_two, hN00, hN01] at h
    exact h
  have hsignγ : Int.sign (M 1 0 * (M 0 0 + M 1 1)) = Int.sign (M 0 0 + M 1 1) := by
    rw [Int.sign_mul, Int.sign_eq_one_of_pos hγ, one_mul]
  rw [hNe, rademacherInvariant_of_lowerLeft_ne_zero M hγ0, hsignγ,
    Int.sign_eq_one_of_pos hγ]
  rcases eq_or_lt_of_le hc0 with hc | hc
  · -- The reduced matrix is already terminal: `M₁₀ = 1`, and no Dedekind sum survives.
    have hc' : N 1 0 = 0 := hc.symm
    have hγ1 : M 1 0 = 1 := by
      rw [hc', mul_zero, sub_zero] at hdetN
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hdetN with h | h
      · exact h
      · omega
    have h11 : N 1 1 = 1 := by rw [hγ1, one_mul, hc', mul_zero, sub_zero] at hdetN; exact hdetN
    have haα : (hjStep M).1 = M 0 0 := by rw [hγ1, mul_one] at hN10; omega
    obtain ⟨hΨN, _⟩ :=
      rademacherInvariant_of_lowerLeft_eq_zero N hc' (by rw [hN00, hγ1]; norm_num)
    have hs : dedekindSum (M 0 0) (M 1 0) = 0 := by
      rw [hγ1]
      simp [dedekindSum]
    rw [hΨN, hs, hN00, hN01, h11, hγ1, haα]
    norm_num [Int.sign]
    ring
  · -- The generic step, where reciprocity enters.
    have hc0' : N 1 0 ≠ 0 := hc.ne'
    have hcop : IsCoprime (N 1 0) (M 1 0) := ⟨-(M 1 1), N 1 1, by linarith [hdetN]⟩
    have hsα : dedekindSum (M 0 0) (M 1 0) = -dedekindSum (N 1 0) (M 1 0) := by
      have hαeq : M 0 0 = -(N 1 0) + (hjStep M).1 * M 1 0 := by omega
      rw [hαeq, dedekindSum_add_mul_right, dedekindSum_neg_left]
    have hsignc : Int.sign (N 1 0 * (N 0 0 + N 1 1)) = Int.sign (N 0 0 + N 1 1) := by
      rw [Int.sign_mul, Int.sign_eq_one_of_pos hc, one_mul]
    rw [rademacherInvariant_of_lowerLeft_ne_zero N hc0', hsignc,
      Int.sign_eq_one_of_pos hc, hsα, hN00]
    have hγQ : ((M 1 0 : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hγ0
    have hcQ : ((N 1 0 : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc0'
    have hdetQ : ((M 1 0 : ℤ) : ℚ) * ((N 1 1 : ℤ) : ℚ) -
        ((M 1 1 : ℤ) : ℚ) * ((N 1 0 : ℤ) : ℚ) = 1 := by
      exact_mod_cast congrArg (fun t : ℤ => (t : ℚ)) hdetN
    have haQ : ((M 0 0 : ℤ) : ℚ) =
        (((hjStep M).1 : ℤ) : ℚ) * ((M 1 0 : ℤ) : ℚ) - ((N 1 0 : ℤ) : ℚ) := by
      have h : M 0 0 = (hjStep M).1 * M 1 0 - N 1 0 := by omega
      exact_mod_cast congrArg (fun t : ℤ => (t : ℚ)) h
    -- Reciprocity, in the denominator-free form that is polynomial in the matrix entries.
    have hrecip' := dedekindSum_reciprocity_mul hc hγ hcop
    push_cast at haQ hdetQ hrecip' ⊢
    rw [haQ]
    field_simp
    linear_combination hrecip' - hdetQ

/-! ### The identity along the whole word

`Ψ - W + 3·sgn(Tr)` is constant along the walk, and `3` at the terminal matrix. -/

/-- The bounded-recursion form of `rademacherInvariant_eq_wordRademacher_add`. Private: only the
`n = (M 1 0).toNat` instance is of interest. -/
private lemma rademacherInvariant_eq_wordRademacher_aux :
    ∀ (n : ℕ) (M : SL(2, ℤ)) (h0 : 0 ≤ M 1 0), (M 1 0).toNat ≤ n → (M 1 0 = 0 → 0 < M 0 0) →
      rademacherInvariant M =
        (wordRademacher M h0 : ℚ) + 3 - 3 * (Int.sign (M 0 0 + M 1 1) : ℚ) := by
  intro n
  induction n with
  | zero =>
      intro M h0 hn hterm
      have hz : M 1 0 = 0 := by omega
      obtain ⟨hΨ, htr⟩ := rademacherInvariant_of_lowerLeft_eq_zero M hz (hterm hz)
      rw [hΨ, wordRademacher_of_lowerLeft_eq_zero M h0 hz, htr]
      norm_num [Int.sign]
  | succ n ih =>
      intro M h0 hn hterm
      rcases eq_or_ne (M 1 0) 0 with hz | hz
      · obtain ⟨hΨ, htr⟩ := rademacherInvariant_of_lowerLeft_eq_zero M hz (hterm hz)
        rw [hΨ, wordRademacher_of_lowerLeft_eq_zero M h0 hz, htr]
        norm_num [Int.sign]
      have hγ : 0 < M 1 0 := h0.lt_of_ne (Ne.symm hz)
      obtain ⟨N, hNe⟩ : ∃ N : SL(2, ℤ), (hjStep M).2 = N := ⟨_, rfl⟩
      have h0N : 0 ≤ N 1 0 := by
        rw [← hNe, hjStep_snd_lowerLeft]; exact Int.emod_nonneg _ hγ.ne'
      have hltN : N 1 0 < M 1 0 := by
        rw [← hNe, hjStep_snd_lowerLeft]; exact Int.emod_lt_of_pos _ hγ
      have hmeas : (N 1 0).toNat ≤ n := by omega
      have htermN : N 1 0 = 0 → 0 < N 0 0 := by
        intro _
        rw [← hNe, (hjStep_snd_entries M).1]; exact hγ
      have hstep := rademacherInvariant_hjStep M hγ
      rw [hNe] at hstep
      rw [hstep, ih N h0N hmeas htermN, wordRademacher_step h0 hz hNe h0N]
      push_cast
      ring

/-- **The Rademacher invariant is the word accumulator, up to a trace sign.** For every `M` whose
word walk is defined -- lower-left entry nonnegative, and top-left entry positive if it vanishes --

```text
Ψ(M) = W(M) + 3 - 3·sgn(Tr M).
```

For the Rademacher *function* `Φ = Ψ + 3·sgn(c·Tr)` the identity reads `Φ(M) = W(M) + 3` whenever
`M₁₀ > 0`, which is [72, Kopp (2024), Proposition 7.21, `prop:globalphase`] -- stated there as
`-3ℓ + Σ b_n = Φ(P) - 3` for the purely periodic word `P = T^{b₀}S⋯T^{b_{ℓ-1}}S`. This statement
adds an arbitrary `M` in place of a purely periodic word, a terminal `T`-power, and hence the
`-3·sgn(Tr M)` correction that the purely periodic case does not need.

It is also the Hirzebruch--Jung counterpart of [86, Rademacher (1955), Satz 8, eq. (26)] and
[88, Rademacher and Grosswald (1972), Lemma 7, eq. (70), p. 58], which state the same evaluation
along a cyclically reduced word in the elliptic generators. The proof uses Rademacher's
reciprocity law [86, Rademacher (1955), eq. (3)] and the transformation theory of
[86, Rademacher (1955), Satz 7].

See the file docstring for why the sign term cannot be dropped from the induction. -/
@[source "86, Satz 8, p. 453 (equation (26), Hirzebruch–Jung word)"
  "88, Lemma 7, p. 58 (equation (70), Hirzebruch–Jung word)"]
theorem rademacherInvariant_eq_wordRademacher_add (M : SL(2, ℤ))
    (h0 : 0 ≤ M 1 0) (hterm : M 1 0 = 0 → 0 < M 0 0) :
    rademacherInvariant M =
      (wordRademacher M h0 : ℚ) + 3 - 3 * (Int.sign (M 0 0 + M 1 1) : ℚ) :=
  rademacherInvariant_eq_wordRademacher_aux (M 1 0).toNat M h0 le_rfl hterm

/-- **At positive trace the two agree exactly.** This is the case the Shintani--Faddeev cocycle
uses: at a fixed point of `M` in its real domain the trace is `j_M(τ) + 1/j_M(τ) > 0`. -/
theorem wordRademacher_eq_rademacherInvariant (M : SL(2, ℤ))
    (h0 : 0 ≤ M 1 0) (hterm : M 1 0 = 0 → 0 < M 0 0) (htr : 0 < M 0 0 + M 1 1) :
    (wordRademacher M h0 : ℚ) = rademacherInvariant M := by
  rw [rademacherInvariant_eq_wordRademacher_add M h0 hterm, Int.sign_eq_one_of_pos htr]
  norm_num

end SIC
