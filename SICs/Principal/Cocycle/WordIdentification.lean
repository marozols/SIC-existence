/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Quadratic.Stabilizers
import SICs.SL2Z.Words

/-!
# Hirzebruch–Jung Steps of the Principal Word

One step of the general Hirzebruch–Jung algorithm peels `T^{d-1}S` from every positive power of
`U_d`, so the word of `A_d` is `[d-1,d-1,d-1,0]`.

`SICs.SL2Z.Words`'s `hjStep` is one step of the general-layer word algorithm, defined for an
arbitrary `SL₂(ℤ)` matrix with positive lower-left entry. `SICs.Principal.Quadratic.Stabilizers`'s
`principalA_eq_T_zpow_mul_S_word` is the
principal family's own, independently derived word `A_d = (T^{d-1}S)³`
(the three-factor word decomposition).

This file proves they agree: the general step, run on `A_d`, peels exactly `T^{d-1}S` three
times and then stops at the identity, so the word of `A_d` is
```text
[d-1, d-1, d-1, 0].
```

This is the matrix-level half of the ground-truth comparison with the independently computed
principal value; the
analytic half (matching the resulting `σ_S` factors) additionally needs
`SICs.Cocycle.SigmaS.Reduction`.

The intermediate matrices are the lower powers of the stabilizer, `U_d²` and `U_d`. The same peel
applies to every positive power of `U_d`, giving the repeated word `[d-1, ..., d-1, 0]` for
`U_d^n`.

## Main declarations

- `principalUPowerWord`, `wordToMatrix_principalUPowerWord`, `hjStep_principalU_pow_succ`: the
  repeated word for `U_d^n`, its matrix, and one canonical peel from every positive power.
- `hjStep_principalA`, `hjStep_principalU_sq`, `hjStep_principalU`: the three peels, each giving
  exponent `d-1` and the next lower power of `U_d`.
- `principalU_sq_lowerLeft`, `principalU_lowerLeft`: the lower-left entries of the intermediate
  matrices.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Theorem `thm:tsaltexpn`, equation (8.5).
-/

open scoped MatrixGroups

namespace SIC

/-! ### Repeated canonical words for powers of the stabilizer

The canonical word for `U_d^n` is the repeated word `[d-1, ..., d-1, 0]`, so one
Hirzebruch--Jung step peels `T^(d-1) S` from every positive power. Specializing to the first three
powers gives the concrete peels below. -/

/-- The repeated Hirzebruch--Jung word
`[d-1, ..., d-1, 0]` with `n` copies of `d-1`, representing `U_d^n`. -/
def principalUPowerWord (d : ℕ) : ℕ → List ℤ
  | 0 => [0]
  | n + 1 => ((d : ℤ) - 1) :: principalUPowerWord d n

/-- The repeated principal word is never empty. -/
private lemma principalUPowerWord_ne_nil (d n : ℕ) : principalUPowerWord d n ≠ [] := by
  cases n <;> simp [principalUPowerWord]

/-- The repeated principal word is a list of `n` copies of `d-1`, followed by `0`. -/
private lemma principalUPowerWord_eq_replicate (d n : ℕ) :
    principalUPowerWord d n = List.replicate n ((d : ℤ) - 1) ++ [0] := by
  induction n with
  | zero => simp [principalUPowerWord]
  | succ n ih => simp [principalUPowerWord, ih, List.replicate_succ]

/-- For `d > 3`, every nonterminal exponent of the repeated principal word is at least two. -/
private lemma principalUPowerWord_isHJTail (d : ℕ) (hd : 3 < d) (n : ℕ) :
    IsHJTail (principalUPowerWord d n) := by
  refine ⟨principalUPowerWord_ne_nil d n, ?_⟩
  rw [principalUPowerWord_eq_replicate]
  simp only [List.dropLast_concat]
  intro x hx
  rw [List.mem_replicate] at hx
  rcases hx with ⟨-, rfl⟩
  omega

/-- The repeated word evaluates to the corresponding power of the principal stabilizer:
`wordToMatrix [d-1, ..., d-1, 0] = U_d^n`. -/
theorem wordToMatrix_principalUPowerWord (d n : ℕ) :
    wordToMatrix (principalUPowerWord d n) = principalU d ^ n := by
  induction n with
  | zero => simp [principalUPowerWord, wordToMatrix]
  | succ n ih =>
      rw [principalUPowerWord, wordToMatrix_cons_of_ne_nil _ _
        (principalUPowerWord_ne_nil d n), ih, ← principalU_eq_T_zpow_mul_S, pow_succ']

/-- One Hirzebruch--Jung step peels one copy of `T^(d-1)S` from every positive power of `U_d`:
`hjStep (U_d^(n+1)) = (d-1, U_d^n)`. The three concrete peels identifying the word of
`A_d=U_d^3` are its first three instances. -/
theorem hjStep_principalU_pow_succ (d : ℕ) (hd : 3 < d) (n : ℕ) :
    hjStep (principalU d ^ (n + 1)) = ((d : ℤ) - 1, principalU d ^ n) := by
  rw [← wordToMatrix_principalUPowerWord d (n + 1), principalUPowerWord,
    hjStep_wordToMatrix_cons (principalUPowerWord_isHJTail d hd n),
    wordToMatrix_principalUPowerWord]

/-! ### The three peels of the level matrix

Specializing the repeated-word step to `U_d³`, `U_d²`, and `U_d` identifies every matrix visited
by the word for `A_d`. The explicit square in `SICs.Principal.Quadratic.Stabilizers` also
supplies its lower-left entry to the word-value calculation.
-/

/-- **First peel.** `hjStep` at `A_d = U_d³` gives exponent `d-1` and reduces to `U_d²`. -/
theorem hjStep_principalA (d : ℕ) (hd : 3 < d) :
    hjStep (principalA d) = ((d : ℤ) - 1, principalU d ^ 2) := by
  simpa only [principalA] using hjStep_principalU_pow_succ d hd 2

/-- **Second peel.** `hjStep` at `U_d²` gives exponent `d-1` and reduces to `U_d`. -/
theorem hjStep_principalU_sq (d : ℕ) (hd : 3 < d) :
    hjStep (principalU d ^ 2) = ((d : ℤ) - 1, principalU d) := by
  simpa only [pow_one] using hjStep_principalU_pow_succ d hd 1

/-- **Third and last peel.** `hjStep` at `U_d` gives exponent `d-1` and reduces to the identity,
whose lower-left entry is `0`: the recursion's stopping condition. -/
theorem hjStep_principalU (d : ℕ) (hd : 3 < d) :
    hjStep (principalU d) = ((d : ℤ) - 1, 1) := by
  simpa only [Nat.zero_add, pow_one, pow_zero] using hjStep_principalU_pow_succ d hd 0

/-! ### Component forms

`wordSigmaS` (`SICs.Cocycle.Word.Basic`) consumes the reduced matrix of `hjStep` inside a
dependent proof argument, so the packed `Prod` equations above are restated for that component.
-/

/-- `hjStep`'s reduced matrix at `A_d`. -/
theorem hjStep_snd_principalA (d : ℕ) (hd : 3 < d) :
    (hjStep (principalA d)).2 = principalU d ^ 2 := by rw [hjStep_principalA d hd]

/-- `hjStep`'s reduced matrix at `U_d²`. -/
theorem hjStep_snd_principalU_sq (d : ℕ) (hd : 3 < d) :
    (hjStep (principalU d ^ 2)).2 = principalU d := by rw [hjStep_principalU_sq d hd]

/-- `hjStep`'s reduced matrix at `U_d` is the identity: the recursion terminates. -/
theorem hjStep_snd_principalU (d : ℕ) (hd : 3 < d) :
    (hjStep (principalU d)).2 = 1 := by rw [hjStep_principalU d hd]

/-- The lower-left entry of `U_d²`, the first intermediate matrix of the word walk. -/
theorem principalU_sq_lowerLeft (d : ℕ) : (principalU d ^ 2 : SL(2, ℤ)) 1 0 = (d : ℤ) - 1 := by
  rw [coe_principalU_sq]
  norm_num

/-- The lower-left entry of `U_d`, the second intermediate matrix of the word walk. -/
theorem principalU_lowerLeft (d : ℕ) : (principalU d : SL(2, ℤ)) 1 0 = 1 := by
  simp [coe_principalU]

end SIC
