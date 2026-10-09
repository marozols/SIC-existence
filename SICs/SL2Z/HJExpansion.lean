/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.WordPeriods
import SICs.SL2Z.WordAccumulator

/-!
# The Hirzebruch--Jung expansion of a real number and its cycle matrices

The Hirzebruch–Jung expansion of a real number: rotated numbers `β_n`, cycle matrices `A_{m,n}`,
Kopp's Lemma 7.5, the bridge to the Hirzebruch–Jung word, and the global phase sum `γ(A) = W(A)`
of Proposition 7.21.

This file builds the real-number half of the Hirzebruch--Jung cycle data of [72, Kopp (2024),
Definition 7.4, `defn:cycledata`] and proves the Jacobi-denominator product formula [72, Kopp
(2024), Lemma 7.5, `lem:betajs`] that the Stark-unit comparison runs on.

## What the file builds

A Hirzebruch--Jung (or minus, or backward) continued fraction expands a real number as
$\beta = b_0 - 1/(b_1 - 1/(b_2 - \cdots))$ with integer partial quotients. One step of the
expansion is the *rotation*

$$
b = \lceil\beta\rceil,\qquad \mathcal R\beta = \frac1{b - \beta},
$$

so that $\beta = b - 1/\mathcal R\beta$; iterating it produces Kopp's rotated numbers
$\beta_n = \mathcal R^n\beta$ and partial quotients $b_n = \lceil\beta_n\rceil$. Since
$b - \beta \in (0,1)$ at an irrational $\beta$, the rotation lands in $(1,\infty)$ and stays
irrational, so every partial quotient after the first is at least $2$.

The one-step identity $\beta = b - 1/\mathcal R\beta$ says exactly that the matrix
$T^bS = \left(\begin{smallmatrix}b&-1\\1&0\end{smallmatrix}\right)$ carries $\mathcal R\beta$ to
$\beta$ under the Möbius action, with Jacobi denominator $j_{T^bS}(x) = x$
(`flt_T_zpow_mul_S` and `fltDenominator_T_zpow_mul_S`, `SICs.SL2Z.WordPeriods`). Chaining
$n$ steps gives Kopp's matrices

$$
A_{0,n} = T^{b_0}S\,T^{b_1}S\cdots T^{b_{n-1}}S,
$$

for which $A_{0,n}\cdot\beta_n = \beta$ and, by the cocycle property of the Jacobi denominator,

$$
j_{A_{0,n}}(\beta_n) = \beta_1\beta_2\cdots\beta_n .
$$

That product formula is [72, Kopp (2024), Lemma 7.5, `lem:betajs`]. Kopp's general matrices
$A_{m,n} = T^{b_m}S\cdots T^{b_{n-1}}S$ for $m\le n$ are not defined separately here: they are
$A_{0,n-m}$ formed at $\beta_m$ in place of $\beta$, because rotating $m$ times shifts the whole
sequence of partial quotients. So `hjCycleMatrix (hjPeriod β m) (n - m)` *is* $A_{m,n}$, and the
single-index statements below, read at $\beta_m$, are Kopp's two-index ones. Kopp's composition
law $A_{n_1,n_2}A_{n_2,n_3} = A_{n_1,n_3}$ is `hjCycleMatrix_add`.

## The expansion as a Hirzebruch--Jung word

The section on the word of the cycle matrix identifies $A_{0,n}$ with a Hirzebruch--Jung word of
[AFK25, Theorem C.4, `thm:tsaltexpn`] in the sense of `SICs.SL2Z.Words`. The two conventions
differ by one letter: an AFK25 word ends in a bare power of $T$, whereas Kopp's purely periodic
word ends in $S$. So $A_{0,n} = $ `wordToMatrix (hjLetters β n ++ [0])`, and this list is an
AFK25-shaped word because its interior letters are the partial quotients of the *rotated* numbers
$\beta_1,\dots,\beta_{n-1}$, all of which exceed $1$ and hence have ceiling at least $2$ — no
hypothesis on $\beta$ beyond irrationality is needed. Since `hjStep` reads the head of such a word
off its matrix (`hjStep_wordToMatrix_cons`), it peels exactly one rotation
(`hjStep_hjCycleMatrix`).

That last identity is what connects the expansion to the word-chained cocycle of
`SICs.Cocycle.Word.Basic`: seeded at $A_{0,n}$, `wordSigmaS`'s recursion visits precisely the
matrices $A_{m,n}$, so its factors are evaluated at the rotated numbers $\beta_m$.

## Periodicity is not proved here

Kopp's cycle data also asks that the expansion of $\beta$ be *purely periodic*, which holds
exactly when $\beta$ is a real quadratic number with $0<\beta'<1<\beta$ [72, Kopp (2024),
Proposition 7.2, `prop:quadhj`]. Nothing in this file needs that: every statement holds for an
arbitrary irrational $\beta$, and periodicity enters only as the hypothesis `hjPeriod β ℓ = β` where
a consumer needs a matrix fixing $\beta$.

## References

- [72, Kopp (2024), Definition 7.4, `defn:cycledata`] and [72, Kopp (2024), Lemma 7.5,
  `lem:betajs`].
- [85, Popescu-Pampu (2007), Definition 2.1, `continued`]: the minus continued fraction and the
  rotation map, the terminology this file follows.
- `SICs.SL2Z.Words`: AFK25-shaped words and `hjStep`.
-/

open ModularGroup MatrixGroups

open scoped MatrixGroups

namespace SIC

/-! ### The rotation map and its partial quotients

One step of the Hirzebruch--Jung expansion records the ceiling of the current number and passes
to the reciprocal of the remaining fractional gap. At an irrational argument that gap lies
strictly between `0` and `1`, so the step lands above `1` and the next ceiling is at least `2`.
The step is the Möbius action of `T^b S` read backwards. -/

/-- The Hirzebruch--Jung partial quotient of `β`: Kopp's `b_n` of [72, Kopp (2024), Definition
7.4, `defn:cycledata`], which equals `⌈β_n⌉` at an irrational `β_n`. Kopp writes no ceiling; the
ceiling is what makes the map total. -/
noncomputable def hjLetter (β : ℝ) : ℤ := ⌈β⌉

/-- One step of the Hirzebruch--Jung rotation, `β ↦ 1/(⌈β⌉ - β)`: the map whose orbits are the
minus continued fraction expansions of [85, Popescu-Pampu (2007), Definition 2.1, `continued`].
Kopp's rotated numbers `β_n` of [72, Kopp (2024), Definition 7.4, `defn:cycledata`] are its iterates
(`hjPeriod`). -/
noncomputable def hjRotate (β : ℝ) : ℝ := ((hjLetter β : ℝ) - β)⁻¹

/-- At an irrational argument the fractional gap `⌈β⌉ - β` is strictly positive. -/
theorem hjLetter_sub_pos {β : ℝ} (hβ : Irrational β) : 0 < (hjLetter β : ℝ) - β := by
  apply sub_pos.mpr
  exact lt_of_le_of_ne (Int.le_ceil β) (hβ.ne_int _)

/-- The fractional gap `⌈β⌉ - β` is always strictly below `1`. -/
theorem hjLetter_sub_lt_one (β : ℝ) : (hjLetter β : ℝ) - β < 1 := by
  have := Int.ceil_lt_add_one β
  dsimp [hjLetter] at *
  linarith

/-- **The rotation lands above `1`.** Since the gap `⌈β⌉ - β` lies in `(0,1)` at an irrational
`β`, its reciprocal exceeds `1`. This is what makes every partial quotient after the first at
least `2`. -/
theorem one_lt_hjRotate {β : ℝ} (hβ : Irrational β) : 1 < hjRotate β := by
  rw [hjRotate, one_lt_inv₀ (hjLetter_sub_pos hβ)]
  exact hjLetter_sub_lt_one β

/-- **The rotation preserves irrationality**: subtracting from an integer and inverting both do.
-/
theorem irrational_hjRotate {β : ℝ} (hβ : Irrational β) : Irrational (hjRotate β) := by
  rw [hjRotate, irrational_inv_iff, irrational_intCast_sub_iff]
  exact hβ

/-- **Partial quotients above `1` are at least `2`**: `⌈β⌉ ≥ 2` whenever `β > 1`. Together with
`one_lt_hjRotate` this gives Kopp's condition `b_n ≥ 2` of [72, Kopp (2024), Definition 7.4,
`defn:cycledata`] at every index after the first. -/
theorem two_le_hjLetter {β : ℝ} (hβ : 1 < β) : 2 ≤ hjLetter β := by
  rw [show (2 : ℤ) = 1 + 1 by rfl, Int.add_one_le_iff]
  change 1 < ⌈β⌉
  exact Int.lt_ceil.mpr (by simpa using hβ)

/-- **The rotation ignores integer shifts**: `ℛ(β + k) = ℛβ` for `k ∈ ℤ`, because
`⌈β + k⌉ - (β + k) = ⌈β⌉ - β`. This is why a matrix `T^k A` that fixes `β` forces `k = 0` in
`SICs.SL2Z.HJStabilizer`. -/
theorem hjRotate_add_intCast (β : ℝ) (k : ℤ) : hjRotate (β + k) = hjRotate β := by
  unfold hjRotate hjLetter
  rw [Int.ceil_add_intCast]
  push_cast
  ring_nf

/-! ### The rotated numbers

Kopp's `β_n` are the iterates of the rotation. Peeling one step from the *left* — the form the
word recursion uses — replaces `β` by `hjRotate β` and lowers the index; peeling from the right
applies one more rotation to `β_n`. -/

/-- Kopp's rotated number `β_n`, the `n`-th iterate of the Hirzebruch--Jung rotation at `β`
([72, Kopp (2024), Definition 7.4, `defn:cycledata`]). -/
noncomputable def hjPeriod (β : ℝ) (n : ℕ) : ℝ := hjRotate^[n] β

/-- The zeroth rotated number is `β` itself: `β_0 = β`. -/
@[simp] theorem hjPeriod_zero (β : ℝ) : hjPeriod β 0 = β := rfl

/-- Peeling one rotation from the left: `β_{n+1}` at `β` is `β_n` at `hjRotate β`. This is the
recursion `hjCycleMatrix` follows. -/
theorem hjPeriod_succ_left (β : ℝ) (n : ℕ) : hjPeriod β (n + 1) = hjPeriod (hjRotate β) n :=
  Function.iterate_succ_apply _ _ _

/-- Peeling one rotation from the right: `β_{n+1} = hjRotate β_n`. -/
theorem hjPeriod_succ (β : ℝ) (n : ℕ) : hjPeriod β (n + 1) = hjRotate (hjPeriod β n) :=
  Function.iterate_succ_apply' _ _ _

/-- **Rotating shifts the whole sequence**: `β_{m+n}` at `β` is `β_n` at `β_m`. This is why
Kopp's two-index data `A_{m,n}`, `β_n` need no separate definition: they are the one-index data
formed at `β_m`. -/
theorem hjPeriod_add (β : ℝ) (m n : ℕ) : hjPeriod β (m + n) = hjPeriod (hjPeriod β m) n := by
  rw [hjPeriod, hjPeriod, hjPeriod, Nat.add_comm, Function.iterate_add_apply]

/-- Every rotated number of an irrational number is irrational. -/
theorem irrational_hjPeriod {β : ℝ} (hβ : Irrational β) (n : ℕ) : Irrational (hjPeriod β n) := by
  induction n generalizing β with
  | zero => exact hβ
  | succ n ih =>
      rw [hjPeriod_succ_left]
      exact ih (irrational_hjRotate hβ)

/-- **Every rotated number after the first exceeds `1`**, with no hypothesis on `β` beyond
irrationality. -/
theorem one_lt_hjPeriod_succ {β : ℝ} (hβ : Irrational β) (n : ℕ) : 1 < hjPeriod β (n + 1) := by
  rw [hjPeriod_succ]
  exact one_lt_hjRotate (irrational_hjPeriod hβ n)

/-- **All rotated numbers exceed `1`** once `β` itself does: Kopp's standing condition `1 < β` of
[72, Kopp (2024), Definition 7.4, `defn:cycledata`] propagates along the whole expansion. -/
theorem one_lt_hjPeriod {β : ℝ} (hβ : Irrational β) (hβ1 : 1 < β) (n : ℕ) :
    1 < hjPeriod β n := by
  cases n with
  | zero => exact hβ1
  | succ n => exact one_lt_hjPeriod_succ hβ n

/-! ### The cycle matrices

Chaining the generators `T^{b_n}S` along the expansion gives Kopp's matrices `A_{0,n}`, and the
list of partial quotients gives the word they spell. Both are defined by the same left-peeling
recursion as `hjPeriod`, so all three stay in step. -/

/-- The first `n` Hirzebruch--Jung partial quotients of `β`, that is `[b_0, b_1, …, b_{n-1}]`. -/
noncomputable def hjLetters (β : ℝ) : ℕ → List ℤ
  | 0 => []
  | n + 1 => hjLetter β :: hjLetters (hjRotate β) n

/-- Kopp's cycle matrix `A_{0,n} = T^{b_0}S T^{b_1}S ⋯ T^{b_{n-1}}S` of [72, Kopp (2024),
Definition 7.4, `defn:cycledata`]. Kopp's `A_{m,n}` for `m ≤ n` is `hjCycleMatrix (hjPeriod β m)
(n - m)`; see the file docstring. -/
noncomputable def hjCycleMatrix (β : ℝ) : ℕ → SL(2, ℤ)
  | 0 => 1
  | n + 1 => T ^ hjLetter β * S * hjCycleMatrix (hjRotate β) n

/-- The empty word of partial quotients. -/
@[simp] theorem hjLetters_zero (β : ℝ) : hjLetters β 0 = [] := rfl

/-- Unfolding one step of `hjLetters`: the leading letter is `b_0 = ⌈β⌉`, the rest is the word of
the rotated number. -/
theorem hjLetters_succ (β : ℝ) (n : ℕ) :
    hjLetters β (n + 1) = hjLetter β :: hjLetters (hjRotate β) n := rfl

/-- The empty cycle matrix is the identity: `A_{0,0} = I`. -/
@[simp] theorem hjCycleMatrix_zero (β : ℝ) : hjCycleMatrix β 0 = 1 := rfl

/-- Unfolding one step of `hjCycleMatrix`: `A_{0,n+1} = T^{b_0}S · A_{1,n+1}`, the second factor
being the cycle matrix of the rotated number. -/
theorem hjCycleMatrix_succ (β : ℝ) (n : ℕ) :
    hjCycleMatrix β (n + 1) = T ^ hjLetter β * S * hjCycleMatrix (hjRotate β) n := rfl

/-- The word of partial quotients has the expected length. -/
@[simp] theorem hjLetters_length (β : ℝ) (n : ℕ) : (hjLetters β n).length = n := by
  induction n generalizing β with
  | zero => rfl
  | succ n ih => simp [hjLetters_succ, ih]

/-- **Every partial quotient of a number above `1` is at least `2`.** -/
theorem two_le_of_mem_hjLetters {β : ℝ} (hβ : Irrational β) (hβ1 : 1 < β) (n : ℕ) :
    ∀ x ∈ hjLetters β n, 2 ≤ x := by
  induction n generalizing β with
  | zero => simp
  | succ n ih =>
      intro x hx
      rw [hjLetters_succ, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact two_le_hjLetter hβ1
      · exact ih (irrational_hjRotate hβ) (one_lt_hjRotate hβ) x hx

/-- **Kopp's composition law** `A_{n₁,n₂}A_{n₂,n₃} = A_{n₁,n₃}` of [72, Kopp (2024), Definition
7.4, `defn:cycledata`], in the one-index form: `A_{0,m+n} = A_{0,m}·A_{m,m+n}`, the second factor
being the cycle matrix of length `n` formed at `β_m`. -/
theorem hjCycleMatrix_add (β : ℝ) (m n : ℕ) :
    hjCycleMatrix β (m + n) = hjCycleMatrix β m * hjCycleMatrix (hjPeriod β m) n := by
  induction m generalizing β with
  | zero => simp
  | succ m ih =>
      rw [show m + 1 + n = (m + n) + 1 by omega, hjCycleMatrix_succ, ih,
        hjCycleMatrix_succ, hjPeriod_succ_left]
      group

/-- **Right peeling**: `A_{0,n+1} = A_{0,n}·T^{b_n}S`, the case `m = n`, `n = 1` of
`hjCycleMatrix_add`. -/
theorem hjCycleMatrix_succ_right (β : ℝ) (n : ℕ) :
    hjCycleMatrix β (n + 1) = hjCycleMatrix β n * (T ^ hjLetter (hjPeriod β n) * S) := by
  rw [hjCycleMatrix_add β n 1, hjCycleMatrix_succ, hjCycleMatrix_zero, mul_one]

/-- **The top row of `A_{0,n+1}⁻¹` is the bottom row of `A_{0,n}⁻¹`**: from
`hjCycleMatrix_succ_right`, `A_{0,n+1}⁻¹ = (T^{b_n}S)⁻¹ A_{0,n}⁻¹` with
`(T^bS)⁻¹ = [[0, 1], [-1, b]]`, whose top row picks out the bottom row of the other factor. So
consecutive bottom rows of the inverse cycle matrices are the two rows of one determinant-one
matrix, which is what makes them a basis of `ℤ²` in `SICs.SL2Z.HJStabilizer`. -/
theorem hjCycleMatrix_inv_succ_apply_zero (β : ℝ) (n : ℕ) (j : Fin 2) :
    ((hjCycleMatrix β (n + 1))⁻¹ : SL(2, ℤ)) 0 j = ((hjCycleMatrix β n)⁻¹ : SL(2, ℤ)) 1 j := by
  rw [hjCycleMatrix_succ_right, mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, coe_T_zpow_mul_S]
  fin_cases j <;> simp

/-! ### Companion sequences and the action along the cycle

The two identities of this section, `A_{0,n}·β_n = β` and `j_{A_{0,n}}(β_n) = β_1⋯β_n`, use only
the recursion `β_n = b_n - 1/β_{n+1}` of the rotated numbers, never their definition. They are
therefore proved for every sequence `x` obeying that recursion, `x_n = b_n - 1/x_{n+1}` with the
partial quotients `b_n = ⌈β_n⌉` of `β` itself. We call such a sequence a *companion sequence* of
the expansion of `β`; the term is ours. The rotated numbers form one, and so do the Galois
conjugates `β'_n` of a real quadratic `β` (`SICs.Quadratic.ReducedForms`), which is Katok's
sequence `x_i = a_i - 1/x_{i+1}` in the proof of [68, Katok (2003), Theorem 1.4].

Both identities are proved together by one induction on the number of steps, because each
step's Jacobi denominator is the *next* term: peeling `A_{0,n+1} = T^{b_0}S·A_{1,n+1}` and
applying the cocycle laws `flt_mul`/`fltDenominator_mul` gives

```text
A_{0,n+1}·x_{n+1} = (T^{b_0}S)·(A_{1,n+1}·x_{n+1}),
j_{A_{0,n+1}}(x_{n+1}) = j_{T^{b_0}S}(A_{1,n+1}·x_{n+1}) · j_{A_{1,n+1}}(x_{n+1}),
```

and the inner action is `x_1` by the inductive hypothesis (applied to the shifted sequence at the
rotated number), which both evaluates the outer factor to `x_0` and contributes the extra factor
`x_1` to the product. -/

/-- A **companion sequence** of the Hirzebruch--Jung expansion of `β`: a sequence `x` with
`x_{n+1} ≠ 0` and `x_n = b_n - 1/x_{n+1}`, where `b_n = ⌈β_n⌉` are the partial quotients of `β`.
The rotated numbers `β_n` form one (`isHJCompanion_hjPeriod`); so does the sequence of Galois
conjugates of a reduced quadratic irrational, Katok's `x_i` in the proof of [68, Katok (2003),
Theorem 1.4]. The nonvanishing is needed because `1/0 = 0` in Lean would make the recursion
meaningless. -/
def IsHJCompanion (β : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ n, x (n + 1) ≠ 0 ∧ x n = (hjLetter (hjPeriod β n) : ℝ) - 1 / x (n + 1)

/-- A companion sequence has nonzero terms after its initial term. -/
theorem IsHJCompanion.succ_ne_zero {β : ℝ} {x : ℕ → ℝ} (hx : IsHJCompanion β x)
    (n : ℕ) : x (n + 1) ≠ 0 := (hx n).1

/-- The companion recursion is `x_n = b_n - 1/x_{n+1}`. -/
theorem IsHJCompanion.recurrence {β : ℝ} {x : ℕ → ℝ} (hx : IsHJCompanion β x)
    (n : ℕ) : x n = (hjLetter (hjPeriod β n) : ℝ) - 1 / x (n + 1) := (hx n).2

/-- The rotated numbers are a companion sequence of their own expansion: `β_{n+1} ≠ 0` and
`β_n = ⌈β_n⌉ - 1/β_{n+1}`, which is `hjRotate` unfolded. -/
theorem isHJCompanion_hjPeriod {β : ℝ} (hβ : Irrational β) : IsHJCompanion β (hjPeriod β) := by
  intro n
  constructor
  · exact ne_of_gt (lt_trans zero_lt_one (one_lt_hjPeriod_succ hβ n))
  · rw [hjPeriod_succ, hjRotate, one_div, inv_inv]
    ring

/-- **Shifting a companion sequence**: dropping the first term gives a companion sequence of the
rotated number, since the partial quotients of `ℛβ` are those of `β` shifted by one. -/
theorem IsHJCompanion.shift {β : ℝ} {x : ℕ → ℝ} (hx : IsHJCompanion β x) :
    IsHJCompanion (hjRotate β) (fun n ↦ x (n + 1)) := by
  intro n
  obtain ⟨h1, h2⟩ := hx (n + 1)
  exact ⟨h1, by simpa [hjPeriod_succ_left] using h2⟩

/-- The two identities of [72, Kopp (2024), Definition 7.4, `defn:cycledata`] and [72, Kopp (2024),
Lemma 7.5, `lem:betajs`] along a companion sequence, proved by the single induction that needs both.
Private; the two projections `IsHJCompanion.flt_hjCycleMatrix` and
`IsHJCompanion.fltDenominator_hjCycleMatrix` are the interface. -/
private theorem flt_and_fltDenominator_hjCycleMatrix {β : ℝ} {x : ℕ → ℝ}
    (hx : IsHJCompanion β x) (n : ℕ) :
    flt (hjCycleMatrix β n : SL(2, ℤ)) (x n) = x 0 ∧
      fltDenominator (hjCycleMatrix β n : SL(2, ℤ)) (x n) =
        ∏ i ∈ Finset.range n, x (i + 1) := by
  induction n generalizing β x with
  | zero => norm_num [flt, fltDenominator]
  | succ n ih =>
      have ih' := ih hx.shift
      have hprod : ∏ i ∈ Finset.range n, x (i + 1 + 1) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro i _
        exact (hx.succ_ne_zero (i + 1))
      have hB :
          fltDenominator
              ((hjCycleMatrix (hjRotate β) n : SL(2, ℤ)) : Mat(2, ℤ))
              (x (n + 1)) ≠ 0 := by
        rw [ih'.2]
        exact hprod
      constructor
      · rw [hjCycleMatrix_succ, Matrix.SpecialLinearGroup.coe_mul,
          flt_mul _ _ _ hB, ih'.1, flt_T_zpow_mul_S _ (hx.succ_ne_zero 0)]
        simpa using (hx.recurrence 0).symm
      · rw [hjCycleMatrix_succ, Matrix.SpecialLinearGroup.coe_mul,
          fltDenominator_mul _ _ _ hB, ih'.1, fltDenominator_T_zpow_mul_S,
          ih'.2, Finset.prod_range_succ', mul_comm]

/-- **The cycle matrix carries the `n`-th term of a companion sequence back to the first**:
`A_{0,n}·x_n = x_0`. -/
theorem IsHJCompanion.flt_hjCycleMatrix {β : ℝ} {x : ℕ → ℝ} (hx : IsHJCompanion β x)
    (n : ℕ) :
    flt (hjCycleMatrix β n : SL(2, ℤ)) (x n) = x 0 :=
  (flt_and_fltDenominator_hjCycleMatrix hx n).1

/-- **The Jacobi denominator along a companion sequence**: `j_{A_{0,n}}(x_n) = x_1x_2⋯x_n`. -/
theorem IsHJCompanion.fltDenominator_hjCycleMatrix {β : ℝ} {x : ℕ → ℝ}
    (hx : IsHJCompanion β x) (n : ℕ) :
    fltDenominator (hjCycleMatrix β n : SL(2, ℤ)) (x n) =
      ∏ i ∈ Finset.range n, x (i + 1) :=
  (flt_and_fltDenominator_hjCycleMatrix hx n).2

/-- **The inverse cycle matrix carries the first term of a companion sequence to the `n`-th**:
`A_{n,0}·x_0 = x_n`, where `A_{n,0} = A_{0,n}⁻¹` is Kopp's matrix for `m > n` in [72, Kopp (2024),
Definition 7.4, `defn:cycledata`]. -/
theorem IsHJCompanion.flt_hjCycleMatrix_inv {β : ℝ} {x : ℕ → ℝ} (hx : IsHJCompanion β x)
    (n : ℕ) :
    flt (((hjCycleMatrix β n)⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) (x 0) = x n := by
  have hden :
      fltDenominator (hjCycleMatrix β n : SL(2, ℤ))
          (x n) ≠ 0 := by
    rw [hx.fltDenominator_hjCycleMatrix, Finset.prod_ne_zero_iff]
    intro i _
    exact (hx.succ_ne_zero i)
  have h := flt_inv_flt (hjCycleMatrix β n) (x n) hden
  rw [hx.flt_hjCycleMatrix] at h
  exact h

/-- **The Jacobi denominator of the inverse cycle matrix**: `j_{A_{n,0}}(x_0) = (x_1⋯x_n)⁻¹`,
the case `m > n` of [72, Kopp (2024), Lemma 7.5, `lem:betajs`] along a companion sequence. -/
theorem IsHJCompanion.fltDenominator_hjCycleMatrix_inv {β : ℝ} {x : ℕ → ℝ}
    (hx : IsHJCompanion β x) (n : ℕ) :
    fltDenominator (((hjCycleMatrix β n)⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) (x 0) =
      (∏ i ∈ Finset.range n, x (i + 1))⁻¹ := by
  have hden :
      fltDenominator (hjCycleMatrix β n : SL(2, ℤ))
          (x n) ≠ 0 := by
    rw [hx.fltDenominator_hjCycleMatrix, Finset.prod_ne_zero_iff]
    intro i _
    exact (hx.succ_ne_zero i)
  have h := fltDenominator_inv_flt (hjCycleMatrix β n) (x n) hden
  rw [hx.flt_hjCycleMatrix, hx.fltDenominator_hjCycleMatrix] at h
  exact eq_inv_of_mul_eq_one_left h

/-- The inverse HJ cycle matrix has positive Jacobi denominator at its irrational start;
this follows from `IsHJCompanion.fltDenominator_hjCycleMatrix_inv` and
`one_lt_hjPeriod_succ`. -/
lemma fltDenominator_hjCycleMatrix_inv_pos {x : ℝ} (hx : Irrational x) (N : ℕ) :
    0 < fltDenominator
      (((hjCycleMatrix x N)⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) x := by
  have heq := (isHJCompanion_hjPeriod hx).fltDenominator_hjCycleMatrix_inv N
  rw [hjPeriod_zero] at heq
  rw [heq]
  exact inv_pos.mpr (Finset.prod_pos fun i _ =>
    lt_trans zero_lt_one (one_lt_hjPeriod_succ hx i))

/-- **The companion sequence with a prescribed first term**: `x_0` given, and
`x_{n+1} = 1/(b_n - x_n)` with the partial quotients `b_n = ⌈β_n⌉` of `β`. For `x_0 = β'` the
conjugate of a reduced quadratic irrational `β` this is Kopp's sequence `β'_n` of conjugates in
[72, Kopp (2024), Proposition 7.10, `prop:shintanidecomp`], `β'_n = A_{0,n}^{-1}·β'`
(`hjCompanion_eq_flt_inv`). -/
noncomputable def hjCompanion (β x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => ((hjLetter (hjPeriod β n) : ℝ) - hjCompanion β x₀ n)⁻¹

/-- The companion sequence starts at its prescribed first term. -/
@[simp] theorem hjCompanion_zero (β x₀ : ℝ) : hjCompanion β x₀ 0 = x₀ := rfl

/-- The recursion `x_{n+1} = 1/(b_n - x_n)` of the companion sequence. -/
theorem hjCompanion_succ (β x₀ : ℝ) (n : ℕ) :
    hjCompanion β x₀ (n + 1) = ((hjLetter (hjPeriod β n) : ℝ) - hjCompanion β x₀ n)⁻¹ := rfl

/-- **Irrationality propagates along the companion recursion**: `x_n` is irrational for every
`n` when `x_0` is, since `b - x` and `1/(b - x)` are irrational with `x`. -/
theorem irrational_hjCompanion {β x₀ : ℝ} (hx₀ : Irrational x₀) (n : ℕ) :
    Irrational (hjCompanion β x₀ n) := by
  induction n with
  | zero => simpa
  | succ n ih =>
      rw [hjCompanion_succ, irrational_inv_iff, irrational_intCast_sub_iff]
      exact ih

/-- **An irrational start gives a companion sequence**: `x_{n+1} ≠ 0` and
`x_n = b_n - 1/x_{n+1}`, the nonvanishing from `irrational_hjCompanion`. No hypothesis on `β`
is needed: the recursion only reads its partial quotients. -/
theorem isHJCompanion_hjCompanion {β x₀ : ℝ} (hx₀ : Irrational x₀) :
    IsHJCompanion β (hjCompanion β x₀) := by
  intro n
  constructor
  · exact (irrational_hjCompanion hx₀ (n + 1)).ne_zero
  · rw [hjCompanion_succ, one_div, inv_inv]
    ring

/-- **The companion sequence is the inverse cycle matrix applied to its first term**:
`x_n = A_{0,n}^{-1}·x_0` for irrational `x_0`, from `IsHJCompanion.flt_hjCycleMatrix_inv`. -/
theorem hjCompanion_eq_flt_inv {β x₀ : ℝ} (hx₀ : Irrational x₀) (n : ℕ) :
    hjCompanion β x₀ n =
      flt (((hjCycleMatrix β n)⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) x₀ := by
  simpa only [hjCompanion_zero] using
    ((isHJCompanion_hjCompanion hx₀).flt_hjCycleMatrix_inv n).symm

/-- **The cycle matrix carries the `n`-th rotated number back to `β`**: `A_{0,n}·β_n = β`;
`IsHJCompanion.flt_hjCycleMatrix` at the rotated numbers. -/
theorem flt_hjCycleMatrix {β : ℝ} (hβ : Irrational β) (n : ℕ) :
    flt (hjCycleMatrix β n : SL(2, ℤ)) (hjPeriod β n) = β :=
  (isHJCompanion_hjPeriod hβ).flt_hjCycleMatrix n

/-- **The Jacobi denominator along the cycle**: `j_{A_{0,n}}(β_n) = β_1β_2⋯β_n`, the case `m = 0`
of [72, Kopp (2024), Lemma 7.5, `lem:betajs`]; `IsHJCompanion.fltDenominator_hjCycleMatrix` at
the rotated numbers. -/
theorem fltDenominator_hjCycleMatrix {β : ℝ} (hβ : Irrational β) (n : ℕ) :
    fltDenominator (hjCycleMatrix β n : SL(2, ℤ))
      (hjPeriod β n) = ∏ i ∈ Finset.range n, hjPeriod β (i + 1) :=
  (isHJCompanion_hjPeriod hβ).fltDenominator_hjCycleMatrix n

/-- **The Jacobi denominator along the cycle is positive**, since every factor `β_i` with `i ≥ 1`
exceeds `1`. This supplies the initial-period hypothesis for the cocycle product
(`WordSigmaSVisits.period_pos`, `SICs.Cocycle.Word.Basic`). -/
theorem fltDenominator_hjCycleMatrix_pos {β : ℝ} (hβ : Irrational β) (n : ℕ) :
    0 < fltDenominator (hjCycleMatrix β n : SL(2, ℤ))
      (hjPeriod β n) := by
  rw [fltDenominator_hjCycleMatrix hβ n]
  apply Finset.prod_pos
  intro i _
  exact lt_trans zero_lt_one (one_lt_hjPeriod_succ hβ i)

/-! ### The cycle matrix is the canonical Hirzebruch--Jung word

An AFK25 word ends in a bare power of `T`; Kopp's purely periodic word ends in `S`. Appending the
letter `0` reconciles the two, and the resulting list is AFK25-shaped because its interior letters
are partial quotients of numbers above `1`. Since `hjStep` reads the head of such a word off its
matrix, one `hjStep` is one rotation. -/

/-- The cycle matrix is the matrix of the word `[b_0, …, b_{n-1}, 0]`: Kopp's word `T^{b_0}S ⋯
T^{b_{n-1}}S` written in the AFK25 convention, which ends in a power of `T`. -/
theorem wordToMatrix_hjLetters (β : ℝ) (n : ℕ) :
    wordToMatrix (hjLetters β n ++ [0]) = hjCycleMatrix β n := by
  induction n generalizing β with
  | zero => simp [wordToMatrix]
  | succ n ih =>
      rw [hjLetters_succ, List.cons_append,
        wordToMatrix_cons_of_ne_nil _ _ (List.append_ne_nil_of_right_ne_nil _ (by simp)), ih,
        hjCycleMatrix_succ]

/-- The cycle matrix is the letter word of the partial quotients:
`A_{0,n} = ∏_{m<n} T^{b_m}S = letterWord [b_0, …, b_{n-1}]`. -/
theorem hjCycleMatrix_eq_letterWord (β : ℝ) (n : ℕ) :
    hjCycleMatrix β n = letterWord (hjLetters β n) := by
  rw [letterWord_eq_wordToMatrix, wordToMatrix_hjLetters]

/-- **The word of the cycle matrix is AFK25-shaped.** Only irrationality of `β` is needed: the
interior letters are the partial quotients of `β_1, …, β_{n-1}`, all above `1`. -/
theorem isHJWord_hjLetters {β : ℝ} (hβ : Irrational β) {n : ℕ} (hn : n ≠ 0) :
    IsHJWord (hjLetters β n ++ [0]) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  constructor
  · simp
  · intro x hx
    rw [hjLetters_succ, List.cons_append, List.drop_succ_cons, List.drop_zero,
      List.dropLast_concat] at hx
    exact two_le_of_mem_hjLetters (irrational_hjRotate hβ) (one_lt_hjRotate hβ) m x hx

/-- **The word of the cycle matrix is an AFK25 *tail*** once `β` itself is above `1`, so that even
the leading letter `b_0` is at least `2`. This is the shape `hjStep_hjCycleMatrix` peels. -/
theorem isHJTail_hjLetters {β : ℝ} (hβ : Irrational β) (hβ1 : 1 < β) (n : ℕ) :
    IsHJTail (hjLetters β n ++ [0]) := by
  constructor
  · exact List.append_ne_nil_of_right_ne_nil _ (by simp)
  · intro x hx
    rw [List.dropLast_concat] at hx
    exact two_le_of_mem_hjLetters hβ hβ1 n x hx

/-- **The cycle matrix has positive lower-left entry** for `n ≥ 1`, so the word algorithm and the
word-chained cocycle both accept it as a seed. -/
theorem lowerLeft_hjCycleMatrix_pos {β : ℝ} (hβ : Irrational β) {n : ℕ} (hn : n ≠ 0) :
    0 < (hjCycleMatrix β n) 1 0 := by
  rw [← wordToMatrix_hjLetters]
  exact wordToMatrix_lowerLeft_pos (isHJWord_hjLetters hβ hn)

/-- **The cycle matrix has nonnegative lower-left entry** for every `n`: zero at `n = 0`, where
it is the identity, and positive otherwise (`lowerLeft_hjCycleMatrix_pos`). This is the seed
hypothesis of the word-chained cocycle `SICs.Cocycle.Word.Basic.wordSigmaS` and of the word
accumulator `SICs.SL2Z.WordAccumulator.wordRademacher`. -/
theorem lowerLeft_hjCycleMatrix_nonneg {β : ℝ} (hβ : Irrational β) (n : ℕ) :
    0 ≤ (hjCycleMatrix β n) 1 0 := by
  cases n with
  | zero =>
      rw [hjCycleMatrix_zero, Matrix.SpecialLinearGroup.coe_one]
      simp
  | succ n =>
      exact (lowerLeft_hjCycleMatrix_pos hβ (Nat.succ_ne_zero n)).le

/-- **One `hjStep` is one rotation**: peeling the canonical word of `A_{0,n+1}` returns the
leading partial quotient `b_0` and the cycle matrix `A_{1,n+1}`, which is the length-`n` cycle
matrix at `β_1`. Chaining this identity is what makes the word-chained cocycle
`SICs.Cocycle.Word.Basic.wordSigmaS`, seeded at `A_{0,n}`, visit exactly Kopp's matrices `A_{m,n}`
and evaluate its factors at Kopp's rotated numbers `β_m`. -/
theorem hjStep_hjCycleMatrix {β : ℝ} (hβ : Irrational β) (n : ℕ) :
    hjStep (hjCycleMatrix β (n + 1)) = (hjLetter β, hjCycleMatrix (hjRotate β) n) := by
  have htail :=
    isHJTail_hjLetters (irrational_hjRotate hβ) (one_lt_hjRotate hβ) n
  rw [← wordToMatrix_hjLetters, hjLetters_succ, List.cons_append,
    hjStep_wordToMatrix_cons htail, wordToMatrix_hjLetters]

/-- **The word accumulator of a cycle matrix is the sum of its letters minus three each**:
`W(A_{0,n}) = Σ_{m<n} (b_m - 3)`, where `W = SICs.SL2Z.WordAccumulator.wordRademacher`.
Each `hjStep` peels one rotation (`hjStep_hjCycleMatrix`) and contributes `b_m - 3`.
The terminal matrix is the identity, whose upper-right entry `0` is the base value. The resulting
partial-quotient sum is the one in
[72, Kopp (2024), Proposition 7.21, `prop:globalphase`]. -/
theorem wordRademacher_hjCycleMatrix {β : ℝ} (hβ : Irrational β) (n : ℕ)
    (h0 : 0 ≤ (hjCycleMatrix β n) 1 0) :
    wordRademacher (hjCycleMatrix β n) h0 =
      ∑ m ∈ Finset.range n, (hjLetter (hjPeriod β m) - 3) := by
  induction n generalizing β with
  | zero =>
      have hz : (hjCycleMatrix β 0) 1 0 = 0 := by
        rw [hjCycleMatrix_zero, Matrix.SpecialLinearGroup.coe_one]
        simp
      rw [wordRademacher_of_lowerLeft_eq_zero _ h0 hz, hjCycleMatrix_zero,
        Matrix.SpecialLinearGroup.coe_one]
      simp
  | succ n ih =>
      have hz : (hjCycleMatrix β (n + 1)) 1 0 ≠ 0 :=
        (lowerLeft_hjCycleMatrix_pos hβ (Nat.succ_ne_zero n)).ne'
      have hstep := hjStep_hjCycleMatrix hβ n
      have hfst : (hjStep (hjCycleMatrix β (n + 1))).1 = hjLetter β := by
        simpa using congrArg Prod.fst hstep
      have h0N := lowerLeft_hjCycleMatrix_nonneg (irrational_hjRotate hβ) n
      rw [wordRademacher_step h0 hz (congrArg Prod.snd hstep) h0N,
        hfst, ih (irrational_hjRotate hβ) h0N, Finset.sum_range_succ']
      simp_rw [hjPeriod_succ_left]
      rw [hjPeriod_zero]
      abel

/-! ### Purely periodic expansions

Kopp's cycle data asks that the expansion close up: `β_ℓ = β` for some `ℓ ≥ 1`. That equation
says that `β` is a periodic point of the rotation, `Function.IsPeriodicPt hjRotate ℓ β`, and the
first two lemmas are Mathlib's periodic-point API read through `hjPeriod`. Everything the
Stark-unit comparison needs follows from that one equation. The matrix `P = A_{0,ℓ}` then fixes
`β`, the whole sequence of rotated numbers and partial quotients becomes `ℓ`-periodic, the cycle
matrix of `k` full periods is `P^k` — Kopp's `A = P^k` — and the Jacobi denominator of `P` at `β`
is the product `β_0β_1⋯β_{ℓ-1}` of [72, Kopp (2024), Lemma 7.6, `lem:betaunit`], because
periodicity turns the product `β_1⋯β_ℓ` of `fltDenominator_hjCycleMatrix` into it.

Which `β` have a purely periodic expansion is a separate matter: exactly the real quadratic
numbers with `0 < β' < 1 < β` ([72, Kopp (2024), Proposition 7.2, `prop:quadhj`]), proved in
`SICs.Quadratic.ReducedForms`. -/

/-- **Periodicity propagates**: `β_{ℓ+n} = β_n` once `β_ℓ = β`. -/
theorem hjPeriod_add_of_hjPeriod_eq {β : ℝ} {ℓ : ℕ} (hℓ : hjPeriod β ℓ = β) (n : ℕ) :
    hjPeriod β (ℓ + n) = hjPeriod β n := by
  have hper : Function.IsPeriodicPt hjRotate ℓ β := hℓ
  change hjRotate^[ℓ + n] β = hjRotate^[n] β
  rw [Function.iterate_add_apply]
  exact (hper.apply_iterate n).eq

/-- **The minimal period is a period**: `β_ℓ = β` for `ℓ = minimalPeriod ℛ β`, Mathlib's
`Function.isPeriodicPt_minimalPeriod` read through `hjPeriod`. It holds for every `β`, since a
nonperiodic point has minimal period `0` and `β_0 = β`. -/
theorem hjPeriod_minimalPeriod (β : ℝ) :
    hjPeriod β (Function.minimalPeriod hjRotate β) = β :=
  Function.isPeriodicPt_minimalPeriod hjRotate β

/-- **Every multiple of a period is a period**: `β_{ℓk} = β`, which is why Kopp may pass from `P`
to `A = P^k` without leaving the cycle. -/
theorem hjPeriod_mul_of_hjPeriod_eq {β : ℝ} {ℓ : ℕ} (hℓ : hjPeriod β ℓ = β) (k : ℕ) :
    hjPeriod β (ℓ * k) = β :=
  have hper : Function.IsPeriodicPt hjRotate ℓ β := hℓ
  (hper.mul_const k).eq

/-- **The cycle matrix of `k` full periods is `P^k`**: Kopp's `A = P^k` of [72, Kopp (2024),
Definition 7.4, `defn:cycledata`], where `P = A_{0,ℓ}`. -/
theorem hjCycleMatrix_mul_of_hjPeriod_eq {β : ℝ} {ℓ : ℕ} (hℓ : hjPeriod β ℓ = β) (k : ℕ) :
    hjCycleMatrix β (ℓ * k) = hjCycleMatrix β ℓ ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show ℓ * (k + 1) = ℓ * k + ℓ by ring, hjCycleMatrix_add,
        hjPeriod_mul_of_hjPeriod_eq hℓ k, ih, pow_succ]

/-- **`P` fixes `β`**: the cycle matrix of one full period is a fixed-point matrix for `β`, which
is what makes `⟨-I, P⟩` its stabilizer in [72, Kopp (2024), Proposition 7.7,
`prop:betatogamma`]. -/
theorem flt_hjCycleMatrix_of_hjPeriod_eq {β : ℝ} (hβ : Irrational β) {ℓ : ℕ}
    (hℓ : hjPeriod β ℓ = β) :
    flt (hjCycleMatrix β ℓ : SL(2, ℤ)) β = β := by
  calc
    flt (hjCycleMatrix β ℓ : SL(2, ℤ)) β =
        flt (hjCycleMatrix β ℓ : SL(2, ℤ))
          (hjPeriod β ℓ) := congrArg _ hℓ.symm
    _ = β := flt_hjCycleMatrix hβ ℓ

/-- **The unit product of a purely periodic expansion**: `j_P(β) = β_0β_1⋯β_{ℓ-1}`. This is the
product of [72, Kopp (2024), Lemma 7.6, `lem:betaunit`], obtained from
`fltDenominator_hjCycleMatrix`'s product `β_1⋯β_ℓ` by replacing its last factor `β_ℓ` with
`β_0 = β`. Kopp's further identification of the product with the fundamental totally positive
unit of the multiplier ring of `βℤ + ℤ` is not proved here; what is proved is that the product is
the Jacobi denominator at `β` of a matrix fixing `β`, hence an eigenvalue of `P`. -/
theorem fltDenominator_hjCycleMatrix_of_hjPeriod_eq {β : ℝ} (hβ : Irrational β) {ℓ : ℕ}
    (hℓ : hjPeriod β ℓ = β) :
    fltDenominator (hjCycleMatrix β ℓ : SL(2, ℤ)) β =
      ∏ i ∈ Finset.range ℓ, hjPeriod β i := by
  calc
    fltDenominator (hjCycleMatrix β ℓ : SL(2, ℤ)) β =
        fltDenominator (hjCycleMatrix β ℓ : SL(2, ℤ))
          (hjPeriod β ℓ) := congrArg _ hℓ.symm
    _ = ∏ i ∈ Finset.range ℓ, hjPeriod β (i + 1) :=
      fltDenominator_hjCycleMatrix hβ ℓ
    _ = ∏ i ∈ Finset.range ℓ, hjPeriod β i := by
      have hzero : hjPeriod β 0 ≠ 0 := by
        rw [hjPeriod_zero]
        simpa using hβ.ne_int 0
      apply mul_right_cancel₀ hzero
      calc
        (∏ i ∈ Finset.range ℓ, hjPeriod β (i + 1)) * hjPeriod β 0 =
            ∏ i ∈ Finset.range (ℓ + 1), hjPeriod β i :=
          (Finset.prod_range_succ' (hjPeriod β) ℓ).symm
        _ = (∏ i ∈ Finset.range ℓ, hjPeriod β i) * hjPeriod β ℓ :=
          Finset.prod_range_succ (hjPeriod β) ℓ
        _ = (∏ i ∈ Finset.range ℓ, hjPeriod β i) * hjPeriod β 0 := by
          rw [hℓ, hjPeriod_zero]

/-- **The Jacobi denominator of a closed cycle is positive at `β`**: `j_{A_{0,ℓ}}(β) > 0` once
`β_ℓ = β`, since it is `j_{A_{0,ℓ}}(β_ℓ)` (`fltDenominator_hjCycleMatrix_pos`). This is the
domain condition `β ∈ D_{A_{0,ℓ}}` of the real cocycle at a purely periodic point. -/
theorem fltDenominator_hjCycleMatrix_pos_of_hjPeriod_eq {β : ℝ} (hβ : Irrational β) {ℓ : ℕ}
    (hℓ : hjPeriod β ℓ = β) :
    0 < fltDenominator (hjCycleMatrix β ℓ : SL(2, ℤ)) β := by
  have h := fltDenominator_hjCycleMatrix_pos hβ ℓ
  rwa [hℓ] at h

/-- **A closed cycle fixes the first term of a periodic companion sequence**: `A_{0,ℓ}·x_0 = x_0`
when `x_ℓ = x_0`, from `IsHJCompanion.flt_hjCycleMatrix`; for the conjugates of a real
quadratic `β` this is `A_{0,ℓ}·β' = β'`. -/
theorem IsHJCompanion.flt_hjCycleMatrix_of_eq {β : ℝ} {x : ℕ → ℝ} (hx : IsHJCompanion β x)
    {ℓ : ℕ} (hℓ : x ℓ = x 0) :
    flt (hjCycleMatrix β ℓ : SL(2, ℤ)) (x 0) = x 0 := by
  have h := hx.flt_hjCycleMatrix ℓ
  rwa [hℓ] at h

/-- **The Jacobi denominator of a closed cycle along a periodic companion sequence**:
`j_{A_{0,ℓ}}(x_0) = x_1⋯x_ℓ` when `x_ℓ = x_0`, from
`IsHJCompanion.fltDenominator_hjCycleMatrix`; for the conjugates this is the conjugate
`ε' = β'_1⋯β'_ℓ` of the unit product of [72, Kopp (2024), Lemma 7.6, `lem:betaunit`]. -/
theorem IsHJCompanion.fltDenominator_hjCycleMatrix_of_eq {β : ℝ} {x : ℕ → ℝ}
    (hx : IsHJCompanion β x) {ℓ : ℕ} (hℓ : x ℓ = x 0) :
    fltDenominator (hjCycleMatrix β ℓ : SL(2, ℤ)) (x 0) =
      ∏ i ∈ Finset.range ℓ, x (i + 1) := by
  have h := hx.fltDenominator_hjCycleMatrix ℓ
  rwa [hℓ] at h

/-! ### Kopp's global phase sum

The exponential prefactor that the Stark-unit comparison of [72, Kopp (2024), Proposition 7.20,
`prop:almost`] accumulates along a cycle of length `N` is `e(γ(A)/24)` with

$$
\gamma(A) = \sum_{n=0}^{N-1}\left(\beta_n - 3 + \beta_n^{-1}\right),
\qquad A = A_{0,N},
$$

and [72, Kopp (2024), Proposition 7.21, `prop:globalphase`] evaluates it. The evaluation rests on
the one-step identity `1/β_{n+1} = b_n - β_n`, which is the rotation read backwards: pairing `β_n`
with `1/β_{n+1}` turns the sum into `Σ (b_n - 3)` once the cycle closes (`β_N = β`, so that the
leftover term `1/β_0` is `1/β_N`). That sum is the word accumulator `W(A_{0,N})`
(`wordRademacher_hjCycleMatrix`), which `SICs.SL2Z.RademacherWord` identifies with the Rademacher
invariant at positive trace. -/

/-- **The reciprocal of the next rotated number**: `1/β_{n+1} = b_n - β_n`, the rotation
`β_{n+1} = 1/(⌈β_n⌉ - β_n)` read backwards. Unconditional, since `(x⁻¹)⁻¹ = x` in a field. -/
theorem inv_hjPeriod_succ (β : ℝ) (n : ℕ) :
    (hjPeriod β (n + 1))⁻¹ = (hjLetter (hjPeriod β n) : ℝ) - hjPeriod β n := by
  rw [hjPeriod_succ, hjRotate, inv_inv]

/-- Kopp's global phase sum `γ(A) = Σ_{n<N} (β_n - 3 + β_n⁻¹)` of [72, Kopp (2024),
Proposition 7.20, `prop:almost`], attached to the cycle matrix `A = A_{0,N}` through its length
`N`; Kopp's `N = kℓ`, `k` full periods of the minimal period `ℓ`. -/
noncomputable def hjGamma (β : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (hjPeriod β n - 3 + (hjPeriod β n)⁻¹)

/-- Reindexes the reciprocal terms around a closed Hirzebruch--Jung cycle. -/
private theorem sum_inv_hjPeriod_eq_sum_hjLetter_sub {β : ℝ} {N : ℕ}
    (hN : hjPeriod β N = β) :
    ∑ n ∈ Finset.range N, (hjPeriod β n)⁻¹ =
      ∑ n ∈ Finset.range N, ((hjLetter (hjPeriod β n) : ℝ) - hjPeriod β n) := by
  cases N with
  | zero => simp
  | succ M =>
      rw [Finset.sum_range_succ']
      simp_rw [inv_hjPeriod_succ]
      rw [hjPeriod_zero, Finset.sum_range_succ]
      congr 1
      exact (congrArg Inv.inv hN).symm.trans (inv_hjPeriod_succ β M)

/-- **[72, Kopp (2024), Proposition 7.21, `prop:globalphase`], first identity**: along a closed
cycle, `γ(A) = -3N + Σ_{n<N} b_n`, stated as `Σ_{n<N} (b_n - 3)`. Pair `β_n` with `1/β_{n+1} =
b_n - β_n` (`inv_hjPeriod_succ`); the unpaired `1/β_0` is `1/β_N` because the cycle closes. -/
@[source "72, Proposition 7.21, p. 74, prop:globalphase (first identity)"]
theorem hjGamma_eq_sum_hjLetters {β : ℝ} {N : ℕ} (hN : hjPeriod β N = β) :
    hjGamma β N = ∑ n ∈ Finset.range N, ((hjLetter (hjPeriod β n) : ℝ) - 3) := by
  unfold hjGamma
  rw [Finset.sum_add_distrib, sum_inv_hjPeriod_eq_sum_hjLetter_sub hN,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- **[72, Kopp (2024), Proposition 7.21, `prop:globalphase`], the word form**: along a closed
cycle, `γ(A) = W(A)` for the word accumulator `W = SICs.SL2Z.WordAccumulator.wordRademacher`,
which is Kopp's `Φ(P) - 3` in the Rademacher function `Φ` (see `SICs.SL2Z.RademacherWord`). Combines
`hjGamma_eq_sum_hjLetters` with `wordRademacher_hjCycleMatrix`. -/
theorem hjGamma_eq_wordRademacher {β : ℝ} (hβ : Irrational β) {N : ℕ} (hN : hjPeriod β N = β)
    (h0 : 0 ≤ (hjCycleMatrix β N) 1 0) :
    hjGamma β N = (wordRademacher (hjCycleMatrix β N) h0 : ℝ) := by
  rw [hjGamma_eq_sum_hjLetters hN, wordRademacher_hjCycleMatrix hβ N h0]
  push_cast
  rfl

end SIC
